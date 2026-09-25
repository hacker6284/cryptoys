import * as THREE from "three";

/**
 * SPIKE adapter: adopt a cubing.js TwistyPlayer 3D puzzle into our scene.
 *
 * Real cubing.js calls used (verified against js.cubing.net / TwistyPlayer
 * source, cubing@0.63.x):
 *   import { TwistyPlayer } from "https://cdn.cubing.net/v0/js/cubing/twisty"
 *   new TwistyPlayer({ puzzle, alg, hintFacelets, backView, background, controlPanel })
 *   player.experimentalCurrentThreeJSPuzzleObject(onRenderScheduled) → Promise<Object3D>
 *   player.play() / player.pause() / player.jumpToStart()
 *   player.alg = "…"
 *   player.tempoScale = n
 *   player.experimentalModel.indexer.get()
 *   player.experimentalModel.detailedTimelineInfo.get()
 *   player.experimentalModel.timestampRequest.set(ms)
 *
 * `experimentalCurrentThreeJSPuzzleObject` is deprecated/experimental. Changing
 * `player.puzzle` leaves the returned Object3D stale — recreate the player.
 */

export const CUBING_TWISTY_URL = "https://cdn.cubing.net/v0/js/cubing/twisty";

export const PUZZLES = {
    "3x3x3": {
        id: "3x3x3",
        label: "3×3×3",
        alg: "R U R' U R U2' R'",
    },
    megaminx: {
        id: "megaminx",
        label: "Megaminx",
        alg: "R++ D++ R-- D-- U",
    },
    pyraminx: {
        id: "pyraminx",
        label: "Pyraminx",
        alg: "R U R' U' L' U L",
    },
};

export const PUZZLE_IDS = Object.keys(PUZZLES);

let twistyMod = null;

export async function loadTwisty() {
    if (!twistyMod) twistyMod = await import(CUBING_TWISTY_URL);
    return twistyMod;
}

function hidePlayerHost(player) {
    // Must stay in-flow and not `display:none` / `visibility:hidden`.
    // TwistyPlayer never builds the 3D Object3D if the vantage canvas is
    // treated as hidden, so experimentalCurrentThreeJSPuzzleObject hangs.
    player.setAttribute("data-cubing-spike", "host");
    player.style.cssText = [
        "position:fixed",
        "left:0",
        "bottom:0",
        "width:80px",
        "height:56px",
        "opacity:0.02",
        "pointer-events:none",
        "overflow:hidden",
        "z-index:0",
    ].join(";");
    document.body.append(player);
}

function withTimeout(promise, ms, label) {
    return new Promise((resolve, reject) => {
        const timer = setTimeout(() => {
            reject(new Error(`${label} timed out after ${ms}ms`));
        }, ms);
        promise.then(
            (value) => {
                clearTimeout(timer);
                resolve(value);
            },
            (err) => {
                clearTimeout(timer);
                reject(err);
            },
        );
    });
}

function meshBox(object) {
    const box = new THREE.Box3();
    object.updateMatrixWorld(true);
    object.traverse((node) => {
        if (!node.isMesh || !node.visible || !node.geometry) return;
        const geo = node.geometry;
        if (!geo.boundingBox) geo.computeBoundingBox();
        if (!geo.boundingBox) return;
        const next = geo.boundingBox.clone().applyMatrix4(node.matrixWorld);
        if (!next.isEmpty()) box.union(next);
    });
    return box;
}

function centerAndFit(object, edge) {
    object.updateMatrixWorld(true);
    let box = meshBox(object);
    if (box.isEmpty()) box = new THREE.Box3().setFromObject(object);
    const size = new THREE.Vector3();
    const center = new THREE.Vector3();
    box.getSize(size);
    box.getCenter(center);
    if (Number.isFinite(center.x)) object.position.sub(center);
    let max = Math.max(size.x, size.y, size.z);
    if (!Number.isFinite(max) || max < 1e-6) max = 1;
    object.scale.multiplyScalar(edge / max);
    object.updateMatrixWorld(true);
    const fitted = meshBox(object);
    const fittedSize = new THREE.Vector3();
    fitted.getSize(fittedSize);
    const fittedMax = Math.max(fittedSize.x, fittedSize.y, fittedSize.z);
    if (Number.isFinite(fittedMax) && fittedMax > 1e-6 && (fittedMax < edge * 0.4 || fittedMax > edge * 2.2)) {
        object.scale.multiplyScalar(edge / fittedMax);
        object.updateMatrixWorld(true);
    }
    return { size: size.clone(), nativeMax: max, fittedMax: Math.max(fittedSize.x, fittedSize.y, fittedSize.z) || 0 };
}

function sleep(ms) {
    return new Promise((resolve) => setTimeout(resolve, ms));
}

function enableShadows(root) {
    root.traverse((node) => {
        if (!node.isMesh) return;
        node.castShadow = true;
        node.receiveShadow = true;
    });
}

export function inspectMaterials(root) {
    const counts = new Map();
    let meshCount = 0;
    let lit = 0;
    root.traverse((node) => {
        if (!node.isMesh) return;
        meshCount += 1;
        const mats = Array.isArray(node.material) ? node.material : [node.material];
        for (const mat of mats) {
            if (!mat) continue;
            const type = mat.type || mat.constructor?.name || "unknown";
            counts.set(type, (counts.get(type) || 0) + 1);
            if (mat.isMeshStandardMaterial || mat.isMeshPhysicalMaterial) lit += 1;
        }
    });
    return {
        meshCount,
        standardLike: lit,
        types: [...counts.entries()].sort((a, b) => b[1] - a[1]),
    };
}

export function describeThreeSkew(object) {
    return {
        instanceofOurObject3D: object instanceof THREE.Object3D,
        constructorName: object?.constructor?.name || "unknown",
        ourRevision: THREE.REVISION,
    };
}

/**
 * Seat/lift hierarchy:
 *   group  — world pose (shelf / table / toy-director fly). Translate this.
 *   lift   — local Y hook for lift-off-felt without fighting cubing animation.
 *   puzzle — cubing.js Object3D. Do not keyframe this; TwistyPlayer owns motion.
 */
export async function createTwistyRig({
    puzzle = "3x3x3",
    edge = 0.057,
    alg,
    tempoScale = 1.4,
    onRenderScheduled,
    onStage,
    adoptTimeoutMs = 20000,
} = {}) {
    const spec = PUZZLES[puzzle] || PUZZLES["3x3x3"];
    onStage?.("import cubing/twisty");
    const { TwistyPlayer } = await loadTwisty();
    onStage?.("construct TwistyPlayer");
    const player = new TwistyPlayer({
        puzzle: spec.id,
        alg: alg ?? spec.alg,
        hintFacelets: "none",
        backView: "none",
        background: "none",
        controlPanel: "none",
        visualization: spec.id === "3x3x3" ? "3D" : "PG3D",
        tempoScale,
    });
    hidePlayerHost(player);

    const group = new THREE.Group();
    group.name = "twisty-seat";
    const lift = new THREE.Group();
    lift.name = "twisty-lift";
    group.add(lift);

    onStage?.("experimentalCurrentThreeJSPuzzleObject");
    let puzzleObject = null;
    let adoptError = null;
    let firstPaint = null;
    const painted = new Promise((resolve) => {
        firstPaint = resolve;
    });
    try {
        puzzleObject = await withTimeout(
            player.experimentalCurrentThreeJSPuzzleObject(() => {
                firstPaint?.();
                onRenderScheduled?.();
            }),
            adoptTimeoutMs,
            "experimentalCurrentThreeJSPuzzleObject",
        );
        await Promise.race([painted, sleep(1500)]);
        await new Promise((resolve) => requestAnimationFrame(resolve));
        await new Promise((resolve) => requestAnimationFrame(resolve));
    } catch (err) {
        adoptError = err;
        player.style.cssText = [
            "position:fixed",
            "right:20px",
            "top:72px",
            "width:220px",
            "height:160px",
            "z-index:5",
            "background:#111",
            "border:1px solid rgba(255,255,255,0.12)",
            "border-radius:12px",
        ].join(";");
        player.removeAttribute("data-cubing-spike");
    }

    let framed = { size: new THREE.Vector3(), nativeMax: 0 };
    let look = { meshCount: 0, standardLike: 0, types: [] };
    let skew = describeThreeSkew(puzzleObject);
    if (puzzleObject) {
        puzzleObject.removeFromParent();
        puzzleObject.position.set(0, 0, 0);
        puzzleObject.rotation.set(0, 0, 0);
        puzzleObject.quaternion.identity();
        puzzleObject.scale.set(1, 1, 1);
        lift.add(puzzleObject);
        framed = centerAndFit(puzzleObject, edge);
        enableShadows(puzzleObject);
        look = inspectMaterials(puzzleObject);
        skew = describeThreeSkew(puzzleObject);
    }

    let disposed = false;

    async function timeline() {
        const [indexer, info] = await Promise.all([
            player.experimentalModel.indexer.get(),
            player.experimentalModel.detailedTimelineInfo.get(),
        ]);
        return { indexer, info };
    }

    async function status() {
        try {
            const { indexer, info } = await timeline();
            return {
                timestamp: info.timestamp,
                duration: indexer.algDuration(),
                index: indexer.timestampToIndex(info.timestamp),
                total: indexer.numAnimatedLeaves(),
            };
        } catch {
            return { timestamp: 0, duration: 0, index: 0, total: 0 };
        }
    }

    return {
        group,
        lift,
        puzzle: puzzleObject,
        player,
        puzzleId: spec.id,
        alg: String(alg ?? spec.alg),
        framed,
        look,
        skew,
        fallback: Boolean(adoptError),
        fallbackError: adoptError ? String(adoptError.message || adoptError) : null,
        play() {
            player.play();
        },
        pause() {
            player.pause();
        },
        reset() {
            player.pause();
            player.jumpToStart();
        },
        async step() {
            player.pause();
            const { indexer, info } = await timeline();
            const total = indexer.numAnimatedLeaves();
            if (!total) return { index: 0, total: 0 };
            let index = indexer.timestampToIndex(info.timestamp);
            const start = indexer.indexToMoveStartTimestamp(index);
            const end = start + indexer.moveDuration(index);
            if (info.timestamp >= end - 2) {
                index = Math.min(index + 1, total - 1);
            }
            const nextEnd = indexer.indexToMoveStartTimestamp(index) + indexer.moveDuration(index);
            player.experimentalModel.timestampRequest.set(nextEnd);
            return { index, total };
        },
        setAlg(next) {
            player.alg = next;
        },
        setTempo(scale) {
            player.tempoScale = scale;
        },
        setLifted(on, offset = 0.12) {
            lift.position.y = on ? offset : 0;
        },
        status,
        dispose() {
            if (disposed) return;
            disposed = true;
            player.pause();
            lift.remove(puzzleObject);
            if (group.parent) group.parent.remove(group);
            player.remove();
        },
    };
}
