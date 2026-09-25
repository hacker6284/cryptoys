import * as THREE from "three";

/**
 * Adopt a cubing.js TwistyPlayer puzzle into the playroom scene.
 *
 * Verified calls (js.cubing.net / cubing@0.63.x):
 *   import { TwistyPlayer } from "https://cdn.cubing.net/v0/js/cubing/twisty"
 *   new TwistyPlayer({ puzzle, alg, hintFacelets, backView, background, controlPanel })
 *   player.experimentalCurrentThreeJSPuzzleObject(cb) → Promise<Object3D>
 *   player.play() / player.pause() / player.jumpToStart()
 *   player.alg = "…"
 *   player.experimentalSetupAlg = "…"
 *   player.tempoScale = n
 *   player.experimentalModel.indexer.get()
 *   player.experimentalModel.detailedTimelineInfo.get()
 *   player.experimentalModel.timestampRequest.set(ms)
 *
 * `experimentalCurrentThreeJSPuzzleObject` is experimental/deprecated.
 * Changing `player.puzzle` leaves the Object3D stale — recreate the player
 * (`swapPuzzle` / `createTwistyRig`). Never write the adopted object's
 * matrix; scale `fit` only. Host must stay paintable (never display:none).
 *
 * `object instanceof THREE.Object3D` is false: cubing ships its own three
 * copy. Meshes still render. Adopted materials are MeshBasicMaterial —
 * beauty/material retarget is later.
 */

export const CUBING_TWISTY_URL = "https://cdn.cubing.net/v0/js/cubing/twisty";

export const PUZZLES = {
    "3x3x3": { id: "3x3x3", label: "3×3×3", alg: "" },
    megaminx: { id: "megaminx", label: "Megaminx", alg: "" },
    pyraminx: { id: "pyraminx", label: "Pyraminx", alg: "" },
};

export const PUZZLE_IDS = Object.keys(PUZZLES);

let twistyMod = null;

export async function loadTwisty() {
    if (!twistyMod) twistyMod = await import(CUBING_TWISTY_URL);
    return twistyMod;
}

export function createTwistySeat({ edge = 0.057 } = {}) {
    const group = new THREE.Group();
    group.name = "twisty-seat";
    const lift = new THREE.Group();
    lift.name = "twisty-lift";
    const fit = new THREE.Group();
    fit.name = "twisty-fit";
    group.add(lift);
    lift.add(fit);
    return { group, lift, fit, edge, placeholder: null };
}

function hidePlayerHost(player) {
    player.classList.add("twisty-host");
    player.setAttribute("data-twisty-host", "1");
    player.setAttribute("aria-hidden", "true");
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

function sleep(ms) {
    return new Promise((resolve) => setTimeout(resolve, ms));
}

function frame() {
    return new Promise((resolve) => requestAnimationFrame(resolve));
}

function meshBox(object) {
    const box = new THREE.Box3();
    object.updateMatrixWorld(true);
    try {
        box.setFromObject(object);
    } catch {
        // two three.js copies can throw inside setFromObject
    }
    if (!box.isEmpty()) return box;
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

function frameInWrapper(wrapper, object, edge) {
    wrapper.position.set(0, 0, 0);
    wrapper.scale.set(1, 1, 1);
    wrapper.updateMatrixWorld(true);
    const box = meshBox(object);
    const size = new THREE.Vector3();
    const center = new THREE.Vector3();
    box.getSize(size);
    box.getCenter(center);
    const max = Math.max(size.x, size.y, size.z);
    const nativeMax = Number.isFinite(max) && max > 1e-6 ? max : 1;
    const scale = edge / nativeMax;
    wrapper.scale.setScalar(scale);
    if (Number.isFinite(center.x)) {
        wrapper.position.set(-center.x * scale, -center.y * scale, -center.z * scale);
    }
    wrapper.updateMatrixWorld(true);
    return { size: size.clone(), nativeMax, fittedMax: edge };
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

function noopHighlight() {}

/**
 * Seat/lift hierarchy:
 *   group  — world pose (shelf / table / toy-director fly). Translate this.
 *   lift   — local Y hook. Playroom #25 lifts `group` for turns; this stays
 *            available so cubing animation and room motion need not share
 *            a transform.
 *   fit    — 57 mm scale. Do not scale the cubing object itself.
 *   puzzle — cubing.js Object3D. Do not keyframe; TwistyPlayer owns motion.
 */
export async function adoptTwistyPuzzle(seat, {
    puzzle = "3x3x3",
    alg = "",
    tempoScale = 1.4,
    onRenderScheduled,
    onStage,
    adoptTimeoutMs = 20000,
} = {}) {
    const spec = PUZZLES[puzzle] || PUZZLES["3x3x3"];
    const edge = seat.edge ?? 0.057;
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
        tempoScale,
    });
    hidePlayerHost(player);

    onStage?.("experimentalCurrentThreeJSPuzzleObject");
    let firstPaint = null;
    const painted = new Promise((resolve) => {
        firstPaint = resolve;
    });
    let puzzleObject;
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
        await frame();
        await frame();
    } catch (err) {
        player.remove();
        throw err;
    }

    if (seat.placeholder) {
        seat.fit.remove(seat.placeholder);
    }

    puzzleObject.removeFromParent();
    puzzleObject.traverse((node) => {
        if (node.isMesh) node.frustumCulled = false;
    });
    seat.fit.add(puzzleObject);
    const framed = frameInWrapper(seat.fit, puzzleObject, edge);
    enableShadows(puzzleObject);
    const look = inspectMaterials(puzzleObject);
    const skew = describeThreeSkew(puzzleObject);

    let disposed = false;
    let currentAlg = String(alg ?? spec.alg ?? "");

    async function timeline() {
        const [indexer, info] = await Promise.all([
            player.experimentalModel.indexer.get(),
            player.experimentalModel.detailedTimelineInfo.get(),
        ]);
        return { indexer, info };
    }

    async function status() {
        try {
            const { indexer, info } = await withTimeout(timeline(), 2500, "timeline");
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

    function requestTimestamp(value) {
        player.experimentalModel.timestampRequest.set(value);
    }

    async function jumpToLeafEnd(index) {
        player.pause();
        if (index < 0) {
            player.jumpToStart();
            return;
        }
        const { indexer } = await timeline();
        const total = indexer.numAnimatedLeaves();
        if (!total) {
            player.jumpToStart();
            return;
        }
        const leaf = Math.max(0, Math.min(index, total - 1));
        const end = indexer.indexToMoveStartTimestamp(leaf) + indexer.moveDuration(leaf);
        requestTimestamp(end);
    }

    async function playLeaves(from, to, { snap = false } = {}) {
        const { indexer } = await timeline();
        const total = indexer.numAnimatedLeaves();
        const start = Math.max(0, from);
        const end = Math.max(start, Math.min(to, total));
        if (end <= start) return { index: start, total };
        const startTs = indexer.indexToMoveStartTimestamp(start);
        const endTs = indexer.indexToMoveStartTimestamp(end - 1) + indexer.moveDuration(end - 1);
        player.pause();
        requestTimestamp(snap ? endTs : startTs);
        await frame();
        if (snap) return { index: end - 1, total };
        player.play();
        const deadline = performance.now() + 30000;
        while (performance.now() < deadline) {
            const info = await player.experimentalModel.detailedTimelineInfo.get();
            if (info.timestamp >= endTs - 2) break;
            await frame();
        }
        player.pause();
        requestTimestamp(endTs);
        return { index: end - 1, total };
    }

    const api = {
        group: seat.group,
        lift: seat.lift,
        fit: seat.fit,
        inner: seat.lift,
        puzzle: puzzleObject,
        player,
        puzzleId: spec.id,
        framed,
        look,
        skew,
        fallback: false,
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
            if (info.timestamp >= end - 2) index = Math.min(index + 1, total - 1);
            const nextEnd = indexer.indexToMoveStartTimestamp(index) + indexer.moveDuration(index);
            requestTimestamp(nextEnd);
            return { index, total };
        },
        setAlg(next) {
            currentAlg = String(next || "");
            player.experimentalSetupAlg = "";
            player.alg = currentAlg;
        },
        setSetup(setup) {
            player.experimentalSetupAlg = String(setup || "");
        },
        setTempo(scale) {
            player.tempoScale = Number(scale) || 1;
        },
        playLeaves,
        jumpToLeaf: jumpToLeafEnd,
        async playMoves(moves, { setup = "", snap = false } = {}) {
            player.experimentalSetupAlg = String(setup || "");
            player.alg = Array.isArray(moves) ? moves.join(" ") : String(moves || "");
            const { indexer } = await timeline();
            return playLeaves(0, indexer.numAnimatedLeaves(), { snap });
        },
        setLifted(on, offset = 0.12) {
            seat.lift.position.y = on ? offset : 0;
        },
        status,
        // Teach highlights have no cubing.js equivalent. Gated — do not
        // block the cutover on layer glow.
        highlightLayer: noopHighlight,
        highlightCubie: noopHighlight,
        highlightRuleB: noopHighlight,
        clearHighlights: noopHighlight,
        paint() {
            // Facelet paint is cubie-rig only. Timeline jumps replace it.
        },
        async animateMove() {
            // Session should use playLeaves once setAlg is bound.
        },
        async animateReorient() {},
        async swapPuzzle(nextId, nextAlg = "") {
            const next = await createTwistyRig({
                puzzle: nextId,
                edge,
                alg: nextAlg,
                tempoScale,
                onRenderScheduled,
                adoptTimeoutMs,
            });
            next.group.position.copy(seat.group.position);
            next.group.rotation.copy(seat.group.rotation);
            next.group.quaternion.copy(seat.group.quaternion);
            if (seat.group.parent) {
                seat.group.parent.add(next.group);
                seat.group.parent.remove(seat.group);
            }
            api.dispose();
            return next;
        },
        dispose() {
            if (disposed) return;
            disposed = true;
            player.pause();
            if (puzzleObject?.parent) puzzleObject.parent.remove(puzzleObject);
            player.remove();
        },
    };
    return api;
}

export async function createTwistyRig(opts = {}) {
    const seat = opts.seat || createTwistySeat({ edge: opts.edge });
    return adoptTwistyPuzzle(seat, opts);
}
