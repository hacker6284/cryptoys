import { CUBE } from "./constants.js";
import { SOLVED_FACELETS } from "../scramble/cube.js";
import { createCubeRig } from "../scramble/view.js";
import { lucideSvg } from "../shared/icons.js";
import { createBeatClock } from "./beat-clock.js";
import { fadeTree, setTreeOpacity, stageCardTable } from "./card-stage.js";
import { stageCubeView } from "./cube-stage.js";
import { normalizePuzzleId, readPuzzleSearchParam } from "./puzzles.js";
import { adoptTwistyPuzzle, createTwistySeat } from "./twisty-rig.js";
import { pickHandTextures } from "./unbox-hand.js";
import { createDealerKey, disposeDealerKey, playPhysical } from "./unbox-physical.js";
import { createUnboxRig } from "./unbox-rig.js";

/**
 * Demo adapters — Scramble and DoubleDeal share the playroom shell.
 *
 * Thin shells that place toys on the felt and drive step state.
 * Crypto stays in `demos/scramble/` and `demos/doubledeal/`.
 */

function loadScript(src) {
    return new Promise((resolve, reject) => {
        const existing = document.querySelector(`script[data-scramble-vendor="${src}"]`);
        if (existing) {
            if (existing.dataset.loaded === "1") return resolve();
            existing.addEventListener("load", () => resolve(), { once: true });
            existing.addEventListener("error", () => reject(new Error(`Failed to load ${src}`)), { once: true });
            return;
        }
        const script = document.createElement("script");
        script.src = src;
        script.dataset.scrambleVendor = src;
        script.addEventListener("load", () => {
            script.dataset.loaded = "1";
            resolve();
        }, { once: true });
        script.addEventListener("error", () => reject(new Error(`Failed to load ${src}`)), { once: true });
        document.head.append(script);
    });
}

function disposeObject(object) {
    if (!object) return;
    object.traverse?.((node) => {
        if (!node.isMesh) return;
        node.geometry?.dispose();
        const mats = Array.isArray(node.material) ? node.material : [node.material];
        for (const mat of mats) mat?.dispose();
    });
    object.parent?.remove(object);
}

/**
 * Product model (Zach, 2026-09-24): these demo pages are the only
 * place on the internet to perform the algorithms without writing
 * code. Using the hash is primary. Maps chrome: landscape four
 * corners (TL algorithm, TR input card, BL transport card, BR
 * Solve/Spec). Portrait: stage on top (transport over the 3D),
 * input card in the dark band. Teach is opt-in via Step / (i).
 */
function specUrlCandidates(algo = "scramble") {
    const fromModule = new URL(`../${algo}/SPEC.md`, import.meta.url).href;
    const fromPage = new URL(`${algo}/SPEC.md`, document.baseURI).href;
    return [...new Set([fromModule, fromPage])];
}

async function resolveSpecUrl(algo = "scramble") {
    for (const href of specUrlCandidates(algo)) {
        try {
            const response = await fetch(href);
            if (!response.ok) continue;
            const text = await response.text();
            if (!text || /^\s*</.test(text)) continue;
            return URL.createObjectURL(new Blob([text], { type: "text/markdown;charset=utf-8" }));
        } catch {
            // Preview and local checkouts can miss one candidate; try the next.
        }
    }
    return specUrlCandidates(algo)[0];
}

function bindInstrumentChrome(root) {
    const error = root.querySelector("#error");
    const spec = root.querySelector("#spec");
    const info = root.querySelector("#teach-info");
    const clearError = () => {
        if (error) error.textContent = "";
    };
    const setInfo = (on) => {
        root.dataset.info = on ? "1" : "";
        info?.setAttribute("aria-expanded", on ? "true" : "false");
    };
    info?.addEventListener("click", () => setInfo(root.dataset.info !== "1"));
    root.querySelector("#reset")?.addEventListener("click", () => {
        clearError();
        setInfo(false);
    });
    spec?.addEventListener("close", clearError);
    root.querySelector("#digest")?.addEventListener("focus", (event) => {
        event.currentTarget.select?.();
    });
}

function mountDock() {
    let root = document.querySelector("#scramble-dock");
    if (root) return root;
    root = document.createElement("div");
    root.id = "scramble-dock";
    root.className = "playroom-dock";
    root.hidden = true;
    root.innerHTML = `
      <div class="playroom-io">
        <div class="playroom-card playroom-card--io">
          <div class="playroom-io-grid">
            <div class="playroom-ctl playroom-ctl--puzzle" data-puzzle-ctl>
              <span class="playroom-label" id="puzzle-legend">Puzzle</span>
              <div class="playroom-seg" role="group" aria-labelledby="puzzle-legend">
                <button type="button" class="seg-btn on" data-puzzle="3x3x3" aria-label="3×3">3×3</button>
                <button type="button" class="seg-btn" data-puzzle="megaminx" aria-label="Megaminx">Mega</button>
                <button type="button" class="seg-btn" data-puzzle="pyraminx" aria-label="Pyraminx">Pyra</button>
              </div>
            </div>
            <div class="playroom-ctl">
              <span class="playroom-label" id="gen-legend">Gen</span>
              <span id="gen-label" hidden>Gen 2</span>
              <div class="playroom-seg" role="group" aria-labelledby="gen-legend">
                <button type="button" class="seg-btn" data-version="1">1</button>
                <button type="button" class="seg-btn on" data-version="2">2</button>
              </div>
            </div>
            <div class="playroom-ctl">
              <span class="playroom-label" id="enc-legend">Encoding</span>
              <div class="playroom-seg" role="group" aria-labelledby="enc-legend">
                <button type="button" class="seg-btn on" data-encoding="text">Text</button>
                <button type="button" class="seg-btn" data-encoding="hex">Hex</button>
              </div>
            </div>
          </div>
          <label class="playroom-ctl playroom-ctl--field" for="message">
            <span class="playroom-label">Message</span>
            <textarea id="message" rows="1" spellcheck="false" placeholder="hello">hello</textarea>
          </label>
          <label class="playroom-ctl playroom-ctl--field" for="digest">
            <span class="playroom-label">Digest</span>
            <input id="digest" class="digest" type="text" readonly spellcheck="false" autocomplete="off">
          </label>
          <p id="puzzle-note" class="playroom-puzzle-note" hidden>Digest is 3×3 Scramble. This puzzle is visual.</p>
          <p id="status" class="status playroom-status">Solved start · white up, green front, red right</p>
          <p id="error" class="error"></p>
          <button id="digest-btn" type="button" hidden>Digest</button>
        </div>
        <p class="playroom-info-hint" id="teach-hint">Step through to see each turn.</p>
        <div id="teach" class="playroom-note" hidden>
          <div id="tape" class="tape" aria-label="Message tape"></div>
          <article id="teach-card" class="playroom-note-body"></article>
          <div class="transport" id="transport">
          <button type="button" class="icon-btn" data-jump="round-back" aria-label="Previous symbol" title="Previous symbol">${lucideSvg("chevrons-left", 18)}</button>
          <button type="button" class="icon-btn" data-jump="stage-back" aria-label="Previous stage" title="Previous stage">${lucideSvg("chevron-left", 18)}</button>
          <button type="button" class="icon-btn" data-jump="back" aria-label="Prev" title="Prev">${lucideSvg("chevron-left", 18)}</button>
          <span class="pos" id="teach-pos">—</span>
          <button type="button" class="icon-btn" data-jump="fwd" aria-label="Next" title="Next">${lucideSvg("chevron-right", 18)}</button>
          <button type="button" class="icon-btn" data-jump="stage-fwd" aria-label="Next stage" title="Next stage">${lucideSvg("chevron-right", 18)}</button>
          <button type="button" class="icon-btn" data-jump="round-fwd" aria-label="Next symbol" title="Next symbol">${lucideSvg("chevrons-right", 18)}</button>
          </div>
        </div>
        <div id="outline" class="outline" hidden></div>
      </div>
      <div class="playroom-anim">
        <div class="playroom-card playroom-card--transport">
          <div class="row playroom-actions">
            <button id="play" class="icon-btn icon-primary" type="button" aria-label="Play" title="Play">
              <span class="icon-play">${lucideSvg("play")}</span>
              <span class="icon-pause">${lucideSvg("pause")}</span>
            </button>
            <button id="step-through" class="icon-btn" type="button" aria-label="Step through" title="Step through">${lucideSvg("skip-forward")}</button>
            <button id="step" class="icon-btn" type="button" aria-label="Step" title="Step">${lucideSvg("chevron-right")}</button>
            <button id="reset" class="icon-btn" type="button" aria-label="Reset" title="Reset">${lucideSvg("rotate-ccw")}</button>
          </div>
          <label class="slider">Speed <input id="speed" type="range" min="0.5" max="4" step="0.1" value="1.4"></label>
        </div>
      </div>
      <div class="playroom-digins">
        <button id="solve" class="playroom-digin" type="button">Solve</button>
        <button id="spec-btn" class="playroom-digin" type="button">Spec</button>
        <button type="button" class="playroom-info icon-btn" id="teach-info" aria-label="Teach" aria-expanded="false" title="Teach">${lucideSvg("info", 18)}</button>
      </div>
      <dialog id="spec">
        <div class="spec-bar">
          <strong>Specification</strong>
          <button id="spec-close" type="button">Close</button>
        </div>
        <article id="spec-body"></article>
      </dialog>
    `;
    bindInstrumentChrome(root);
    document.body.append(root);
    return root;
}

function wantsLegacyCube() {
    try {
        return new URLSearchParams(location.search).get("legacyCube") === "1";
    } catch {
        return false;
    }
}

function pendingTwistyRig(seat, puzzleId = "3x3x3") {
    const noop = () => {};
    return {
        group: seat.group,
        lift: seat.lift,
        fit: seat.fit,
        inner: seat.lift,
        puzzleId,
        paint: noop,
        animateMove: async () => {},
        animateReorient: async () => {},
        highlightLayer: noop,
        highlightCubie: noop,
        highlightRuleB: noop,
        clearHighlights: noop,
        dispose: noop,
    };
}

function createScrambleAdapter() {
    let rig = null;
    let session = null;
    let root = null;
    let world = null;
    let installOpts = null;
    let puzzleId = "3x3x3";
    let entering = false;
    let sessionMod = null;
    let preloadPromise = null;
    let specObjectUrl = null;
    let adoptPromise = null;

    async function applyPuzzle(nextRaw) {
        const nextId = normalizePuzzleId(nextRaw);
        if (adoptPromise) {
            try {
                await adoptPromise;
            } catch {
                // adopt already logged a fallback
            }
        }
        if (typeof rig?.swapPuzzle !== "function") {
            throw new Error("This cube cannot change puzzle.");
        }
        if ((rig.puzzleId || puzzleId) === nextId) return rig;
        const prev = rig;
        const live = await prev.swapPuzzle(nextId, "");
        if (typeof live.setAlg !== "function" || typeof live.playLeaves !== "function") {
            live.dispose?.();
            throw new Error("cubing.js rig missing timeline API");
        }
        prev.dispose?.();
        if (world) world.replaceToy("cube", live.group);
        rig = stageCubeView(live, installOpts);
        puzzleId = nextId;
        rig.rememberSeated?.();
        return rig;
    }

    function installLegacy(world, { poses, prefersReducedMotion } = {}) {
        const live = createCubeRig({ edge: CUBE, castShadow: true });
        const prev = world.toys.cube;
        live.group.position.copy(prev.position);
        live.group.rotation.copy(prev.rotation);
        world.replaceToy("cube", live.group);
        disposeObject(prev);
        live.paint(SOLVED_FACELETS);
        rig = stageCubeView(live, { poses, prefersReducedMotion });
        return rig;
    }

    async function preload() {
        if (sessionMod && !adoptPromise) return sessionMod;
        if (!preloadPromise) {
            preloadPromise = (async () => {
                const adopt = adoptPromise ? adoptPromise.catch((err) => {
                    console.warn("cubing.js adopt failed; using createCubeRig", err);
                }) : Promise.resolve();
                await loadScript(new URL("../scramble/vendor/cube.js", import.meta.url).href);
                await loadScript(new URL("../scramble/vendor/solve.js", import.meta.url).href);
                const [, mod] = await Promise.all([
                    adopt,
                    import("../scramble/session.js"),
                ]);
                sessionMod = mod;
                return sessionMod;
            })();
        }
        return preloadPromise;
    }

    return {
        id: "scramble",
        install(nextWorld, opts = {}) {
            if (rig) return rig;
            world = nextWorld;
            installOpts = opts;
            if (wantsLegacyCube()) return installLegacy(nextWorld, opts);
            // Seat is sync so toy-director can fly it before cubing.js
            // adopts. createTwistyRig() is the one-shot helper (swapPuzzle).
            puzzleId = readPuzzleSearchParam();
            const seat = createTwistySeat({ edge: CUBE });
            const prev = nextWorld.toys.cube;
            nextWorld.replaceToy("cube", seat.group);
            if (prev) {
                prev.visible = true;
                prev.position.set(0, 0, 0);
                prev.rotation.set(0, 0, 0);
                prev.quaternion?.identity?.();
                seat.fit.add(prev);
                seat.placeholder = prev;
            }
            nextWorld.applyPose(seat.group, nextWorld.getShelfPose("cube"));
            rig = stageCubeView(pendingTwistyRig(seat, puzzleId), opts);
            adoptPromise = adoptTwistyPuzzle(seat, { puzzle: puzzleId, edge: CUBE })
                .then((live) => {
                    if (typeof live.setAlg !== "function" || typeof live.playLeaves !== "function") {
                        live.dispose?.();
                        throw new Error("cubing.js rig missing timeline API");
                    }
                    if (seat.placeholder) {
                        disposeObject(seat.placeholder);
                        seat.placeholder = null;
                    }
                    rig = stageCubeView(live, opts);
                    if (typeof rig.setAlg !== "function" || typeof rig.playLeaves !== "function") {
                        throw new Error("staged cubing.js rig missing timeline API");
                    }
                    return rig;
                })
                .catch((err) => {
                    console.warn("cubing.js adopt failed; using createCubeRig", err);
                    adoptPromise = null;
                    return installLegacy(world, opts);
                });
            return rig;
        },
        preload,
        view() {
            return rig;
        },
        async enter() {
            if (session || entering) return session;
            entering = true;
            try {
                root = mountDock();
                const { createScrambleSession } = await preload();
                const specUrl = await resolveSpecUrl();
                if (specUrl.startsWith("blob:")) specObjectUrl = specUrl;
                const puzzleCtl = root.querySelector("[data-puzzle-ctl]");
                if (puzzleCtl) puzzleCtl.hidden = typeof rig?.swapPuzzle !== "function";
                session = createScrambleSession({
                    view: rig,
                    specUrl,
                    root,
                    exposeTeach: true,
                    puzzle: puzzleId,
                    swapPuzzle: applyPuzzle,
                });
                rig.rememberSeated?.();
                // Stay in use mode. Session enterTeach() is for Step through.
                root.hidden = false;
                root.classList.add("on");
                return session;
            } finally {
                entering = false;
            }
        },
        leave() {
            session?.dispose();
            session = null;
            if (specObjectUrl) {
                URL.revokeObjectURL(specObjectUrl);
                specObjectUrl = null;
            }
            if (root) {
                root.classList.remove("on");
                root.hidden = true;
            }
            if (rig) {
                void rig.settle?.({ snap: true });
                rig.clearHighlights?.();
                rig.pauseTimeline?.();
                rig.resetTimeline?.();
                rig.jumpToLeaf?.(-1);
                rig.paint?.(SOLVED_FACELETS);
            }
        },
    };
}

function mountDoubleDealDock() {
    let root = document.querySelector("#doubledeal-dock");
    if (root) return root;
    root = document.createElement("div");
    root.id = "doubledeal-dock";
    root.className = "playroom-dock";
    root.hidden = true;
    root.innerHTML = `
      <div class="playroom-io">
        <div class="playroom-card playroom-card--io">
          <div class="playroom-io-grid">
            <div class="playroom-ctl">
              <span class="playroom-label" id="mode-legend">Mode</span>
              <div class="playroom-seg" role="group" aria-labelledby="mode-legend">
                <button type="button" class="seg-btn on" data-mode="ecb">ECB</button>
                <button type="button" class="seg-btn" data-mode="ctr">CTR</button>
              </div>
            </div>
            <div class="playroom-ctl">
              <span class="playroom-label" id="dir-legend">Direction</span>
              <div class="playroom-seg" role="group" aria-labelledby="dir-legend">
                <button type="button" class="seg-btn on" data-direction="encrypt">Enc</button>
                <button type="button" class="seg-btn" data-direction="decrypt">Dec</button>
              </div>
            </div>
          </div>
          <label class="playroom-ctl playroom-ctl--field" for="message">
            <span class="playroom-label" id="input-label">Message</span>
            <textarea id="message" rows="1" spellcheck="false" placeholder="hello">hello</textarea>
          </label>
          <label class="playroom-ctl playroom-ctl--field" for="key">
            <span class="playroom-label">Key</span>
            <textarea id="key" rows="1" spellcheck="false" placeholder="cryptoy">cryptoy</textarea>
          </label>
          <div id="nonce-field" hidden>
            <label class="playroom-ctl playroom-ctl--field" for="nonce">
              <span class="playroom-label">Nonce</span>
              <textarea id="nonce" rows="1" spellcheck="false" placeholder="nonce">nonce</textarea>
            </label>
          </div>
          <label class="playroom-ctl playroom-ctl--field" for="digest">
            <span class="playroom-label" id="output-label">Digest</span>
            <input id="digest" class="digest" type="text" readonly spellcheck="false" autocomplete="off">
          </label>
          <p id="status" class="status playroom-status">Plaintext on the left. Key on the right.</p>
          <p id="error" class="error"></p>
          <button id="digest-btn" type="button" hidden>Copy</button>
        </div>
        <p class="playroom-info-hint" id="teach-hint">Step through to see each table beat.</p>
        <div id="teach" class="playroom-note" hidden>
          <article id="teach-card" class="playroom-note-body"></article>
          <div class="transport" id="transport">
          <button type="button" class="icon-btn" data-jump="round-back" aria-label="Previous round" title="Previous round">${lucideSvg("chevrons-left", 18)}</button>
          <button type="button" class="icon-btn" data-jump="stage-back" aria-label="Previous stage" title="Previous stage">${lucideSvg("chevron-left", 18)}</button>
          <button type="button" class="icon-btn" data-jump="back" aria-label="Prev" title="Prev">${lucideSvg("chevron-left", 18)}</button>
          <span class="pos" id="teach-pos">—</span>
          <button type="button" class="icon-btn" data-jump="fwd" aria-label="Next" title="Next">${lucideSvg("chevron-right", 18)}</button>
          <button type="button" class="icon-btn" data-jump="stage-fwd" aria-label="Next stage" title="Next stage">${lucideSvg("chevron-right", 18)}</button>
          <button type="button" class="icon-btn" data-jump="round-fwd" aria-label="Next round" title="Next round">${lucideSvg("chevrons-right", 18)}</button>
          </div>
        </div>
        <div id="outline" class="outline" hidden></div>
      </div>
      <div class="playroom-anim">
        <div class="playroom-card playroom-card--transport">
          <div class="row playroom-actions">
            <button id="play" class="icon-btn icon-primary" type="button" aria-label="Play" title="Play">
              <span class="icon-play">${lucideSvg("play")}</span>
              <span class="icon-pause">${lucideSvg("pause")}</span>
            </button>
            <button id="step-through" class="icon-btn" type="button" aria-label="Step through" title="Step through">${lucideSvg("skip-forward")}</button>
            <button id="step" class="icon-btn" type="button" aria-label="Step" title="Step">${lucideSvg("chevron-right")}</button>
            <button id="reset" class="icon-btn" type="button" aria-label="Reset" title="Reset">${lucideSvg("rotate-ccw")}</button>
          </div>
          <label class="slider">Speed <input id="speed" type="range" min="0.6" max="8" step="0.1" value="1.8"></label>
        </div>
      </div>
      <div class="playroom-digins">
        <button id="random-key" class="playroom-digin" type="button">Random key</button>
        <button id="spec-btn" class="playroom-digin" type="button">Spec</button>
        <button type="button" class="playroom-info icon-btn" id="teach-info" aria-label="Teach" aria-expanded="false" title="Teach">${lucideSvg("info", 18)}</button>
      </div>
      <dialog id="spec">
        <div class="spec-bar">
          <strong>Specification</strong>
          <button id="spec-close" type="button">Close</button>
        </div>
        <article id="spec-body"></article>
      </dialog>
    `;
    bindInstrumentChrome(root);
    document.body.append(root);
    return root;
}

function createDoubleDealAdapter() {
    let world = null;
    let table = null;
    let session = null;
    let root = null;
    let poses = null;
    let entering = false;
    let sessionMod = null;
    let textures = null;
    let preloadPromise = null;
    let specObjectUrl = null;
    let unbox = null;
    let clock = null;
    let enterGen = 0;
    let keyLight = null;
    let cancelEnter = false;

    async function preload() {
        if (sessionMod && textures) return { sessionMod, textures };
        if (!preloadPromise) {
            preloadPromise = (async () => {
                const [{ loadCardTextures }, mod] = await Promise.all([
                    import("../doubledeal/table.js"),
                    import("../doubledeal/session.js"),
                ]);
                sessionMod = mod;
                textures = await loadCardTextures(4);
                return { sessionMod, textures };
            })();
        }
        return preloadPromise;
    }

    function stowUnboxHidden() {
        if (!unbox) return;
        for (const mesh of unbox.cards) {
            if (mesh.parent && mesh.parent !== unbox.packet) unbox.packet.attach(mesh);
        }
        if (unbox.packet.parent !== unbox.group) unbox.group.add(unbox.packet);
        unbox.restow();
        unbox.group.visible = false;
        setTreeOpacity(unbox.group, 1);
        if (keyLight) keyLight.intensity = 0;
    }

    async function prepareEnter() {
        if (!world) return null;
        const loaded = await preload();
        if (!unbox) {
            const anisotropy = Math.min(8, world.renderer?.capabilities?.getMaxAnisotropy?.() || 4);
            unbox = await createUnboxRig({
                anisotropy,
                textures: pickHandTextures(loaded.textures),
                sharedMaps: true,
            });
            const prev = world.toys.deck;
            if (prev) {
                unbox.group.position.copy(prev.position);
                unbox.group.rotation.copy(prev.rotation);
                if (prev.quaternion && unbox.group.quaternion) {
                    unbox.group.quaternion.copy(prev.quaternion);
                }
            }
            world.replaceToy("deck", unbox.group);
            disposeObject(prev);
        }
        unbox.restow();
        unbox.group.visible = true;
        setTreeOpacity(unbox.group, 1);
        if (!unbox.group.userData.flightBusy) world.shelfHome("deck");
        return unbox;
    }

    async function handoffToTable({ snap = false } = {}) {
        const box = unbox?.group || world?.toys.deck;
        const fadeMs = snap ? 0 : 220;
        const jobs = [];
        if (unbox) {
            jobs.push(fadeTree(unbox.sleeve, 0, { ms: fadeMs, snap }));
            jobs.push(fadeTree(unbox.packet, 0, { ms: fadeMs, snap }));
            for (const mesh of unbox.cards) {
                jobs.push(fadeTree(mesh, 0, { ms: fadeMs, snap }));
            }
        } else if (box) {
            jobs.push(fadeTree(box, 0, { ms: snap ? 0 : 200, snap }));
        }
        if (table) jobs.push(table.fadeIn({ ms: snap ? 0 : 260, snap }));
        if (keyLight) {
            const from = keyLight.intensity;
            jobs.push(new Promise((resolve) => {
                if (snap || fadeMs <= 0) {
                    keyLight.intensity = 0;
                    resolve();
                    return;
                }
                const start = performance.now();
                function tick(now) {
                    const t = Math.min(1, (now - start) / fadeMs);
                    keyLight.intensity = from * (1 - t);
                    if (t < 1) requestAnimationFrame(tick);
                    else resolve();
                }
                requestAnimationFrame(tick);
            }));
        }
        await Promise.all(jobs);
        if (unbox) stowUnboxHidden();
        else if (box) {
            box.visible = false;
            setTreeOpacity(box, 1);
        }
    }

    function skipEnter() {
        clock?.skip();
    }

    function showDock() {
        if (!root) return;
        root.hidden = false;
        root.classList.add("on");
    }

    return {
        id: "doubledeal",
        install(nextWorld, { poses: nextPoses } = {}) {
            world = nextWorld;
            poses = nextPoses;
            return world.toys.deck;
        },
        preload,
        prepareEnter,
        skipEnter,
        get busy() {
            return Boolean(entering && clock && !clock.dead(enterGen));
        },
        view() {
            return table || (world ? { group: world.toys.deck } : null);
        },
        async enter({ snap = false } = {}) {
            if (session || entering) return session;
            entering = true;
            cancelEnter = false;
            try {
                const loaded = await preload();
                if (!unbox) await prepareEnter();
                root = mountDoubleDealDock();
                const reduced = snap || Boolean(poses?.prefersReducedMotion?.());
                poses?.lockOrbit?.();
                if (!keyLight && world) keyLight = createDealerKey(world);
                clock = createBeatClock({ reduced });
                enterGen = clock.begin();
                if (!reduced && !cancelEnter && unbox) {
                    await playPhysical({
                        world,
                        rig: unbox,
                        poses,
                        clock,
                        gen: enterGen,
                        keyLight,
                        trackBox: () => world.toys.deck?.position,
                    });
                }
                if (cancelEnter) return null;
                const skipped = reduced || clock.dead(enterGen);
                if (!skipped) await clock.wait(200, enterGen);
                table = stageCardTable(world, loaded.textures, { poses, snap: skipped });
                const specUrl = await resolveSpecUrl("doubledeal");
                if (specUrl.startsWith("blob:")) specObjectUrl = specUrl;
                session = loaded.sessionMod.createDoubleDealSession({
                    view: table,
                    specUrl,
                    root,
                    exposeTeach: true,
                    liveDigest: true,
                });
                table.rememberSeated?.();
                poses?.snap?.("doubledeal");
                await handoffToTable({ snap: skipped || clock.dead(enterGen) });
                if (cancelEnter) return session;
                showDock();
                return session;
            } finally {
                entering = false;
                clock = null;
                poses?.unlockOrbit?.();
            }
        },
        async leave({ snap = false } = {}) {
            cancelEnter = true;
            skipEnter();
            session?.dispose();
            session = null;
            if (specObjectUrl) {
                URL.revokeObjectURL(specObjectUrl);
                specObjectUrl = null;
            }
            if (root) {
                root.classList.remove("on");
                root.hidden = true;
            }
            if (table) {
                await table.fadeOut({ ms: 180, snap });
                table.dispose();
                table = null;
            }
            if (unbox) stowUnboxHidden();
            else if (world?.toys.deck) world.toys.deck.visible = false;
            disposeDealerKey(world, keyLight);
            keyLight = null;
            poses?.unlockOrbit?.();
        },
        revealShelf() {
            const box = world?.toys.deck;
            if (!box) return;
            if (unbox) {
                unbox.restow();
                setTreeOpacity(unbox.group, 1);
            } else {
                setTreeOpacity(box, 1);
            }
            box.visible = true;
        },
    };
}

export const adapters = {
    doubledeal: createDoubleDealAdapter(),
    scramble: createScrambleAdapter(),
};
