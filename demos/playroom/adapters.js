import { CUBE } from "./constants.js";
import { SOLVED_FACELETS } from "../scramble/cube.js";
import { createCubeRig } from "../scramble/view.js";
import { lucideSvg } from "../shared/icons.js";
import { fadeTree, setTreeOpacity, stageCardTable } from "./card-stage.js";
import { stageCubeView } from "./cube-stage.js";
import { adoptTwistyPuzzle, createTwistySeat } from "./twisty-rig.js";

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

function pendingTwistyRig(seat) {
    const noop = () => {};
    return {
        group: seat.group,
        lift: seat.lift,
        fit: seat.fit,
        inner: seat.lift,
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
    let entering = false;
    let sessionMod = null;
    let preloadPromise = null;
    let specObjectUrl = null;
    let adoptPromise = null;

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
        install(world, opts = {}) {
            if (rig) return rig;
            if (wantsLegacyCube()) return installLegacy(world, opts);
            const seat = createTwistySeat({ edge: CUBE });
            const prev = world.toys.cube;
            world.replaceToy("cube", seat.group);
            if (prev) {
                prev.visible = true;
                prev.position.set(0, 0, 0);
                prev.rotation.set(0, 0, 0);
                prev.quaternion?.identity?.();
                seat.fit.add(prev);
                seat.placeholder = prev;
            }
            world.applyPose(seat.group, world.getShelfPose("cube"));
            rig = stageCubeView(pendingTwistyRig(seat), opts);
            adoptPromise = adoptTwistyPuzzle(seat, { puzzle: "3x3x3", edge: CUBE })
                .then((live) => {
                    if (seat.placeholder) {
                        disposeObject(seat.placeholder);
                        seat.placeholder = null;
                    }
                    rig = stageCubeView(live, opts);
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
                session = createScrambleSession({
                    view: rig,
                    specUrl,
                    root,
                    exposeTeach: true,
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

    return {
        id: "doubledeal",
        install(nextWorld, { poses: nextPoses } = {}) {
            world = nextWorld;
            poses = nextPoses;
            return world.toys.deck;
        },
        preload,
        view() {
            return table || (world ? { group: world.toys.deck } : null);
        },
        async enter({ snap = false } = {}) {
            if (session || entering) return session;
            entering = true;
            try {
                const loaded = await preload();
                root = mountDoubleDealDock();
                table = stageCardTable(world, loaded.textures, { poses, snap });
                const box = world.toys.deck;
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
                root.hidden = false;
                root.classList.add("on");
                if (box) {
                    if (snap) {
                        box.visible = false;
                        setTreeOpacity(box, 1);
                    } else {
                        await Promise.all([
                            table.fadeIn({ ms: 260 }),
                            fadeTree(box, 0, { ms: 200 }).then(() => {
                                box.visible = false;
                                setTreeOpacity(box, 1);
                            }),
                        ]);
                    }
                }
                return session;
            } finally {
                entering = false;
            }
        },
        async leave({ snap = false } = {}) {
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
            // Keep the shelf prop hidden until it is home. Showing it
            // on the felt here is the flash Back used to make.
            if (world?.toys.deck) world.toys.deck.visible = false;
        },
        revealShelf() {
            const box = world?.toys.deck;
            if (!box) return;
            setTreeOpacity(box, 1);
            box.visible = true;
        },
    };
}

export const adapters = {
    doubledeal: createDoubleDealAdapter(),
    scramble: createScrambleAdapter(),
};
