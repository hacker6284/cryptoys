import { CUBE, GATHER_MS, RESTOW_MS } from "./constants.js";
import { SOLVED_FACELETS } from "../scramble/cube.js";
import { bindGrowFields } from "../shared/grow-field.js";
import { lucideSvg } from "../shared/icons.js";
import { createBeatClock, yieldFrame } from "./beat-clock.js";
import { stageCardTable } from "./card-stage.js";
import { stageCubeView } from "./cube-stage.js";
import { playroomDebugEnabled, readPuzzleSearchParam, resolveProductPuzzleId } from "./puzzles.js";
import { adoptTwistyPuzzle, createTwistySeat } from "./twisty-rig.js";
import { continueTo, markBeat, trackActive, waitToyIdle } from "./motion.js";
import { formSessionTable, gatherSessionTable } from "./table-form.js";
import { pickHandTextures, pickMsgTextures } from "./unbox-hand.js";
import { createDealerKey, disposeDealerKey, playDualUnbox, playRestow, restBoxes } from "./unbox-physical.js";
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
    bindGrowFields(root);
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
            <div class="playroom-ctl playroom-ctl--puzzle" data-puzzle-ctl hidden>
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
            <textarea id="message" class="grow-field" rows="1" spellcheck="false" placeholder="hello">hello</textarea>
          </label>
          <p id="io-note" class="io-note" hidden></p>
          <label class="playroom-ctl playroom-ctl--field" for="digest">
            <span class="playroom-label">Digest</span>
            <textarea id="digest" class="digest grow-field" rows="1" readonly spellcheck="false" autocomplete="off"></textarea>
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
        const nextId = resolveProductPuzzleId(nextRaw);
        if (adoptPromise) {
            try {
                await adoptPromise;
            } catch {
                // adopt already logged the failure
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
        if (world) {
            world.replaceToy("cube", live.group);
            reseatCube(live.group, "table");
        }
        rig = stageCubeView(live, installOpts);
        puzzleId = nextId;
        rig.rememberSeated?.();
        return rig;
    }

    function cubeSurface(group) {
        const named = group?.userData?.seatSurface;
        return named === "table" || named === "shelf" ? named : "shelf";
    }

    function reseatCube(group = world?.toys?.cube, surface) {
        if (!world || !group) return null;
        const destSurface = surface === "table" || surface === "shelf"
            ? surface
            : cubeSurface(group);
        group.userData.seatSurface = destSurface;
        const dest = destSurface === "table"
            ? world.getTablePose("cube")
            : world.getShelfPose("cube");
        if (!dest) return null;
        if (group.userData?.flightBusy) {
            // Refresh landing Y for the surface we are already flying to.
            // Never invent table vs shelf from flightBusy.
            group.userData.pendingDest = dest;
        } else if (group.userData?.easeBusy) {
            group.userData.seatedY = dest.position.y;
        } else {
            world.applyPose(group, dest);
            group.userData.seatedY = dest.position.y;
        }
        group.userData.boundsDirty = false;
        return dest;
    }

    async function waitAdopted() {
        if (!adoptPromise) return rig;
        try {
            return await adoptPromise;
        } catch (err) {
            console.warn("cubing.js adopt failed", err);
            return rig;
        }
    }

    async function preload() {
        if (sessionMod && !adoptPromise) return sessionMod;
        if (!preloadPromise) {
            preloadPromise = (async () => {
                const adopt = waitAdopted();
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
            // Seat is sync so the hub can hold the wrapper. Fly waits
            // for adopt via prepareEnter / ready. Fit is kept on every
            // Twisty render so a later layout cannot crush scale.
            puzzleId = readPuzzleSearchParam();
            const seat = createTwistySeat({ edge: CUBE });
            const prev = nextWorld.toys.cube;
            nextWorld.replaceToy("cube", seat.group);
            if (prev) disposeObject(prev);
            nextWorld.applyPose(seat.group, nextWorld.getShelfPose("cube"));
            seat.group.userData.seatSurface = "shelf";
            rig = stageCubeView(pendingTwistyRig(seat, puzzleId), opts);
            adoptPromise = adoptTwistyPuzzle(seat, {
                puzzle: puzzleId,
                edge: CUBE,
                onFitChange() {
                    const group = world?.toys?.cube || seat.group;
                    reseatCube(group);
                },
            })
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
                    reseatCube(live.group);
                    return rig;
                })
                .catch((err) => {
                    console.warn("cubing.js adopt failed", err);
                    adoptPromise = null;
                    throw err;
                });
            return rig;
        },
        async ready() {
            return waitAdopted();
        },
        async prepareEnter() {
            return waitAdopted();
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
                if (puzzleCtl) {
                    puzzleCtl.hidden = !playroomDebugEnabled() || typeof rig?.swapPuzzle !== "function";
                }
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
            <textarea id="message" class="grow-field" rows="1" spellcheck="false" placeholder="hello">hello</textarea>
          </label>
          <p id="io-note" class="io-note" hidden></p>
          <label class="playroom-ctl playroom-ctl--field" for="key">
            <span class="playroom-label">Key</span>
            <textarea id="key" class="grow-field" rows="1" spellcheck="false" placeholder="cryptoy">cryptoy</textarea>
          </label>
          <div id="nonce-field" hidden>
            <label class="playroom-ctl playroom-ctl--field" for="nonce">
              <span class="playroom-label">Nonce</span>
              <textarea id="nonce" class="grow-field" rows="1" spellcheck="false" placeholder="nonce">nonce</textarea>
            </label>
          </div>
          <label class="playroom-ctl playroom-ctl--field" for="digest">
            <span class="playroom-label" id="output-label">Digest</span>
            <textarea id="digest" class="digest grow-field" rows="1" readonly spellcheck="false" autocomplete="off"></textarea>
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
    let unbox2 = null;
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

    function restowOne(rig) {
        if (!rig) return;
        for (const mesh of rig.cards) {
            if (mesh.parent && mesh.parent !== rig.packet) rig.packet.attach(mesh);
        }
        if (rig.packet.parent !== rig.group) rig.group.add(rig.packet);
        rig.restow();
        rig.group.visible = true;
        rig.group.userData.unboxBusy = false;
        if (rig.packet) rig.packet.userData.unboxBusy = false;
    }

    function restowUnbox() {
        restowOne(unbox);
        restowOne(unbox2);
        if (keyLight) keyLight.intensity = 0;
    }

    async function adoptRig(name, rig, prev) {
        if (prev) {
            rig.group.position.copy(prev.position);
            rig.group.rotation.copy(prev.rotation);
            if (prev.quaternion && rig.group.quaternion) {
                rig.group.quaternion.copy(prev.quaternion);
            }
        }
        world.replaceToy(name, rig.group);
        disposeObject(prev);
        return rig;
    }

    async function prepareEnter() {
        if (!world) return null;
        // Already adopted: do not restow / shelfHome on click — that
        // snapped both decks at the hub→enter handoff.
        if (unbox && unbox2) return unbox;
        const loaded = await preload();
        const anisotropy = Math.min(8, world.renderer?.capabilities?.getMaxAnisotropy?.() || 4);
        if (!unbox) {
            unbox = await createUnboxRig({
                anisotropy,
                textures: pickHandTextures(loaded.textures),
                sharedMaps: true,
                label: "KEY",
                bodyHex: "#6b1e1e",
            });
            await adoptRig("deck", unbox, world.toys.deck);
            await yieldFrame();
        }
        if (!unbox2) {
            unbox2 = await createUnboxRig({
                anisotropy,
                textures: pickMsgTextures(loaded.textures),
                sharedMaps: true,
                label: "MSG",
                bodyHex: "#1a2a44",
            });
            await adoptRig("deck2", unbox2, world.toys.deck2);
            await yieldFrame();
        }
        restowUnbox();
        if (!unbox.group.userData.flightBusy) world.shelfHome("deck");
        if (unbox2 && !unbox2.group.userData.flightBusy) world.shelfHome("deck2");
        return unbox;
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
        leaveMs({ snap = false } = {}) {
            if (snap || Boolean(poses?.prefersReducedMotion?.())) return 0;
            return table ? GATHER_MS + RESTOW_MS : RESTOW_MS;
        },
        view() {
            return table || (world ? { group: world.toys.deck } : null);
        },
        async enter({ snap = false } = {}) {
            if (session || entering) return session;
            entering = true;
            cancelEnter = false;
            try {
                if (!unbox) await prepareEnter();
                root = mountDoubleDealDock();
                const reduced = snap || Boolean(poses?.prefersReducedMotion?.());
                poses?.lockOrbit?.();
                if (!keyLight && world) keyLight = createDealerKey(world);
                clock = createBeatClock({ reduced });
                enterGen = clock.begin();
                const enterTrack = trackActive(world, ["deck", "deck2"], [
                    () => unbox?.packet,
                    () => unbox2?.packet,
                ]);
                // Flap first. 104-card table + SPEC fetch used to run
                // here and freeze the room after the fly landed.
                let unboxJob = Promise.resolve();
                if (!reduced && !cancelEnter && unbox) {
                    poses?.followLive?.(enterTrack);
                    poses?.setTrack?.(enterTrack);
                    unboxJob = playDualUnbox({
                        world,
                        key: unbox,
                        msg: unbox2,
                        clock,
                        gen: enterGen,
                        keyLight,
                    });
                } else if (!cancelEnter) {
                    // Abbreviated continuous path (skip / reduced-motion):
                    // both boxes slide to a standing rest, then cards
                    // stream from those piles. Instant seat only happens
                    // if the shared pose controller snaps for a11y.
                    unboxJob = restBoxes({ world, clock, gen: enterGen });
                }
                let holdLayout = true;
                let layout = null;
                const setupJob = (async () => {
                    await yieldFrame();
                    if (cancelEnter) return;
                    const loaded = await preload();
                    if (!table) {
                        table = stageCardTable(world, loaded.textures, { poses, visible: true });
                    } else {
                        table.show();
                    }
                    const specUrl = await resolveSpecUrl("doubledeal");
                    if (specUrl.startsWith("blob:")) specObjectUrl = specUrl;
                    const view = {
                        ...table,
                        showDecks(message, key) {
                            layout = { message: message.slice(), key: key.slice() };
                            if (holdLayout) return;
                            table.showDecks(message, key);
                        },
                    };
                    session = loaded.sessionMod.createDoubleDealSession({
                        view,
                        specUrl,
                        root,
                        exposeTeach: true,
                        liveDigest: true,
                    });
                    table.rememberSeated?.();
                })();
                await unboxJob;
                if (cancelEnter) return session;
                await waitToyIdle(world.toys.deck2, clock, enterGen);
                poses?.followLive?.(null);
                poses?.releaseFrame?.();
                await setupJob;
                const seated = continueTo(poses, "doubledeal", {
                    duration: reduced ? 480 : 1280,
                });
                if (layout && !cancelEnter) {
                    const keyBox = world.toys.deck?.position;
                    const msgToy = world.toys.deck2;
                    const messageBox = msgToy?.userData.flightBusy
                        ? world.getBoxRestPose?.("deck2")?.position
                        : msgToy?.position || keyBox;
                    await formSessionTable({
                        table,
                        clock,
                        gen: enterGen,
                        messageOrder: layout.message,
                        keyOrder: layout.key,
                        keyBox,
                        messageBox,
                        packet: reduced || !unbox ? null : unbox,
                        msgPacket: reduced || !unbox2 ? null : unbox2,
                    });
                }
                holdLayout = false;
                if (layout) table.showDecks(layout.message, layout.key);
                await seated;
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
            poses?.followLive?.(null);
            poses?.releaseFrame?.();
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
            const reduced = snap || Boolean(poses?.prefersReducedMotion?.());
            if (table && !reduced) {
                clock = createBeatClock({ reduced: false });
                const gen = clock.begin();
                markBeat("leave-gather");
                await gatherSessionTable({
                    table,
                    clock,
                    gen,
                    keyBox: world?.toys?.deck?.position,
                    messageBox: world?.toys?.deck2?.position,
                });
                markBeat("leave-restow");
                table.setCardsVisible?.(false);
                await Promise.all([
                    playRestow({ rig: unbox, clock, gen, ms: RESTOW_MS }),
                    playRestow({ rig: unbox2, clock, gen, ms: RESTOW_MS }),
                ]);
                table.dispose();
                table = null;
            } else {
                if (table) {
                    table.dispose();
                    table = null;
                }
                restowUnbox();
            }
            if (world?.toys.deck2) world.toys.deck2.visible = true;
            disposeDealerKey(world, keyLight);
            keyLight = null;
            clock = null;
            poses?.unlockOrbit?.();
        },
        revealShelf() {
            if (unbox) unbox.restow();
            if (unbox2) unbox2.restow();
            if (world?.toys.deck) world.toys.deck.visible = true;
            if (world?.toys.deck2) world.toys.deck2.visible = true;
        },
    };
}

export const adapters = {
    doubledeal: createDoubleDealAdapter(),
    scramble: createScrambleAdapter(),
};
