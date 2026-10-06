import { GATHER_MS, RESTOW_MS } from "./constants.js";
import { SOLVED_FACELETS } from "../scramble/cube.js";
import { bindGrowFields } from "../shared/grow-field.js";
import { lucideSvg } from "../shared/icons.js";
import { createBeatClock, yieldFrame } from "./beat-clock.js";
import { stageCardTable } from "./card-stage.js";
import { stageCubeView } from "./cube-stage.js";
import { timing as scrambleTurnTiming } from "../anim/cube/index.js";
import { playroomDebugEnabled, readPuzzleSearchParam, resolveProductPuzzleId } from "./puzzles.js";
import { adoptTwistyPuzzle, createTwistySeat } from "./twisty-rig.js";
import { continueTo, markBeat, trackActive, waitToyIdle } from "./motion.js";
import { createDreiToy, stageDrei } from "./drei-stage.js";
import { formSessionTable, gatherSessionTable } from "./table-form.js";
import { pickHandTextures, pickMsgTextures } from "./unbox-hand.js";
import { createDealerKey, playDualUnbox, playRestow, restBoxes } from "./unbox-physical.js";
import { createInnerGlow, createUnboxRig } from "./unbox-rig.js";

/**
 * Demo adapters — Scramble, DoubleDeal and MegaDreifach share the playroom shell.
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
function specUrlCandidates(algo) {
    const fromModule = new URL(`../${algo}/SPEC.md`, import.meta.url).href;
    const fromPage = new URL(`${algo}/SPEC.md`, document.baseURI).href;
    return [...new Set([fromModule, fromPage])];
}

async function resolveSpecUrl(algo) {
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

function jumpButton(jump, label, icon) {
    return `<button type="button" class="icon-btn" data-jump="${jump}" aria-label="${label}" title="${label}">`
        + `${lucideSvg(icon, 18)}</button>`;
}

/** Shared dock markup; each demo passes its controls, fields and labels.
 * Markup chunks start with a newline so the rendered dock stays byte-identical to the old per-demo docks. */
function mountDock(algo, { controls, fields, digestButton, hint, tape = "", roundName, speed, digin }) {
    let root = document.querySelector(`#${algo}-dock`);
    if (root) return root;
    root = document.createElement("div");
    root.id = `${algo}-dock`;
    root.className = "playroom-dock";
    root.hidden = true;
    root.innerHTML = `
      <div class="playroom-io">
        <div class="playroom-card playroom-card--io">
          <div class="playroom-io-grid">${controls}
          </div>${fields}
          <p id="error" class="error"></p>
          <button id="digest-btn" type="button" hidden>${digestButton}</button>
        </div>
        <p class="playroom-info-hint" id="teach-hint">${hint}</p>
        <div id="teach" class="playroom-note" hidden>${tape}
          <article id="teach-card" class="playroom-note-body"></article>
          <div class="transport" id="transport">
          ${jumpButton("round-back", `Previous ${roundName}`, "chevrons-left")}
          ${jumpButton("stage-back", "Previous stage", "chevron-left")}
          ${jumpButton("back", "Prev", "chevron-left")}
          <span class="pos" id="teach-pos">—</span>
          ${jumpButton("fwd", "Next", "chevron-right")}
          ${jumpButton("stage-fwd", "Next stage", "chevron-right")}
          ${jumpButton("round-fwd", `Next ${roundName}`, "chevrons-right")}
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
            <button id="skip-end" class="icon-btn" type="button" aria-label="Skip to end"
              title="Skip to end">${lucideSvg("skip-forward")}</button>
            <button id="step" class="icon-btn" type="button" aria-label="Step"
              title="Step">${lucideSvg("chevron-right")}</button>
            <button id="reset" class="icon-btn" type="button" aria-label="Reset"
              title="Reset">${lucideSvg("rotate-ccw")}</button>
          </div>
          <label class="slider">Speed <input id="speed" type="range" min="${speed.min}" max="${speed.max}" step="0.1"
            value="${speed.value}"></label>
        </div>
      </div>
      <div class="playroom-digins">
        ${digin}
        <button id="spec-btn" class="playroom-digin" type="button">Spec</button>
        <button type="button" class="playroom-info icon-btn" id="teach-info" aria-label="Teach" aria-expanded="false"
          title="Teach">${lucideSvg("info", 18)}</button>
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

/** Dock lifecycle shared by the demo adapters: mount, spec URL, show, close. */
function createDock(algo, parts) {
    let root = null;
    let specObjectUrl = null;
    return {
        mount() {
            root = mountDock(algo, parts);
            return root;
        },
        async specUrl() {
            const url = await resolveSpecUrl(algo);
            if (url.startsWith("blob:")) specObjectUrl = url;
            return url;
        },
        show() {
            root.hidden = false;
            root.classList.add("on");
        },
        close() {
            if (specObjectUrl) {
                URL.revokeObjectURL(specObjectUrl);
                specObjectUrl = null;
            }
            if (root) {
                root.classList.remove("on");
                root.hidden = true;
            }
        },
    };
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

export function createScrambleAdapter() {
    const dock = createDock("scramble", {
        controls: `
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
            </div>`,
        fields: `
          <div class="playroom-ctl playroom-ctl--field">
            <label class="playroom-label" for="message">Message</label>
            <div class="playroom-message-row">
              <textarea id="message" class="grow-field" rows="1" spellcheck="false" placeholder="hello">hello</textarea>
              <button type="button" class="file-btn" id="message-file-btn" aria-label="Hash a file"
                title="Hash a file">${lucideSvg("paperclip", 16)}</button>
            </div>
            <div id="message-file" class="file-chip" hidden>
              <span id="message-file-name"></span>
              <button type="button" class="file-action" id="message-file-clear" aria-label="Clear file">Clear</button>
            </div>
            <input id="message-file-input" type="file" hidden>
          </div>
          <p id="io-note" class="io-note" hidden></p>
          <label class="playroom-ctl playroom-ctl--field" for="digest">
            <span class="playroom-label">Digest</span>
            <textarea id="digest" class="digest grow-field" rows="1" readonly spellcheck="false"
              autocomplete="off"></textarea>
          </label>
          <p id="puzzle-note" class="playroom-puzzle-note" hidden>Digest is 3×3 Scramble. This puzzle is visual.</p>
          <p id="status" class="status playroom-status">Solved start · white up, green front, red right</p>`,
        digestButton: "Digest",
        hint: "Step to see each turn.",
        tape: `
          <div id="tape" class="tape" aria-label="Message tape"></div>`,
        roundName: "symbol",
        speed: { min: 0.5, max: 4, value: scrambleTurnTiming.speed },
        digin: '<button id="solve" class="playroom-digin" type="button">Solve</button>',
    });
    let rig = null;
    let session = null;
    let world = null;
    let installOpts = null;
    let puzzleId = "3x3x3";
    let entering = false;
    let sessionMod = null;
    let preloadPromise = null;
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
        // swapPuzzle detached the old seat: move its lights before any throw.
        if (world) world.replaceToy("cube", live.group);
        if (typeof live.setAlg !== "function" || typeof live.playLeaves !== "function") {
            live.dispose?.();
            throw new Error("cubing.js rig missing timeline API");
        }
        prev.dispose?.();
        if (world) reseatCube(live.group, "table");
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
        install(nextWorld, opts = {}) {
            if (rig) return rig;
            world = nextWorld;
            installOpts = opts;
            // Seat is sync so the hub can hold the wrapper. Fly waits
            // for adopt via prepareEnter / ready. Fit is kept on every
            // Twisty render so a later layout cannot crush scale. Each
            // puzzle shows at its own real size (constants.js REAL_SIZES).
            puzzleId = readPuzzleSearchParam();
            const seat = createTwistySeat({ puzzle: puzzleId });
            const prev = nextWorld.toys.cube;
            nextWorld.replaceToy("cube", seat.group);
            if (prev) disposeObject(prev);
            nextWorld.applyPose(seat.group, nextWorld.getShelfPose("cube"));
            seat.group.userData.seatSurface = "shelf";
            rig = stageCubeView(pendingTwistyRig(seat, puzzleId), opts);
            adoptPromise = adoptTwistyPuzzle(seat, {
                puzzle: puzzleId,
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
                const root = dock.mount();
                const { createScrambleSession } = await preload();
                const specUrl = await dock.specUrl();
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
                // Stay in use mode. Step enters teach.
                dock.show();
                return session;
            } finally {
                entering = false;
            }
        },
        leave() {
            session?.dispose();
            session = null;
            dock.close();
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

export function createDoubleDealAdapter() {
    const dock = createDock("doubledeal", {
        controls: `
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
            </div>`,
        fields: `
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
            <textarea id="digest" class="digest grow-field" rows="1" readonly spellcheck="false"
              autocomplete="off"></textarea>
          </label>
          <p id="status" class="status playroom-status">Plaintext on the left. Key on the right.</p>`,
        digestButton: "Copy",
        hint: "Step to see each table beat.",
        roundName: "round",
        speed: { min: 0.6, max: 8, value: 1.8 },
        digin: '<button id="random-key" class="playroom-digin" type="button">Random key</button>',
    });
    let world = null;
    let table = null;
    let session = null;
    let poses = null;
    let entering = false;
    let sessionMod = null;
    let textures = null;
    let preloadPromise = null;
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
    }

    async function adoptRig(name, rig, prev) {
        if (prev) {
            rig.group.position.copy(prev.position);
            rig.group.rotation.copy(prev.rotation);
            if (prev.quaternion && rig.group.quaternion) {
                rig.group.quaternion.copy(prev.quaternion);
            }
        }
        // Sleeve glow rejoins the scene here; no await since createUnboxRig.
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
                innerGlow: world.lights.get("glow:deck"),
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
                innerGlow: world.lights.get("glow:deck2"),
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

    return {
        install(nextWorld, { poses: nextPoses } = {}) {
            world = nextWorld;
            poses = nextPoses;
            // Add the dark dealer key and sleeve glows at boot: adding a
            // light mid-scene recompiles every lit shader (unbox freeze).
            keyLight = createDealerKey(world);
            world.lights.add("glow:deck", createInnerGlow());
            world.lights.add("glow:deck2", createInnerGlow());
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
                const root = dock.mount();
                const reduced = snap || Boolean(poses?.prefersReducedMotion?.());
                poses?.lockOrbit?.();
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
                    const specUrl = await dock.specUrl();
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
                dock.show();
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
            dock.close();
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
            keyLight.intensity = 0;
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

/**
 * MegaDreifach: three megaminxes standing on the felt in a row, B | A | C
 * (A carries h, B its inverse, C stays solved), and a real deck for each
 * block's deal. Only toys: no tray, no label cards. A (the shelf's only
 * megaminx) flies off the shelf; B, C and the boxed deck come out of the
 * toy chest; enter lands them on the felt, then the three puzzles hop in
 * turn (A, B, C) under a caption naming them left to right, and the deck's flap
 * lifts while the camera settles on the `drei` seat. Hashing and tracing
 * run in a worker on the generated module (demos/megadreifach/).
 */
// The roll call's caption, and the start of the idle status: which
// puzzle is which, left to right as seen from the seat (the table has no
// labels).
const DREI_CAST = "Left to right: B, A, C. A carries h, B its inverse, C stays solved.";

/** A brief on-screen caption over the room for the roll call. */
function dreiCastCaption() {
    let el = null;
    return {
        show() {
            if (typeof document === "undefined") return;
            if (!el) {
                el = document.createElement("p");
                el.className = "drei-cast";
                el.setAttribute("role", "status");
                el.innerHTML = '<span class="drei-cast-row"><b>B</b><b>A</b><b>C</b></span>'
                    + '<span class="drei-cast-note">left to right · A carries h, B its inverse, C stays solved</span>';
                document.body.append(el);
            }
            void el.offsetWidth;
            el.classList.add("on");
        },
        hide() {
            el?.classList.remove("on");
        },
    };
}

export function createMegaDreifachAdapter() {
    const dock = createDock("megadreifach", {
        controls: `
            <div class="playroom-ctl">
              <span class="playroom-label" id="enc-legend">Encoding</span>
              <div class="playroom-seg" role="group" aria-labelledby="enc-legend">
                <button type="button" class="seg-btn on" data-encoding="text">Text</button>
                <button type="button" class="seg-btn" data-encoding="hex">Hex</button>
              </div>
            </div>`,
        fields: `
          <label class="playroom-ctl playroom-ctl--field" for="message">
            <span class="playroom-label">Message</span>
            <textarea id="message" class="grow-field" rows="1" spellcheck="false"
              placeholder="Type a message to hash"></textarea>
          </label>
          <p id="io-note" class="io-note" hidden></p>
          <div id="kat-menu" class="drei-kat-menu" role="group" aria-label="Known-answer tests" hidden></div>
          <label class="playroom-ctl playroom-ctl--field" for="digest">
            <span class="playroom-label">Digest</span>
            <textarea id="digest" class="digest grow-field" rows="1" readonly spellcheck="false" autocomplete="off"
              placeholder="No message yet"></textarea>
          </label>
          <p class="drei-warning" role="note">MegaDreifach v3, a toy hash: it makes no cryptographic
            security claim and is not for protecting anything.</p>
          <p id="anim-note" class="drei-anim-note" role="status" hidden></p>
          <p id="status" class="status drei-status" aria-live="polite">Type a message, or pick a known answer.</p>`,
        digestButton: "Copy",
        hint: "Step to see each turn.",
        roundName: "block",
        // Starts at the library's megaminx tempo (demos/anim/megaminx, 1.4).
        speed: { min: 0.5, max: 12, value: 1.4 },
        digin: '<button id="kat" class="playroom-digin" type="button" aria-controls="kat-menu" aria-expanded="false">'
            + 'KAT</button>'
            + '<button id="recentre" class="playroom-digin" type="button" title="Back to the table view">'
            + 'Recentre</button>',
    });
    let world = null;
    let poses = null;
    let drei = null;
    let stage = null;
    let deck = null;
    let session = null;
    let sessionMod = null;
    let textures = null;
    let preloadPromise = null;
    let entering = false;
    let clock = null;
    let enterGen = 0;
    let cancelEnter = false;
    let recentreBound = null;
    const castCaption = dreiCastCaption();

    async function preload() {
        if (sessionMod && textures) return { sessionMod, textures };
        if (!preloadPromise) {
            preloadPromise = (async () => {
                const [{ loadCardTextures }, mod] = await Promise.all([
                    import("../doubledeal/table.js"),
                    import("../megadreifach/session.js"),
                ]);
                sessionMod = mod;
                textures = await loadCardTextures(4);
                return { sessionMod, textures };
            })().catch((err) => {
                preloadPromise = null;
                throw err;
            });
        }
        return preloadPromise;
    }

    async function waitAdopted() {
        try {
            await stage?.adopt();
        } catch (err) {
            console.warn("cubing.js megaminx adopt failed", err);
            throw err;
        }
        // Seat heights move once the real puzzles are measured.
        for (const name of ["drei", "dreiB", "dreiC"]) {
            const toy = world?.toys?.[name];
            if (toy && !toy.userData.flightBusy && toy.userData.seatSurface !== "table") world.shelfHome(name);
        }
        return stage;
    }

    async function prepareEnter() {
        if (!world) return null;
        await waitAdopted();
        if (deck) return deck;
        const loaded = await preload();
        const anisotropy = Math.min(8, world.renderer?.capabilities?.getMaxAnisotropy?.() || 4);
        // The deck's cards in card-id order (rank × 4 + suit), backs navy.
        const faces = [];
        for (let card = 0; card < 52; card++) faces.push(loaded.textures.faces[(card % 4) * 13 + Math.floor(card / 4)]);
        deck = await createUnboxRig({
            anisotropy,
            textures: { faces, back: loaded.textures.navy },
            sharedMaps: true,
            label: "DEAL",
            bodyHex: "#3a2140",
            innerGlow: world.lights.get("glow:deck3"),
        });
        const prev = world.toys.deck3;
        if (prev) {
            deck.group.position.copy(prev.position);
            deck.group.quaternion.copy(prev.quaternion);
            deck.group.rotation.copy(prev.rotation);
        }
        world.replaceToy("deck3", deck.group);
        disposeObject(prev);
        deck.restow();
        stage.setDeck(deck);
        if (!deck.group.userData.flightBusy) world.shelfHome("deck3");
        await yieldFrame();
        return deck;
    }

    function recentre() {
        continueTo(poses, "drei", { duration: 900 });
    }

    return {
        install(nextWorld, { poses: nextPoses, prefersReducedMotion } = {}) {
            world = nextWorld;
            poses = nextPoses;
            // The deck's sleeve glow, registered dark before the seal.
            world.lights.add("glow:deck3", createInnerGlow());
            drei = createDreiToy();
            const prev = world.toys.drei;
            world.replaceToy("drei", drei.group);
            if (prev) disposeObject(prev);
            world.shelfHome("drei");
            // B and C wait in the toy chest.
            for (const [name, toy] of Object.entries(drei.extras)) {
                const old = world.toys[name];
                world.replaceToy(name, toy);
                if (old) disposeObject(old);
                world.shelfHome(name);
            }
            stage = stageDrei(world, drei, { prefersReducedMotion });
            return drei.group;
        },
        async ready() {
            try {
                await waitAdopted();
            } catch {
                // enter reports it; the hub still loads.
            }
            return stage;
        },
        preload,
        prepareEnter,
        skipEnter() {
            clock?.skip();
        },
        get busy() {
            return Boolean(entering && clock && !clock.dead(enterGen));
        },
        leaveMs({ snap = false } = {}) {
            if (snap || Boolean(poses?.prefersReducedMotion?.())) return 0;
            return stage?.dealt ? stage.gatherMs() : 0;
        },
        view() {
            return stage;
        },
        async enter({ snap = false } = {}) {
            if (session || entering) return session;
            entering = true;
            cancelEnter = false;
            try {
                if (!deck) await prepareEnter();
                const root = dock.mount();
                const reduced = snap || Boolean(poses?.prefersReducedMotion?.());
                poses?.lockOrbit?.();
                clock = createBeatClock({ reduced });
                enterGen = clock.begin();
                const { sessionMod: mod } = await preload();
                const specUrl = await dock.specUrl();
                if (cancelEnter) return session;
                // Beat sheet (full motion): the director has flown A off the
                // shelf and, out of the toy chest, B, C and the DEAL deck
                // (260 ms apart) onto the felt, B left and C right of A, the
                // deck left of B; the app's follow shot (wide enough for the
                // chest) is still under way.
                // 0 ms: live follow ends (as DoubleDeal's enter does) and
                // the camera eases from wherever it is onto the drei seat
                // (1,400 ms, about Scramble's glide). `restart`: the follow shot is flying to this
                // same pose, and asking for it again used to skip() the
                // shot, a one-frame cut (3.5 m, 44°, 8° of fov in one frame,
                // measured frame by frame against Scramble, which glides).
                // Once B and C are down: B, A, C hop in turn, left to right
                // (0 / 170 / 340 ms, 420 ms each) while the caption names
                // them (the table has no labels). If the puzzles kept turns
                // from last time, they undo them in place, turn by turn.
                // Then the dock.
                markBeat("drei-present");
                poses?.followLive?.(null);
                poses?.releaseFrame?.();
                const seated = continueTo(poses, "drei", { duration: reduced ? 480 : 1400, restart: true });
                // B and C must be down before the roll call.
                for (const name of ["dreiB", "dreiC"]) await waitToyIdle(world.toys[name], clock, enterGen);
                const statusEl = root.querySelector("#status");
                if (statusEl) statusEl.textContent = DREI_CAST;
                castCaption.show();
                if (!reduced) await stage.rollCall(clock, enterGen);
                if (stage.hasLeftover && !cancelEnter) {
                    markBeat("drei-reset");
                    await stage.resetPuzzles({ snap: reduced });
                }
                await seated;
                // The caption stays a moment once the camera is on the table.
                const castGen = enterGen;
                setTimeout(() => {
                    if (castGen === enterGen) castCaption.hide();
                }, 1600);
                if (cancelEnter) {
                    castCaption.hide();
                    return session;
                }
                // Sound is on hold project-wide: none here.
                session = mod.createMegaDreifachSession({
                    view: stage,
                    specUrl,
                    root,
                    exposeTeach: true,
                    cast: DREI_CAST,
                });
                stage.rememberSeated();
                const button = root.querySelector("#recentre");
                if (button && recentreBound !== button) {
                    button.addEventListener("click", recentre);
                    recentreBound = button;
                }
                dock.show();
                return session;
            } finally {
                entering = false;
                clock = null;
                poses?.unlockOrbit?.();
            }
        },
        async leave({ snap = false } = {}) {
            cancelEnter = true;
            castCaption.hide();
            clock?.skip();
            const reduced = snap || Boolean(poses?.prefersReducedMotion?.());
            session?.dispose();
            session = null;
            dock.close();
            if (stage?.dealt && !reduced) {
                markBeat("leave-gather");
                await stage.gather();
            }
            stage?.settle();
            await stage?.clearShow();
            deck?.restow();
        },
        revealShelf() {
            deck?.restow();
            if (world?.toys.drei) world.toys.drei.visible = true;
            if (world?.toys.deck3) world.toys.deck3.visible = true;
        },
    };
}
