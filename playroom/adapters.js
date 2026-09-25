import { CUBE } from "./constants.js";
import { SOLVED_FACELETS } from "../scramble/cube.js";
import { createCubeRig } from "../scramble/view.js";
import { lucideSvg } from "../shared/icons.js";
import { stageCubeView } from "./cube-stage.js";

/**
 * Demo adapters — Unify-1 implements Scramble.
 *
 * Thin shells that place toys on the felt and drive step state.
 * Crypto stays in `demos/scramble/` (session + generated module).
 * DoubleDeal-in-room is Unify-2.
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
function specUrlCandidates() {
    const fromModule = new URL("../scramble/SPEC.md", import.meta.url).href;
    const fromPage = new URL("scramble/SPEC.md", document.baseURI).href;
    return [...new Set([fromModule, fromPage])];
}

async function resolveSpecUrl() {
    for (const href of specUrlCandidates()) {
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
    return specUrlCandidates()[0];
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

function createScrambleAdapter() {
    let rig = null;
    let session = null;
    let root = null;
    let entering = false;
    let sessionMod = null;
    let preloadPromise = null;
    let specObjectUrl = null;

    async function preload() {
        if (sessionMod) return sessionMod;
        if (!preloadPromise) {
            preloadPromise = (async () => {
                await loadScript(new URL("../scramble/vendor/cube.js", import.meta.url).href);
                await loadScript(new URL("../scramble/vendor/solve.js", import.meta.url).href);
                sessionMod = await import("../scramble/session.js");
                return sessionMod;
            })();
        }
        return preloadPromise;
    }

    return {
        id: "scramble",
        install(world, { poses, prefersReducedMotion } = {}) {
            if (rig) return rig;
            const live = createCubeRig({ edge: CUBE, castShadow: true });
            const prev = world.toys.cube;
            live.group.position.copy(prev.position);
            live.group.rotation.copy(prev.rotation);
            world.replaceToy("cube", live.group);
            disposeObject(prev);
            live.paint(SOLVED_FACELETS);
            world.applyPose(live.group, world.getShelfPose("cube"));
            rig = stageCubeView(live, { poses, prefersReducedMotion });
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
                rig.clearHighlights();
                rig.paint(SOLVED_FACELETS);
            }
        },
    };
}

export const adapters = {
    doubledeal: null,
    scramble: createScrambleAdapter(),
};
