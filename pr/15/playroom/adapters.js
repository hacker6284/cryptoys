import { CUBE } from "./constants.js";
import { SOLVED_FACELETS } from "../scramble/cube.js";
import { createCubeRig } from "../scramble/view.js";

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
 * code. Using the hash is primary. Message is the field that always
 * matters. Teach is opt-in (Step through / Step) and must not hide
 * or replace the instrument. The always-on tool is an edge strip,
 * not a floating card.
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
    const clearError = () => {
        if (error) error.textContent = "";
    };
    root.querySelector("#reset")?.addEventListener("click", clearError);
    spec?.addEventListener("close", clearError);
}

function mountDock() {
    let root = document.querySelector("#scramble-dock");
    if (root) return root;
    root = document.createElement("div");
    root.id = "scramble-dock";
    root.className = "playroom-dock";
    root.hidden = true;
    root.innerHTML = `
      <div class="playroom-hands">
        <label class="playroom-message-label" for="message">Message</label>
        <textarea id="message" rows="3" spellcheck="false" placeholder="hello">hello</textarea>
        <p id="digest" class="digest"></p>
        <p id="status" class="status">Solved start · white up, green front, red right</p>
        <p id="error" class="error"></p>
        <div class="row playroom-actions">
          <button id="play" class="primary" type="button">Play</button>
          <button id="step-through" type="button">Step through</button>
          <button id="step" type="button">Step</button>
          <button id="reset" type="button">Reset</button>
          <button id="digest-btn" type="button">Digest</button>
          <button id="solve" type="button">Solve</button>
          <button id="spec-btn" type="button">Spec</button>
        </div>
        <div class="row playroom-meta">
          <label class="slider">Speed <input id="speed" type="range" min="0.5" max="4" step="0.1" value="1.4"></label>
          <div class="row playroom-toggles">
            <span id="gen-label" class="playroom-hands-label">Gen 2</span>
            <button type="button" data-version="1">Gen 1</button>
            <button type="button" class="on" data-version="2">Gen 2</button>
            <button type="button" class="on" data-encoding="text">text</button>
            <button type="button" data-encoding="hex">hex</button>
          </div>
        </div>
        <div id="outline" class="outline" hidden></div>
      </div>
      <div id="teach" class="playroom-note" hidden>
        <div id="tape" class="tape" aria-label="Message tape"></div>
        <article id="teach-card" class="playroom-note-body"></article>
        <div class="transport" id="transport">
          <button type="button" data-jump="round-back" title="Previous symbol">«</button>
          <button type="button" data-jump="stage-back" title="Previous stage">‹</button>
          <button type="button" data-jump="back">Prev</button>
          <span class="pos" id="teach-pos">—</span>
          <button type="button" data-jump="fwd">Next</button>
          <button type="button" data-jump="stage-fwd" title="Next stage">›</button>
          <button type="button" data-jump="round-fwd" title="Next symbol">»</button>
        </div>
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
        install(world) {
            if (rig) return rig;
            rig = createCubeRig({ edge: CUBE, castShadow: true });
            const prev = world.toys.cube;
            rig.group.position.copy(prev.position);
            rig.group.rotation.copy(prev.rotation);
            world.replaceToy("cube", rig.group);
            disposeObject(prev);
            rig.paint(SOLVED_FACELETS);
            world.applyPose(rig.group, world.getShelfPose("cube"));
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
