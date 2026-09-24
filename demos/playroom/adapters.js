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

function mountDock() {
    let root = document.querySelector("#scramble-dock");
    if (root) return root;
    root = document.createElement("div");
    root.id = "scramble-dock";
    root.className = "playroom-dock";
    root.hidden = true;
    root.innerHTML = `
      <div id="teach" class="playroom-note" hidden>
        <div id="tape" class="tape" aria-label="Message tape"></div>
        <article id="teach-card" class="playroom-note-body"></article>
        <div class="transport" id="transport">
          <button type="button" class="chrome-action" data-jump="round-back" title="Previous symbol">«</button>
          <button type="button" class="chrome-action" data-jump="stage-back" title="Previous stage">‹</button>
          <button type="button" class="chrome-action" data-jump="back">Prev</button>
          <span class="pos" id="teach-pos">—</span>
          <button type="button" class="chrome-action" data-jump="fwd">Next</button>
          <button type="button" class="chrome-action" data-jump="stage-fwd" title="Next stage">›</button>
          <button type="button" class="chrome-action" data-jump="round-fwd" title="Next symbol">»</button>
        </div>
      </div>
      <div class="playroom-hands">
        <p class="playroom-hands-label"><span id="gen-label">Gen 2</span> · scramble</p>
        <p id="status" class="status">Solved start · white up, green front, red right</p>
        <p id="digest" class="digest"></p>
        <p id="error" class="error"></p>
        <div class="row playroom-actions">
          <button id="play" class="chrome-action" type="button">Play</button>
          <button id="step-through" class="chrome-action" type="button">Step through</button>
          <button id="step" class="chrome-action" type="button">Step</button>
          <button id="reset" class="chrome-action" type="button">Reset</button>
          <button id="digest-btn" class="chrome-action" type="button">Digest</button>
          <button id="solve" class="chrome-action" type="button">Solve</button>
          <button id="spec-btn" class="chrome-action" type="button">Spec</button>
        </div>
        <label class="slider">Speed <input id="speed" type="range" min="0.5" max="4" step="0.1" value="1.4"></label>
        <div class="row playroom-toggles">
          <button type="button" class="chrome-action" data-version="1">Gen 1</button>
          <button type="button" class="chrome-action on" data-version="2">Gen 2</button>
          <button type="button" class="chrome-action on" data-encoding="text">text</button>
          <button type="button" class="chrome-action" data-encoding="hex">hex</button>
        </div>
        <textarea id="message" rows="2" spellcheck="false" placeholder="hello">hello</textarea>
        <div id="outline" class="outline" hidden></div>
      </div>
      <dialog id="spec">
        <div class="spec-bar">
          <strong>Specification</strong>
          <button id="spec-close" type="button">Close</button>
        </div>
        <article id="spec-body"></article>
      </dialog>
    `;
    document.body.append(root);
    return root;
}

function createScrambleAdapter() {
    let rig = null;
    let session = null;
    let root = null;
    let entering = false;

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
        view() {
            return rig;
        },
        async enter() {
            if (session || entering) return session;
            entering = true;
            try {
                root = mountDock();
                await loadScript(new URL("../scramble/vendor/cube.js", import.meta.url).href);
                await loadScript(new URL("../scramble/vendor/solve.js", import.meta.url).href);
                const { createScrambleSession } = await import("../scramble/session.js");
                session = createScrambleSession({
                    view: rig,
                    specUrl: new URL("../scramble/SPEC.md", import.meta.url).href,
                    root,
                    exposeTeach: true,
                });
                session.enterTeach();
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
