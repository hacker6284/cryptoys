/**
 * Microdemo harness: one animation primitive from the real demo code,
 * looping in the playroom with its sounds. No controls: the page is the
 * scene, a small title and a back link. What you hear and how it moves
 * live in the page's settings.js (one plain file per page).
 *
 * mountMicro(spec, settings)
 *   spec.id, spec.title
 *   spec.camera { position, target, fov, margin }  view direction + fov;
 *                 the view is fitted to spec.frame(ctx) (a THREE.Box3)
 *   spec.voice  a library entry's voice (demos/anim/<name>/): the page
 *               is then only a viewer, and the code the entry drives
 *               plays its sounds (ctx.contact is not needed)
 *   spec.slots  without a voice: [{ name, gapMs, voices, jitter, perClick }]
 *               perClick: { slot, clicks(tempo) } lets settings say
 *               `{ perClick: true }`: play `slot`'s file once per click
 *               (clicks(tempo) returns ms relative to the contact, ≤ 0)
 *   spec.setup(ctx)  build the scene (before the light registry is sealed)
 *   spec.ready(ctx)  async loads after the first render
 *   spec.frame(ctx)  → THREE.Box3 to fit the view to (before reset)
 *   spec.reset(ctx)  instant start state
 *   spec.cycle(ctx)  one loop; ctx.contact(slot, perfMs) per contact
 *   spec.stop(ctx)
 *
 * settings (settings.js): { loopGapMs, choices, timing, sounds: { slot:
 *   { file, gainDb, offsetMs, fadeMs, maxMs } | { perClick: true } | null } }
 *   file: path under demos/micro/sounds/ (demos/anim/sounds/ for a
 *   library entry) without extension.
 *   offsetMs: when the file starts relative to the contact (−peak lands
 *   the loudest sample on the contact). startMs: skip the file's head.
 *
 * Sounds go through demos/shared/sound.js (the MegaDreifach Web Audio
 * path), limiter on the master. Sound is on: the page's AudioContext
 * starts on load where autoplay is allowed; otherwise the first tap,
 * click or key anywhere unlocks it, and a small prompt shows until then.
 */
import * as THREE from "three";
import { OrbitControls } from "three/addons/controls/OrbitControls.js";
import { mountWorld } from "../../playroom/world.js";
import { sharedAudio } from "../../shared/sound.js";
import { createVoice } from "../../anim/voice.js";

const SOUND_BASE = new URL("../sounds/", import.meta.url);

function el(tag, attrs = {}, ...kids) {
    const node = document.createElement(tag);
    for (const [k, v] of Object.entries(attrs)) {
        if (k === "class") node.className = v;
        else node.setAttribute(k, v);
    }
    for (const kid of kids.flat()) if (kid != null) node.append(kid.nodeType ? kid : document.createTextNode(String(kid)));
    return node;
}

/**
 * Camera distance along `dir` (unit, target → camera) so every corner of
 * `box` fits a perspective view of vertical fov `fovDeg` and `aspect`.
 */
export function fitDistance(box, target, dir, fovDeg, aspect) {
    const forward = dir.clone().negate();
    const right = new THREE.Vector3().crossVectors(forward, new THREE.Vector3(0, 1, 0)).normalize();
    const up = new THREE.Vector3().crossVectors(right, forward).normalize();
    const tanV = Math.tan((fovDeg * Math.PI) / 360);
    const tanH = tanV * aspect;
    let d = 0;
    const q = new THREE.Vector3();
    for (let i = 0; i < 8; i++) {
        q.set(i & 1 ? box.max.x : box.min.x, i & 2 ? box.max.y : box.min.y, i & 4 ? box.max.z : box.min.z).sub(target);
        const toward = q.dot(dir);
        d = Math.max(d, Math.abs(q.dot(right)) / tanH + toward, Math.abs(q.dot(up)) / tanV + toward);
    }
    return d;
}

export async function mountMicro(spec, settings) {
    document.title = `${spec.title} · microdemo`;
    const voice = spec.voice ?? createVoice({ settings, slots: spec.slots || [], base: SOUND_BASE });
    const sound = voice.sound;
    // The page's shared AudioContext: started on load where autoplay is
    // allowed, otherwise unlocked by the first tap, click or key anywhere.
    sharedAudio().tryStart();

    const canvas = el("canvas", { class: "micro-canvas", "aria-label": `${spec.title} in the playroom` });
    const status = el("p", { class: "micro-status", role: "status" }, "Loading…");
    const touch = globalThis.matchMedia?.("(pointer: coarse)").matches;
    const ask = touch ? "Tap to turn sound on" : "Click to turn sound on";
    const hint = el("button", { type: "button", class: "micro-hint", hidden: "" }, ask);
    document.body.append(el("main", { class: "micro" },
        canvas,
        el("header", { class: "micro-head" }, el("a", { href: "../", class: "micro-back" }, "← microdemos"), el("h1", {}, spec.title)),
        status,
        hint,
    ));
    // The prompt shows only while the context is not running (after a
    // short grace for autoplay), hides as soon as it is, and says so if a
    // gesture did not start it.
    let shown = false;
    let checkTimer = 0;
    function syncHint() {
        const state = sound.state;
        if (state === "running") {
            hint.hidden = true;
            hint.classList.remove("is-blocked");
            hint.textContent = ask;
            return;
        }
        if (!shown) return;
        hint.hidden = false;
        if (state === "unsupported") {
            hint.textContent = "Sound isn't supported in this browser";
            hint.disabled = true;
        }
    }
    sound.onState(syncHint);
    setTimeout(() => {
        shown = true;
        syncHint();
    }, 500);
    function afterGesture() {
        clearTimeout(checkTimer);
        checkTimer = setTimeout(() => {
            if (sound.running || sound.state === "unsupported") return;
            shown = true;
            hint.hidden = false;
            hint.classList.add("is-blocked");
            hint.textContent = touch ? "Sound didn't start. Tap here to try again" : "Sound didn't start. Click here to try again";
        }, 1200);
    }
    hint.addEventListener("click", () => sound.unlock());
    for (const type of ["pointerup", "touchend", "click", "keydown"]) window.addEventListener(type, afterGesture, { capture: true, passive: true });

    const world = await mountWorld(canvas);
    const camera = world.camera;
    const controls = new OrbitControls(camera, canvas);
    controls.enableDamping = true;
    let userMoved = false;
    controls.addEventListener("start", () => {
        userMoved = true;
    });

    let frameBox = null;
    function viewHome() {
        const cam = spec.camera;
        const target = new THREE.Vector3(...cam.target);
        const from = new THREE.Vector3(...cam.position);
        camera.fov = cam.fov ?? 34;
        camera.aspect = canvas.clientWidth / Math.max(1, canvas.clientHeight);
        if (frameBox && !frameBox.isEmpty()) {
            const dir = from.clone().sub(target).normalize();
            frameBox.getCenter(target);
            const d = fitDistance(frameBox, target, dir, camera.fov, camera.aspect) * (cam.margin ?? 1.08);
            from.copy(target).addScaledVector(dir, d);
        }
        camera.position.copy(from);
        camera.updateProjectionMatrix();
        controls.target.copy(target);
        camera.lookAt(target);
        controls.update();
    }
    window.addEventListener("resize", () => {
        if (!userMoved) requestAnimationFrame(viewHome);
    });

    let generation = 0;
    const timers = new Set();
    function later(ms, fn) {
        const id = setTimeout(() => {
            timers.delete(id);
            fn();
        }, Math.max(0, ms));
        timers.add(id);
        return id;
    }

    /** Sound for slot `name` at a contact at performance.now() time `atMs` (file starts at contact + offsetMs). */
    function contact(name, atMs) {
        voice.contact?.(name, atMs, { tempo: settings.timing?.speed ?? 1 });
    }

    /** Lead-in so every listed contact's file can start on time: max(0, −(atMs + offset)). */
    function leadIn(list) {
        return voice.leadIn ? voice.leadIn(list, settings.timing?.speed ?? 1) : 0;
    }

    function wait(ms) {
        const mine = generation;
        return new Promise((resolve) => later(ms, () => resolve(mine === generation)));
    }

    const ctx = {
        THREE,
        world,
        camera,
        settings,
        sound,
        contact,
        leadIn,
        wait,
        get alive() {
            return generation;
        },
        timing: (k) => settings.timing?.[k],
        choice: (k) => settings.choices?.[k],
        onFrame: null,
        status(text) {
            status.textContent = text || "";
            status.hidden = !text;
        },
        /** Fit the view to `box` (THREE.Box3), unless the visitor has moved it. */
        frame(box) {
            frameBox = box;
            if (!userMoved) viewHome();
        },
    };

    await spec.setup?.(ctx);
    world.lights.seal?.();
    viewHome();

    function tick(now) {
        world.resize();
        controls.update();
        ctx.onFrame?.(now);
        world.render();
        requestAnimationFrame(tick);
    }
    requestAnimationFrame(tick);

    async function loop() {
        const mine = generation;
        try {
            while (mine === generation) {
                await spec.cycle(ctx);
                if (mine !== generation) break;
                await wait(settings.loopGapMs ?? 900);
            }
        } catch (err) {
            console.error(err);
            ctx.status(`Loop stopped: ${err.message}`);
        }
    }

    ctx.status("");
    await spec.ready?.(ctx);
    if (spec.frame) {
        world.scene.updateMatrixWorld(true);
        ctx.frame(await spec.frame(ctx));
    }
    await spec.reset?.(ctx);
    void loop();
    window.__micro = ctx;
    return ctx;
}
