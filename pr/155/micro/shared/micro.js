/**
 * Microdemo harness: one looping animation primitive in the real
 * playroom, with its sound slots and timing sliders.
 *
 * A page passes a spec:
 *   id, title, summary, source   (source: which real file the motion is from)
 *   camera { position, target, fov }
 *   timing  [{ key, label, min, max, step, value, unit, note }]   numeric
 *   choices [{ key, label, options: [[value, label]], value }]    selects
 *   slots   [{ name, label, contact, from, pick, gapMs, voices, jitter, gainTrimDb, off }]
 *            from: ["primitive" | ["primitive", "group"], ...] in sounds/index.json
 *            pick: default file (index.json path); else the first candidate
 *            perClick: { slot, label, clicks(ctx) }  adds a picker option that
 *              plays `slot`'s file once per detent click instead; clicks(ctx)
 *              returns the click times in ms relative to the contact (≤ 0)
 *   loopGapMs  default gap between loops
 *   timingTitle  heading for the timing sliders (new primitives: not real code)
 *   setup(ctx)  build the scene (before the light registry is sealed)
 *   cycle(ctx)  one loop; call ctx.contact(slot, perfMs) for each contact
 *   config(ctx) the JSON shaped like the real demo's config
 *
 * Sounds go through demos/shared/sound.js (the MegaDreifach Web Audio
 * path): unlocked on the first gesture, mute remembered.
 */
import * as THREE from "three";
import { OrbitControls } from "three/addons/controls/OrbitControls.js";
import { mountWorld } from "../../playroom/world.js";
import { createSound, dbToGain } from "../../shared/sound.js";

const SOUND_BASE = new URL("../sounds/", import.meta.url);
/** Picker value: play the perClick slot's file once per click. */
export const PER_CLICK = "@per-click";

let indexPromise = null;
export function loadSoundIndex() {
    if (!indexPromise) {
        indexPromise = fetch(new URL("index.json", SOUND_BASE)).then((r) => r.json());
    }
    return indexPromise;
}

function candidatesFor(index, from) {
    const out = [];
    for (const entry of from || []) {
        const [prim, group] = Array.isArray(entry) ? entry : [entry, undefined];
        const list = index.primitives?.[prim]?.candidates || [];
        for (const c of list) {
            if (group !== undefined && c.group !== group) continue;
            out.push({ ...c, primitive: prim });
        }
    }
    return out;
}

// Default gain: Scrounger's "To −16" (level-matched at −16 LUFS; short
// transients were left unlimited, so some need +10…+15 dB). The master
// limiter in shared/sound.js keeps the boosted ones from clipping.
function levelDb(c) {
    if (!c) return 0;
    const db = Number.isFinite(c.gainTo16) ? c.gainTo16 : Number.isFinite(c.lufs) ? -16 - c.lufs : 0;
    return Math.max(-24, Math.min(18, Math.round(db * 2) / 2));
}

function el(tag, attrs = {}, ...kids) {
    const node = document.createElement(tag);
    for (const [k, v] of Object.entries(attrs)) {
        if (k === "class") node.className = v;
        else if (k === "text") node.textContent = v;
        else if (k.startsWith("on")) node.addEventListener(k.slice(2), v);
        else if (v !== undefined && v !== null && v !== false) node.setAttribute(k, v === true ? "" : v);
    }
    for (const kid of kids.flat()) if (kid != null) node.append(kid.nodeType ? kid : document.createTextNode(String(kid)));
    return node;
}

function round(v, step) {
    const digits = Math.max(0, (String(step).split(".")[1] || "").length);
    return Number(Number(v).toFixed(digits));
}

export async function mountMicro(spec) {
    document.title = `${spec.title} · microdemo`;
    const storeKey = `cryptoys.micro.${spec.id}`;
    const index = await loadSoundIndex();

    const slotInfo = {};
    for (const slot of spec.slots || []) {
        const cands = candidatesFor(index, slot.from);
        const pick = cands.find((c) => c.file === slot.pick) || cands[0] || null;
        slotInfo[slot.name] = { slot, cands, pick };
    }

    function defaults() {
        const s = { loopGapMs: spec.loopGapMs ?? 900, timing: {}, choices: {}, slots: {} };
        for (const t of spec.timing || []) s.timing[t.key] = t.value;
        for (const c of spec.choices || []) s.choices[c.key] = c.value;
        for (const [name, { slot, pick }] of Object.entries(slotInfo)) {
            s.slots[name] = {
                file: slot.off || !pick ? "" : pick.file,
                gainDb: levelDb(pick) + (slot.gainTrimDb || 0),
                offsetMs: pick ? -(pick.peakMs || 0) : 0,
                maxMs: 0,
                fadeMs: slot.fadeMs ?? 0,
            };
        }
        return s;
    }

    function load() {
        const base = defaults();
        try {
            const saved = JSON.parse(localStorage.getItem(storeKey) || "null");
            if (!saved) return base;
            if (Number.isFinite(saved.loopGapMs)) base.loopGapMs = saved.loopGapMs;
            for (const k of Object.keys(base.timing)) if (Number.isFinite(saved.timing?.[k])) base.timing[k] = saved.timing[k];
            for (const k of Object.keys(base.choices)) if (saved.choices?.[k] !== undefined) base.choices[k] = saved.choices[k];
            for (const k of Object.keys(base.slots)) {
                const v = saved.slots?.[k];
                if (!v) continue;
                const known = v.file === "" || (v.file === PER_CLICK && slotInfo[k].slot.perClick) || slotInfo[k].cands.some((c) => c.file === v.file);
                if (known) base.slots[k].file = v.file;
                if (Number.isFinite(v.gainDb)) base.slots[k].gainDb = v.gainDb;
                if (Number.isFinite(v.offsetMs)) base.slots[k].offsetMs = v.offsetMs;
                if (Number.isFinite(v.maxMs)) base.slots[k].maxMs = v.maxMs;
                if (Number.isFinite(v.fadeMs)) base.slots[k].fadeMs = v.fadeMs;
            }
        } catch {
            // bad JSON: defaults
        }
        return base;
    }

    const settings = load();
    function save() {
        try {
            localStorage.setItem(storeKey, JSON.stringify(settings));
        } catch {
            // private mode
        }
    }

    function candidate(name) {
        const file = settings.slots[name]?.file;
        return slotInfo[name]?.cands.find((c) => c.file === file) || null;
    }

    function soundTable() {
        const table = {};
        for (const [name, { slot }] of Object.entries(slotInfo)) {
            const s = settings.slots[name];
            if (!s.file || s.file === PER_CLICK) continue;
            table[name] = {
                files: [s.file],
                gains: [dbToGain(s.gainDb)],
                gapMs: slot.gapMs ?? 0,
                voices: slot.voices ?? 4,
                offsetMs: s.offsetMs,
                ...(s.maxMs ? { maxMs: s.maxMs } : {}),
                ...(s.fadeMs ? { fadeMs: s.fadeMs } : {}),
                ...(slot.jitter ? { jitter: slot.jitter } : {}),
            };
        }
        return table;
    }

    const sound = createSound({ sounds: soundTable(), base: SOUND_BASE, store: "cryptoys.micro.muted", limiter: true });

    // ---- layout ---------------------------------------------------------
    const canvas = el("canvas", { class: "micro-canvas", "aria-label": `${spec.title} in the playroom` });
    const panel = el("aside", { class: "micro-panel" });
    const status = el("p", { class: "micro-status", role: "status" }, "Loading the playroom…");
    document.body.append(el("main", { class: "micro" }, el("div", { class: "micro-stage" }, canvas, status), panel));

    const world = await mountWorld(canvas);
    const camera = world.camera;
    const controls = new OrbitControls(camera, canvas);
    controls.enableDamping = true;
    function viewHome() {
        const cam = spec.camera;
        camera.position.set(...cam.position);
        camera.fov = cam.fov;
        camera.updateProjectionMatrix();
        controls.target.set(...cam.target);
        camera.lookAt(controls.target);
        controls.update();
    }

    let generation = 0;
    const timers = new Set();
    const lamps = {};

    function later(ms, fn) {
        const id = setTimeout(() => {
            timers.delete(id);
            fn();
        }, Math.max(0, ms));
        timers.add(id);
        return id;
    }

    function flash(name) {
        const lamp = lamps[name];
        if (!lamp) return;
        lamp.classList.remove("on");
        void lamp.offsetWidth;
        lamp.classList.add("on");
    }

    /**
     * Schedule slot `name` for a contact at performance.now() time
     * `atMs`. The file starts at contact + offsetMs (Web Audio clock);
     * the lamp flashes at contact.
     */
    function contact(name, atMs) {
        const s = settings.slots[name];
        if (!s) return;
        const now = performance.now();
        later(atMs - now, () => flash(name));
        if (!s.file) return;
        if (s.file === PER_CLICK) {
            const pc = slotInfo[name].slot.perClick;
            for (const rel of pc.clicks(ctx)) contact(pc.slot, atMs + rel);
            return;
        }
        const startIn = atMs + s.offsetMs - now;
        if (startIn > 90) later(startIn - 60, () => sound.play(name, { leadMs: atMs - performance.now() }));
        else sound.play(name, { leadMs: atMs - now });
    }

    /** Lead-in so every listed contact's file can start on time: max(0, −(atMs + offset)). */
    function leadIn(list) {
        let lead = 0;
        for (const [name, atMs] of list) {
            const s = settings.slots[name];
            if (!s?.file) continue;
            if (s.file === PER_CLICK) {
                const pc = slotInfo[name].slot.perClick;
                const off = settings.slots[pc.slot]?.offsetMs ?? 0;
                for (const rel of pc.clicks(ctx)) lead = Math.max(lead, -(atMs + rel + off));
                continue;
            }
            lead = Math.max(lead, -(atMs + s.offsetMs));
        }
        return Math.min(2000, lead);
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
        timing: (k) => settings.timing[k],
        choice: (k) => settings.choices[k],
        candidate,
        onFrame: null,
        status(text) {
            status.textContent = text || "";
            status.hidden = !text;
        },
    };

    await spec.setup?.(ctx);
    world.lights.seal?.();
    viewHome();

    function frame(now) {
        world.resize();
        controls.update();
        ctx.onFrame?.(now);
        world.render();
        requestAnimationFrame(frame);
    }
    requestAnimationFrame(frame);

    // ---- panel ----------------------------------------------------------
    function range({ label, min, max, step, value, unit = "", note }, onInput) {
        const out = el("output", {}, `${value}${unit}`);
        const input = el("input", { type: "range", min, max, step, value });
        input.addEventListener("input", () => {
            const v = round(input.value, step);
            out.textContent = `${v}${unit}`;
            onInput(v);
        });
        const row = el("label", { class: "micro-row" }, el("span", { class: "micro-label" }, label), input, out);
        if (note) row.title = note;
        row.set = (v) => {
            input.value = v;
            out.textContent = `${round(v, step)}${unit}`;
        };
        return row;
    }

    function changed({ restart = false } = {}) {
        save();
        if (restart) restartLoop();
    }

    panel.append(
        el("header", { class: "micro-head" },
            el("a", { href: "../", class: "micro-back" }, "← microdemos"),
            el("h1", {}, spec.title),
            el("p", { class: "micro-summary" }, spec.summary || ""),
            spec.source ? el("p", { class: "micro-source" }, "Motion: ", el("code", {}, spec.source)) : null,
        ),
    );

    const playBtn = el("button", { type: "button", class: "micro-btn" }, "Pause");
    const onceBtn = el("button", { type: "button", class: "micro-btn" }, "Once");
    const muteBtn = el("button", { type: "button", class: "micro-btn micro-sound", "aria-pressed": "true" }, "Sound");
    const viewBtn = el("button", { type: "button", class: "micro-btn", title: "Back to the starting view" }, "View");
    sound.bindToggle(muteBtn);
    viewBtn.addEventListener("click", viewHome);
    panel.append(el("div", { class: "micro-bar" }, playBtn, onceBtn, muteBtn, viewBtn));
    const hint = el("p", { class: "micro-hint" }, "Click anywhere to turn sound on (browsers need a gesture).");
    panel.append(hint);
    const hideHint = () => {
        if (sound.running) hint.hidden = true;
    };
    window.addEventListener("pointerdown", () => setTimeout(hideHint, 50));
    window.addEventListener("keydown", () => setTimeout(hideHint, 50));

    const loopSec = el("section", { class: "micro-sec" }, el("h2", {}, "Loop"));
    loopSec.append(range({ label: "Loop gap", min: 0, max: 4000, step: 50, value: settings.loopGapMs, unit: " ms" }, (v) => {
        settings.loopGapMs = v;
        changed();
    }));
    for (const c of spec.choices || []) {
        const select = el("select", {}, c.options.map(([value, label]) => el("option", { value }, label)));
        select.value = String(settings.choices[c.key]);
        select.addEventListener("change", () => {
            const opt = c.options.find(([value]) => String(value) === select.value);
            settings.choices[c.key] = opt ? opt[0] : select.value;
            changed({ restart: true });
        });
        loopSec.append(el("label", { class: "micro-row micro-row--select" }, el("span", { class: "micro-label" }, c.label), select));
    }
    panel.append(loopSec);

    if (spec.timing?.length) {
        const sec = el("section", { class: "micro-sec" }, el("h2", {}, spec.timingTitle || "Timing (real code values)"));
        for (const t of spec.timing) {
            sec.append(range({ ...t, value: settings.timing[t.key] }, (v) => {
                settings.timing[t.key] = v;
                changed();
                spec.onTiming?.(ctx, t.key, v);
                for (const fn of describers) fn();
            }));
        }
        panel.append(sec);
    }

    const soundSec = el("section", { class: "micro-sec" }, el("h2", {}, "Sounds"));
    const describers = [];
    for (const [name, { slot, cands }] of Object.entries(slotInfo)) {
        const s = settings.slots[name];
        const lamp = el("span", { class: "micro-lamp", title: "Flashes at the contact moment" });
        lamps[name] = lamp;
        const select = el("select", {},
            el("option", { value: "" }, cands.length ? "(none)" : "(no candidates yet)"),
            cands.map((c) => el("option", { value: c.file }, `${c.file.split("/").pop()}  ·  peak ${c.peakMs ?? "?"} ms${/COMPOSITE/.test(c.description || "") ? "  ·  composite" : ""}`)),
            slot.perClick ? el("option", { value: PER_CLICK }, slot.perClick.label || `${slot.perClick.slot} file once per click`) : null,
        );
        select.value = s.file;
        const info = el("p", { class: "micro-info" });
        let gainRow = null;
        let offsetRow = null;
        const describe = () => {
            const c = candidate(name);
            if (s.file === PER_CLICK) {
                const pc = slot.perClick;
                const at = pc.clicks(ctx).map((v) => Math.round(v)).join(", ");
                info.textContent = `Plays the “${slotInfo[pc.slot]?.slot.label || pc.slot}” file (its gain and offset) at each detent click: ${at} ms from contact at the current timing.`;
                return;
            }
            info.textContent = c
                ? `${c.author || "?"} · CC0 · ${c.durationS ?? "?"} s · peak ${c.peakMs ?? "?"} ms${c.clicksMs?.length > 1 ? ` · clicks ${c.clicksMs.join("/")} ms` : ""}${c.description ? ` · ${c.description}` : ""}`
                : "";
        };
        select.addEventListener("change", () => {
            const before = candidate(name);
            s.file = select.value;
            const after = candidate(name);
            // Keep the trim relative to level-matched, re-seed the offset on the peak.
            if (after) {
                s.gainDb = round(levelDb(after) + (s.gainDb - levelDb(before || after)), 0.5);
                s.offsetMs = -(after.peakMs || 0);
                gainRow.set(s.gainDb);
                offsetRow.set(s.offsetMs);
            }
            describe();
            sound.configure(soundTable());
            changed();
        });
        gainRow = range({ label: "Gain", min: -30, max: 24, step: 0.5, value: s.gainDb, unit: " dB" }, (v) => {
            s.gainDb = v;
            sound.configure(soundTable());
            changed();
        });
        offsetRow = range({ label: "Offset", min: -1500, max: 1500, step: 5, value: s.offsetMs, unit: " ms", note: "File start relative to the contact moment (negative = before). Seeded to −peak so the loudest sample lands on contact." }, (v) => {
            s.offsetMs = v;
            sound.configure(soundTable());
            changed();
        });
        const lengthRow = range({ label: "Length", min: 0, max: 3000, step: 10, value: s.maxMs, unit: " ms", note: "Stop the file this long after it starts (0 = play it out)" }, (v) => {
            s.maxMs = v;
            sound.configure(soundTable());
            changed();
        });
        const fadeRow = range({ label: "Fade-out", min: 0, max: 1500, step: 10, value: s.fadeMs, unit: " ms", note: "Linear fade over the last part (for long creaks)" }, (v) => {
            s.fadeMs = v;
            sound.configure(soundTable());
            changed();
        });
        const peakBtn = el("button", { type: "button", class: "micro-mini", title: "Offset = −peak (the loudest sample lands on contact)" }, "−peak");
        peakBtn.addEventListener("click", () => {
            const c = candidate(name);
            s.offsetMs = c ? -(c.peakMs || 0) : 0;
            offsetRow.set(s.offsetMs);
            sound.configure(soundTable());
            changed();
        });
        const test = el("button", { type: "button", class: "micro-mini", title: "Play this sound alone" }, "▶");
        test.addEventListener("click", () => {
            sound.unlock();
            setTimeout(() => contact(name, performance.now() + Math.max(0, -s.offsetMs) + 30), 40);
        });
        describe();
        describers.push(describe);
        soundSec.append(el("div", { class: "micro-slot" },
            el("div", { class: "micro-slot-head" }, lamp, el("strong", {}, slot.label || name), el("span", { class: "micro-contact" }, `contact: ${slot.contact}`), test, peakBtn),
            el("label", { class: "micro-row micro-row--select" }, el("span", { class: "micro-label" }, "File"), select),
            info, gainRow, offsetRow, lengthRow, fadeRow,
        ));
    }
    panel.append(soundSec);

    const out = el("textarea", { class: "micro-json", rows: 8, readonly: true, spellcheck: "false", hidden: true });
    const copyBtn = el("button", { type: "button", class: "micro-btn micro-btn--main" }, "Copy settings");
    const resetBtn = el("button", { type: "button", class: "micro-btn" }, "Reset to demo values");
    function exportJson() {
        const sounds = soundTable();
        for (const v of Object.values(sounds)) v.gains = v.gains.map((g) => Number(g.toFixed(3)));
        for (const [name, { slot }] of Object.entries(slotInfo)) {
            if (settings.slots[name].file !== PER_CLICK) continue;
            sounds[name] = { perClick: slot.perClick.slot, clicksMs: slot.perClick.clicks(ctx).map((v) => Math.round(v)) };
        }
        const body = {
            microdemo: spec.id,
            ...(spec.config ? spec.config(ctx) : {}),
            sounds,
            soundsBase: "demos/micro/sounds/",
            loopGapMs: settings.loopGapMs,
        };
        return JSON.stringify(body, null, 2);
    }
    copyBtn.addEventListener("click", async () => {
        const text = exportJson();
        console.log(`[microdemo ${spec.id}] settings\n${text}`);
        out.value = text;
        out.hidden = false;
        try {
            await navigator.clipboard.writeText(text);
            copyBtn.textContent = "Copied";
        } catch {
            out.select();
            copyBtn.textContent = "Copy from the box below";
        }
        setTimeout(() => {
            copyBtn.textContent = "Copy settings";
        }, 1600);
    });
    resetBtn.addEventListener("click", () => {
        localStorage.removeItem(storeKey);
        location.reload();
    });
    panel.append(el("section", { class: "micro-sec" }, el("div", { class: "micro-bar" }, copyBtn, resetBtn), out));
    ctx.exportJson = exportJson;

    // ---- loop -----------------------------------------------------------
    let running = true;
    let looping = false;

    async function loop() {
        if (looping) return;
        looping = true;
        const mine = generation;
        try {
            while (running && mine === generation) {
                await spec.cycle(ctx);
                if (mine !== generation) break;
                await wait(settings.loopGapMs);
            }
        } catch (err) {
            console.error(err);
            ctx.status(`Loop stopped: ${err.message}`);
        } finally {
            looping = false;
        }
    }

    function stopAll() {
        generation += 1;
        for (const id of timers) clearTimeout(id);
        timers.clear();
        spec.stop?.(ctx);
    }

    async function restartLoop() {
        stopAll();
        while (looping) await new Promise((r) => setTimeout(r, 16));
        await spec.reset?.(ctx);
        if (running) void loop();
    }

    playBtn.addEventListener("click", () => {
        running = !running;
        playBtn.textContent = running ? "Pause" : "Play";
        if (running) void restartLoop();
        else stopAll();
    });
    onceBtn.addEventListener("click", async () => {
        running = false;
        playBtn.textContent = "Play";
        stopAll();
        while (looping) await new Promise((r) => setTimeout(r, 16));
        await spec.reset?.(ctx);
        const mine = generation;
        await spec.cycle(ctx);
        if (mine === generation) ctx.status("");
    });

    ctx.status("");
    await spec.ready?.(ctx);
    await spec.reset?.(ctx);
    void loop();
    window.__micro = ctx;
    return ctx;
}
