import assert from "node:assert/strict";
import { test } from "node:test";
import { createSound, dbToGain, gainToDb } from "./sound.js";

function fakeAudio() {
    const made = [];
    class Ctx {
        constructor() {
            this.state = "running";
            this.destination = {};
            this.currentTime = 10;
            this.started = [];
            made.push(this);
        }
        createGain() {
            return { gain: { value: 1 }, connect: (x) => x };
        }
        createBufferSource() {
            const src = {
                playbackRate: { value: 1 },
                connect: (g) => g,
                start: (...args) => this.started.push({ src, args }),
            };
            return src;
        }
        decodeAudioData() {
            return Promise.resolve({ duration: 0.5 });
        }
        resume() {}
    }
    return { Ctx, made };
}

function target() {
    const handlers = {};
    return {
        addEventListener: (type, fn) => { handlers[type] = fn; },
        removeEventListener: (type) => { delete handlers[type]; },
        fire: (type) => handlers[type]?.(),
    };
}

const fetched = [];
globalThis.fetch = async (url) => {
    fetched.push(String(url));
    return { ok: true, arrayBuffer: async () => new ArrayBuffer(4) };
};
globalThis.localStorage = { store: {}, getItem(k) { return this.store[k] ?? null; }, setItem(k, v) { this.store[k] = v; } };

const BASE = "https://example.test/sounds/";
const SOUNDS = {
    tick: { files: ["a/one", "a/two"], gains: [0.5, 0.25], gapMs: 40, voices: 2 },
    thud: { files: ["b/thud"], gains: [0.4], gapMs: 0, voices: 8, offsetMs: -120 },
};

const settle = () => new Promise((r) => setTimeout(r, 10));

test("nothing loads before the first gesture", async () => {
    const { Ctx, made } = fakeAudio();
    const t = target();
    const sound = createSound({ sounds: SOUNDS, base: BASE, gestureTarget: t, AudioCtx: Ctx, store: "t1" });
    assert.equal(sound.play("tick"), false);
    assert.equal(made.length, 0);
    t.fire("pointerdown");
    await settle();
    assert.equal(sound.play("tick"), true);
});

test("without offsetMs a sound starts now, round-robin, gap and voice capped", async () => {
    const { Ctx, made } = fakeAudio();
    const t = target();
    const sound = createSound({ sounds: SOUNDS, base: BASE, gestureTarget: t, AudioCtx: Ctx, store: "t2" });
    t.fire("keydown");
    await settle();
    assert.equal(sound.play("tick", { leadMs: 500 }), true);
    assert.equal(sound.play("tick"), false, "inside the gap");
    await new Promise((r) => setTimeout(r, 45));
    assert.equal(sound.play("tick"), true);
    await new Promise((r) => setTimeout(r, 45));
    assert.equal(sound.play("tick"), false, "voice cap (fake sources never end)");
    const starts = made[0].started;
    assert.deepEqual(starts[0].args, [], "leadMs is ignored without offsetMs");
    assert.equal(starts.length, 2);
});

test("offsetMs schedules relative to contact; too late skips into the file", async () => {
    const { Ctx, made } = fakeAudio();
    const t = target();
    const sound = createSound({ sounds: SOUNDS, base: BASE, gestureTarget: t, AudioCtx: Ctx, store: "t3" });
    t.fire("pointerdown");
    await settle();
    sound.play("thud", { leadMs: 400 });
    sound.play("thud", { leadMs: 20 });
    const [a, b] = made[0].started;
    assert.ok(Math.abs(a.args[0] - 10.28) < 1e-9, "starts 120 ms before contact");
    assert.equal(b.args[0], 10);
    assert.ok(Math.abs(b.args[1] - 0.1) < 1e-9, "skips the 100 ms it missed");
});

test("configure swaps files and gains", async () => {
    const { Ctx, made } = fakeAudio();
    const t = target();
    const sound = createSound({ sounds: SOUNDS, base: BASE, gestureTarget: t, AudioCtx: Ctx, store: "t4" });
    t.fire("pointerdown");
    await settle();
    await sound.configure({ tick: { files: ["c/new"], gains: [dbToGain(-6)], gapMs: 0, voices: 4 } });
    assert.ok(fetched.some((u) => u.endsWith("c/new.mp3") || u.endsWith("c/new.ogg")));
    assert.equal(sound.play("thud"), false, "dropped from the table");
    assert.equal(sound.play("tick"), true);
    assert.ok(Math.abs(gainToDb(dbToGain(-6)) + 6) < 1e-9);
    assert.equal(made[0].started.length, 1);
});

test("mute persists and the toggle reflects it", async () => {
    const { Ctx } = fakeAudio();
    const t = target();
    const sound = createSound({ sounds: SOUNDS, base: BASE, gestureTarget: t, AudioCtx: Ctx, store: "t5" });
    const button = { attrs: {}, textContent: "", setAttribute(k, v) { this.attrs[k] = v; }, addEventListener(_, fn) { this.click = fn; }, removeEventListener() {} };
    sound.bindToggle(button);
    assert.equal(button.attrs["aria-pressed"], "true");
    button.click();
    assert.equal(sound.muted, true);
    assert.equal(globalThis.localStorage.store.t5, "1");
    assert.equal(button.attrs["aria-pressed"], "false");
    assert.equal(sound.play("tick"), false);
});

test("store: null ignores and never writes a remembered mute", async () => {
    const { Ctx } = fakeAudio();
    globalThis.localStorage.store.null = "1";
    const sound = createSound({ sounds: SOUNDS, base: BASE, gestureTarget: target(), AudioCtx: Ctx, store: null });
    assert.equal(sound.muted, false);
    const before = { ...globalThis.localStorage.store };
    sound.setMuted(true);
    assert.equal(sound.muted, true);
    assert.deepEqual(globalThis.localStorage.store, before);
});

test("maxMs stops early with a fade; the limiter sits on the master", async () => {
    const { Ctx, made } = fakeAudio();
    const ramps = [];
    const stops = [];
    let compressors = 0;
    Ctx.prototype.createGain = function () {
        return {
            gain: { value: 1, setValueAtTime: (v, t) => ramps.push(["set", v, t]), linearRampToValueAtTime: (v, t) => ramps.push(["ramp", v, t]) },
            connect: (x) => x,
        };
    };
    Ctx.prototype.createDynamicsCompressor = function () {
        compressors += 1;
        const p = () => ({ value: 0 });
        return { threshold: p(), knee: p(), ratio: p(), attack: p(), release: p(), connect: (x) => x };
    };
    const base = Ctx.prototype.createBufferSource;
    Ctx.prototype.createBufferSource = function () {
        const src = base.call(this);
        src.stop = (t) => stops.push(t);
        return src;
    };
    const t = target();
    const sound = createSound({
        sounds: { creak: { files: ["c/creak"], gains: [1], gapMs: 0, voices: 2, offsetMs: 0, maxMs: 300, fadeMs: 100 } },
        base: BASE, gestureTarget: t, AudioCtx: Ctx, store: "t6", limiter: true,
    });
    t.fire("pointerdown");
    await settle();
    assert.equal(compressors, 1);
    assert.equal(sound.play("creak", { leadMs: 0 }), true);
    assert.deepEqual(stops, [10.3]);
    assert.deepEqual(ramps.map((r) => [r[0], r[1], Number(r[2].toFixed(3))]), [["set", 1, 10.2], ["ramp", 0, 10.3]]);
    assert.equal(made.length, 1);
});

test("an MP3 that will not decode falls back to the OGG twin, and is logged", async () => {
    const { Ctx } = fakeAudio();
    class Picky extends Ctx {
        decodeAudioData(buf) {
            return buf.kind === "mp3" && buf.file.includes("short") ? Promise.reject(new Error("EncodingError")) : Promise.resolve({ duration: 0.1 });
        }
    }
    const before = globalThis.fetch;
    globalThis.fetch = async (url) => {
        const u = String(url);
        const buf = new ArrayBuffer(4);
        buf.kind = u.split(".").pop();
        buf.file = u;
        return { ok: true, arrayBuffer: async () => buf };
    };
    const warn = console.warn;
    const warned = [];
    console.warn = (...a) => warned.push(a.join(" "));
    try {
        const t = target();
        const sound = createSound({ sounds: { tick: { files: ["c/short", "c/long"], gains: [1, 1] } }, base: BASE, gestureTarget: t, AudioCtx: Picky, store: "t7" });
        t.fire("pointerdown");
        await settle();
        await sound.ready();
        assert.equal(sound.play("tick"), true);
        assert.deepEqual(sound.fallbacks.map((f) => [f.file, f.from, f.to]), [["c/short", "mp3", "ogg"]]);
        assert.ok(warned.some((w) => w.includes("c/short.mp3")));
    } finally {
        globalThis.fetch = before;
        console.warn = warn;
    }
});
