import assert from "node:assert/strict";
import { test } from "node:test";
import { createAudioHub, createSound, dbToGain, gainToDb } from "./sound.js";

function fakeAudio({ startState = "running", resumable = () => true } = {}) {
    const made = [];
    class Ctx {
        constructor() {
            this.state = startState;
            this.handlers = [];
            this.resumes = 0;
            this.silent = 0;
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
        createBuffer(channels, length) {
            return { length, duration: 0 };
        }
        decodeAudioData() {
            return Promise.resolve({ duration: 0.5 });
        }
        addEventListener(type, fn) {
            if (type === "statechange") this.handlers.push(fn);
        }
        resume() {
            this.resumes += 1;
            if (!resumable()) return Promise.reject(new Error("NotAllowedError"));
            this.state = "running";
            for (const fn of this.handlers) fn();
            return Promise.resolve();
        }
    }
    return { Ctx, made };
}

function target() {
    const handlers = {};
    return {
        handlers,
        addEventListener: (type, fn) => { (handlers[type] ||= []).push(fn); },
        removeEventListener: (type, fn) => { handlers[type] = (handlers[type] || []).filter((f) => f !== fn); },
        fire: (type) => (handlers[type] || []).forEach((fn) => fn({ type })),
    };
}

const fetched = [];
globalThis.fetch = async (url) => {
    fetched.push(String(url));
    return { ok: true, arrayBuffer: async () => new ArrayBuffer(4) };
};

const BASE = "https://example.test/sounds/";
const SOUNDS = {
    tick: { files: ["a/one", "a/two"], gains: [0.5, 0.25], gapMs: 40, voices: 2 },
    thud: { files: ["b/thud"], gains: [0.4], gapMs: 0, voices: 8, offsetMs: -120 },
};

const settle = () => new Promise((r) => setTimeout(r, 10));

test("autostart: no context before the first gesture without it, one with it", async () => {
    const { Ctx, made } = fakeAudio();
    const t = target();
    const sound = createSound({ sounds: SOUNDS, base: BASE, gestureTarget: t, AudioCtx: Ctx, autostart: false });
    assert.equal(sound.play("tick"), false);
    assert.equal(made.length, 0);
    assert.equal(sound.state, "none");
    t.fire("pointerdown");
    await settle();
    assert.equal(sound.play("tick"), true);

    const auto = fakeAudio();
    const sound2 = createSound({ sounds: SOUNDS, base: BASE, gestureTarget: target(), AudioCtx: auto.Ctx });
    assert.equal(auto.made.length, 1, "created on load");
    await settle();
    assert.equal(sound2.running, true, "autoplay allowed: runs with no gesture");
    assert.equal(sound2.play("tick"), true, "and its sounds decoded");
});

test("autoplay blocked: stays suspended until a gesture, which resumes synchronously", async () => {
    let gesture = false;
    const { Ctx, made } = fakeAudio({ startState: "suspended", resumable: () => gesture });
    const t = target();
    const states = [];
    const sound = createSound({ sounds: SOUNDS, base: BASE, gestureTarget: t, AudioCtx: Ctx });
    sound.onState((s) => states.push(s));
    await settle();
    assert.equal(sound.running, false);
    assert.equal(sound.play("tick"), false);
    assert.equal(made[0].resumes, 1, "tried once on load");
    // A touch pointerdown is not a gesture on iOS: the resume is refused.
    t.fire("pointerdown");
    await settle();
    assert.equal(sound.running, false);
    // touchend is: resume() and the silent buffer happen inside the handler.
    gesture = true;
    t.fire("touchend");
    gesture = false;
    assert.equal(made[0].state, "running", "resumed synchronously in the gesture");
    assert.equal(made[0].started.filter((s) => s.src.buffer?.length === 1).length >= 1, true, "silent buffer started");
    await settle();
    assert.equal(sound.running, true);
    assert.equal(states.at(-1), "running");
    assert.equal(sound.play("tick"), true);
    assert.equal(made.length, 1, "one context throughout");
});

test("every gesture type is caught on the target in the capture phase", () => {
    const t = target();
    const seen = [];
    t.addEventListener = (type, fn, opts) => seen.push([type, opts?.capture]);
    createAudioHub({ AudioCtx: fakeAudio().Ctx, gestureTarget: t }).install();
    assert.deepEqual(seen.map((s) => s[0]).sort(), ["click", "keydown", "mousedown", "pointerdown", "pointerup", "touchend"]);
    assert.ok(seen.every((s) => s[1] === true));
});

test("one hub, two engines: a demo opened after the unlock needs no gesture", async () => {
    const { Ctx, made } = fakeAudio({ startState: "suspended" });
    const t = target();
    const hub = createAudioHub({ AudioCtx: Ctx, gestureTarget: t });
    hub.install();
    t.fire("click");
    await settle();
    assert.equal(hub.state, "running");
    const later = createSound({ sounds: SOUNDS, base: BASE, audio: hub });
    await later.ready();
    assert.equal(later.play("tick"), true);
    assert.equal(made.length, 1);
});

test("audioSession is set to playback inside the unlock", () => {
    const nav = { audioSession: { type: "auto" }, userAgent: "iPhone" };
    const hub = createAudioHub({ AudioCtx: fakeAudio().Ctx, gestureTarget: target(), nav });
    hub.unlock();
    assert.equal(nav.audioSession.type, "playback");
});

test("old iOS without audioSession loops a silent <audio> clip from the gesture", () => {
    const clips = [];
    class FakeAudio {
        constructor(src) { this.src = src; this.paused = true; clips.push(this); }
        setAttribute() {}
        play() { this.paused = false; return Promise.resolve(); }
    }
    const t = target();
    const hub = createAudioHub({ AudioCtx: fakeAudio().Ctx, gestureTarget: t, nav: { userAgent: "Mozilla/5.0 (iPhone; CPU iPhone OS 15_0 like Mac OS X)" }, HtmlAudio: FakeAudio });
    hub.install();
    t.fire("touchend");
    assert.equal(clips.length, 1);
    assert.equal(clips[0].loop, true);
    assert.equal(clips[0].paused, false);
    assert.match(clips[0].src, /^data:audio\/wav;base64,/);
    const desktop = createAudioHub({ AudioCtx: fakeAudio().Ctx, gestureTarget: target(), nav: { userAgent: "Mozilla/5.0 (X11; Linux x86_64) Chrome/140" }, HtmlAudio: FakeAudio });
    desktop.unlock();
    assert.equal(clips.length, 1, "not on other browsers");
});

test("without offsetMs a sound starts now, round-robin, gap and voice capped", async () => {
    const { Ctx, made } = fakeAudio();
    const t = target();
    const sound = createSound({ sounds: SOUNDS, base: BASE, gestureTarget: t, AudioCtx: Ctx });
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
    const sound = createSound({ sounds: SOUNDS, base: BASE, gestureTarget: t, AudioCtx: Ctx });
    t.fire("pointerdown");
    await settle();
    sound.play("thud", { leadMs: 400 });
    sound.play("thud", { leadMs: 20 });
    const [a, b] = made[0].started;
    assert.ok(Math.abs(a.args[0] - 10.28) < 1e-9, "starts 120 ms before contact");
    assert.equal(b.args[0], 10);
    assert.ok(Math.abs(b.args[1] - 0.1) < 1e-9, "skips the 100 ms it missed");
});

test("startMs trims the head; offsetMs still counts from the untrimmed start", async () => {
    const { Ctx, made } = fakeAudio();
    const t = target();
    const sound = createSound({ sounds: { land: { files: ["d/land"], gains: [1], gapMs: 0, voices: 4, offsetMs: -250, startMs: 200 } }, base: BASE, gestureTarget: t, AudioCtx: Ctx });
    t.fire("click");
    await settle();
    sound.play("land", { leadMs: 400 });
    sound.play("land", { leadMs: 10 });
    const [a, b] = made[0].started;
    assert.ok(Math.abs(a.args[0] - 10.35) < 1e-9, "audible part starts 50 ms before contact");
    assert.ok(Math.abs(a.args[1] - 0.2) < 1e-9, "from 200 ms into the file");
    assert.equal(b.args[0], 10);
    assert.ok(Math.abs(b.args[1] - 0.24) < 1e-9, "late: skips the head and the 40 ms it missed");
});

test("configure swaps files and gains", async () => {
    const { Ctx, made } = fakeAudio();
    const t = target();
    const sound = createSound({ sounds: SOUNDS, base: BASE, gestureTarget: t, AudioCtx: Ctx });
    t.fire("pointerdown");
    await settle();
    await sound.configure({ tick: { files: ["c/new"], gains: [dbToGain(-6)], gapMs: 0, voices: 4 } });
    assert.ok(fetched.some((u) => u.endsWith("c/new.mp3") || u.endsWith("c/new.ogg")));
    assert.equal(sound.play("thud"), false, "dropped from the table");
    assert.equal(sound.play("tick"), true);
    assert.ok(Math.abs(gainToDb(dbToGain(-6)) + 6) < 1e-9);
    assert.equal(made[0].started.length, 1);
});

test("sound starts on; the toggle mutes for this page only", async () => {
    const { Ctx } = fakeAudio();
    const t = target();
    const sound = createSound({ sounds: SOUNDS, base: BASE, gestureTarget: t, AudioCtx: Ctx });
    assert.equal(sound.muted, false);
    const button = { attrs: {}, textContent: "", setAttribute(k, v) { this.attrs[k] = v; }, addEventListener(_, fn) { this.click = fn; }, removeEventListener() {} };
    sound.bindToggle(button);
    assert.equal(button.attrs["aria-pressed"], "true");
    button.click();
    assert.equal(sound.muted, true);
    assert.equal(button.attrs["aria-pressed"], "false");
    assert.equal(sound.play("tick"), false);
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
        base: BASE, gestureTarget: t, AudioCtx: Ctx, limiter: true,
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
        const sound = createSound({ sounds: { tick: { files: ["c/short", "c/long"], gains: [1, 1] } }, base: BASE, gestureTarget: t, AudioCtx: Picky });
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

test("peakMs: where each sound's loudest sample is, once decoded", async () => {
    const { Ctx } = fakeAudio();
    class Peaky extends Ctx {
        decodeAudioData() {
            const data = new Float32Array(1000);
            data[250] = -0.9;
            data[600] = 0.5;
            return Promise.resolve({ duration: 1, sampleRate: 1000, numberOfChannels: 1, length: 1000, getChannelData: () => data });
        }
    }
    const before = globalThis.fetch;
    globalThis.fetch = async () => ({ ok: true, arrayBuffer: async () => new ArrayBuffer(4) });
    try {
        const sound = createSound({
            sounds: { tick: { files: ["a"], gains: [1], gapMs: 0, voices: 2 } },
            base: "http://x/",
            AudioCtx: Peaky,
            gestureTarget: new EventTarget(),
            autostart: false,
        });
        assert.equal(sound.peakMs("tick"), null, "unknown before decoding");
        sound.unlock();
        await sound.ready();
        assert.equal(sound.peakMs("tick"), 250);
    } finally {
        globalThis.fetch = before;
    }
});

test("anchorMs holds a moment of the file in place under pitch jitter", async () => {
    const { Ctx, made } = fakeAudio();
    const t = target();
    const sound = createSound({ sounds: { click: { files: ["e/click"], gains: [1], gapMs: 0, voices: 4, offsetMs: 0, jitter: 0.1 } }, base: BASE, gestureTarget: t, AudioCtx: Ctx });
    t.fire("click");
    await settle();
    const random = Math.random;
    Math.random = () => 0; // rate 0.9: the 180 ms click would land 20 ms late
    try {
        sound.play("click", { leadMs: 400, anchorMs: 180 });
    } finally {
        Math.random = random;
    }
    const [a] = made[0].started;
    assert.ok(Math.abs(a.args[0] - 10.38) < 1e-9, "starts 20 ms early so the click lands at 400 + 180 ms");
});

test("audibleCentroidMs: energy centre of the part within −30 dB of the peak", async () => {
    const { audibleCentroidMs } = await import(new URL("./sound.js", import.meta.url));
    const sr = 1000;
    const data = new Float32Array(1000);
    for (let i = 100; i < 110; i++) data[i] = 1; // a click at 100–110 ms
    for (let i = 300; i < 310; i++) data[i] = 1; // an equal click at 300–310 ms
    for (let i = 600; i < 700; i++) data[i] = 0.001; // −60 dB hiss: not audible
    const buffer = { sampleRate: sr, length: data.length, numberOfChannels: 1, getChannelData: () => data };
    assert.ok(Math.abs(audibleCentroidMs(buffer) - 204.5) < 1e-9, "centre of the cluster, hiss ignored");
});

test("swellMs: centre of the loudest 10 ms", async () => {
    const { swellMs } = await import(new URL("./sound.js", import.meta.url));
    const sr = 1000;
    const data = new Float32Array(500);
    for (let i = 50; i < 200; i++) data[i] = 0.2; // body
    for (let i = 120; i < 130; i++) data[i] = 0.5; // swell 120–130 ms
    const buffer = { sampleRate: sr, length: data.length, numberOfChannels: 1, getChannelData: () => data };
    assert.equal(swellMs(buffer), 125);
});
