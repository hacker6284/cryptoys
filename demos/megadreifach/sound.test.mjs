import assert from "node:assert/strict";
import { test } from "node:test";
import { createSound, SOUNDS } from "./sound.js";

function fakeAudio() {
    const made = [];
    class Ctx {
        constructor() {
            this.state = "running";
            this.destination = {};
            made.push(this);
            this.started = [];
        }
        createGain() {
            return { gain: { value: 1 }, connect: (x) => x };
        }
        createBufferSource() {
            const src = {
                playbackRate: { value: 1 },
                connect: (g) => g,
                start: () => this.started.push(src),
            };
            return src;
        }
        decodeAudioData() {
            return Promise.resolve({ duration: 0.1 });
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

globalThis.fetch = async () => ({ ok: true, arrayBuffer: async () => new ArrayBuffer(4) });
globalThis.localStorage = { store: {}, getItem(k) { return this.store[k] ?? null; }, setItem(k, v) { this.store[k] = v; } };

test("nothing starts before the first gesture", async () => {
    const { Ctx, made } = fakeAudio();
    const t = target();
    const sound = createSound({ gestureTarget: t, AudioCtx: Ctx });
    assert.equal(sound.play("chime"), false);
    assert.equal(made.length, 0);
    t.fire("pointerdown");
    assert.equal(made.length, 1);
    await new Promise((r) => setTimeout(r, 10));
    assert.equal(sound.play("chime"), true);
});

test("rapid turns are throttled and voice-capped", async () => {
    const { Ctx, made } = fakeAudio();
    const t = target();
    const sound = createSound({ gestureTarget: t, AudioCtx: Ctx });
    t.fire("keydown");
    await new Promise((r) => setTimeout(r, 10));
    let played = 0;
    for (let i = 0; i < 50; i++) played += sound.play("turn") ? 1 : 0;
    assert.equal(played, 1, "a burst in one instant plays once");
    for (let i = 0; i < 6; i++) {
        await new Promise((r) => setTimeout(r, SOUNDS.turn.gapMs + 5));
        sound.play("turn");
    }
    // Sources never end in the fake, so the voice cap holds.
    assert.equal(made[0].started.length, SOUNDS.turn.voices);
});

test("mute silences, persists, and the toggle reflects it", async () => {
    const { Ctx } = fakeAudio();
    const t = target();
    const sound = createSound({ gestureTarget: t, AudioCtx: Ctx });
    t.fire("pointerdown");
    await new Promise((r) => setTimeout(r, 10));
    const button = { attrs: {}, textContent: "", setAttribute(k, v) { this.attrs[k] = v; }, addEventListener(_, fn) { this.click = fn; }, removeEventListener() {} };
    sound.bindToggle(button);
    assert.equal(button.attrs["aria-pressed"], "true");
    button.click();
    assert.equal(sound.muted, true);
    assert.equal(button.attrs["aria-pressed"], "false");
    assert.equal(button.textContent, "Sound");
    assert.match(button.title, /off/);
    assert.equal(globalThis.localStorage.getItem("cryptoys.megadreifach.muted"), "1");
    assert.equal(sound.play("chime"), false);
    button.click();
    assert.equal(sound.muted, false);
});
