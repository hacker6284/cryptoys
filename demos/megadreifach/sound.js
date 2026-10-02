/**
 * MegaDreifach sound (new to the demos; CC0 files, assets/LICENSE.md).
 *
 * Web Audio only, and only after the first user gesture: nothing is
 * fetched or decoded until then. A visible toggle mutes it (remembered
 * in localStorage). Rapid turns at high speed are thinned: each sound
 * has a minimum gap and a voice cap, so a 12× solve is a patter, not
 * noise.
 *
 * Gains come from measured max-momentary loudness (ffmpeg ebur128, 400 ms
 * window) of the processed files: turn-1 −23.3, turn-2 −25.7, re-grip
 * −23.9, deal −26.7, felt −26.8, chime −23.2 LUFS. Clicks sit about
 * 10 dB under the chime.
 */

const BASE = new URL("./assets/sounds/", import.meta.url);
const STORE = "cryptoys.megadreifach.muted";

export const SOUNDS = {
    turn: { files: ["turn/turn-1_spacejoe-486576", "turn/turn-2_spacejoe-486585"], gains: [0.33, 0.43], gapMs: 55, voices: 3 },
    regrip: { files: ["regrip/regrip-2_bwarpus99-452535-slice"], gains: [0.31], gapMs: 140, voices: 2 },
    deal: { files: ["card-deal/deal-1_realsquink-787405"], gains: [0.54], gapMs: 70, voices: 3 },
    felt: { files: ["card-felt/felt-1_kenney-card-place-1"], gains: [0.49], gapMs: 90, voices: 2 },
    chime: { files: ["chime/chime-1_hollandm-691805-kalimba-g4"], gains: [0.8], gapMs: 400, voices: 1 },
};

function readMuted() {
    try {
        return globalThis.localStorage?.getItem(STORE) === "1";
    } catch {
        return false;
    }
}

export function createSound({ gestureTarget = globalThis.window, AudioCtx = globalThis.AudioContext || globalThis.webkitAudioContext } = {}) {
    let ctx = null;
    let master = null;
    let muted = readMuted();
    let loading = null;
    const buffers = {};
    const last = {};
    const live = {};
    const rr = {};
    const listeners = new Set();

    function ext() {
        try {
            const probe = new Audio();
            return probe.canPlayType("audio/ogg; codecs=vorbis") ? "ogg" : "mp3";
        } catch {
            return "mp3";
        }
    }

    async function load() {
        if (loading) return loading;
        const kind = ext();
        loading = Promise.all(Object.entries(SOUNDS).map(async ([name, spec]) => {
            buffers[name] = await Promise.all(spec.files.map(async (file) => {
                const response = await fetch(new URL(`${file}.${kind}`, BASE));
                if (!response.ok) throw new Error(`sound ${file}`);
                return ctx.decodeAudioData(await response.arrayBuffer());
            }));
        })).catch((err) => {
            console.warn("MegaDreifach sound failed to load", err);
        });
        return loading;
    }

    function unlock() {
        if (!AudioCtx) return;
        if (!ctx) {
            ctx = new AudioCtx();
            master = ctx.createGain();
            master.gain.value = muted ? 0 : 0.8;
            master.connect(ctx.destination);
            void load();
        }
        if (ctx.state === "suspended") void ctx.resume();
    }

    const onGesture = () => unlock();
    gestureTarget?.addEventListener?.("pointerdown", onGesture, { once: false, passive: true });
    gestureTarget?.addEventListener?.("keydown", onGesture);

    /** Fire one sound now (dropped if muted, locked, too soon or too busy). */
    function play(name, { gain = 1 } = {}) {
        if (muted || !ctx || ctx.state !== "running") return false;
        const spec = SOUNDS[name];
        const list = buffers[name];
        if (!spec || !list?.length) return false;
        const now = performance.now();
        if (now - (last[name] ?? -1e9) < spec.gapMs) return false;
        if ((live[name] ?? 0) >= spec.voices) return false;
        last[name] = now;
        const i = (rr[name] = ((rr[name] ?? -1) + 1) % list.length);
        const src = ctx.createBufferSource();
        src.buffer = list[i];
        src.playbackRate.value = name === "turn" ? 0.94 + Math.random() * 0.12 : 1;
        const g = ctx.createGain();
        g.gain.value = spec.gains[i] * gain;
        src.connect(g).connect(master);
        live[name] = (live[name] ?? 0) + 1;
        src.onended = () => {
            live[name] -= 1;
        };
        src.start();
        return true;
    }

    function setMuted(on) {
        muted = Boolean(on);
        try {
            globalThis.localStorage?.setItem(STORE, muted ? "1" : "0");
        } catch {
            // private mode
        }
        if (master) master.gain.value = muted ? 0 : 0.8;
        if (!muted) unlock();
        for (const fn of listeners) fn(muted);
    }

    /** Wire a toggle button: aria-pressed = sound on. */
    function bindToggle(button) {
        if (!button) return () => {};
        const sync = () => {
            // One short label; aria-pressed (and a strike-through) carry the state.
            button.setAttribute("aria-pressed", muted ? "false" : "true");
            button.setAttribute("aria-label", "Sound");
            button.textContent = "Sound";
            button.title = muted ? "Sound is off: turn it on" : "Sound is on: mute";
        };
        const click = () => setMuted(!muted);
        button.addEventListener("click", click);
        listeners.add(sync);
        sync();
        return () => {
            button.removeEventListener("click", click);
            listeners.delete(sync);
        };
    }

    return {
        play,
        unlock,
        setMuted,
        bindToggle,
        get muted() {
            return muted;
        },
        get started() {
            return Boolean(ctx);
        },
        dispose() {
            gestureTarget?.removeEventListener?.("pointerdown", onGesture);
            gestureTarget?.removeEventListener?.("keydown", onGesture);
        },
    };
}

/** No-op stand-in (tests, or before the adapter wires one). */
export const SILENT = { play: () => false, unlock() {}, setMuted() {}, bindToggle: () => () => {}, muted: true, started: false, dispose() {} };
