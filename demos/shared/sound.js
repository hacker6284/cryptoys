/**
 * Demo sound: the MegaDreifach Web Audio path (keynote/megadreifach-demo,
 * demos/megadreifach/sound.js), with the sound table passed in.
 *
 * Web Audio only, and only after the first user gesture: nothing is
 * fetched or decoded until then. Mute is remembered in localStorage
 * under `store` (store: null keeps it in memory only).
 * Each sound has a minimum gap and a voice cap, so fast play is a
 * patter, not noise.
 *
 * sounds: { name: { files, gains (linear), gapMs, voices, offsetMs?, jitter? } }
 *   files    paths under `base`, without extension (.ogg or .mp3 is picked)
 *   offsetMs where the file starts relative to the sound's contact
 *            moment (negative = before). Callers pass `leadMs`, the time
 *            from now to contact. Without offsetMs the file starts now
 *            (the MegaDreifach behaviour).
 *   jitter   playbackRate spread (±); MegaDreifach's "turn" uses 0.06.
 *   maxMs    stop the file this long after it starts (0 = play it out)
 *   fadeMs   linear fade to silence over the last fadeMs before the stop
 *
 * limiter: a fast compressor on the master so boosted transients (gains
 * well above 0 dB) cannot clip.
 */

export function createSound({
    sounds,
    base,
    store = "cryptoys.sound.muted",
    gestureTarget = globalThis.window,
    AudioCtx = globalThis.AudioContext || globalThis.webkitAudioContext,
    level = 0.8,
    limiter = false,
} = {}) {
    let table = sounds || {};
    let ctx = null;
    let master = null;
    let muted = readMuted(store);
    let loading = null;
    let buffers = {};
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

    const cache = new Map();
    const fallbacks = [];
    async function fetchDecode(file, kind) {
        const url = new URL(`${file}.${kind}`, base).href;
        const response = await fetch(url);
        if (!response.ok) throw new Error(`sound ${file}.${kind}: HTTP ${response.status}`);
        return ctx.decodeAudioData(await response.arrayBuffer());
    }
    // A file that will not decode in the preferred format (a few very
    // short MP3s) falls back to its twin; the fallbacks are logged.
    function decode(file, kind) {
        const key = `${file}.${kind}`;
        if (!cache.has(key)) {
            cache.set(key, fetchDecode(file, kind).catch(async (err) => {
                const other = kind === "mp3" ? "ogg" : "mp3";
                try {
                    const buffer = await fetchDecode(file, other);
                    fallbacks.push({ file, from: kind, to: other, error: String(err?.message || err) });
                    console.warn(`sound: ${file}.${kind} did not decode; using .${other}`);
                    return buffer;
                } catch {
                    cache.delete(key);
                    throw err;
                }
            }));
        }
        return cache.get(key);
    }

    function load() {
        if (loading) return loading;
        const kind = ext();
        const next = {};
        loading = Promise.all(Object.entries(table).map(async ([name, spec]) => {
            next[name] = await Promise.all((spec.files || []).map((file) => decode(file, kind)));
        })).then(() => {
            buffers = next;
        }).catch((err) => {
            console.warn("sound failed to load", err);
        });
        return loading;
    }

    function unlock() {
        if (!AudioCtx) return;
        if (!ctx) {
            ctx = new AudioCtx();
            master = ctx.createGain();
            master.gain.value = muted ? 0 : level;
            if (limiter && ctx.createDynamicsCompressor) {
                const comp = ctx.createDynamicsCompressor();
                comp.threshold.value = -3;
                comp.knee.value = 0;
                comp.ratio.value = 20;
                comp.attack.value = 0.001;
                comp.release.value = 0.12;
                master.connect(comp).connect(ctx.destination);
            } else {
                master.connect(ctx.destination);
            }
            void load();
        }
        if (ctx.state === "suspended") void ctx.resume();
    }

    const onGesture = () => unlock();
    gestureTarget?.addEventListener?.("pointerdown", onGesture, { once: false, passive: true });
    gestureTarget?.addEventListener?.("keydown", onGesture);

    /**
     * Fire one sound (dropped if muted, locked, too soon or too busy).
     * leadMs: time from now to the sound's contact moment; the file
     * starts at contact + offsetMs (clamped to now: an earlier start
     * skips into the file instead).
     */
    function play(name, { gain = 1, leadMs = 0 } = {}) {
        if (muted || !ctx || ctx.state !== "running") return false;
        const spec = table[name];
        const list = buffers[name];
        if (!spec || !list?.length) return false;
        const now = performance.now();
        if (now - (last[name] ?? -1e9) < spec.gapMs) return false;
        if ((live[name] ?? 0) >= spec.voices) return false;
        last[name] = now;
        const i = (rr[name] = ((rr[name] ?? -1) + 1) % list.length);
        const src = ctx.createBufferSource();
        src.buffer = list[i];
        const jitter = spec.jitter ?? 0;
        src.playbackRate.value = jitter ? 1 - jitter + Math.random() * 2 * jitter : 1;
        const g = ctx.createGain();
        g.gain.value = (spec.gains[i] ?? spec.gains[0] ?? 1) * gain;
        src.connect(g).connect(master);
        live[name] = (live[name] ?? 0) + 1;
        src.onended = () => {
            live[name] -= 1;
        };
        const delay = spec.offsetMs === undefined ? 0 : (leadMs + spec.offsetMs) / 1000;
        const skip = delay < 0 ? Math.min(-delay, Math.max(0, (src.buffer.duration ?? 0) - 0.005)) : 0;
        const at = ctx.currentTime + Math.max(0, delay);
        if (delay > 0) src.start(at);
        else if (delay < 0) src.start(ctx.currentTime, skip);
        else src.start();
        const rate = src.playbackRate.value || 1;
        const natural = Math.max(0, ((src.buffer.duration ?? 0) - skip) / rate);
        const length = spec.maxMs > 0 ? Math.min(natural, spec.maxMs / 1000) : natural;
        if (spec.fadeMs > 0 && length > 0 && g.gain.setValueAtTime) {
            const fade = Math.min(length, spec.fadeMs / 1000);
            g.gain.setValueAtTime(g.gain.value, at + length - fade);
            g.gain.linearRampToValueAtTime(0, at + length);
        }
        if (spec.maxMs > 0 && length < natural) src.stop?.(at + length);
        return true;
    }

    /** Swap the sound table (files, gains, offsets); new files load now. */
    function configure(next) {
        table = next || {};
        for (const name of Object.keys(rr)) if (!table[name]) delete rr[name];
        if (!ctx) return Promise.resolve();
        loading = null;
        return load();
    }

    function setMuted(on) {
        muted = Boolean(on);
        try {
            if (store) globalThis.localStorage?.setItem(store, muted ? "1" : "0");
        } catch {
            // private mode
        }
        if (master) master.gain.value = muted ? 0 : level;
        if (!muted) unlock();
        for (const fn of listeners) fn(muted);
    }

    /** Wire a toggle button: aria-pressed = sound on. */
    function bindToggle(button) {
        if (!button) return () => {};
        const sync = () => {
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
        configure,
        setMuted,
        bindToggle,
        get muted() {
            return muted;
        },
        get started() {
            return Boolean(ctx);
        },
        get running() {
            return Boolean(ctx && ctx.state === "running");
        },
        get sounds() {
            return table;
        },
        /** Files that fell back to their twin format: [{ file, from, to, error }]. */
        get fallbacks() {
            return fallbacks.slice();
        },
        ready() {
            return loading || Promise.resolve();
        },
        dispose() {
            gestureTarget?.removeEventListener?.("pointerdown", onGesture);
            gestureTarget?.removeEventListener?.("keydown", onGesture);
        },
    };
}

function readMuted(store) {
    if (!store) return false;
    try {
        return globalThis.localStorage?.getItem(store) === "1";
    } catch {
        return false;
    }
}

/** dB ↔ linear gain helpers for tuning UIs. */
export function dbToGain(db) {
    return 10 ** (db / 20);
}

export function gainToDb(gain) {
    return gain > 0 ? 20 * Math.log10(gain) : -60;
}
