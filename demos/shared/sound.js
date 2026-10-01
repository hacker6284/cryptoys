/**
 * Demo sound: the MegaDreifach Web Audio path (keynote/megadreifach-demo,
 * demos/megadreifach/sound.js), with the sound table passed in.
 *
 * One AudioContext per page (`sharedAudio()`), unlocked by the first
 * gesture anywhere: pointerdown, pointerup, mousedown, touchend, click or
 * keydown, caught on window in the capture phase so a canvas that stops
 * or prevents events (OrbitControls) cannot swallow it. Inside the
 * gesture, synchronously: audioSession "playback" (iOS: play with the
 * ring switch on silent), create or resume() the context, start a silent
 * one-sample buffer, and on iOS without audioSession loop a silent
 * <audio> clip (which switches the page to the playback category).
 * Browsers differ on which events count as a gesture (iOS: touchend and
 * click, not a touch pointerdown), so all of them try.
 *
 * Every createSound() on the page shares that context, so a demo opened
 * after the visitor has tapped the hub needs no prompt. With autostart
 * (the default) the context is also created on load and resume() tried:
 * where autoplay is allowed it simply runs; otherwise it stays suspended
 * until the first gesture. Sounds are fetched and decoded as soon as the
 * context exists, never blocking the unlock. Sound starts on; mute is
 * per page and not remembered.
 * Each sound has a minimum gap and a voice cap, so fast play is a
 * patter, not noise.
 *
 * sounds: { name: { files, gains (linear), gapMs, voices, offsetMs?, jitter? } }
 *   files    paths under `base`, without extension (.ogg or .mp3 is picked;
 *            a file that will not decode falls back to its twin)
 *   offsetMs where the file starts relative to the sound's contact
 *            moment (negative = before). Callers pass `leadMs`, the time
 *            from now to contact. Without offsetMs the file starts now
 *            (the MegaDreifach behaviour).
 *   jitter   playbackRate spread (±); MegaDreifach's "turn" uses 0.06.
 *   startMs  skip this much of the file's head (pre-roll); offsetMs still
 *            counts from the untrimmed start
 *   maxMs    stop the file this long after it starts (0 = play it out)
 *   fadeMs   linear fade to silence over the last fadeMs before the stop
 *
 * limiter: a fast compressor on the master so boosted transients (gains
 * well above 0 dB) cannot clip.
 */

const GESTURES = ["pointerdown", "pointerup", "mousedown", "touchend", "click", "keydown"];

function isIOS(nav) {
    const ua = nav?.userAgent || "";
    return /iPad|iPhone|iPod/.test(ua) || (nav?.platform === "MacIntel" && nav?.maxTouchPoints > 1);
}

let silentClip = null;
/** A short silent 8 kHz mono WAV as a data: URL (for the iOS <audio> trick). */
function silentWavUrl() {
    if (silentClip) return silentClip;
    const samples = 2000;
    const bytes = new Uint8Array(44 + samples * 2);
    const view = new DataView(bytes.buffer);
    const text = (at, str) => [...str].forEach((c, i) => view.setUint8(at + i, c.charCodeAt(0)));
    text(0, "RIFF");
    view.setUint32(4, 36 + samples * 2, true);
    text(8, "WAVEfmt ");
    view.setUint32(16, 16, true);
    view.setUint16(20, 1, true);
    view.setUint16(22, 1, true);
    view.setUint32(24, 8000, true);
    view.setUint32(28, 16000, true);
    view.setUint16(32, 2, true);
    view.setUint16(34, 16, true);
    text(36, "data");
    view.setUint32(40, samples * 2, true);
    let bin = "";
    for (const b of bytes) bin += String.fromCharCode(b);
    silentClip = `data:audio/wav;base64,${btoa(bin)}`;
    return silentClip;
}

/**
 * The page's audio: one context, unlocked by the first gesture.
 * state: "unsupported" | "none" (not created yet) | the context's state.
 */
export function createAudioHub({
    AudioCtx = globalThis.AudioContext || globalThis.webkitAudioContext,
    gestureTarget = globalThis.window,
    nav = globalThis.navigator,
    HtmlAudio = globalThis.Audio,
} = {}) {
    let ctx = null;
    let installed = false;
    let clip = null;
    let gestures = 0;
    const fns = new Set();

    const state = () => (!AudioCtx ? "unsupported" : ctx ? ctx.state : "none");
    function notify() {
        const now = state();
        for (const fn of fns) {
            try {
                fn(now);
            } catch (err) {
                console.warn("sound: state listener failed", err);
            }
        }
    }

    function playbackSession() {
        try {
            if (nav?.audioSession && nav.audioSession.type !== "playback") nav.audioSession.type = "playback";
        } catch {
            // read-only or unsupported
        }
    }

    function ensure() {
        if (!AudioCtx) return null;
        if (ctx && ctx.state !== "closed") return ctx;
        playbackSession();
        try {
            ctx = new AudioCtx({ latencyHint: "interactive" });
        } catch {
            ctx = new AudioCtx();
        }
        if (ctx.addEventListener) ctx.addEventListener("statechange", notify);
        else ctx.onstatechange = notify;
        queueMicrotask(notify);
        return ctx;
    }

    function resume() {
        if (!ctx || ctx.state === "running" || ctx.state === "closed") return;
        try {
            const p = ctx.resume();
            if (p?.then) p.then(notify, notify);
        } catch {
            // old WebKit: resume() may throw instead of rejecting
        }
    }

    function silentTick() {
        try {
            const src = ctx.createBufferSource();
            src.buffer = ctx.createBuffer(1, 1, ctx.sampleRate || 22050);
            src.connect(ctx.destination);
            src.start(0);
        } catch {
            // fakes and very old engines
        }
    }

    function silentClipLoop() {
        if (nav?.audioSession || !isIOS(nav) || !HtmlAudio) return;
        try {
            if (!clip) {
                clip = new HtmlAudio(silentWavUrl());
                clip.loop = true;
                clip.preload = "auto";
                clip.setAttribute?.("playsinline", "");
            }
            if (clip.paused) clip.play()?.catch?.(() => {});
        } catch {
            // no <audio>
        }
    }

    /** Create the context and try resume() without a gesture (works where autoplay is allowed). */
    function tryStart() {
        if (nav?.getAutoplayPolicy?.("audiocontext") === "disallowed") return ctx;
        if (ensure()) resume();
        return ctx;
    }

    /** Call inside a user gesture; everything happens synchronously here. */
    function unlock() {
        playbackSession();
        if (!ensure()) return null;
        if (ctx.state !== "running") {
            resume();
            silentTick();
        }
        silentClipLoop();
        return ctx;
    }

    function onGesture() {
        gestures += 1;
        if (state() !== "running" || clip?.paused) unlock();
    }

    function install() {
        if (installed || !gestureTarget?.addEventListener) return;
        installed = true;
        for (const type of GESTURES) gestureTarget.addEventListener(type, onGesture, { capture: true, passive: true });
    }

    function uninstall() {
        if (!installed) return;
        installed = false;
        for (const type of GESTURES) gestureTarget.removeEventListener?.(type, onGesture, { capture: true });
    }

    return {
        get ctx() {
            return ctx;
        },
        get state() {
            return state();
        },
        get gestures() {
            return gestures;
        },
        tryStart,
        unlock,
        install,
        uninstall,
        onState(fn) {
            fns.add(fn);
            return () => fns.delete(fn);
        },
    };
}

let pageHub = null;
/** The page's shared audio hub (one AudioContext for every demo on the page). */
export function sharedAudio() {
    if (!pageHub) pageHub = createAudioHub();
    return pageHub;
}

/** Unlock the page's audio on the first gesture anywhere (call once at startup). */
export function installAudioUnlock() {
    const hub = sharedAudio();
    hub.install();
    return hub;
}

export function createSound({
    sounds,
    base,
    audio,
    gestureTarget,
    AudioCtx,
    level = 0.8,
    limiter = false,
    autostart = true,
} = {}) {
    // A private hub when the caller injects its own context class or
    // gesture target (tests); otherwise the page's shared one.
    const hub = audio || (AudioCtx || gestureTarget ? createAudioHub({ AudioCtx, gestureTarget }) : sharedAudio());
    let table = sounds || {};
    let ctx = null;
    let master = null;
    let muted = false;
    let loading = null;
    let buffers = {};
    const last = {};
    const live = {};
    const rr = {};
    const listeners = new Set();

    function ext() {
        // WebKit (Safari, every iOS browser): MP3, its Ogg decoding is patchy.
        const ua = globalThis.navigator?.userAgent || "";
        if (isIOS(globalThis.navigator) || (/Safari\//.test(ua) && !/Chrome|Chromium|Android/.test(ua))) return "mp3";
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
        const data = await response.arrayBuffer();
        // Callback form too: old WebKit's decodeAudioData returns no promise.
        return new Promise((resolve, reject) => {
            const p = ctx.decodeAudioData(data, resolve, reject);
            if (p?.then) p.then(resolve, reject);
        });
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

    // Build this engine's master (and limiter) on the hub's context once
    // it exists, then fetch and decode in the background.
    function attach() {
        const now = hub.ctx;
        if (!now || now === ctx) return;
        ctx = now;
        cache.clear();
        loading = null;
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

    /** Unlock now (call from inside a gesture; the hub's listeners already do). */
    function unlock() {
        hub.unlock();
        attach();
    }

    const stateFns = new Set();
    const offState = hub.onState((state) => {
        attach();
        for (const fn of stateFns) fn(state);
    });
    hub.install();
    if (autostart) hub.tryStart();
    attach();

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
        // startMs trims the file's head; offsetMs still counts from the
        // untrimmed start, so −peak keeps the peak on the contact.
        const head = Math.max(0, spec.startMs ?? 0) / 1000;
        const delay = spec.offsetMs === undefined ? 0 : (leadMs + spec.offsetMs) / 1000 + head;
        const skip = Math.min(head + (delay < 0 ? -delay : 0), Math.max(0, (src.buffer.duration ?? 0) - 0.005));
        const at = ctx.currentTime + Math.max(0, delay);
        if (delay > 0) src.start(at, ...(skip ? [skip] : []));
        else if (delay < 0 || skip) src.start(ctx.currentTime, skip);
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
            return Boolean(hub.ctx);
        },
        get running() {
            return hub.state === "running";
        },
        /** "unsupported" | "none" | "suspended" | "running" | "interrupted" | "closed" */
        get state() {
            return hub.state;
        },
        /** Call fn(state) whenever the context's state changes. Returns an unsubscribe. */
        onState(fn) {
            stateFns.add(fn);
            return () => stateFns.delete(fn);
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
            offState();
            stateFns.clear();
        },
    };
}

/** dB ↔ linear gain helpers for tuning UIs. */
export function dbToGain(db) {
    return 10 ** (db / 20);
}

export function gainToDb(gain) {
    return gain > 0 ? 20 * Math.log10(gain) : -60;
}
