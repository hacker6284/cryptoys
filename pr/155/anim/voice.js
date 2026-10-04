/**
 * A library entry's sounds: its settings.sounds turned into a
 * demos/shared/sound.js player, plus contact() to time them.
 *
 * createVoice({ settings, slots, base })
 *   slots  [{ name, gapMs, voices, jitter, perClick }]
 *          perClick: { slot, clicks(tempo) } lets settings say
 *          `{ perClick: true }`: play `slot`'s file once per click
 *          (clicks(tempo) returns ms relative to the contact, ≤ 0)
 *   base   URL of the folder holding the files (demos/anim/sounds/)
 *
 * A sound is placed one of two ways (settings.sounds[slot]):
 *   offsetMs   the file starts this long after the contact (negative =
 *              before; −peak puts the loudest sample on it)
 *   peakAtMs   the file's loudest sample lands this long after the
 *              contact (0 = on it; positive = later), whatever the file's
 *              head; measured from the decoded file
 *   align      the centre of the file lands on the contact, + nudgeMs
 *              (later if positive); the entry says what the contact is
 *              for its align rule (e.g. "peak-velocity"). centre: which
 *              centre: "audible" (default; sound.js audibleCentroidMs, for
 *              clicks) or "swell" (sound.js swellMs, its loudest 10 ms,
 *              for a swish).
 *              align "motion-start" instead puts the file's audible onset
 *              (sound.js audibleOnsetMs: its attack, the first moment
 *              within −30 dB of its peak) on the contact, + nudgeMs: for
 *              an action sound that starts as the motion starts (the
 *              contact is the motion's start); nudge it later if it feels
 *              early.
 *
 * The voice uses the page's shared AudioContext (sharedAudio() in
 * sound.js), so the hub tap, the iOS unlock and mute work the same in
 * every demo. It never starts the context itself.
 */
import { createSound, dbToGain } from "../shared/sound.js";

/** The sound.js table for `settings.sounds` (slots without a file are left out). */
export function soundTable(slots, sounds) {
    const table = {};
    for (const slot of slots) {
        const s = sounds?.[slot.name];
        if (!s?.file) continue;
        table[slot.name] = {
            files: [s.file],
            gains: [dbToGain(s.gainDb ?? 0)],
            gapMs: slot.gapMs ?? 0,
            voices: slot.voices ?? 4,
            // peakAtMs / align: contact() passes the time to the file's start itself.
            offsetMs: placed(s) ? 0 : s.offsetMs ?? 0,
            ...(s.startMs ? { startMs: s.startMs } : {}),
            ...(s.maxMs ? { maxMs: s.maxMs } : {}),
            ...(s.fadeMs ? { fadeMs: s.fadeMs } : {}),
            ...(slot.jitter ? { jitter: slot.jitter } : {}),
        };
    }
    return table;
}

/**
 * The contact time that puts the file's loudest sample `stretch` times
 * as far from the real contact `atMs` as it is when tuned (the file
 * starts at the returned time + offsetMs).
 */
export function stretchContact(atMs, offsetMs, peakMs, stretch) {
    return atMs + (offsetMs + peakMs) * (stretch - 1);
}

/** Placed by a moment inside the file (peakAtMs or align) rather than by its start. */
function placed(s) {
    return s.peakAtMs != null || s.align != null;
}

/**
 * When the file starts (performance.now() ms) for a sound `s` whose
 * contact is at `atMs`. `file` = { peakMs, centroidMs, swellMs } of the
 * decoded file (+ onsetMs). align: its centre (motion-start: its
 * audible onset) lands nudgeMs × stretch after the contact. peakAtMs:
 * its loudest sample lands peakAtMs × stretch after.
 * offsetMs: see stretchContact.
 */
export function fileStart(s, atMs, file = {}, stretch = 1) {
    const { peakMs = 0 } = typeof file === "number" ? { peakMs: file } : file;
    if (s.align != null) return atMs + (s.nudgeMs ?? 0) * stretch - centreOf(s, file);
    if (s.peakAtMs != null) return atMs + s.peakAtMs * stretch - (peakMs ?? 0);
    const off = s.offsetMs ?? 0;
    return stretchContact(atMs, off, peakMs ?? 0, stretch) + off;
}

/** The aligned moment of a file: its audible onset (motion-start), audible centroid, or swell. */
function centreOf(s, file) {
    if (s.align === "motion-start") return file.onsetMs ?? 0;
    return (s.centre === "swell" ? file.swellMs : file.centroidMs) ?? 0;
}

/** The file moment that holds still under pitch jitter (0: its start). */
function anchorOf(s, file) {
    if (s.align != null) return centreOf(s, file);
    if (s.peakAtMs != null) return file.peakMs ?? 0;
    return 0;
}

export function createVoice({ settings, slots, base, autostart = false }) {
    const sounds = settings.sounds || {};
    const sound = createSound({ sounds: soundTable(slots, sounds), base, limiter: true, autostart });
    const timers = new Set();
    const describe = (name) => ({ peakMs: sound.peakMs(name) ?? 0, centroidMs: sound.centroidMs?.(name) ?? 0, swellMs: sound.swellMs?.(name) ?? 0, onsetMs: sound.onsetMs?.(name) ?? 0 });

    function later(ms, fn) {
        const id = setTimeout(() => {
            timers.delete(id);
            fn();
        }, Math.max(0, ms));
        timers.add(id);
    }

    /**
     * Sound for slot `name` whose contact is at performance.now() time
     * `atMs` (the file starts at contact + offsetMs, or so its loudest
     * sample lands at contact + peakAtMs). `when()` is asked again just
     * before a later start, so a cancelled motion stays quiet.
     *
     * stretch: for a sound tied to a motion played at another speed than
     * the one it was tuned at (tuned tempo / actual tempo). The time from
     * the contact to the file's loudest sample is multiplied by it, so the
     * sound keeps its place in the motion: half the tempo, twice as far.
     */
    function contact(name, atMs, { tempo = settings.timing?.speed ?? 1, stretch = 1, when = null } = {}) {
        const s = sounds[name];
        if (!s) return;
        if (s.perClick) {
            const pc = slots.find((slot) => slot.name === name)?.perClick;
            if (pc) for (const rel of pc.clicks(tempo)) contact(pc.slot, atMs + rel, { tempo, stretch, when });
            return;
        }
        if (!s.file) return;
        const file = describe(name);
        const start = fileStart(s, atMs, file, stretch);
        // sound.js starts the file at leadMs + its table offsetMs.
        const tableOffset = placed(s) ? 0 : s.offsetMs ?? 0;
        // The placed moment (loudest click / audible centre) holds still under pitch jitter.
        const anchorMs = anchorOf(s, file);
        const now = performance.now();
        const startIn = start - now;
        if (startIn > 90) {
            later(startIn - 60, () => {
                if (!when || when()) sound.play(name, { leadMs: start - tableOffset - performance.now(), anchorMs });
            });
        } else {
            sound.play(name, { leadMs: start - tableOffset - now, anchorMs });
        }
    }

    /**
     * How long before `atMs` the earliest file of these contacts starts
     * (0 if none starts before it): [[slot, contactMs, stretch]].
     */
    function startsBefore(list, atMs, tempo = settings.timing?.speed ?? 1) {
        let lead = 0;
        for (const [name, at, stretch = 1] of list) {
            const s = sounds[name];
            if (!s) continue;
            if (s.perClick) {
                const pc = slots.find((slot) => slot.name === name)?.perClick;
                if (pc) lead = Math.max(lead, startsBefore(pc.clicks(tempo).map((rel) => [pc.slot, at + rel, stretch]), atMs, tempo));
            } else if (s.file) {
                lead = Math.max(lead, atMs - fileStart(s, at, describe(name), stretch));
            }
        }
        return lead;
    }

    /** Lead-in so every listed [slot, atMs] file can start on time (atMs relative to now = 0). */
    function leadIn(list, tempo = settings.timing?.speed ?? 1) {
        return Math.min(2000, startsBefore(list, 0, tempo));
    }

    function cancel() {
        for (const id of timers) clearTimeout(id);
        timers.clear();
    }

    return { sound, settings, slots, contact, startsBefore, leadIn, cancel };
}
