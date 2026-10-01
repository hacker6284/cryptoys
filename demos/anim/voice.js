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
            offsetMs: s.offsetMs ?? 0,
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

export function createVoice({ settings, slots, base, autostart = false }) {
    const sounds = settings.sounds || {};
    const sound = createSound({ sounds: soundTable(slots, sounds), base, limiter: true, autostart });
    const timers = new Set();

    function later(ms, fn) {
        const id = setTimeout(() => {
            timers.delete(id);
            fn();
        }, Math.max(0, ms));
        timers.add(id);
    }

    /**
     * Sound for slot `name` whose contact is at performance.now() time
     * `atMs` (the file starts at contact + offsetMs). `when()` is asked
     * again just before a later start, so a cancelled motion stays quiet.
     *
     * stretch: for a sound tied to a motion played at another speed than
     * the one it was tuned at (tuned tempo / actual tempo). The time from
     * the file's loudest sample to the contact is multiplied by it, so the
     * sound keeps its place in the motion: half the tempo, twice the lead.
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
        atMs = stretchContact(atMs, s.offsetMs ?? 0, sound.peakMs(name) ?? 0, stretch);
        const now = performance.now();
        const startIn = atMs + (s.offsetMs ?? 0) - now;
        if (startIn > 90) {
            later(startIn - 60, () => {
                if (!when || when()) sound.play(name, { leadMs: atMs - performance.now() });
            });
        } else {
            sound.play(name, { leadMs: atMs - now });
        }
    }

    /** Lead-in so every listed [slot, atMs] file can start on time: max(0, −(atMs + offset)). */
    function leadIn(list, tempo = settings.timing?.speed ?? 1) {
        let lead = 0;
        for (const [name, atMs] of list) {
            const s = sounds[name];
            if (!s) continue;
            if (s.perClick) {
                const pc = slots.find((slot) => slot.name === name)?.perClick;
                const off = sounds[pc?.slot]?.offsetMs ?? 0;
                for (const rel of pc ? pc.clicks(tempo) : []) lead = Math.max(lead, -(atMs + rel + off));
            } else if (s.file) {
                lead = Math.max(lead, -(atMs + (s.offsetMs ?? 0)));
            }
        }
        return Math.min(2000, lead);
    }

    function cancel() {
        for (const id of timers) clearTimeout(id);
        timers.clear();
    }

    return { sound, settings, slots, contact, leadIn, cancel };
}
