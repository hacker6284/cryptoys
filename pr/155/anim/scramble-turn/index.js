/**
 * Scramble face turn: the cube lifts off the felt, cubing.js turns the
 * faces (each turn's click centred where its face turns fastest) and the cube sets
 * down with a muffled pat. The values live in ./settings.js.
 *
 * Played by playroom/cube-stage.js around the Scramble rig (the
 * playroom's Scramble seat) and audited by demos/micro/scramble-turn.
 */
import settings from "./settings.js";
import { createVoice } from "../voice.js";
import { PEAK_VELOCITY, amountOf, cubingMs, slotOf, twistySlots } from "../twisty.js";

export { settings };
export const timing = settings.timing;
export const slots = twistySlots();

const SOUNDS = new URL("../sounds/", import.meta.url);
let voice = null;

/**
 * The entry's sounds on the page's shared AudioContext (made once).
 * Each hook takes a `when()` guard, asked again just before a sound
 * that starts later, so a cancelled motion stays quiet.
 */
/**
 * [slot, contactMs, stretch, tempo] per leaf of a playback starting at
 * `at`. A face turn with align "peak-velocity" has its contact where its
 * face turns fastest (PEAK_VELOCITY of the way through, scaling with the
 * turn); other face turns on their start; rotations (and per-click
 * turns, whose clicks count back from the seat) on their end.
 */
export function turnContacts({ at, durations = [], tempo = timing.speed, leaves = [] }) {
    const stretch = timing.speed / tempo;
    const out = [];
    let t = at;
    leaves.forEach((move, k) => {
        const len = (durations[k] ?? cubingMs(amountOf(move))) / tempo;
        const slot = slotOf(move);
        const s = settings.sounds[slot];
        const onEnd = slot === "rotation" || s?.perClick;
        const contact = onEnd ? t + len : s?.align === "peak-velocity" ? t + PEAK_VELOCITY * len : t;
        out.push([slot, contact, stretch, tempo]);
        t += len;
    });
    return out;
}

export function scrambleTurnVoice() {
    if (voice) return voice;
    const v = createVoice({ settings, slots, base: SOUNDS });
    voice = {
        sound: v.sound,
        /** The cube leaves the felt at `atMs`. */
        lift(atMs, when) {
            v.contact("lift", atMs, { when });
        },
        /**
         * Playback of `leaves` starts at `at` (performance.now()), each
         * leaf `durations[k]` ms long at tempo 1. A face turn's contact
         * is the moment its face turns fastest (align "peak-velocity");
         * a rotation's is the moment it ends. Tuned
         * at timing.speed; at another tempo each sound keeps its place in
         * the turn. `at` may be in the future (see lead()).
         */
        turns(info, when) {
            for (const [slot, atMs, stretch, tempo] of turnContacts(info)) v.contact(slot, atMs, { tempo, stretch, when });
        },
        /**
         * How long before the turn starts its first sound's file has to
         * start (a click on the turn start begins before it), plus 30 ms
         * for pitch jitter and timers: the stage hands the voice the turn
         * this long ahead.
         */
        lead(info) {
            const list = turnContacts({ ...info, at: 0 });
            const ms = list.length ? v.startsBefore(list.map(([slot, atMs, stretch]) => [slot, atMs, stretch]), 0, list[0][3]) : 0;
            return ms > 0 ? ms + 30 : 0;
        },
        /** The cube touches the felt at `atMs`. */
        landing(atMs, when) {
            v.contact("settle", atMs, { when });
        },
    };
    return voice;
}
