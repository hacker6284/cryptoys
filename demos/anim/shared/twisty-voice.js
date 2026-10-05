/**
 * The voice of a twisty-puzzle turn entry (scramble-turn, megaminx-turn):
 * a lift sound, a sound per face turn and per whole-puzzle rotation, and
 * a pat where the puzzle lands, played by playroom/cube-stage.js.
 */
import { createVoice } from "./voice.js";
import { PEAK_VELOCITY, amountOf, cubingMs, slotOf } from "./twisty.js";

/**
 * [slot, contactMs, stretch, tempo] per leaf of a playback starting at
 * `at` (performance.now()), each leaf `durations[k]` ms long at tempo 1.
 * A turn or rotation with align "peak-velocity" has its contact where it
 * turns fastest (`peakVelocity` of the way through, scaling with the
 * move); otherwise rotations (and per-click turns, whose clicks count
 * back from the seat) on their end, face turns on their start.
 */
export function twistyContacts(settings, { at, durations = [], tempo = settings.timing.speed, leaves = [] }, peakVelocity = PEAK_VELOCITY) {
    const stretch = settings.timing.speed / tempo;
    const out = [];
    let t = at;
    leaves.forEach((move, k) => {
        const len = (durations[k] ?? cubingMs(amountOf(move))) / tempo;
        const slot = slotOf(move);
        const s = settings.sounds[slot];
        const contact = s?.align === "peak-velocity" ? t + peakVelocity * len
            : slot === "rotation" || s?.perClick ? t + len : t;
        out.push([slot, contact, stretch, tempo]);
        t += len;
    });
    return out;
}

/**
 * The entry's sounds on the page's shared AudioContext. Each hook takes
 * a `when()` guard, asked again just before a sound that starts later,
 * so a cancelled motion stays quiet.
 */
export function createTwistyVoice({ settings, slots, base, peakVelocity = PEAK_VELOCITY }) {
    const v = createVoice({ settings, slots, base });
    const contacts = (info) => twistyContacts(settings, info, peakVelocity);
    return {
        sound: v.sound,
        /** The puzzle leaves the felt at `atMs`. */
        lift(atMs, when) {
            v.contact("lift", atMs, { when });
        },
        /**
         * Playback of `leaves` starts at `at` (it may be in the future, see
         * lead()). Tuned at timing.speed; at another tempo each sound keeps
         * its place in the move.
         */
        turns(info, when) {
            for (const [slot, atMs, stretch, tempo] of contacts(info)) v.contact(slot, atMs, { tempo, stretch, when });
        },
        /**
         * How long before the playback starts its first sound's file has
         * to start, plus 30 ms for pitch jitter and timers: the stage hands
         * the voice the turn this long ahead (during the lift).
         */
        lead(info) {
            const list = contacts({ ...info, at: 0 });
            const ms = list.length ? v.startsBefore(list.map(([slot, atMs, stretch]) => [slot, atMs, stretch]), 0, list[0][3]) : 0;
            return ms > 0 ? ms + 30 : 0;
        },
        /** The puzzle touches the felt at `atMs`. */
        landing(atMs, when) {
            v.contact("settle", atMs, { when });
        },
    };
}
