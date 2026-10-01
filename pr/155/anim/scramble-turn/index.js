/**
 * Scramble face turn: the cube lifts off the felt, cubing.js turns the
 * faces (each turn clicks just before its face seats) and the cube sets
 * down with a muffled pat. The values live in ./settings.js.
 *
 * Played by playroom/cube-stage.js around the Scramble rig (the
 * playroom's Scramble seat) and audited by demos/micro/scramble-turn.
 */
import settings from "./settings.js";
import { createVoice } from "../voice.js";
import { amountOf, cubingMs, slotOf, twistySlots } from "../twisty.js";

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
         * Playback of `leaves` started at `at` (performance.now()), each
         * leaf `durations[k]` ms long at tempo 1. A turn's contact is the
         * moment its face seats.
         */
        turns({ at, durations = [], tempo = timing.speed, leaves = [] }, when) {
            let t = at;
            leaves.forEach((move, k) => {
                t += (durations[k] ?? cubingMs(amountOf(move))) / tempo;
                v.contact(slotOf(move), t, { tempo, when });
            });
        },
        /** The cube touches the felt at `atMs`. */
        landing(atMs, when) {
            v.contact("settle", atMs, { when });
        },
    };
    return voice;
}
