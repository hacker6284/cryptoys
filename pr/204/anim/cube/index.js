/**
 * Scramble face turn: the cube lifts off the felt, cubing.js turns the
 * faces (each turn's sound centred where its face turns fastest, each
 * rotation's where the cube does) and the cube sets down with a muffled
 * pat. The values live in ./settings.js.
 *
 * Played by playroom/cube-stage.js around the Scramble rig (the
 * playroom's Scramble seat) and audited by demos/micro/cube/face-turn and
 * demos/micro/cube/rotate.
 */
import settings from "./settings.js";
import { twistySlots } from "../shared/twisty.js";
import { createTwistyVoice, twistyContacts } from "../shared/twisty-voice.js";

export { settings };
export const timing = settings.timing;
export const slots = twistySlots();

const SOUNDS = new URL("../sounds/", import.meta.url);
let voice = null;

/** [slot, contactMs, stretch, tempo] per leaf (see twisty-voice.js twistyContacts). */
export function turnContacts(info) {
    return twistyContacts(settings, info);
}

/** The entry's sounds on the page's shared AudioContext (made once). */
export function scrambleTurnVoice() {
    voice ??= createTwistyVoice({ settings, slots, base: SOUNDS });
    return voice;
}
