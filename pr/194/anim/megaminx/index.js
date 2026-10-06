/**
 * Megaminx face turn: the puzzle lifts off the felt, cubing.js turns a
 * face (its sound centred where the face turns fastest) and the puzzle
 * sets down with the muffled pat. The values live in ./settings.js.
 *
 * Played by playroom/cube-stage.js around a megaminx rig (pass
 * { voice: megaminxTurnVoice(), timing } to stageCubeView) and audited by
 * demos/micro/megaminx/face-turn. MegaDreifach's own stage (PR #153) should
 * import it from here when it lands.
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
export function megaminxTurnVoice() {
    voice ??= createTwistyVoice({ settings, slots, base: SOUNDS });
    return voice;
}
