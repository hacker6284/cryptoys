// Viewer for the megaminx library entry (demos/anim/megaminx):
// loops it on the real playroom code, the megaminx in the Scramble seat
// (the adapter's debug puzzle path; MegaDreifach's own stage is on
// PR #194). The values are in demos/anim/megaminx/settings.js. The
// default loop (choices.move "U-U2-U3") is a single, double and triple
// turn, one step each, with its sound and landing pat.
import { mountTwistyTurn } from "../../shared/twisty-turn.js";
import { settings, timing, megaminxTurnVoice } from "../../../anim/megaminx/index.js";

void mountTwistyTurn({
    id: "megaminx-turn",
    title: "Megaminx face turn",
    puzzle: "megaminx",
    order: 5, // 72° turns
    defaultMove: "U",
    moves: { U: ["U"], Ui: ["U'"], U2: ["U2"], U3: ["U3"], R: ["R"], R2: ["R2"], seq: ["R", "U", "R'", "U'"], "U-U2-U3": { steps: ["U", "U2", "U3"] } },
    voice: megaminxTurnVoice(),
    timing,
}, settings);
