// Viewer for the scramble-turn library entry (demos/anim/scramble-turn):
// loops it on the real playroom code. The values are in
// demos/anim/scramble-turn/settings.js. The default loop (choices.move
// "R-R2-R3") is one step each of a single, double and triple turn, each
// with its own lift, sound and landing pat, as the playroom plays a step.
import { mountTwistyTurn } from "../shared/twisty-turn.js";
import { settings, scrambleTurnVoice } from "../../anim/scramble-turn/index.js";

void mountTwistyTurn({
    id: "scramble-turn",
    title: "Scramble face turn",
    defaultMove: "R",
    moves: { R: ["R"], Ri: ["R'"], R2: ["R2"], seq: ["R", "U", "R'", "U'"], x: ["x"], R3: ["R3"], "R-R2-R3": { steps: ["R", "R2", "R3"] } },
    voice: scrambleTurnVoice(),
}, settings);
