// Viewer for the scramble-turn library entry (demos/anim/scramble-turn):
// loops it on the real playroom code. The values are in
// demos/anim/scramble-turn/settings.js.
import { mountTwistyTurn } from "../shared/twisty-turn.js";
import { settings, scrambleTurnVoice } from "../../anim/scramble-turn/index.js";

void mountTwistyTurn({
    id: "scramble-turn",
    title: "Scramble face turn",
    defaultMove: "R",
    moves: { R: ["R"], Ri: ["R'"], R2: ["R2"], seq: ["R", "U", "R'", "U'"], x: ["x"], R3: ["R3"] },
    voice: scrambleTurnVoice(),
}, settings);
