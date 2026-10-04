// Viewer for the scramble-turn library entry's whole-cube rotation
// (its rotation slot): the cube lifts, turns over as one piece the way
// the playroom's Scramble does, and sets down. The values are in
// demos/anim/scramble-turn/settings.js (choices.rotation picks the move).
import { mountTwistyTurn } from "../shared/twisty-turn.js";
import { settings, scrambleTurnVoice } from "../../anim/scramble-turn/index.js";

void mountTwistyTurn({
    id: "scramble-rotate",
    title: "Scramble whole-cube rotation",
    choice: "rotation",
    defaultMove: "y",
    moves: { y: ["y"], yi: ["y'"], x: ["x"], xi: ["x'"], z: ["z"], zy: ["z", "y"] },
    voice: scrambleTurnVoice(),
}, settings);
