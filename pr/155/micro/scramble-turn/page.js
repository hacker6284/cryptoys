import { mountTwistyTurn } from "../shared/twisty-turn.js";
import settings from "./settings.js";

void mountTwistyTurn({
    id: "scramble-turn",
    title: "Scramble face turn",
    defaultMove: "R",
    moves: { R: ["R"], Ri: ["R'"], R2: ["R2"], seq: ["R", "U", "R'", "U'"], x: ["x"], R3: ["R3"] },
}, settings);
