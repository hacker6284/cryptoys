import { mountTwistyTurn } from "../shared/twisty-turn.js";
import settings from "./settings.js";

// The megaminx in the playroom Scramble seat (the adapter's debug puzzle
// path; MegaDreifach's own stage is not on main). 72° per click.
void mountTwistyTurn({
    id: "megaminx-turn",
    title: "Megaminx face turn",
    puzzle: "megaminx",
    defaultMove: "U",
    moves: { U: ["U"], Ui: ["U'"], U2: ["U2"], U3: ["U3"], R: ["R"], R2: ["R2"], seq: ["R", "U", "R'", "U'"] },
}, settings);
