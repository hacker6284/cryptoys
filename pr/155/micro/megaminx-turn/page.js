import { mountTwistyTurn } from "../shared/twisty-turn.js";
import { DEN } from "../../playroom/constants.js";

// The megaminx in the playroom Scramble seat (the adapter's debug
// puzzle path; MegaDreifach's own stage is not on main). Same lift /
// turn / settle beats as the 3×3; a face turn is 72° per click.
void mountTwistyTurn({
    id: "megaminx-turn",
    title: "Megaminx: face turn",
    demo: "megadreifach (megaminx on the Scramble adapter)",
    puzzle: "megaminx",
    summary: "The megaminx lifts, turns one face by one, two or three clicks (72° each, cubing.js smootherStep at the dock speed) and settles. Compare the recorded and COMPOSITE doubles/triples with the single file played once per click at the real click times.",
    source: "playroom/adapters.js createScrambleAdapter (puzzle megaminx) · cube-stage.js · twisty-rig.js",
    turnSlots: "megaminx-turn",
    rotation: false,
    camera: { position: [DEN.x + 0.32, 1.17, DEN.z + 0.74], target: [DEN.x, 0.9, DEN.z], fov: 22 },
    defaultMove: "U",
    moves: { U: ["U"], Ui: ["U'"], U2: ["U2"], U3: ["U3"], R: ["R"], R2: ["R2"], seq: ["R", "U", "R'", "U'"] },
    moveOptions: [["U", "U (one click)"], ["Ui", "U' (one click back)"], ["U2", "U2 (two clicks: double)"], ["U3", "U3 (three clicks: triple)"], ["R", "R (one click)"], ["R2", "R2 (two clicks)"], ["seq", "R U R' U' (one lift)"]],
});
