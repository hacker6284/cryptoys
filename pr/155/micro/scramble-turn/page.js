import { mountTwistyTurn } from "../shared/twisty-turn.js";

// Moves as Scramble plays them (see shared/twisty-turn.js).
void mountTwistyTurn({
    id: "scramble-turn",
    title: "Scramble: face turn",
    demo: "scramble",
    summary: "The playroom Scramble cube lifts, turns (cubing.js at the dock speed) and settles on the felt. Each loop undoes the last. Double and triple slots can also play the single file once per detent click.",
    source: "playroom/adapters.js createScrambleAdapter · cube-stage.js · twisty-rig.js",
    turnSlots: "scramble-turn",
    rotation: true,
    defaultMove: "R",
    moves: { R: ["R"], Ri: ["R'"], R2: ["R2"], seq: ["R", "U", "R'", "U'"], x: ["x"], R3: ["R3"] },
    moveOptions: [["R", "R (quarter)"], ["Ri", "R' (quarter back)"], ["R2", "R2 (half: double)"], ["seq", "R U R' U' (one lift)"], ["x", "x (whole-cube rotation)"], ["R3", "R3 (three clicks, triple slot)"]],
});
