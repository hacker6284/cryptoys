import assert from "node:assert/strict";
import { apply_move, solved_facelets } from "./generated/scramble.mjs";
import { applyMove, LETTERS } from "./cube.js";

// Recorded from the hand-written turn code cube.js had before it used apply_move:
// each move on LETTERS, then three sequences.
const ONE = {
    "U": "258147036ijkcdefghABClmnopqrstuvwxyzJKLDEFGHI9abMNOPQR",
    "U'": "630741852JKLcdefgh9ablmnopqrstuvwxyzijkDEFGHIABCMNOPQR",
    "U2": "876543210ABCcdefghJKLlmnopqrstuvwxyz9abDEFGHIijkMNOPQR",
    "D": "0123456789abcdeopqijklmnGHIxuryvszwtABCDEFPQRJKLMNOfgh",
    "D'": "0123456789abcdePQRijklmnfghtwzsvyruxABCDEFopqJKLMNOGHI",
    "D2": "0123456789abcdeGHIijklmnPQRzyxwvutsrABCDEFfghJKLMNOopq",
    "R": "01k34n67qfc9gdahebijtlmwopzrsPuvMxyJABCDEFGHI8KL5NO2QR",
    "R'": "01P34M67Jbehadg9cfij2lm5op8rskuvnxyqABCDEFGHIzKLwNOtQR",
    "R2": "01t34w67zhgfedcba9ijPlmMopJrs2uv5xy8ABCDEFGHIqKLnNOkQR",
    "L": "R12O45L789abcdefgh0jk3mn6pqistlvwoyzGDAHEBIFCJKxMNuPQr",
    "L'": "i12l45o789abcdefghrjkumnxpqRstOvwLyzCFIBEHADGJK6MN3PQ0",
    "L2": "r12u45x789abcdefghRjkOmnLpq0st3vw6yzIHGFEDCBAJKoMNlPQi",
    "F": "012345IFC6ab7de8gholipmjqnkfc9uvwxyzABrDEsGHtJKLMNOPQR",
    "F'": "0123459cftabsderghknqjmpiloCFIuvwxyzAB8DE7GH6JKLMNOPQR",
    "F2": "012345tsrIabFdeCghqponmlkji876uvwxyzABfDEcGH9JKLMNOPQR",
    "B": "beh3456789azcdyfgxijklmnopqrstuvwADG2BC1EF0HIPMJQNKROL",
    "B'": "GDA3456789a0cd1fg2ijklmnopqrstuvwhebxBCyEFzHILORKNQJMP",
    "B2": "zyx3456789aGcdDfgAijklmnopqrstuvw210hBCeEFbHIRQPONMLKJ",
};
const ALL = Object.keys(ONE).join(" ");
const SEQUENCES = [
    [solved_facelets(), ALL, "WYWYWYWYWRORORORORGBGBGBGBGYWYWYWYWYOROROROROBGBGBGBGB"],
    [LETTERS, ALL, "0s2w4u6y89HbDdFfBhiQkMmOoKqr1t5v3x7zAgCcEeGaIJpLlNnPjR"],
    [solved_facelets(), "R U R' U' F2 D' L B2 L' D2 B' F U2 R2", "GGOGWBOOYGRYYRYBOYBBRBGOYGWBORYYWRRBORWYOWWBOGWWGBRRWG"],
];

for (const turn of [apply_move, applyMove]) {
    for (const [move, want] of Object.entries(ONE)) assert.equal(turn(LETTERS, move), want, move);
    for (const [start, moves, want] of SEQUENCES) assert.equal(moves.split(" ").reduce(turn, start), want, moves);
}
assert.throws(() => apply_move(LETTERS, "X"));
