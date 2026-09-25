import assert from "node:assert/strict";
import { applyMove, SOLVED_FACELETS } from "../scramble/cube.js";
import {
    applyRotationToCenters,
    colorOnFace,
    mapTraceToAlg,
    prefixAlg,
    projectAlgForPuzzle,
    reorientMoves,
    unitInAlphabet,
} from "./scramble-alg.js";

assert.deepEqual(reorientMoves(SOLVED_FACELETS, "W", "G"), []);
assert.deepEqual(reorientMoves(SOLVED_FACELETS, "R", "G"), ["z'"]);
assert.deepEqual(reorientMoves(SOLVED_FACELETS, "G", "W"), ["x", "y2"]);
assert.deepEqual(reorientMoves(SOLVED_FACELETS, "Y", "G"), ["x2", "y2"]);

function seat(facelets, up, front) {
    let next = facelets;
    for (const move of reorientMoves(facelets, up, front)) {
        next = applyRotationToCenters(next, move);
    }
    return { u: colorOnFace(next, "U"), f: colorOnFace(next, "F") };
}

for (const [up, front] of [["W", "G"], ["R", "G"], ["G", "W"], ["Y", "B"], ["O", "W"], ["B", "R"]]) {
    const got = seat(SOLVED_FACELETS, up, front);
    assert.equal(got.u, up, `${up} should sit on U (front ${front})`);
    assert.equal(got.f, front, `${front} should sit on F (up ${up})`);
}

const afterR = applyMove(SOLVED_FACELETS, "R");
const afterRuleB = applyRotationToCenters(afterR, "z'");
const mapped = mapTraceToAlg([
    { kind: "move", move: "R", facelets: afterR },
    { kind: "ruleB", up: "R", front: "G", facelets: afterRuleB },
    { kind: "closer", move: "F2", facelets: afterRuleB },
    { kind: "canonicalize", up: "W", front: "G", facelets: SOLVED_FACELETS },
]);
assert.equal(mapped.alg, "R z' F2 z");
assert.deepEqual(mapped.ranges, [
    { from: 0, to: 1 },
    { from: 1, to: 2 },
    { from: 2, to: 3 },
    { from: 3, to: 4 },
]);
assert.equal(prefixAlg(mapped, -1), "");
assert.equal(prefixAlg(mapped, 0), "R");
assert.equal(prefixAlg(mapped, 1), "R z'");

const cubeProj = projectAlgForPuzzle(mapped, "3x3x3");
assert.equal(cubeProj.alg, mapped.alg);
assert.equal(cubeProj.hash, true);
assert.equal(cubeProj.dropped, 0);

const megaProj = projectAlgForPuzzle(mapped, "megaminx");
assert.equal(megaProj.alg, "R z' F2 z");
assert.equal(megaProj.hash, false);
assert.equal(megaProj.dropped, 0);

const pyraProj = projectAlgForPuzzle(mapped, "pyraminx");
assert.equal(pyraProj.alg, "R z' z");
assert.equal(pyraProj.hash, false);
assert.equal(pyraProj.dropped, 1);
assert.deepEqual(pyraProj.ranges, [
    { from: 0, to: 1 },
    { from: 1, to: 2 },
    { from: 2, to: 2 },
    { from: 2, to: 3 },
]);
assert.equal(unitInAlphabet("F2", "pyraminx"), false);
assert.equal(unitInAlphabet("B2", "pyraminx"), true);
assert.equal(unitInAlphabet("x'", "megaminx"), true);

const identityB = mapTraceToAlg([
    { kind: "move", move: "U", facelets: applyMove(SOLVED_FACELETS, "U") },
    { kind: "ruleB", up: "W", front: "G", facelets: applyMove(SOLVED_FACELETS, "U") },
]);
assert.equal(identityB.alg, "U");
assert.deepEqual(identityB.ranges[1], { from: 1, to: 1 });

console.log("scramble alg tests ok");
