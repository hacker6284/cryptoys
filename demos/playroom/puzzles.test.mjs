import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import {
    PUZZLE_IDS,
    PUZZLES,
    normalizePuzzleId,
    puzzleHashes,
    readPuzzleSearchParam,
    writePuzzleSearchParam,
} from "./puzzles.js";

assert.deepEqual(PUZZLE_IDS, ["3x3x3", "megaminx", "pyraminx"]);
assert.equal(PUZZLES["3x3x3"].hash, true);
assert.equal(PUZZLES.megaminx.hash, false);
assert.equal(PUZZLES.pyraminx.hash, false);

assert.equal(normalizePuzzleId("mega"), "megaminx");
assert.equal(normalizePuzzleId("Pyra"), "pyraminx");
assert.equal(normalizePuzzleId("3x3"), "3x3x3");
assert.equal(normalizePuzzleId("nope"), "3x3x3");
assert.equal(puzzleHashes("3x3x3"), true);
assert.equal(puzzleHashes("megaminx"), false);
assert.equal(puzzleHashes("pyraminx"), false);

assert.equal(readPuzzleSearchParam("?algo=scramble&puzzle=mega"), "megaminx");
assert.equal(readPuzzleSearchParam("?algo=scramble"), "3x3x3");
assert.equal(
    writePuzzleSearchParam("pyraminx", "https://example.test/cryptoys/?algo=scramble"),
    "/cryptoys/?algo=scramble&puzzle=pyraminx",
);
assert.equal(
    writePuzzleSearchParam("3x3x3", "https://example.test/cryptoys/?algo=scramble&puzzle=megaminx"),
    "/cryptoys/?algo=scramble",
);

const adapters = readFileSync(new URL("./adapters.js", import.meta.url), "utf8");
const scrambleDockAt = adapters.indexOf('root.id = "scramble-dock"');
const doubleDealDockAt = adapters.indexOf('root.id = "doubledeal-dock"');
assert.ok(scrambleDockAt >= 0 && doubleDealDockAt > scrambleDockAt);
assert.match(adapters.slice(scrambleDockAt, doubleDealDockAt), /data-puzzle="megaminx"/);
assert.match(adapters.slice(scrambleDockAt, doubleDealDockAt), /data-puzzle="pyraminx"/);
assert.equal(adapters.slice(doubleDealDockAt).includes("data-puzzle"), false, "DoubleDeal dock stays untouched");
assert.match(adapters, /swapPuzzle: applyPuzzle/);

const session = readFileSync(new URL("../scramble/session.js", import.meta.url), "utf8");
assert.match(session, /projectAlgForPuzzle/);
assert.match(session, /data-puzzle/);
assert.match(session, /Solve is 3×3 only/);

console.log("puzzle mode tests ok");
