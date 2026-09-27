import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import {
    PUZZLE_IDS,
    PUZZLES,
    normalizePuzzleId,
    playroomDebugEnabled,
    puzzleHashes,
    readPuzzleSearchParam,
    resolveProductPuzzleId,
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

assert.equal(playroomDebugEnabled(""), false);
assert.equal(playroomDebugEnabled("?algo=scramble"), false);
assert.equal(playroomDebugEnabled("?debug=1"), true);
assert.equal(playroomDebugEnabled("?algo=scramble&debug=1"), true);
assert.equal(playroomDebugEnabled("?debug=0"), false);

assert.equal(resolveProductPuzzleId("mega"), "3x3x3");
assert.equal(resolveProductPuzzleId("mega", "?debug=1"), "megaminx");
assert.equal(resolveProductPuzzleId("Pyra", "?algo=scramble&debug=1"), "pyraminx");

assert.equal(readPuzzleSearchParam("?algo=scramble&puzzle=mega"), "3x3x3");
assert.equal(readPuzzleSearchParam("?algo=scramble&puzzle=pyraminx"), "3x3x3");
assert.equal(readPuzzleSearchParam("?algo=scramble"), "3x3x3");
assert.equal(readPuzzleSearchParam("?algo=scramble&puzzle=mega&debug=1"), "megaminx");
assert.equal(readPuzzleSearchParam("?algo=scramble&debug=1&puzzle=pyra"), "pyraminx");
assert.equal(
    writePuzzleSearchParam("pyraminx", "https://example.test/cryptoys/?algo=scramble"),
    "/cryptoys/?algo=scramble",
);
assert.equal(
    writePuzzleSearchParam("pyraminx", "https://example.test/cryptoys/?algo=scramble&debug=1"),
    "/cryptoys/?algo=scramble&debug=1&puzzle=pyraminx",
);
assert.equal(
    writePuzzleSearchParam("3x3x3", "https://example.test/cryptoys/?algo=scramble&debug=1&puzzle=megaminx"),
    "/cryptoys/?algo=scramble&debug=1",
);
assert.equal(
    writePuzzleSearchParam("3x3x3", "https://example.test/cryptoys/?algo=scramble&puzzle=megaminx"),
    "/cryptoys/?algo=scramble",
);

const adapters = readFileSync(new URL("./adapters.js", import.meta.url), "utf8");
const scrambleDockAt = adapters.indexOf('root.id = "scramble-dock"');
const doubleDealDockAt = adapters.indexOf('root.id = "doubledeal-dock"');
assert.ok(scrambleDockAt >= 0 && doubleDealDockAt > scrambleDockAt);
assert.match(adapters.slice(scrambleDockAt, doubleDealDockAt), /data-puzzle-ctl hidden/);
assert.match(adapters.slice(scrambleDockAt, doubleDealDockAt), /data-puzzle="megaminx"/);
assert.match(adapters.slice(scrambleDockAt, doubleDealDockAt), /data-puzzle="pyraminx"/);
assert.equal(adapters.slice(doubleDealDockAt).includes("data-puzzle"), false, "DoubleDeal dock stays untouched");
assert.match(adapters, /swapPuzzle: applyPuzzle/);
assert.match(adapters, /playroomDebugEnabled\(\)/);
assert.match(adapters, /resolveProductPuzzleId/);

const session = readFileSync(new URL("../scramble/session.js", import.meta.url), "utf8");
assert.match(session, /projectAlgForPuzzle/);
assert.match(session, /data-puzzle/);
assert.match(session, /Solve is 3×3 only/);
assert.match(session, /resolveProductPuzzleId/);
assert.match(session, /playroomDebugEnabled\(\)/);

const app = readFileSync(new URL("./app.js", import.meta.url), "utf8");
assert.match(app, /playroomDebugEnabled\(url\.search\)/);
assert.match(app, /dataset\.playroomDebug = "1"/);

const css = readFileSync(new URL("./style.css", import.meta.url), "utf8");
assert.match(css, /html:not\(\[data-playroom-debug="1"\]\) \.playroom-ctl--puzzle/);

console.log("puzzle mode tests ok");
