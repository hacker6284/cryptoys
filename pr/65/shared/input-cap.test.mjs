import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { clipInputValue, DEMO_INPUT_MAX_CHARS } from "./input-cap.js";

assert.equal(DEMO_INPUT_MAX_CHARS, 4096, "demo Message cap is 4 KiB of characters");
assert.deepEqual(clipInputValue("hello"), { value: "hello", truncated: false });
assert.deepEqual(clipInputValue("x".repeat(4096)), { value: "x".repeat(4096), truncated: false });
const clipped = clipInputValue("x".repeat(4096) + "OVERFLOW");
assert.equal(clipped.truncated, true);
assert.equal(clipped.value.length, 4096);
assert.equal(clipped.value.endsWith("x"), true);
assert.equal(clipped.value.includes("OVERFLOW"), false);

const src = readFileSync(new URL("./input-cap.js", import.meta.url), "utf8");
assert.match(src, /Bee Movie/);
assert.match(src, /preventDefault/);
assert.match(src, /DEMO_INPUT_DEBOUNCE_MS/);

const scramble = readFileSync(new URL("../scramble/session.js", import.meta.url), "utf8");
const doubledeal = readFileSync(new URL("../doubledeal/session.js", import.meta.url), "utf8");
assert.match(scramble, /bindCappedInput/);
assert.match(doubledeal, /bindCappedInput/);
assert.doesNotMatch(scramble, /input\?\.addEventListener\("input", \(\) => recompute\(\)/);
assert.doesNotMatch(scramble, /onChange:\s*\(\)\s*=>\s*recompute\(\)/);
assert.match(scramble, /onChange:\s*\(\)\s*=>\s*refreshDigest\(\)/);
assert.doesNotMatch(doubledeal, /messageEl\?\.addEventListener\("input", preview/);

const adapters = readFileSync(new URL("../playroom/adapters.js", import.meta.url), "utf8");
assert.match(adapters, /id="io-note"/);

console.log("input-cap tests ok");
