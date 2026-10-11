import assert from "node:assert/strict";
import { readFileSync } from "node:fs";

// Source guard: app.js is a top-level browser module node cannot run.
// startAlgo starts a live follow that keeps orbit off until released
// (pose-controller.test.mjs), so it must end it once the enter is done.
const app = readFileSync(new URL("./app.js", import.meta.url), "utf8").replace(/\/\/.*$/gm, "");
const from = app.indexOf("async function startAlgo");
const next = app.slice(from + 1).search(/\n\s*(async )?function /);
const body = app.slice(from, next < 0 ? undefined : from + 1 + next);
const order = [/followLive(\?\.)?\(enterTrack\)/, /await adapter\.enter\(/, /followLive\s*(\?\.)?\s*\(\s*null\s*\)/, /markBeat\("enter-done"\)/];
let at = 0;
for (const re of order) {
    const i = body.slice(at).search(re);
    assert.ok(i >= 0, `startAlgo: ${re} after the previous step (follow, enter, release, enter-done)`);
    at += i + 1;
}
console.log("enter-follow tests ok");
