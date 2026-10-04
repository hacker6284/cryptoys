import assert from "node:assert/strict";
import { readFileSync } from "node:fs";

// startAlgo starts a live follow for the hub→seat flight. While it is set the
// pose controller disables orbit every frame, so startAlgo must release it
// itself once the enter is done; an adapter that does not clear it (Scramble)
// otherwise leaves touch/mouse drag dead after picking it from the hub.
// app.js is a top-level browser module (DOM, WebGL), so this checks its source.
const app = readFileSync(new URL("./app.js", import.meta.url), "utf8");
const start = app.indexOf("async function startAlgo(");
const end = app.indexOf("async function leaveAlgo(");
assert.ok(start >= 0 && end > start, "startAlgo and leaveAlgo are where this test expects");
const body = app.slice(start, end);

const setAt = body.search(/poses\.followLive\?\.\(enterTrack\)/);
assert.ok(setAt >= 0, "startAlgo starts a live follow for the enter flight");
const enterAt = body.indexOf("await adapter.enter(");
assert.ok(enterAt > setAt, "the adapter enter runs after the follow starts");
const clearAt = body.indexOf("poses.followLive?.(null)", enterAt);
const doneAt = body.indexOf('markBeat("enter-done")', enterAt);
assert.ok(clearAt > enterAt && clearAt < doneAt, "startAlgo releases its live follow after adapter.enter, before enter-done");

console.log("enter-follow tests ok");
