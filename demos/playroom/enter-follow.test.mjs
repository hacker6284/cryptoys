import assert from "node:assert/strict";
import { readFileSync } from "node:fs";

// Source guard, not a behaviour test. startAlgo starts a live follow for
// the hub→seat flight, and while one is set the pose controller keeps
// orbit off (pose-controller.test.mjs covers that part). Whoever starts
// the follow ends it: if startAlgo does not, a demo picked from the hub
// stays undraggable. app.js is a top-level browser module (WebGL, DOM,
// top-level await), so node cannot run startAlgo; this reads its source.
const app = readFileSync(new URL("./app.js", import.meta.url), "utf8")
    .replace(/^\s*\/\/.*$/gm, "");

/** Text between the bracket at `open` and its match. */
function inside(src, open) {
    const [o, c] = src[open] === "(" ? ["(", ")"] : ["{", "}"];
    let depth = 0;
    for (let i = open; i < src.length; i += 1) {
        if (src[i] === o) depth += 1;
        else if (src[i] === c && --depth === 0) return { body: src.slice(open + 1, i), end: i };
    }
    assert.fail(`unbalanced ${o}${c} in app.js`);
}

function fnBody(name) {
    const m = new RegExp(`async function ${name}\\s*\\(`).exec(app);
    assert.ok(m, `${name} is in app.js`);
    const params = inside(app, m.index + m[0].length - 1);
    return inside(app, app.indexOf("{", params.end)).body;
}

const followCalls = (src) => [...src.matchAll(/\bfollowLive\s*(?:\?\.)?\s*\(\s*([\w$.]+)\s*\)/g)]
    .map((m) => ({ at: m.index, arg: m[1] }));

const start = fnBody("startAlgo");
const tryAt = start.search(/\btry\s*\{/);
assert.ok(tryAt >= 0, "startAlgo has a try block");
const success = inside(start, start.indexOf("{", tryAt)).body;
const starts = followCalls(success).filter((c) => c.arg !== "null");
assert.ok(starts.length > 0, "startAlgo starts a live follow for the enter flight");
const lastStart = Math.max(...starts.map((c) => c.at));
const enterAt = success.search(/await\s+adapter\.enter\s*\(/);
const doneAt = success.search(/markBeat\(\s*["']enter-done["']\s*\)/);
assert.ok(enterAt > lastStart && doneAt > enterAt, "follow, then adapter.enter, then enter-done");
const releases = followCalls(success).filter((c) => c.arg === "null" && c.at > enterAt && c.at < doneAt);
assert.ok(
    releases.length > 0,
    "startAlgo ends every live follow it starts, after adapter.enter and before enter-done",
);

// A leave during the enter returns early with the follow still set;
// leaveAlgo then owns it and must end it too.
assert.ok(
    followCalls(fnBody("leaveAlgo")).some((c) => c.arg === "null"),
    "leaveAlgo ends the live follow",
);

console.log("enter-follow tests ok");
