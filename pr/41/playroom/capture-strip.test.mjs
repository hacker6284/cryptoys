import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import {
    CAPTURE_INTERVAL_MS,
    CAPTURE_MAX_WIDTH,
    captureEnabled,
    frameIsBlank,
    installCapture,
    sheetLayout,
    slugBeat,
} from "./capture-strip.js";
import { CLOCK_STEP_MS } from "./constants.js";
import { markBeat, onMarkBeat } from "./motion.js";

assert.equal(captureEnabled(""), false);
assert.equal(captureEnabled("?debug=1"), false);
assert.equal(captureEnabled("?debugCapture=0"), false);
assert.equal(captureEnabled("?debugCapture=1"), true);
assert.equal(captureEnabled("?algo=doubledeal&debugCapture=1"), true);
assert.ok(CAPTURE_INTERVAL_MS >= 200 && CAPTURE_INTERVAL_MS <= 300);
assert.ok(CAPTURE_MAX_WIDTH >= 480 && CAPTURE_MAX_WIDTH <= 800);
assert.equal(CLOCK_STEP_MS, 50);
assert.equal(frameIsBlank(new Uint8ClampedArray(16)), true);
assert.equal(frameIsBlank(new Uint8ClampedArray([200, 180, 90, 255])), false);

assert.equal(slugBeat("lid-open"), "lid-open");
assert.equal(slugBeat("MSG out!"), "msg-out");

const layout = sheetLayout(13, { cols: 6, cellW: 320, cellH: 200 });
assert.equal(layout.cols, 6);
assert.equal(layout.rows, 3);
assert.equal(layout.width, 1920);
assert.equal(layout.height, 600);
assert.equal(sheetLayout(0).rows, 1);

const heard = [];
const stop = onMarkBeat((beat) => heard.push(beat));
markBeat("lid-receive");
assert.deepEqual(heard, ["lid-receive"]);
stop();
markBeat("ignored");
assert.deepEqual(heard, ["lid-receive"]);

const off = installCapture(null);
assert.equal(off.enabled, false);
off.begin("nope");
assert.equal(off.end(), null);
off.tick();
assert.equal(await off.exportSheet(), null);

const src = readFileSync(new URL("./capture-strip.js", import.meta.url), "utf8");
assert.match(src, /debugCapture/);
assert.match(src, /composeContactSheet/);
assert.match(src, /exportSheet/);
assert.match(src, /pendingBeat/);
assert.match(src, /frameIsBlank/);
assert.match(src, /onMarkBeat\(\(beat\) => \{/);
assert.ok(
    /onMarkBeat\(\(beat\) => \{[^}]*pendingBeat = true/s.test(src),
    "markBeat labels; tick samples after render",
);
assert.equal(src.includes("gsap"), false);

const app = readFileSync(new URL("./app.js", import.meta.url), "utf8");
assert.match(app, /installCapture/);
assert.match(app, /capture\.tick/);
assert.match(app, /capture\.begin/);
assert.match(app, /capture\.end/);

const director = readFileSync(new URL("./toy-director.js", import.meta.url), "utf8");
assert.match(director, /markBeat\("lid-open"\)/);
assert.match(director, /markBeat\("lid-receive"\)/);
assert.match(director, /markBeat\("fly-home"\)/);

const adapters = readFileSync(new URL("./adapters.js", import.meta.url), "utf8");
assert.match(adapters, /markBeat\("leave-gather"\)/);

console.log("capture-strip tests ok");
