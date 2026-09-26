import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import {
    CAM_ACCEL_LOOK,
    CAM_ACCEL_POS,
    CAPTURE_DEDUPE_MS,
    CAPTURE_INTERVAL_MS,
    CAPTURE_MAX_WIDTH,
    cameraAccel,
    captureEnabled,
    frameIsBlank,
    installCapture,
    isCamAccelSpike,
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
assert.equal(CAPTURE_INTERVAL_MS, 200);
assert.equal(CAPTURE_DEDUPE_MS, CLOCK_STEP_MS);
assert.ok(CAPTURE_MAX_WIDTH >= 400 && CAPTURE_MAX_WIDTH <= 800);
assert.equal(CLOCK_STEP_MS, 50);
assert.equal(frameIsBlank(new Uint8ClampedArray(16)), true);
assert.equal(frameIsBlank(new Uint8ClampedArray([200, 180, 90, 255])), false);

assert.equal(slugBeat("lid-open"), "lid-open");
assert.equal(slugBeat("camAccel"), "camaccel");
assert.equal(slugBeat("MSG out!"), "msg-out");

const layout = sheetLayout(13, { cols: 6, cellW: 320, cellH: 200 });
assert.equal(layout.cols, 6);
assert.equal(layout.rows, 3);
assert.equal(layout.width, 1920);
assert.equal(layout.height, 600);
assert.equal(sheetLayout(0).rows, 1);

const still = cameraAccel(
    { pos: { x: 0.1, y: 0, z: 0 }, look: { x: 0, y: 0, z: 0 } },
    { pos: { x: 0.12, y: 0, z: 0 }, look: { x: 0, y: 0, z: 0 } },
    0.05,
);
assert.ok(still.pos < CAM_ACCEL_POS, "ease-sized Δv is not a spike");
assert.equal(isCamAccelSpike(still, {}, { pos: { x: 0.4, y: 0, z: 0 }, look: { x: 0, y: 0, z: 0 } }, { pos: { x: 0.2, y: 0, z: 0 }, look: { x: 0, y: 0, z: 0 } }), false);

const snap = cameraAccel(
    { pos: { x: 0, y: 0, z: 0 }, look: { x: 0, y: 0, z: 0 } },
    { pos: { x: 3, y: 0, z: 0 }, look: { x: 1.5, y: 0, z: 0 } },
    0.05,
);
assert.ok(snap.pos >= CAM_ACCEL_POS);
assert.ok(snap.look >= CAM_ACCEL_LOOK);
assert.equal(isCamAccelSpike(snap), true);

const reverse = cameraAccel(
    { pos: { x: 1.2, y: 0, z: 0 }, look: { x: 0.4, y: 0, z: 0 } },
    { pos: { x: -1.1, y: 0, z: 0 }, look: { x: -0.5, y: 0, z: 0 } },
    0.05,
);
assert.equal(reverse.reverse, true);
assert.equal(isCamAccelSpike(reverse), true);

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
assert.match(src, /pendingAccel/);
assert.match(src, /nextGridAt/);
assert.match(src, /camAccel/);
assert.match(src, /onMarkBeat\(\(beat\) => \{/);
assert.ok(
    /onMarkBeat\(\(beat\) => \{[^}]*pendingBeat = true/s.test(src),
    "markBeat labels; tick samples after render",
);
assert.equal(src.includes("evenly spaced between beats"), false);
assert.equal(src.includes("gsap"), false);

const app = readFileSync(new URL("./app.js", import.meta.url), "utf8");
assert.match(app, /installCapture/);
assert.match(app, /capture\.tick/);
assert.match(app, /poses\.lookTarget/);
assert.match(app, /capture\.begin/);
assert.match(app, /capture\.end/);

assert.match(app, /markBeat\("enter-start"\)/);
assert.match(app, /markBeat\("enter-landed"\)/);
assert.match(app, /markBeat\("leave-start"\)/);
assert.match(app, /markBeat\("hub-settle"\)/);

const director = readFileSync(new URL("./toy-director.js", import.meta.url), "utf8");
assert.match(director, /cube-fly/);
assert.match(director, /markBeat\("fly-home"\)/);

console.log("capture-strip tests ok");
