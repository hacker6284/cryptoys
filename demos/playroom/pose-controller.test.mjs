import assert from "node:assert/strict";
import { register } from "node:module";

// pose-controller imports three from the CDN import map. Node has no
// map, so stand in a tiny Vector3 (only what the controller uses).
const threeStub = `
export class Vector3 {
    constructor(x = 0, y = 0, z = 0) { this.x = x; this.y = y; this.z = z; this.isVector3 = true; }
    set(x, y, z) { this.x = x; this.y = y; this.z = z; return this; }
    copy(v) { return this.set(v.x, v.y, v.z); }
    clone() { return new Vector3(this.x, this.y, this.z); }
    add(v) { return this.set(this.x + v.x, this.y + v.y, this.z + v.z); }
    sub(v) { return this.set(this.x - v.x, this.y - v.y, this.z - v.z); }
    multiplyScalar(s) { return this.set(this.x * s, this.y * s, this.z * s); }
    addScaledVector(v, s) { return this.set(this.x + v.x * s, this.y + v.y * s, this.z + v.z * s); }
    length() { return Math.hypot(this.x, this.y, this.z); }
    lerp(v, a) { return this.set(this.x + (v.x - this.x) * a, this.y + (v.y - this.y) * a, this.z + (v.z - this.z) * a); }
    lerpVectors(a, b, t) { return this.copy(a).lerp(b, t); }
}`;
// Only the OrbitControls surface the controller touches.
const orbitStub = `
export class OrbitControls {
    constructor() {
        this.enabled = true;
        this.updates = 0;
        this.target = { copy(v) { this.x = v.x; this.y = v.y; this.z = v.z; return this; } };
        (globalThis.orbitControls ||= []).push(this);
    }
    update() { this.updates += 1; }
}`;
const hooks = `
const MAP = {
    "three": "data:text/javascript," + encodeURIComponent(${JSON.stringify(threeStub)}),
    "three/addons/controls/OrbitControls.js": "data:text/javascript," + encodeURIComponent(${JSON.stringify(orbitStub)}),
};
export async function resolve(spec, ctx, next) {
    if (MAP[spec]) return { url: MAP[spec], shortCircuit: true };
    return next(spec, ctx);
}`;
register("data:text/javascript," + encodeURIComponent(hooks));
globalThis.window ??= {};

const { createPoseController } = await import("./pose-controller.js");
const { POSES } = await import("./poses.js");
const { Vector3 } = await import("three");

function makeCamera() {
    return {
        position: new Vector3(),
        up: new Vector3(0, 1, 0),
        fov: 40,
        updateProjectionMatrix() {},
        lookAt() {},
    };
}

// Play→hub return must land on the hub look with no final-frame snap.
// The toy set sits off the hub target (shelf + chest), as in production.
const poses = createPoseController(makeCamera());
poses.snap("scramble");
const track = { x: -1.445, y: 0.635, z: -0.55, r: 1.2 };
poses.followTo("landing", { mode: "return", track, duration: 2000, settleAt: 0.78 });
let now = performance.now();
const looks = [];
while (poses.busy) {
    now += 16;
    poses.update(now);
    looks.push({ ...poses.lookTarget });
}
const step = (a, b) => Math.hypot(a.x - b.x, a.y - b.y, a.z - b.z);
const hub = { x: POSES.landing.target[0], y: POSES.landing.target[1], z: POSES.landing.target[2] };
assert.ok(step(looks.at(-1), hub) < 1e-9, "return ends on the hub target");
const finalStep = step(looks.at(-1), looks.at(-2));
const settleSteps = looks.slice(-40, -1).map((l, i, arr) => (i ? step(l, arr[i - 1]) : 0));
assert.ok(finalStep < 0.005, `last return frame snaps the look by ${finalStep.toFixed(4)}`);
assert.ok(finalStep <= Math.max(...settleSteps) + 1e-9, "final frame is not the biggest look step");

// Hub→play enter: startAlgo pairs followTo with followLive on the same
// track. Orbit stays off while the live follow is set, even after the
// tween lands, and drives again once it is released. Whether startAlgo
// does release it is enter-follow.test.mjs.
{
    const poses = createPoseController(makeCamera(), { domElement: {} });
    const controls = globalThis.orbitControls.at(-1);
    const cube = { x: -0.35, y: 0.8, z: 0.15, r: 0.08 };
    let now = 0;
    const run = (ms) => {
        for (const end = now + ms; now < end;) poses.update((now += 16));
    };
    poses.snap("landing");
    poses.followTo("scramble", { track: cube, delay: 400, duration: 1600 });
    poses.followLive(cube);
    run(4000);
    assert.equal(poses.busy, false, "enter tween has landed");
    assert.equal(controls.enabled, false, "orbit stays off while the live follow is set");
    assert.equal(controls.updates, 0, "nothing drives orbit while following");
    poses.followLive(null);
    run(32);
    assert.equal(controls.enabled, true, "orbit is back once the follow is released");
    assert.ok(controls.updates > 0, "orbit is driven again after release");
    // startAlgo's error path snaps instead of releasing; snap clears it too.
    poses.followLive(cube);
    run(32);
    assert.equal(controls.enabled, false);
    poses.snap("landing");
    run(32);
    assert.equal(controls.enabled, true, "snap ends the live follow");
}

console.log("pose-controller tests ok");
