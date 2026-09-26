import assert from "node:assert/strict";
import { createBeatClock, lerp } from "./beat-clock.js";
import {
    continueTo,
    hopTo,
    pose3,
    seatToys,
    trackEnter,
    trackToy,
    waitToyIdle,
} from "./motion.js";

assert.deepEqual(pose3({ x: 1, y: 2, z: 3 }), {
    x: 1, y: 2, z: 3, rx: null, ry: null, rz: null,
});
assert.deepEqual(pose3({
    position: { x: 1, y: 2, z: 3 },
    rotation: { x: 0.1, y: 0.2, z: 0.3 },
}), { x: 1, y: 2, z: 3, rx: 0.1, ry: 0.2, rz: 0.3 });

function makeObject(x, y, z) {
    return {
        position: { x, y, z },
        rotation: { x: 0, y: 0, z: 0, set(nx, ny, nz) {
            this.x = nx; this.y = ny; this.z = nz;
        } },
        quaternion: { setFromEuler() {} },
        userData: {},
    };
}

const clock = createBeatClock({ reduced: true });
const gen = clock.begin();
const toy = makeObject(0, 0, 0);
await hopTo(toy, { x: 2, y: 1, z: 4, rx: 0, ry: 0.5, rz: 0 }, clock, gen, {
    ms: 400,
    lift: 0.1,
});
assert.equal(toy.position.x, 2);
assert.equal(toy.position.y, 1);
assert.equal(toy.position.z, 4);
assert.equal(toy.rotation.y, 0.5);

toy.userData.flightBusy = true;
const idle = waitToyIdle(toy, clock, gen, { tries: 3, ms: 10 });
toy.userData.flightBusy = false;
await idle;

const world = { toys: { cube: { position: { x: 9, y: 8, z: 7 } } } };
assert.deepEqual(trackToy(world, "cube")(), { x: 9, y: 8, z: 7 });

const snaps = [];
const goes = [];
const poses = {
    snap(name) { snaps.push(name); return name; },
    goTo(name, opts) { goes.push({ name, opts }); return name; },
    playTo(name, opts) { goes.push({ name, play: true, opts }); return Promise.resolve(name); },
};
trackEnter(poses, { to: "lean", track: () => {}, holdMs: 760, duration: 1000, reduced: true });
assert.deepEqual(snaps, ["lean"]);
trackEnter(poses, { to: "unbox_travel", track: "fn", holdMs: 760, duration: 1040 });
assert.equal(goes[0].name, "unbox_travel");
assert.equal(goes[0].opts.delay, 760);
assert.equal(goes[0].opts.duration, 1040);
assert.equal(goes[0].opts.track, "fn");

await continueTo(poses, "doubledeal", { duration: 1280 });
assert.equal(goes.at(-1).name, "doubledeal");
assert.equal(goes.at(-1).play, true);

const restWorld = {
    toys: { deck: makeObject(0, 1, 0) },
    getBoxRestPose() {
        return { position: { x: 3, y: 1, z: -1 }, rotation: { x: 0, y: 0.2, z: 0 } };
    },
};
await seatToys(restWorld, clock, gen, ["deck"]);
assert.equal(restWorld.toys.deck.position.x, 3);
assert.equal(restWorld.toys.deck.position.z, -1);
assert.ok(Math.abs(lerp(0, 1, 0.5) - 0.5) < 1e-9);

console.log("motion tests ok");
