import assert from "node:assert/strict";
import { createBeatClock, lerp } from "./beat-clock.js";
import {
    centroidOf,
    continueTo,
    followEnter,
    followLeave,
    hopTo,
    pose3,
    seatToys,
    trackActive,
    trackEnter,
    trackToy,
    trackToys,
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
assert.deepEqual(centroidOf([{ x: 0, y: 0, z: 0 }, { x: 2, y: 4, z: 6 }]), { x: 1, y: 2, z: 3 });
assert.equal(centroidOf([]), null);

const two = {
    toys: {
        deck: { position: { x: 0, y: 1, z: 0 }, userData: { flightBusy: true } },
        deck2: { position: { x: 4, y: 1, z: 0 }, userData: {} },
        cube: { position: { x: 9, y: 8, z: 7 }, userData: {} },
    },
};
const both = trackToys(two, ["deck", "deck2"])();
assert.equal(both.x, 2);
assert.equal(both.y, 1);
assert.equal(both.z, 0);
assert.ok(both.r >= 2, "bounds span both decks");
const flying = trackActive(two, ["deck", "deck2"])();
assert.equal(flying.x, 0);
assert.equal(flying.y, 1);
assert.equal(flying.z, 0);
two.toys.deck.userData.flightBusy = false;
const rested = trackActive(two, ["deck", "deck2"])();
assert.equal(rested.x, 2);
assert.equal(rested.z, 0);
two.toys.deck2.userData.unboxBusy = true;
const unbox = trackActive(two, ["deck", "deck2"])();
assert.equal(unbox.x, 4);
assert.equal(unbox.z, 0);

const packet = {
    name: "packet",
    position: { x: 1, y: 2, z: 3 },
    userData: { unboxBusy: true },
};
const extract = trackActive(two, ["deck", "deck2"], [packet])();
assert.equal(extract.x, 1);
assert.equal(extract.z, 3);

const snaps = [];
const goes = [];
const follows = [];
const poses = {
    snap(name) { snaps.push(name); return name; },
    goTo(name, opts) { goes.push({ name, opts }); return name; },
    followTo(name, opts) { follows.push({ name, opts }); return name; },
    playTo(name, opts) { goes.push({ name, play: true, opts }); return Promise.resolve(name); },
};
trackEnter(poses, { to: "lean", track: () => {}, holdMs: 760, duration: 1000, reduced: true });
assert.deepEqual(snaps, ["lean"]);
trackEnter(poses, { to: "unbox_travel", track: "fn", holdMs: 760, duration: 1040 });
assert.equal(goes[0].name, "unbox_travel");
assert.equal(goes[0].opts.delay, 760);
assert.equal(goes[0].opts.duration, 1040);
assert.equal(goes[0].opts.track, "fn");

followEnter(poses, { to: "scramble", track: "cube", holdMs: 220, duration: 1800, reduced: true });
assert.equal(snaps.at(-1), "scramble");
followEnter(poses, { to: "doubledeal", track: "toys", holdMs: 220, duration: 1800 });
assert.equal(follows[0].name, "doubledeal");
assert.equal(follows[0].opts.delay, 220);
assert.equal(follows[0].opts.duration, 1800);
assert.equal(follows[0].opts.track, "toys");
assert.equal(follows[0].opts.settleAt, 0.9);

followLeave(poses, { track: "home", holdMs: 220, duration: 2880, reduced: true });
assert.equal(snaps.at(-1), "landing");
followLeave(poses, { track: "home", holdMs: 220, duration: 2880 });
assert.equal(follows[1].name, "landing");
assert.equal(follows[1].opts.delay, 220);
assert.equal(follows[1].opts.duration, 2880);
assert.equal(follows[1].opts.track, "home");
assert.equal(follows[1].opts.settleAt, 0.78);
assert.equal(follows[1].opts.mode, "return");

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
