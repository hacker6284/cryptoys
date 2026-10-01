import assert from "node:assert/strict";

globalThis.window = { setTimeout, clearTimeout };
globalThis.requestAnimationFrame = (fn) => setTimeout(() => fn(performance.now()), 16);

const { CUBE_STAGE_TIMING, stageCubeView } = await import(new URL("./cube-stage.js", import.meta.url));
const scrambleTurn = await import(new URL("../anim/scramble-turn/index.js", import.meta.url));
const calls = [];
const rig = {
    group: { position: { y: 0 }, userData: {} },
    playLeaves: async (from, to) => {
        calls.push([from, to]);
        return { index: to - 1, total: to };
    },
};
const stage = stageCubeView(rig, {});
stage.rememberSeated();
const lifting = stage.playLeaves(0, 1);
await stage.settle({ snap: true });
assert.equal(await lifting, undefined, "a settle during the lift drops the pending turn");
assert.deepEqual(calls, [], "the stale turn never reaches the rig");
await new Promise((r) => setTimeout(r, 500));
assert.equal(rig.group.position.y, 0, "cube is back on its seat");
assert.deepEqual(await stage.playLeaves(0, 1), { index: 0, total: 1 }, "next Play still lifts and plays");

// Sound: the stage hands each turn to its voice as playback starts, and
// sounds the landing where the set-down ends (not on a snap settle).
const heard = [];
const voice = {
    lift: (at) => heard.push(["lift"]),
    turns: (info, when) => heard.push(["turns", info.leaves, info.tempo, when]),
    landing: (at, when) => heard.push(["landing", at, when]),
};
const sounding = {
    group: { position: { y: 0 }, userData: {} },
    playLeaves: async (from, to, { onStart }) => {
        onStart?.({ at: performance.now(), durations: [1000], tempo: 1.4, leaves: ["R"] });
        return { index: to - 1, total: to };
    },
};
const timing = { TURN_LIFT: 0.1, TURN_LIFT_MS: 40, SETTLE_HOLD_MS: 10 };
const loud = stageCubeView(sounding, { voice, timing });
loud.rememberSeated();
await loud.playLeaves(0, 1);
const turn = heard.find(([kind]) => kind === "turns");
assert.deepEqual(turn.slice(1, 3), [["R"], 1.4], "the voice gets the leaves and the tempo");
assert.equal(turn[3](), false, "clicks still pending after playback ends stay quiet");
const setDownAt = performance.now();
await new Promise((r) => setTimeout(r, 200));
const landings = heard.filter(([kind]) => kind === "landing");
assert.equal(landings.length, 1, "one landing when the cube sets down");
assert.ok(Math.abs(landings[0][1] - (setDownAt + timing.SETTLE_HOLD_MS + timing.TURN_LIFT_MS)) < 40, "landing at the end of the set-down");
assert.equal(sounding.group.position.y, 0, "cube is back on its seat");
await loud.settle({ snap: true });
assert.equal(heard.filter(([kind]) => kind === "landing").length, 1, "a snap settle makes no landing sound");
assert.ok(CUBE_STAGE_TIMING === scrambleTurn.timing, "stage timing is the library entry's, not a copy");

console.log("cube-stage lift/settle tests ok");
