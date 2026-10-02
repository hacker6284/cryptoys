import assert from "node:assert/strict";

globalThis.window = { setTimeout, clearTimeout };
globalThis.requestAnimationFrame = (fn) => setTimeout(() => fn(performance.now()), 16);

const { CUBE_STAGE_TIMING, stageCubeView } = await import(new URL("./cube-stage.js", import.meta.url));
const scrambleTurn = await import(new URL("../anim/scramble-turn/index.js", import.meta.url));
const calls = [];
const rig = {
    group: { position: { y: 0 }, userData: {} },
    // Like twisty-rig: readies the leaves, asks beforeStart, then plays.
    playLeaves: async (from, to, { beforeStart } = {}) => {
        if (beforeStart && !(await beforeStart({ durations: [1000], tempo: 1.4, leaves: ["R"] }))) return { index: from, total: to };
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
let startedAt = 0;
const voice = {
    lift: (at) => heard.push(["lift"]),
    lead: () => 30,
    turns: (info, when) => heard.push(["turns", info.leaves, info.tempo, when, info.at, performance.now()]),
    landing: (at, when) => heard.push(["landing", at, when]),
};
const sounding = {
    group: { position: { y: 0 }, userData: {} },
    playLeaves: async (from, to, { onStart, beforeStart }) => {
        const info = { durations: [1000], tempo: 1.4, leaves: ["R"] };
        if (beforeStart && !(await beforeStart(info))) return { index: from, total: to };
        startedAt = performance.now();
        onStart?.({ at: startedAt, ...info });
        return { index: to - 1, total: to };
    },
};
const timing = { TURN_LIFT: 0.1, TURN_LIFT_MS: 40, SETTLE_HOLD_MS: 10 };
const loud = stageCubeView(sounding, { voice, timing });
loud.rememberSeated();
const liftStart = performance.now();
await loud.playLeaves(0, 1);
const turn = heard.find(([kind]) => kind === "turns");
assert.deepEqual(turn.slice(1, 3), [["R"], 1.4], "the voice gets the leaves and the tempo");
assert.equal(turn[3](), false, "clicks still pending after playback ends stay quiet");
assert.ok(turn[5] < turn[4] - 20, "the voice hears the turn before it starts (during the lift)");
assert.ok(Math.abs(startedAt - turn[4]) < 20, "the turn starts when planned");
assert.ok(turn[4] - liftStart >= timing.TURN_LIFT_MS - 5, "and not before the lift ends");
// Already up (the next step of a Play): the turn waits out the lead-in.
heard.length = 0;
const again = loud.playLeaves(1, 2);
const askedAt = performance.now();
await again;
const next = heard.find(([kind]) => kind === "turns");
assert.ok(next[4] - askedAt >= 25 && Math.abs(startedAt - next[4]) < 20, "cube already up: the turn starts after the voice's lead-in");
// No lead-in (the single click): no wait, and the voice hears the turn
// as it really starts (onStart), as before.
voice.lead = () => 0;
heard.length = 0;
const quick = loud.playLeaves(2, 3);
const quickAt = performance.now();
await quick;
const plain = heard.find(([kind]) => kind === "turns");
assert.ok(startedAt - quickAt < 15, "cube already up and no lead-in: the turn starts at once");
assert.ok(Math.abs(plain[4] - startedAt) < 1e-6 && plain[5] >= startedAt, "the voice hears it at the real start");
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
