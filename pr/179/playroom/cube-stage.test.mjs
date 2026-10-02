import assert from "node:assert/strict";

globalThis.window = { setTimeout, clearTimeout };
globalThis.requestAnimationFrame = (fn) => setTimeout(() => fn(performance.now()), 16);

const { stageCubeView } = await import(new URL("./cube-stage.js", import.meta.url));
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
console.log("cube-stage lift/settle tests ok");
