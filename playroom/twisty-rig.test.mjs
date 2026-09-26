import assert from "node:assert/strict";
import { readFileSync } from "node:fs";

const src = readFileSync(new URL("./twisty-rig.js", import.meta.url), "utf8");

assert.equal(src.includes("export function inspectMaterials"), false, "spike inspectMaterials stays out");
assert.equal(src.includes("export function describeThreeSkew"), false, "spike describeThreeSkew stays out");
assert.equal(src.includes("userData.twistySkew"), false, "no twistySkew probe");
assert.equal(src.includes("look,"), false, "rig.look probe stays out");
assert.match(src, /if \(disposed\) return/, "playLeaves bails after dispose");
assert.match(src, /fitToLocalEdge/, "fit uses parent-space TRS, not world AABB");
assert.match(src, /keepFitted/, "post-spawn Twisty writes are re-fitted");
assert.match(src, /export function frameInWrapper/, "fit is exported for seat/scale tests");
assert.match(src, /keepPuzzleFitted/, "Twisty render-scheduled re-applies fit");
assert.match(src, /userData.keepFitted/, "host render can re-apply fit");
assert.match(src, /userData.worldEdge/, "debug size is world AABB Y, not pixels");
assert.equal(src.includes("wrapper.scale.set(1, 1, 1)"), false, "do not flash native scale on refit");
assert.equal(src.includes("Box3().setFromObject"), false, "do not Box3.setFromObject across two threes");

const { fitToLocalEdge, keepFitted } = await import("./motion.js");

function vec3(x = 0, y = 0, z = 0) {
    return {
        x, y, z,
        set(nx, ny, nz) { this.x = nx; this.y = ny; this.z = nz; return this; },
        setScalar(s) { this.x = this.y = this.z = s; return this; },
        multiplyScalar(s) { this.x *= s; this.y *= s; this.z *= s; return this; },
    };
}

function makeMesh(edge = 2) {
    const h = edge / 2;
    return {
        visible: true,
        isMesh: true,
        position: vec3(),
        scale: vec3(1, 1, 1),
        quaternion: { x: 0, y: 0, z: 0, w: 1 },
        geometry: {
            attributes: {
                position: {
                    count: 2,
                    itemSize: 3,
                    array: new Float32Array([-h, -h, -h, h, h, h]),
                },
            },
        },
        matrixWorld: { elements: [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1] },
        children: [],
        updateMatrixWorld() {},
    };
}

const wrapper = {
    position: vec3(),
    scale: vec3(1, 1, 1),
    updateMatrixWorld() {},
};
const puzzle = makeMesh(3);
const framed = fitToLocalEdge(wrapper, puzzle, 0.12);
assert.ok(Math.abs(framed.scale - 0.04) < 1e-6);
assert.ok(Math.abs(wrapper.scale.x - 0.04) < 1e-6);

// Late cubing.js 1/3 would crush a one-shot world fit. keepFitted
// sees the local scale and restores the 120 mm edge.
puzzle.scale.setScalar(1 / 3);
const held = keepFitted(wrapper, puzzle, 0.12, framed);
assert.equal(held.changed, true);
assert.ok(Math.abs(held.scale - 0.12) < 1e-6, "late 1/3 is compensated on fit");
assert.ok(Math.abs(wrapper.scale.x - 0.12) < 1e-6);

const again = keepFitted(wrapper, puzzle, 0.12, held);
assert.equal(again.changed, false, "stable local edge is a no-op");

// Mid-turn cubie AABB swell must not pulse the locked rest fit.
const turning = makeMesh(3);
turning.scale.setScalar(1 / 3);
const rest = fitToLocalEdge(wrapper, turning, 0.12);
turning.children = [makeMesh(5)];
const midTurn = keepFitted(wrapper, turning, 0.12, rest);
assert.equal(midTurn.changed, false, "turning cubies do not remesure nativeMax");
assert.ok(Math.abs(wrapper.scale.x - rest.scale) < 1e-6, "rest scale holds mid-turn");
assert.equal(rest.fittedMax, 0.12, "rest presentation edge is 120 mm");
assert.equal(held.fittedMax, 0.12, "late 1/3 still targets 120 mm");
assert.equal(midTurn.fittedMax, 0.12, "mid-turn lock stays 120 mm");

assert.match(src, /turnBusy/, "playLeaves marks the turn so keep-fit can skip");

const hostRemove = src.indexOf("hidePlayerHost(player)");
const tryAt = src.indexOf("try {", hostRemove);
const catchRemove = src.indexOf("player.remove();", tryAt);
assert.ok(hostRemove >= 0 && tryAt > hostRemove && catchRemove > tryAt, "host is removed if adopt throws after append");

console.log("twisty-rig source tests ok");
