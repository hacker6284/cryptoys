import assert from "node:assert/strict";
import { register } from "node:module";

// The DoubleDeal dealer key is a SpotLight. three bakes the number of
// spot lights into every lit shader, so adding or removing one mid-scene
// relinks every lit material on the next frame (the freeze when the KEY
// box landed). The light must join the scene at install and stay there.
const threeStub = `
class V3 { constructor() { this.x = 0; this.y = 0; this.z = 0; } set(x, y, z) { this.x = x; this.y = y; this.z = z; return this; } }
export class SpotLight {
    constructor(color, intensity = 1) { this.isLight = true; this.isSpotLight = true; this.intensity = intensity; this.position = new V3(); this.target = { position: new V3() }; }
    dispose() {}
}`;
const hooks = `
const MAP = {
    "three": "data:text/javascript," + encodeURIComponent(${JSON.stringify(threeStub)}),
};
export async function resolve(spec, ctx, next) {
    if (MAP[spec]) return { url: MAP[spec], shortCircuit: true };
    if (spec.startsWith("three/")) return { url: "data:text/javascript,", shortCircuit: true };
    return next(spec, ctx);
}`;
register("data:text/javascript," + encodeURIComponent(hooks));
globalThis.window ??= {};

const { adapters } = await import("./adapters.js");

function makeWorld() {
    const children = new Set();
    return {
        scene: {
            add(...objects) { for (const o of objects) children.add(o); },
            remove(...objects) { for (const o of objects) children.delete(o); },
            children,
        },
        table: { den: { x: 0, z: 0 }, feltTopY: 0.76 },
        toys: { deck: {}, deck2: {} },
    };
}
const spotLights = (world) => [...world.scene.children].filter((o) => o.isSpotLight);

const dd = adapters.doubledeal;
const world = makeWorld();
dd.install(world, { poses: null });
const atInstall = spotLights(world);
assert.equal(atInstall.length, 1, "dealer key joins the scene at install, before any enter");
assert.equal(atInstall[0].intensity, 0, "dealer key is dark at the hub");

atInstall[0].intensity = 2.55; // as the unbox leaves it
await dd.leave({ snap: true });
const afterLeave = spotLights(world);
assert.equal(afterLeave.length, 1, "leave keeps the dealer key in the scene (no spot-light count change)");
assert.equal(afterLeave[0], atInstall[0], "same light object; nothing re-added on the next enter");
assert.equal(afterLeave[0].intensity, 0, "leave darkens the dealer key");

console.log("dealer-key.test.mjs ok");
