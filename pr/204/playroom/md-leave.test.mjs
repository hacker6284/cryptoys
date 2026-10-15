// Leaving MegaDreifach once its stage exists (install has run) must finish:
// a throw in leave() skips session.dispose() and leaves the hub stuck
// mid-leave. Node has no three: the stand-ins are just enough to install.
import assert from "node:assert/strict";
import { stubThree } from "./three-stub.mjs";

const mini = new URL("./three-mini.mjs", import.meta.url).href;
stubThree(`export * from ${JSON.stringify(mini)};
import { Object3D, Quaternion as MiniQuaternion } from ${JSON.stringify(mini)};
const Thing = class extends Object3D { constructor(...args) { super(); this.args = args; } dispose() {} };
export class Quaternion extends MiniQuaternion { setFromEuler() { return this; } }
export class PointLight extends Thing { isLight = true; intensity = 0; }
export class Mesh extends Object3D { constructor(geometry, material) { super(); this.geometry = geometry; this.material = material; } }
export class BoxGeometry extends Thing {}
export class PlaneGeometry extends Thing {}
export class RingGeometry extends Thing {}
export class SphereGeometry extends Thing {}
export class MeshBasicMaterial extends Thing {}
export class MeshStandardMaterial extends Thing {}
export class CanvasTexture extends Thing {}
export class Euler { constructor(x = 0, y = 0, z = 0) { this.x = x; this.y = y; this.z = z; } }
export const DoubleSide = 2;
export const SRGBColorSpace = "srgb";`);
globalThis.window ??= {};

const { Scene } = await import("./three-mini.mjs");
const { DEMOS } = await import("./demos.js");

const scene = new Scene();
const toys = {};
const pose = { position: { x: 0, y: 0.8, z: 0 }, rotation: { x: 0, y: 0, z: 0 } };
const world = {
    scene,
    toys,
    lights: { add() {}, get: () => null },
    table: { den: { x: 0, z: 0 }, feltTopY: 0.76 },
    replaceToy(name, group) {
        toys[name] = group;
        scene.add(group);
    },
    shelfHome() {},
    setHighlight() {},
    setSlotEmpty() {},
    getTablePose: () => pose,
    getShelfPose: () => pose,
    applyPose() {},
};

const md = DEMOS.megadreifach.adapter;
md.install(world, { poses: null });
await md.leave({ snap: true });
await md.leave(); // and again, unsnapped: still nothing to throw on
console.log("md-leave: ok");
