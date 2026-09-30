import assert from "node:assert/strict";
import { register } from "node:module";

// three bakes light counts into every lit shader: a light added, removed,
// hidden (or under a hidden parent) or shadow-toggled after boot relinks
// every lit material. Lights register at boot and only intensity changes.
const threeStub = `
class V3 { constructor() { this.x = 0; this.y = 0; this.z = 0; } set(x, y, z) { this.x = x; this.y = y; this.z = z; return this; } }
class Object3D {
    constructor() { this.children = []; this.parent = null; this.visible = true; this.castShadow = false; this.userData = {}; this.position = new V3(); this.rotation = new V3(); this.quaternion = { setFromEuler() {} }; }
    add(...os) { for (const o of os) { o.parent?.remove(o); o.parent = this; this.children.push(o); } return this; }
    remove(...os) { for (const o of os) { const i = this.children.indexOf(o); if (i >= 0) { this.children.splice(i, 1); o.parent = null; } } return this; }
    traverseVisible(fn) { if (!this.visible) return; fn(this); for (const c of this.children) c.traverseVisible(fn); }
    updateMatrixWorld() {}
}
class Light extends Object3D { constructor(color, intensity = 1) { super(); this.isLight = true; this.intensity = intensity; } }
export class Group extends Object3D {}
export class Scene extends Object3D {}
export class PointLight extends Light { type = "PointLight"; }
export class SpotLight extends Light { type = "SpotLight"; target = new Object3D(); }`;
const hooks = `
const MAP = { "three": "data:text/javascript," + encodeURIComponent(${JSON.stringify(threeStub)}) };
export async function resolve(spec, ctx, next) {
    if (MAP[spec]) return { url: MAP[spec], shortCircuit: true };
    if (spec.startsWith("three/")) return { url: "data:text/javascript,", shortCircuit: true };
    return next(spec, ctx);
}`;
register("data:text/javascript," + encodeURIComponent(hooks));
globalThis.window ??= {};
globalThis.requestAnimationFrame ??= (fn) => setTimeout(() => fn(performance.now()), 16);

const THREE = await import("three");
const { createLights } = await import("../shared/lights.js");
const { adapters } = await import("./adapters.js");
const { createToyDirector } = await import("./toy-director.js");
const { createBeatClock } = await import("./beat-clock.js");
const { playUnbox } = await import("./unbox-physical.js");
const sleep = (ms) => new Promise((r) => setTimeout(r, ms));

// Registry: seal locks the set; check catches any count change.
{
    const scene = new THREE.Scene();
    const lights = createLights(scene);
    const shelf = new THREE.Group();
    scene.add(shelf);
    const rim = lights.add("rim", new THREE.PointLight(0xffffff, 0), shelf);
    const spot = lights.add("spot", new THREE.SpotLight(0xffffff, 0));
    assert.equal(lights.get("rim"), rim);
    assert.equal(spot.target.parent, scene, "spot target joins the scene");
    assert.throws(() => lights.add("rim", new THREE.PointLight()), /already registered/);
    lights.seal();
    lights.check();
    assert.throws(() => lights.add("late", new THREE.PointLight()), /sealed/);
    rim.intensity = 3;
    lights.check();
    const other = new THREE.Group();
    scene.add(other);
    other.add(rim);
    lights.check(); // reparenting keeps the count
    for (const [what, breakIt, fix] of [
        ["hidden light", () => { rim.visible = false; }, () => { rim.visible = true; }],
        ["hidden parent", () => { other.visible = false; }, () => { other.visible = true; }],
        ["removed light", () => other.remove(rim), () => other.add(rim)],
        ["castShadow toggle", () => { spot.castShadow = true; }, () => { spot.castShadow = false; }],
        ["unregistered light", () => scene.add(new THREE.PointLight()), () => scene.children.pop()],
    ]) {
        breakIt();
        assert.throws(() => lights.check(), /changed after boot/, what);
        fix();
        lights.check();
    }
    assert.throws(() => lights.get("nope"), /unknown light/);
}
{
    // seal: a registered light lost (hidden parent) before seal throws,
    // even when a stray unregistered light keeps the count equal.
    const scene = new THREE.Scene();
    const lights = createLights(scene);
    const oldRoot = new THREE.Group();
    scene.add(oldRoot);
    lights.add("rim", new THREE.PointLight(0xffffff, 0), oldRoot);
    oldRoot.visible = false;
    const stray = new THREE.PointLight();
    scene.add(stray);
    assert.throws(() => lights.seal(), /light "rim" not visible at seal/);
    oldRoot.visible = true;
    assert.throws(() => lights.seal(), /unregistered PointLight visible at seal/);
    scene.remove(stray);
    lights.seal();
}

// Playroom stand-in: toys carry rim / travel lights like world.js.
const scene = new THREE.Scene();
const lights = createLights(scene);
const toys = {};
for (const name of ["deck", "deck2", "cube"]) {
    toys[name] = new THREE.Group();
    scene.add(toys[name]);
    lights.add(`rim:${name}`, new THREE.PointLight(0xffc078, 0), toys[name]);
    lights.add(`travel:${name}`, new THREE.PointLight(0xffd0a0, 0), toys[name]);
}
const pose = { position: { x: 0, y: 0.8, z: 0 }, rotation: { x: 0, y: 0, z: 0 } };
const world = {
    scene,
    lights,
    toys,
    table: { den: { x: 0, z: 0 }, feltTopY: 0.76 },
    setHighlight() {},
    setSlotEmpty() {},
    getTablePose: () => pose,
    getShelfPose: () => pose,
    applyPose() {},
    setChestLid() {},
    getChestLid: () => 0,
};

// DoubleDeal install registers the dealer key and both sleeve glows dark.
const dd = adapters.doubledeal;
dd.install(world, { poses: null });
lights.seal();
lights.check();
const keyLight = lights.get("dealerKey");
const glow = lights.get("glow:deck");
for (const light of [keyLight, glow, lights.get("glow:deck2")]) assert.equal(light.intensity, 0, "dark at boot");

// Flights light the travel glow by intensity only.
const director = createToyDirector(world);
for (const id of ["scramble", "doubledeal"]) {
    const job = director.borrow(id);
    const primary = id === "scramble" ? "cube" : "deck";
    assert.equal(lights.get(`travel:${primary}`).intensity, 4.2, `${id} flight lights its toy`);
    lights.check();
    director.skip();
    await job;
    assert.equal(lights.get(`travel:${primary}`).intensity, 0, `${id} landing darkens it`);
    lights.check();
    await director.home({ snap: true });
}

// Unbox glow rides into a sleeve; a skip then restow must leave it dark
// (the dead tween's apply(1) must not relight it).
const rigGroup = new THREE.Group();
const sleeve = new THREE.Group();
rigGroup.add(sleeve);
sleeve.add(glow);
scene.add(rigGroup);
lights.check();
const rig = { group: rigGroup, packet: new THREE.Group(), cards: [], innerGlow: glow, setFlap() {} };
const clock = createBeatClock({ reduced: false });
const gen = clock.begin();
const unbox = playUnbox({ world, rig, clock, gen, keyLight });
while (!(glow.intensity > 0)) await sleep(5);
lights.check();
clock.skip(); // as leave's skipEnter does; the dead tween must not write
const [glowAtSkip, keyAtSkip] = [glow.intensity, keyLight.intensity];
assert.ok(glowAtSkip < 0.55, "skipped mid-tween");
await unbox;
await sleep(40);
assert.equal(glow.intensity, glowAtSkip, "skipped unbox does not relight the sleeve glow");
assert.equal(keyLight.intensity, keyAtSkip, "skipped unbox does not relight the dealer key");

// This stand-in rig is not the adapter's, so leave's restow cannot reach
// the glow here; the dealer key it must darken.
keyLight.intensity = 2.55;
await dd.leave({ snap: true });
lights.check();
assert.equal(keyLight.intensity, 0, "leave darkens the dealer key");

console.log("lights.test.mjs ok");
