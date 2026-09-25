import assert from "node:assert/strict";
import { tableSpan } from "../doubledeal/layout.js";
import {
    CUBE,
    DEAL_SCALE,
    DEN,
    SHELF_TOP,
    SHELF_Z,
    SLOTS,
    TABLE_R,
    TOP_Y,
    toyHalfHeight,
} from "./constants.js";
import { POSES, resolvePoseName } from "./poses.js";
import { createToyDirector } from "./toy-director.js";

const span = tableSpan();
const feltDiameter = 2 * (TABLE_R - 0.08);
const scaledWidth = span.width * DEAL_SCALE;
const scaledDepth = span.depth * DEAL_SCALE;

assert.ok(span.width > 0, "standalone table has a width");
assert.ok(scaledWidth < feltDiameter, `scaled decks ${scaledWidth.toFixed(3)}m must sit on the ${feltDiameter.toFixed(3)}m felt`);
assert.ok(scaledDepth < feltDiameter, `scaled depth ${scaledDepth.toFixed(3)}m must sit on the felt`);

assert.ok(POSES.doubledeal, "doubledeal pose exists");
assert.equal(resolvePoseName("doubledeal"), "doubledeal");
assert.equal(resolvePoseName("lean_deck"), "doubledeal");
assert.equal(resolvePoseName("scramble"), "scramble");
assert.ok(POSES.doubledeal.fov <= 32, "doubledeal FOV stays in the scramble-lean family");
assert.ok(POSES.doubledeal.position[1] <= 1.28, "doubledeal camera height matches seated lean");
assert.ok(POSES.doubledeal.position[2] - DEN.z <= 1.05, "doubledeal stay close to the felt");

assert.equal(toyHalfHeight("cube"), CUBE / 2);
assert.equal(toyHalfHeight("deck"), 0.046);
assert.notEqual(toyHalfHeight("deck"), CUBE / 2, "deck seatOn fallback is not the cube half-height");

const recipeDirector = createToyDirector({});
const recipe = recipeDirector.recipeOf("doubledeal");
assert.deepEqual(recipe.toys, ["deck"]);
assert.deepEqual(recipe.extras, ["chest"]);
assert.equal(recipe.pose, "doubledeal");
assert.equal(recipeDirector.recipeOf("scramble").toys[0], "cube");

function vec3(x = 0, y = 0, z = 0) {
    return {
        x,
        y,
        z,
        set(nx, ny, nz) {
            this.x = nx;
            this.y = ny;
            this.z = nz;
            return this;
        },
        clone() {
            return vec3(this.x, this.y, this.z);
        },
        copy(other) {
            this.x = other.x;
            this.y = other.y;
            this.z = other.z;
            return this;
        },
    };
}

function makeToy(x, y, z) {
    return {
        position: vec3(x, y, z),
        rotation: vec3(),
        quaternion: { setFromEuler() {}, clone() { return {}; }, copy() {} },
        updateMatrixWorld() {},
        userData: {},
    };
}

// Mirrors world.seatOn fallback (no live Box3 in Node).
function seatOn(object, { x, surfaceY, z, rotation, name }) {
    const fallback = toyHalfHeight(name);
    if (!object || object.userData?.flightBusy) {
        return {
            position: { x, y: surfaceY + fallback, z },
            rotation: { x: rotation.x, y: rotation.y, z: rotation.z },
        };
    }
    return {
        position: { x, y: surfaceY + fallback, z },
        rotation: { x: rotation.x, y: rotation.y, z: rotation.z },
    };
}

function makeMockWorld() {
    const feltTopY = TOP_Y + 0.032;
    const slotsEmpty = { deck: false, cube: false };
    const toys = {
        deck: makeToy(SLOTS.deck.x, SHELF_TOP + toyHalfHeight("deck"), SHELF_Z),
        cube: makeToy(SLOTS.cube.x, SHELF_TOP + toyHalfHeight("cube"), SHELF_Z),
    };
    return {
        toys,
        slotsEmpty,
        getShelfPose(name) {
            const slot = SLOTS[name];
            return seatOn(toys[name], {
                x: slot.x,
                surfaceY: SHELF_TOP + 0.001,
                z: SHELF_Z,
                rotation: { x: 0, y: name === "cube" ? 0.45 : 0.15, z: 0 },
                name,
            });
        },
        getTablePose(name) {
            return seatOn(toys[name], {
                x: DEN.x,
                surfaceY: feltTopY + 0.001,
                z: DEN.z,
                rotation: { x: 0, y: 0, z: 0 },
                name,
            });
        },
        applyPose(object, pose) {
            object.position.set(pose.position.x, pose.position.y, pose.position.z);
            object.rotation.set(pose.rotation.x, pose.rotation.y, pose.rotation.z);
        },
        setSlotEmpty(name, empty) {
            slotsEmpty[name] = Boolean(empty);
        },
    };
}

const missingDeck = seatOn(null, {
    x: DEN.x,
    surfaceY: 1,
    z: DEN.z,
    rotation: { x: 0, y: 0, z: 0 },
    name: "deck",
});
assert.equal(missingDeck.position.y, 1 + toyHalfHeight("deck"));
assert.notEqual(missingDeck.position.y, 1 + CUBE / 2);

const world = makeMockWorld();
const director = createToyDirector(world);
const shelfY = world.getShelfPose("deck").position.y;
const tableY = world.getTablePose("deck").position.y;
assert.equal(world.toys.deck.position.x, SLOTS.deck.x);
assert.ok(Math.abs(tableY - (TOP_Y + 0.033 + toyHalfHeight("deck"))) < 1e-9);

await director.borrow("doubledeal", { snap: true });
assert.equal(director.occupied, "doubledeal");
assert.equal(world.slotsEmpty.deck, true);
assert.equal(world.toys.deck.position.x, DEN.x);
assert.equal(world.toys.deck.position.z, DEN.z);
assert.equal(world.toys.deck.position.y, tableY);
assert.notEqual(world.toys.deck.position.y, TOP_Y + 0.033 + CUBE / 2);

await director.home({ snap: true });
assert.equal(director.occupied, null);
assert.equal(world.slotsEmpty.deck, false);
assert.equal(world.toys.deck.position.x, SLOTS.deck.x);
assert.equal(world.toys.deck.position.z, SHELF_Z);
assert.equal(world.toys.deck.position.y, shelfY);

const cubeWorld = makeMockWorld();
const cubeDirector = createToyDirector(cubeWorld);
await cubeDirector.borrow("scramble", { snap: true });
assert.equal(cubeWorld.toys.cube.position.x, DEN.x);
assert.equal(cubeWorld.toys.cube.position.y, cubeWorld.getTablePose("cube").position.y);
await cubeDirector.home({ snap: true });
assert.equal(cubeWorld.toys.cube.position.x, SLOTS.cube.x);
assert.equal(cubeWorld.slotsEmpty.cube, false);

console.log("playroom room tests ok");

await import("./scramble-alg.test.mjs");
