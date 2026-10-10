/**
 * The BS microdemos' scenery: a Battleship unit (lid up) on the playroom
 * felt, from the demo's own models (demos/bs/assets/models, CC0), at real
 * size, and the grid's hole seats. Scenery only: the moves are the library
 * entry's own (demos/anim/peg, ship, dice).
 */
import * as THREE from "three";
import { GLTFLoader } from "three/addons/loaders/GLTFLoader.js";
import { DEN } from "../../playroom/constants.js";

export const MODELS = new URL("../../bs/assets/models/", import.meta.url);
const PITCH = 0.12 / 9;

export function loadGlb(file) {
    return new Promise((resolve, reject) => new GLTFLoader().load(new URL(file, MODELS).href, resolve, undefined, reject));
}

/** Hide the room's toys (each microdemo shows one object). */
export function hideToys(world) {
    for (const toy of Object.values(world.toys || {})) toy.visible = false;
}

/** The felt top under the table centre. */
export function feltAt(world) {
    return new THREE.Vector3(DEN.x, (world.table?.feltTopY ?? 0.772) + 0.001, DEN.z);
}

/** A unit on the felt: { root, lid, ocean(h), lid(cell) } seats (ocean: unit frame; lid: lid_pivot frame). */
export async function placeUnit(world, file = "bs_unit_red.glb") {
    const gltf = await loadGlb(file);
    const root = gltf.scene;
    root.position.copy(feltAt(world));
    world.scene.add(root);
    const lid = root.getObjectByName("lid_pivot");
    return {
        root,
        lid,
        ocean: (h) => new THREE.Vector3(-0.06393 + (h % 10) * PITCH, 0.0124, -0.04683 + Math.floor(h / 10) * PITCH),
        lidSeat: (cell) => new THREE.Vector3(-0.06393 + (cell % 10) * PITCH, 0.005, 0.135833 - Math.floor(cell / 10) * PITCH),
    };
}

export const CAMERA = { position: [DEN.x, 1.06, DEN.z + 0.42], target: [DEN.x, 0.82, DEN.z], fov: 34, fill: 0.8 };
