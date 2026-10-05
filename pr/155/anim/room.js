/**
 * The playroom's solid geometry for the motion primitives: what a carry
 * must clear and what a hinge must not swing into. Numbers are measured
 * from the drawn meshes (playroom/world.js, the chest GLB) and checked
 * against them when a microdemo loads (micro/shared/room-check.js), so a
 * change to the room shows up there and in ../anim/library.test.mjs.
 * Metres, world axes.
 */
import { boxSolid, quatFromEuler, quatAxisAngle, quatMul, quatRotate, add, obbOf } from "./geom.js";

export const DEN = { x: -0.35, z: 0.15 };
export const FELT_Y = 0.772; // felt top (TOP_Y + 0.032)
export const FELT_R = 0.945; // felt disc radius (TABLE_R − 0.08)
export const SHELF_TOP = 1.24; // top shelf board's top
export const SHELF_Z = -2.15;
/** A seat is the surface plus 1 mm, as world.js seats toys. */
export const SEAT_GAP = 0.001;

/**
 * The toy chest as the microdemos place it: turned to yaw π about its
 * own centre, still against the −X wall, so its lid hinges on the +Z
 * side and swings up along the wall, clear of the wall and of every
 * flight out of the chest (to the table, the rest poses, the shelf).
 * PROPOSED, not the live room: in the live playroom (yaw π/2) the lid
 * hinges on the wall side and its 47 cm dome swings into the wall (35 cm
 * past it at full open; it meets the wall at 26°). Yaw 0 would also
 * clear the wall, but its open lid stands between the chest and the
 * table, so every flight out has to climb over it.
 */
export const CHEST = {
    yaw: Math.PI,
    centre: [-2.3393, 1.05],
    outer: { min: [-2.81, 0, 0.5793], max: [-1.8687, 0.4801, 1.5207] }, // square about the centre, so the same at any quarter turn
    inner: { min: [-2.6049, 0.0463, 0.7845], max: [-2.0738, 0.4801, 1.3155] }, // the cavity: walls and floor, raycast
    hinge: [0, 0.4801, -0.4496], // the lid's hinge line (along the chest's x) from the centre, chest frame
    lid: { min: [-0.4497, 0, 0], max: [0.4497, 0.47, 0.8993] }, // the lid's drawn bounds in the hinge frame
    lidOpenAngle: 1.45, // rad (world.js rigChestLid openAngle −1.45)
};

/** The chest's yaw as a quaternion and its hinge line in the world. */
export function chestFrame(chest = CHEST) {
    const q = quatFromEuler(0, chest.yaw, 0);
    const h = quatRotate(q, chest.hinge);
    return { q, pivot: [chest.centre[0] + h[0], h[1], chest.centre[1] + h[2]] };
}

/** The lid's oriented box with the lid open by `angle` rad (0 shut). */
export function chestLidObb(angle, chest = CHEST) {
    const { q, pivot } = chestFrame(chest);
    return obbOf({ p: pivot, q: quatMul(q, quatAxisAngle([1, 0, 0], -angle)) }, chest.lid);
}

/** The chest body as solids: floor slab and four walls around the cavity. */
function chestBody() {
    const o = CHEST.outer, i = CHEST.inner;
    return [
        boxSolid(o.min, [o.max[0], i.min[1], o.max[2]]),
        boxSolid(o.min, [i.min[0], o.max[1], o.max[2]]),
        boxSolid([i.max[0], o.min[1], o.min[2]], o.max),
        boxSolid(o.min, [o.max[0], o.max[1], i.min[2]]),
        boxSolid([o.min[0], o.min[1], i.max[2]], o.max),
    ].map((s, k) => ({ ...s, kind: "box", name: `chest-${["floor", "wall-x", "wall+x", "wall-z", "wall+z"][k]}` }));
}

const B = (name, min, max) => ({ ...boxSolid(min, max), kind: "box", name });

/** Fixed room solids (everything but the chest lid and the toys). */
export const ROOM = [
    B("floor", [-3, -1, -3], [3, 0, 3]),
    B("wall-x", [-3.85, 0, -3], [-2.85, 2.7, 3]),
    B("wall+x", [2.85, 0, -3], [3.85, 2.7, 3]),
    B("wall-z", [-3, 0, -3.37], [3, 2.7, -2.37]),
    B("ceiling", [-3, 2.68, -3], [3, 3.7, 3]),
    { kind: "cyl", name: "table", x: DEN.x, z: DEN.z, r: 1.033, y0: 0, y1: FELT_Y },
    { kind: "cyl", name: "table-rim", x: DEN.x, z: DEN.z, r: 1.033, rIn: FELT_R, y0: FELT_Y - 0.02, y1: 0.79 },
    B("pendant", [-0.55, 2.14, -0.05], [-0.15, 2.695, 0.35]),
    B("shelf-top", [-2.2, 1.2, -2.3], [2.2, SHELF_TOP, -2.0]),
    B("shelf-low", [-2.2, 0.76, -2.3], [2.2, 0.8, -2.0]),
    B("shelf-back", [-2.2, 0.525, -2.3], [2.2, 1.475, -2.28]),
    B("bracket-1", [-2.02, 0.525, -2.05], [-1.98, 1.475, -2.01]),
    B("bracket-2", [-0.72, 0.525, -2.05], [-0.68, 1.475, -2.01]),
    B("bracket-3", [0.68, 0.525, -2.05], [0.72, 1.475, -2.01]),
    B("bracket-4", [1.98, 0.525, -2.05], [2.02, 1.475, -2.01]),
    B("plant-a", [0.315, 1.22, -2.1898], [0.385, 1.44, -2.1102]),
    B("plant-b", [0.9872, 1.22, -2.2071], [1.1128, 1.4, -2.0929]),
    B("floor-plant", [-2.3643, 0, -2.0763], [-1.8777, 0.3982, -1.5103]),
    B("sconce-chest", [-2.79, 1.6281, 0.8081], [-2.624, 1.8119, 0.9919]),
    B("sconce-shelf", [1.2581, 1.5881, -2.08], [1.4419, 1.7719, -1.914]),
    ...chestBody(),
];

/** Every solid with the chest lid open by `lidAngle` rad. */
export function roomSolids({ lidAngle = 0 } = {}) {
    return [...ROOM, { ...chestLidObb(lidAngle), kind: "box", name: "chest-lid" }];
}

/**
 * Seating surfaces: where a toy can be set down. y is the surface top;
 * a toy seats at y + SEAT_GAP by its drawn bottom.
 */
export const SURFACES = {
    felt: { y: FELT_Y, inside: (x, z, r) => Math.hypot(x - DEN.x, z - DEN.z) <= FELT_R - 0.03 - r },
    shelf: { y: SHELF_TOP, inside: (x, z, r) => x - r >= -2.15 && x + r <= 0.25 && z - r >= -2.28 && z + r <= -2.01 },
    chest: { y: CHEST.inner.min[1], inside: (x, z, r) => x - r >= CHEST.inner.min[0] + 0.01 && x + r <= CHEST.inner.max[0] - 0.01 && z - r >= CHEST.inner.min[2] + 0.01 && z + r <= CHEST.inner.max[2] - 0.01 },
};

/** The real poses the playroom uses (world.js), as { surface, x, z, yaw }. */
export const REAL_POSES = {
    shelfSlot: { surface: "shelf", x: -1.35, z: SHELF_Z, yaw: 0.15 }, // KEY's shelf slot (getShelfPose)
    tableCentre: { surface: "felt", x: DEN.x, z: DEN.z, yaw: 0 }, // KEY borrowed (getTablePose)
    restLeft: { surface: "felt", x: DEN.x - 0.78, z: DEN.z - 0.34, yaw: -0.2 }, // MSG borrowed (getBoxRestPose deck2)
    restRight: { surface: "felt", x: DEN.x + 0.78, z: DEN.z - 0.34, yaw: 0.2 }, // the KEY sleeve set aside (getBoxRestPose deck)
    chestSeat: { surface: "chest", x: CHEST.centre[0] + 0.08, z: CHEST.centre[1] - 0.02, yaw: 0.1 }, // MSG at home in the chest (on its drawn floor)
};

export { quatFromEuler, quatMul, quatRotate, add };
