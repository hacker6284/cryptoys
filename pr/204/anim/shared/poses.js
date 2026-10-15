/**
 * Placement helpers shared by the primitives' placements (no motion here):
 * the playroom deck box's drawn bounds, the orientations a toy is set down
 * in, and a seated pose on a surface. Every primitive takes placement as
 * an input; these only build those inputs.
 */
import { quatFromEuler, quatMul, seatY } from "./geom.js";

/** Drawn local bounds of the playroom deck box (world.js makeDeckBox: 67 × 92 × 20 mm, label 0.4 mm proud). */
export const DECK_BOX = { min: [-0.0335, -0.046, -0.01], max: [0.0335, 0.046, 0.0104] };

// Orientations, as Euler XYZ before the yaw: standing, lying face up
// (label up), face down, on its long side.
export const STAND = [0, 0, 0], FACE_UP = [-Math.PI / 2, 0, 0], FACE_DOWN = [Math.PI / 2, 0, 0], SIDE = [0, 0, Math.PI / 2];

/** Orientation `o` turned by `yaw` about the vertical. */
export function orient(o, yaw) {
    return quatMul(quatFromEuler(0, yaw, 0), quatFromEuler(...o));
}

/** A seated pose: the drawn bottom on surfaceY + gap at (x, z) with orientation q. */
export function seatPose({ x, z, q, surfaceY, gap = 0.001 }, shape) {
    return { p: [x, seatY(surfaceY + gap, q, shape), z], q };
}

/** A readable name for an orientation. */
export function orientName(o) {
    return o === STAND ? "standing" : o === FACE_UP ? "face up" : o === FACE_DOWN ? "face down" : "on its side";
}
