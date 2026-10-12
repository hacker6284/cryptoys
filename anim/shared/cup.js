/**
 * The dice cup's shape, the one place it is written down: the leather dice
 * cup, 3 1/4" × 4" (Ø 82.6 × 101.6 mm, "perfect for 5 dice";
 * dicegames.com/products/deluxe-leather-dice-cup-3-1-4-x-4), as
 * demos/bs/assets/models/proc_dice_cup_83x102mm.glb draws it (origin the
 * middle of its underside, +y up). What holds the cup (yahtzee/box), what
 * goes in and out of it (dice, the BS stage) and the playroom's real-size
 * table (playroom/constants.js REAL_SIZES.diceCup) all take it from here.
 *
 *   CUP                  → { r, rIn, h, floor } metres
 *   cupBox()             → the cup as one box, its own frame
 *   cupSolids(pose)      → its wall (a ring) and its floor, world (named)
 *   cupRimY(pose)        → the rim's height at `pose` (standing upright)
 */
import { obbOf } from "./geom.js";

/** Outer radius, inner radius (the wall 7.1 mm), height, floor thickness (all drawn). */
export const CUP = { r: 0.0413, rIn: 0.0342, h: 0.1016, floor: 0.0041 };

/** The cup as one box (what holds it packs it by this), its own frame. */
export function cupBox(cup = CUP) {
    return { min: [-cup.r, 0, -cup.r], max: [cup.r, cup.h, cup.r] };
}

/** The cup standing upright at `pose` as what goes in and out of it meets it: its wall (a ring) and its floor. */
export function cupSolids(pose, cup = CUP) {
    return [
        { kind: "cyl", x: pose.p[0], z: pose.p[2], r: cup.r, rIn: cup.rIn, y0: pose.p[1], y1: pose.p[1] + cup.h, name: "the cup's wall" },
        { ...obbOf(pose, { min: [-cup.r, 0, -cup.r], max: [cup.r, cup.floor, cup.r] }), name: "the cup's floor" },
    ];
}

/** The rim's height of the cup standing at `pose`. */
export const cupRimY = (pose, cup = CUP) => pose.p[1] + cup.h;
