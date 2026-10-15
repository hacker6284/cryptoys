/**
 * battleship/box: the Battleship retail box, which holds both closed
 * units side by side across its card divider, and its own moves.
 *
 *   import { battleship } from "demos/anim/index.js";
 *   await battleship.box.liftLid(box, to, { solids });       // box: { group, lid }
 *   await battleship.box.liftOut(box, k, unit, to, { solids });
 *   await battleship.box.putIn(box, k, unit, { solids });
 *   await battleship.box.putLid(box, { solids });
 *
 * group: the base, its origin under the middle of its floor (+y up, the
 * long side along x); lid: the lid's node (a child of the group, at the
 * group's origin, while it is on). A lid or unit lifted out becomes a
 * child of the group's parent; put back, a child of the group again.
 * to: world poses { p, q }. solids: what is around (anim/shared/geom.js
 * oriented boxes); the base's own walls, divider and fleet strip are
 * added here. `run(ms, step)` plays it on another clock. planLidOff,
 * planLidOn, planOut, planIn are the same moves as plans, for checks.
 *
 * Audited by demos/micro/battleship/box/, pinned by ../../library.test.mjs.
 */
import settings from "./settings.js";
import { baseParts as sharedBaseParts, lidBoxMoves, lidParts as sharedLidParts, solidsAt } from "../../shared/lidbox.js";
import { checkHop } from "../../shared/hop.js";

export { settings, checkHop };
export const timing = settings.timing;
export const slots = [];

/** Real size (the GLB, MEASURED): 400 × 265 × 52.5 mm closed, 1.5 mm card. */
export const SIZE = { w: 0.4, h: 0.0525, d: 0.265 };
/** The base: outer half-sizes, wall height, card. */
export const BASE = { hx: 0.1982, hz: 0.1307, h: 0.0507, wall: 0.0015, floor: 0.0015 };
/** The lid (full depth): outer half-sizes, height, card. */
export const LID = { hx: 0.2, hz: 0.1325, h: 0.0525, wall: 0.0015, top: 0.0015 };
/** The card inserts (the GLB's navalbox_insert_divider and _fleet_strip). */
export const DIVIDER = { min: [-0.0225, 0.0015, -0.1268], max: [0.0225, 0.0415, 0.1022] };
export const STRIP = { min: [-0.1967, 0.0015, 0.1022], max: [0.1967, 0.0315, 0.1292] };
/** A closed unit (bs_unit_*.glb with lid_pivot shut): 230 × 35.1 × 171.4 mm, origin its underside. */
export const UNIT = { min: [-0.115, 0, -0.0854], max: [0.115, 0.0351, 0.086] };
/**
 * Where each unit lies in the base, box frame: on the floor either side of
 * the divider, turned a quarter (its 230 mm along the box's depth), its
 * hinge to the end wall; 0.7 mm to the back wall and to the fleet strip,
 * 1.4 mm to the end wall and to the divider.
 */
export const POCKETS = [
    { p: [-0.1099, 0.0015, -0.0135], yaw: Math.PI / 2 },
    { p: [0.1099, 0.0015, -0.0135], yaw: -Math.PI / 2 },
];

/** The lid's drawn parts, lid frame (its top and four walls: it sits over the base). */
export function lidParts() {
    return sharedLidParts({ hx: LID.hx, hz: LID.hz, y0: 0, y1: LID.h, wall: LID.wall, top: LID.top });
}

/** The base's own parts, box frame: floor, four walls, the divider, the fleet strip. */
export function baseParts() {
    return [...sharedBaseParts(BASE), { ...DIVIDER, name: "box divider" }, { ...STRIP, name: "box fleet strip" }];
}

/** The base's own solids at its pose. */
export function baseSolids(pose) {
    return solidsAt(pose, baseParts());
}

/** The lid's solids at its pose. */
export function lidSolids(pose) {
    return solidsAt(pose, lidParts());
}

// The lid and the units clear the base's walls (the units' lids are shut: 35.1 mm, under the walls).
const moves = lidBoxMoves({
    lid: lidParts(),
    baseSolids,
    lidClearY: (box) => box.p[1] + BASE.h,
    packClearY: (box) => box.p[1] + BASE.h,
    pockets: POCKETS,
    held: [[UNIT], [UNIT]],
    laws: { lid: settings.lid, held: settings.unit },
    timing,
});

/** World pose of unit k lying in the box at `boxPose`. */
export const pocketPose = (boxPose, k) => moves.pocketPose(boxPose, k);
/** The lid lifted off the box at `box` and set down at `to`: planLidOff({ box, to, solids, tempo }). */
export const planLidOff = moves.planLidOff;
/** The lid from `from` back onto the box at `box`: planLidOn({ box, from, solids, tempo }). */
export const planLidOn = moves.planLidOn;
/** Unit k lifted out of the box at `box` and set down at `to`: planOut({ box, k, to, solids, tempo }). */
export const planOut = moves.planOut;
/** Unit k from `from` back into its pocket: planIn({ box, k, from, solids, tempo }). */
export const planIn = moves.planIn;
/** Take the lid off the box and set it down at `to`. Resolves with the plan (null if stopped). */
export const liftLid = moves.liftLid;
/** Put the lid back on the box. */
export const putLid = moves.putLid;
/** Lift unit k (its root object, closed) out of the box and set it down at `to`. */
export const liftOut = moves.liftOut;
/** Put unit k (closed) back into its pocket. */
export const putIn = moves.putIn;
/** Pack unit k in its pocket at once (a box that starts packed). */
export const pack = moves.pack;
