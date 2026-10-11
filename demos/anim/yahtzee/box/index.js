/**
 * yahtzee/box: the dice game's retail box, designed to fit what it holds:
 * the dice cup lying on its side in its well and the dice in a strip
 * beside it, behind a card divider; and its own moves.
 *
 *   import { yahtzee } from "demos/anim/index.js";
 *   await yahtzee.box.liftLid(box, to, { solids });       // box: { group, lid }
 *   await yahtzee.box.liftOut(box, cup, to, { solids });  // lying in the box, to stand at `to`
 *   await yahtzee.box.putIn(box, cup, { solids });
 *   await yahtzee.box.putLid(box, { solids });
 *
 * group: the base, its origin under the middle of its floor (+y up, the
 * long side along x); lid: the lid's node (a child of the group, at the
 * group's origin, while it is on). A lid or cup lifted out becomes a child
 * of the group's parent; put back, a child of the group again. to: world
 * poses { p, q }. solids: what is around (anim/shared/geom.js oriented
 * boxes); the base's own card (and the divider) is added here. The cup
 * turns from lying to standing on the way across. `run(ms, step)` plays it
 * on another clock. planLidOff, planLidOn, planOut, planIn are the same
 * moves as plans, for checks. The cup's shape is ../../shared/cup.js.
 *
 * Audited by demos/micro/yahtzee/box/, pinned by ../../library.test.mjs.
 */
import settings from "./settings.js";
import { baseParts as sharedBaseParts, lidBoxMoves, lidParts as sharedLidParts, solidsAt } from "../../shared/lidbox.js";
import { checkHop } from "../../shared/hop.js";
import { cupBox } from "../../shared/cup.js";

export { settings, checkHop };
export const timing = settings.timing;
export const slots = [];

// DESIGNED TO FIT (tools/bs_boxes.py works every size out from the
// contents; bs-layout.test checks the GLB and the fit): the cup lying along
// z (Ø 82.6 × 101.6 mm) with 2 mm all round and above; one die wide (a
// d10's 20.2 mm, 2 mm each side) for the dice strip along the −x wall, as
// long as the cup's well; 1.5 mm divider; 2 mm chipboard base and lid top;
// 1.5 mm lid walls, 0.5 mm over the base; the lid down to 3 mm off the table.
/** Real size (the GLB): 120.3 × 113.6 × 88.6 mm closed (lid). */
export const SIZE = { w: 0.1203, h: 0.0886, d: 0.1136 };
/** The base: outer half-sizes, height (the lid's top rests on its rim), card. */
export const BASE = { hx: 0.05815, hz: 0.0548, h: 0.0866, wall: 0.002, floor: 0.002 };
/** The lid (over the whole base, down to 3 mm off the table): outer half-sizes, y range in the box frame, card. */
export const LID = { hx: 0.06015, hz: 0.0568, y0: 0.003, y1: 0.0886, wall: 0.0015, top: 0.002 };
/** The divider card between the dice strip (−x) and the cup's well, box frame. */
export const DIVIDER = { min: [-0.03195, 0.002, -0.0528], max: [-0.03045, 0.0866, 0.0528] };
/** The dice strip (inside the base, −x of the divider), box frame: what lies in it is the caller's. */
export const STRIP = { min: [-0.05615, 0.002, -0.0528], max: [-0.03195, 0.0866, 0.0528] };
/** The dice cup (anim/shared/cup.js), origin its underside, as a box. */
export const CUP = cupBox();
/**
 * Where the cup lies in its well, box frame: its underside's middle at the
 * −z wall's clearance, its axis along +z (turned a quarter about x), on the
 * floor, 2 mm from every wall.
 */
export const POCKET = { p: [0.01285, 0.0433, -0.0508], q: [Math.SQRT1_2, 0, 0, Math.SQRT1_2] };

export function lidParts() {
    return sharedLidParts(LID);
}

export function baseParts() {
    return [...sharedBaseParts(BASE), { ...DIVIDER, name: "box divider" }];
}

export function baseSolids(pose) {
    return solidsAt(pose, baseParts());
}

export function lidSolids(pose) {
    return solidsAt(pose, lidParts());
}

// The lid clears its own top (it is lifted straight off over the base); the cup, lying, clears the base's rim.
const moves = lidBoxMoves({
    lid: lidParts(),
    baseSolids,
    lidClearY: (box) => box.p[1] + LID.y1,
    packClearY: (box) => box.p[1] + BASE.h,
    pockets: [POCKET],
    held: [[CUP]],
    laws: { lid: settings.lid, held: settings.cup },
    timing,
});

/** World pose of the cup lying in the box at `boxPose`. */
export const pocketPose = (boxPose) => moves.pocketPose(boxPose, 0);
/** The lid lifted off the box at `box` and set down at `to`: planLidOff({ box, to, solids, tempo }). */
export const planLidOff = moves.planLidOff;
/** The lid from `from` back onto the box at `box`: planLidOn({ box, from, solids, tempo }). */
export const planLidOn = moves.planLidOn;
/** The cup lifted out of the box at `box`, turned upright on the way, and stood at `to`: planOut({ box, to, solids, tempo }). */
export const planOut = ({ k, ...o }) => moves.planOut({ ...o, k: 0 });
/** The cup from `from` back into the box at `box`, laid on its side on the way: planIn({ box, from, solids, tempo }). */
export const planIn = ({ k, ...o }) => moves.planIn({ ...o, k: 0 });
/** Take the lid off and set it down at `to`. Resolves with the plan (null if stopped). */
export const liftLid = moves.liftLid;
/** Put the lid back on. */
export const putLid = moves.putLid;
/** Lift the cup (with whatever is in it) out and stand it at `to`. */
export const liftOut = (rig, cup, to, opts) => moves.liftOut(rig, 0, cup, to, opts);
/** Put the cup back in the box. */
export const putIn = (rig, cup, opts) => moves.putIn(rig, 0, cup, opts);
/** Lay the cup in the box at once (a box that starts packed). */
export const pack = (rig, cup) => moves.pack(rig, 0, cup);
