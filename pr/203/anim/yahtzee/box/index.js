/**
 * yahtzee/box: the dice game's retail box, which holds the dice cup
 * standing up (the dice in the cup), and its own moves.
 *
 *   import { yahtzee } from "demos/anim/index.js";
 *   await yahtzee.box.liftLid(box, to, { solids });       // box: { group, lid }
 *   await yahtzee.box.liftOut(box, cup, to, { solids });
 *   await yahtzee.box.putIn(box, cup, { solids });
 *   await yahtzee.box.putLid(box, { solids });
 *
 * group: the base, its origin under the middle of its floor (+y up, the
 * long side along x); lid: the lid's node (a child of the group, at the
 * group's origin, while it is on). A lid or cup lifted out becomes a child
 * of the group's parent; put back, a child of the group again. to: world
 * poses { p, q }. solids: what is around (anim/shared/geom.js oriented
 * boxes); the base's own card is added here. `run(ms, step)` plays it on
 * another clock. planLidOff, planLidOn, planOut, planIn are the same
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

/** Real size (the GLB): 248 × 163 × 108 mm closed (lid), 1.5 mm card. */
export const SIZE = { w: 0.248, h: 0.108, d: 0.163 };
/** The base: outer half-sizes, height, card. */
export const BASE = { hx: 0.1225, hz: 0.08, h: 0.1025, wall: 0.0015, floor: 0.0015 };
/** The lid (50 mm deep, over the top of the base): outer half-sizes, y range in the box frame, card. */
export const LID = { hx: 0.124, hz: 0.0815, y0: 0.058, y1: 0.108, wall: 0.0011, top: 0.0015 };
/** The dice cup (anim/shared/cup.js), origin its underside, as a box. */
export const CUP = cupBox();
/** Where the cup stands in the base, box frame: in the middle, on the floor. */
export const POCKET = { p: [0, 0.0015, 0] };

export function lidParts() {
    return sharedLidParts(LID);
}

export function baseParts() {
    return sharedBaseParts(BASE);
}

export function baseSolids(pose) {
    return solidsAt(pose, baseParts());
}

export function lidSolids(pose) {
    return solidsAt(pose, lidParts());
}

// The lid clears its own top (it is lifted straight off over the base); the cup clears the base's rim.
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

/** World pose of the cup standing in the box at `boxPose`. */
export const pocketPose = (boxPose) => moves.pocketPose(boxPose, 0);
/** The lid lifted off the box at `box` and set down at `to`: planLidOff({ box, to, solids, tempo }). */
export const planLidOff = moves.planLidOff;
/** The lid from `from` back onto the box at `box`: planLidOn({ box, from, solids, tempo }). */
export const planLidOn = moves.planLidOn;
/** The cup lifted out of the box at `box` and stood at `to`: planOut({ box, to, solids, tempo }). */
export const planOut = ({ k, ...o }) => moves.planOut({ ...o, k: 0 });
/** The cup from `from` back into the box at `box`: planIn({ box, from, solids, tempo }). */
export const planIn = ({ k, ...o }) => moves.planIn({ ...o, k: 0 });
/** Take the lid off and set it down at `to`. Resolves with the plan (null if stopped). */
export const liftLid = moves.liftLid;
/** Put the lid back on. */
export const putLid = moves.putLid;
/** Lift the cup (with whatever is in it) out and stand it at `to`. */
export const liftOut = (rig, cup, to, opts) => moves.liftOut(rig, 0, cup, to, opts);
/** Put the cup back in the box. */
export const putIn = (rig, cup, opts) => moves.putIn(rig, 0, cup, opts);
/** Stand the cup in the box at once (a box that starts packed). */
export const pack = (rig, cup) => moves.pack(rig, 0, cup);
