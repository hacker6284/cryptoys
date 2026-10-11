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
import { quatAxisAngle, quatMul, quatRotate } from "../../shared/geom.js";
import { baseParts as sharedBaseParts, lidParts as sharedLidParts, solidsAt } from "../../shared/lidbox.js";
import { planHop, checkHop } from "../../shared/hop.js";
import { playPose, rafRun, worldPose } from "../../shared/run.js";

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
 * hinge to the end wall; 0.7 mm to the walls and the fleet strip.
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

/** World pose of unit k lying in the box at `boxPose`. */
export function pocketPose(boxPose, k) {
    const c = POCKETS[k];
    return { p: addv(boxPose.p, quatRotate(boxPose.q, c.p)), q: quatMul(boxPose.q, quatAxisAngle([0, 1, 0], c.yaw)) };
}

const addv = (a, b) => [a[0] + b[0], a[1] + b[1], a[2] + b[2]];
const topOf = (boxPose) => boxPose.p[1] + BASE.h;

/** The lid lifted off the box at `box` and set down at `to`. */
export function planLidOff({ box: boxPose, to, solids = [], tempo = timing.tempo }) {
    return planHop({ from: boxPose, to, parts: lidParts(), clearY: topOf(boxPose) + settings.lid.clearM, solids, law: settings.lid, tempo });
}

/** The lid from `from` back onto the box at `box`. */
export function planLidOn({ box: boxPose, from, solids = [], tempo = timing.tempo }) {
    return planHop({ from, to: boxPose, parts: lidParts(), clearY: topOf(boxPose) + settings.lid.clearM, solids, law: settings.lid, tempo });
}

/** Unit k lifted out of the box at `box` and set down at `to`. */
export function planOut({ box: boxPose, k, to, solids = [], tempo = timing.tempo }) {
    const all = [...baseSolids(boxPose), ...solids];
    return planHop({ from: pocketPose(boxPose, k), to, parts: [UNIT], clearY: topOf(boxPose) + settings.unit.clearM, solids: all, law: settings.unit, tempo });
}

/** Unit k from `from` back into its pocket in the box at `box`. */
export function planIn({ box: boxPose, k, from, solids = [], tempo = timing.tempo }) {
    const all = [...baseSolids(boxPose), ...solids];
    return planHop({ from, to: pocketPose(boxPose, k), parts: [UNIT], clearY: topOf(boxPose) + settings.unit.clearM, solids: all, law: settings.unit, tempo });
}

function reparent(object, parent) {
    if (parent && object.parent !== parent) parent.attach(object);
}

/** Take the lid off the box and set it down at `to`. Resolves with the plan (null if stopped). */
export function liftLid(rig, to, { solids = [], tempo = timing.tempo, run = rafRun } = {}) {
    const plan = planLidOff({ box: worldPose(rig.group), to, solids, tempo });
    reparent(rig.lid, rig.group.parent);
    return playPose(rig.lid, plan, run);
}

/** Put the lid back on the box. */
export async function putLid(rig, { solids = [], tempo = timing.tempo, run = rafRun } = {}) {
    const plan = planLidOn({ box: worldPose(rig.group), from: worldPose(rig.lid), solids, tempo });
    const done = await playPose(rig.lid, plan, run);
    reparent(rig.lid, rig.group);
    rig.lid.position.set(0, 0, 0);
    rig.lid.quaternion.set(0, 0, 0, 1);
    return done;
}

/** Lift unit k (its root object, closed) out of the box and set it down at `to`. */
export function liftOut(rig, k, unit, to, { solids = [], tempo = timing.tempo, run = rafRun } = {}) {
    const plan = planOut({ box: worldPose(rig.group), k, to, solids, tempo });
    reparent(unit, rig.group.parent);
    return playPose(unit, plan, run);
}

/** Put unit k (closed) back into its pocket. */
export async function putIn(rig, k, unit, { solids = [], tempo = timing.tempo, run = rafRun } = {}) {
    const plan = planIn({ box: worldPose(rig.group), k, from: worldPose(unit), solids, tempo });
    const done = await playPose(unit, plan, run);
    reparent(unit, rig.group);
    return done;
}

/** Pack unit k in its pocket at once (a box that starts packed). */
export function pack(rig, k, unit) {
    reparent(unit, rig.group);
    const c = POCKETS[k];
    unit.position.set(c.p[0], c.p[1], c.p[2]);
    unit.quaternion.set(0, Math.sin(c.yaw / 2), 0, Math.cos(c.yaw / 2));
}
