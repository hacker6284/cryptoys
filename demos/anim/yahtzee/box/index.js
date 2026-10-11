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
 * moves as plans, for checks.
 *
 * Audited by demos/micro/yahtzee/box/, pinned by ../../library.test.mjs.
 */
import settings from "./settings.js";
import { baseParts as sharedBaseParts, lidParts as sharedLidParts, solidsAt } from "../../shared/lidbox.js";
import { planHop, checkHop } from "../../shared/hop.js";
import { playPose, rafRun, worldPose } from "../../shared/run.js";

export { settings, checkHop };
export const timing = settings.timing;
export const slots = [];

/** Real size (the GLB): 248 × 163 × 108 mm closed (lid), 1.5 mm card. */
export const SIZE = { w: 0.248, h: 0.108, d: 0.163 };
/** The base: outer half-sizes, height, card. */
export const BASE = { hx: 0.1225, hz: 0.08, h: 0.1025, wall: 0.0015, floor: 0.0015 };
/** The lid (50 mm deep, over the top of the base): outer half-sizes, y range in the box frame, card. */
export const LID = { hx: 0.124, hz: 0.0815, y0: 0.058, y1: 0.108, wall: 0.0011, top: 0.0015 };
/** The dice cup (proc_dice_cup_83x102mm.glb, Ø 82.6 × 101.6 mm), origin its underside, as a box. */
export const CUP = { min: [-0.0413, 0, -0.0413], max: [0.0413, 0.1016, 0.0413] };
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

const rot = ([x, y, z, w], v) => {
    const t = [2 * (y * v[2] - z * v[1]), 2 * (z * v[0] - x * v[2]), 2 * (x * v[1] - y * v[0])];
    return [v[0] + w * t[0] + y * t[2] - z * t[1], v[1] + w * t[1] + z * t[0] - x * t[2], v[2] + w * t[2] + x * t[1] - y * t[0]];
};

/** World pose of the cup standing in the box at `boxPose`. */
export function pocketPose(boxPose) {
    const d = rot(boxPose.q, POCKET.p);
    return { p: [boxPose.p[0] + d[0], boxPose.p[1] + d[1], boxPose.p[2] + d[2]], q: boxPose.q.slice() };
}

const topOf = (boxPose) => boxPose.p[1] + BASE.h;

export function planLidOff({ box: boxPose, to, solids = [], tempo = timing.tempo }) {
    return planHop({ from: boxPose, to, parts: lidParts(), clearY: boxPose.p[1] + LID.y1 + settings.lid.clearM, solids, law: settings.lid, tempo });
}

export function planLidOn({ box: boxPose, from, solids = [], tempo = timing.tempo }) {
    return planHop({ from, to: boxPose, parts: lidParts(), clearY: boxPose.p[1] + LID.y1 + settings.lid.clearM, solids, law: settings.lid, tempo });
}

/** The cup lifted out of the box at `box` and stood at `to`. */
export function planOut({ box: boxPose, to, solids = [], tempo = timing.tempo }) {
    const all = [...baseSolids(boxPose), ...solids];
    return planHop({ from: pocketPose(boxPose), to, parts: [CUP], clearY: topOf(boxPose) + settings.cup.clearM, solids: all, law: settings.cup, tempo });
}

/** The cup from `from` back into the box at `box`. */
export function planIn({ box: boxPose, from, solids = [], tempo = timing.tempo }) {
    const all = [...baseSolids(boxPose), ...solids];
    return planHop({ from, to: pocketPose(boxPose), parts: [CUP], clearY: topOf(boxPose) + settings.cup.clearM, solids: all, law: settings.cup, tempo });
}

function reparent(object, parent) {
    if (parent && object.parent !== parent) parent.attach(object);
}

/** Take the lid off and set it down at `to`. Resolves with the plan (null if stopped). */
export function liftLid(rig, to, { solids = [], tempo = timing.tempo, run = rafRun } = {}) {
    const plan = planLidOff({ box: worldPose(rig.group), to, solids, tempo });
    reparent(rig.lid, rig.group.parent);
    return playPose(rig.lid, plan, run);
}

/** Put the lid back on. */
export async function putLid(rig, { solids = [], tempo = timing.tempo, run = rafRun } = {}) {
    const plan = planLidOn({ box: worldPose(rig.group), from: worldPose(rig.lid), solids, tempo });
    const done = await playPose(rig.lid, plan, run);
    reparent(rig.lid, rig.group);
    rig.lid.position.set(0, 0, 0);
    rig.lid.quaternion.set(0, 0, 0, 1);
    return done;
}

/** Lift the cup (with whatever is in it) out and stand it at `to`. */
export function liftOut(rig, cup, to, { solids = [], tempo = timing.tempo, run = rafRun } = {}) {
    const plan = planOut({ box: worldPose(rig.group), to, solids, tempo });
    reparent(cup, rig.group.parent);
    return playPose(cup, plan, run);
}

/** Put the cup back in the box. */
export async function putIn(rig, cup, { solids = [], tempo = timing.tempo, run = rafRun } = {}) {
    const plan = planIn({ box: worldPose(rig.group), from: worldPose(cup), solids, tempo });
    const done = await playPose(cup, plan, run);
    reparent(cup, rig.group);
    return done;
}

/** Stand the cup in the box at once (a box that starts packed). */
export function pack(rig, cup) {
    reparent(cup, rig.group);
    cup.position.set(...POCKET.p);
    cup.quaternion.set(0, 0, 0, 1);
}
