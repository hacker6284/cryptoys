/**
 * battleship/unit: one Battleship unit and its own moves, open the lid and
 * close it, wherever the unit stands.
 *
 *   import { battleship } from "demos/anim/index.js";
 *   await battleship.unit.openLid(unit, { solids });   // unit: { group, lid }
 *   await battleship.unit.closeLid(unit, { solids });
 *
 * group: the unit (its origin its underside, the hinge at −z); lid: its
 * lid_pivot node (shut: no rotation; open: −openRad about x). solids:
 * what is around (anim/shared/geom.js oriented boxes; the lid shuts onto
 * its own tray, so the tray is not one). `run(ms, step)` plays it on
 * another clock. planLid / checkLid are the same move as a plan, for
 * checks and tests.
 *
 * Audited by demos/micro/battleship/unit/open-close-lid/, pinned by
 * ../../library.test.mjs.
 */
import settings from "./settings.js";
import { add, obbOf, quatAxisAngle, quatMul, quatRotate } from "../../shared/geom.js";
import { planSwing, checkSwing } from "../../shared/swing.js";
import { rafRun, worldPose } from "../../shared/run.js";

export { settings };
export const timing = settings.timing;
export const lid = settings.lid;
export const slots = [];

/** The hinge (the GLB's lid_pivot), unit frame. */
export const HINGE = [0, 0.018, -0.073];
/** The lid's drawn bounds in the hinge frame, shut (empty: no pegs in it). */
export const LID = { min: [-0.115, -0.0066, -0.012], max: [0.115, 0.0171, 0.159] };
/** The tray under it (tray_shell, inner, ocean grid, hinge bosses), unit frame. */
export const TRAY = { min: [-0.1131, 0, -0.0854], max: [0.1131, 0.0114, 0.0834] };
/** The whole unit's drawn bounds shut and open (the GLB, MEASURED). */
export const SHUT = { min: [-0.115, 0, -0.0854], max: [0.115, 0.0351, 0.086] };
export const OPEN = { min: [-0.115, 0, -0.0901], max: [0.115, 0.177, 0.0834] };
/** Open, as solids: the tray and the standing lid (the GLB's open lid bounds). */
export const OPEN_PARTS = [
    { min: [-0.1131, 0, -0.0854], max: [0.1131, 0.024, 0.0834] },
    { min: [-0.115, 0.006, -0.0901], max: [0.115, 0.177, -0.0664] },
];

/** The lid's box at `angle` (0 shut) with the unit at `pose`. */
export function lidObb(pose, angle) {
    const pivot = { p: add(pose.p, quatRotate(pose.q, HINGE)), q: quatMul(pose.q, quatAxisAngle([1, 0, 0], -angle)) };
    return obbOf(pivot, LID);
}

/** The lid swinging from `from` to `to` (fractions of openRad) with the unit at `pose`. */
export function planLid({ pose, from = 0, to = 1, solids = [], tempo = timing.tempo }) {
    const sweep = (a) => lidObb(pose, a);
    const plan = planSwing({ part: lid, from, to, sweep, solids, tempo });
    plan.sweep = sweep;
    plan.solids = solids;
    return plan;
}

/** The plan's checks: no overlap, exact ends, duration and peak on the law. */
export function checkLid(plan, tempo = timing.tempo) {
    return checkSwing(plan, { sweep: plan.sweep, solids: plan.solids, tempo });
}

const at = new WeakMap();

/** The lid's rotation at `angle`, as three's lid_pivot quaternion. */
export function setLid(unit, angle) {
    unit.lid.quaternion.set(-Math.sin(angle / 2), 0, 0, Math.cos(angle / 2));
    at.set(unit, angle / lid.openRad);
}

async function swing(unit, to, { from, solids = [], tempo = timing.tempo, run = rafRun } = {}) {
    const plan = planLid({ pose: worldPose(unit.group), from: from ?? at.get(unit) ?? 0, to, solids, tempo });
    const ok = await run(plan.ms, (t) => setLid(unit, plan.at(t)));
    setLid(unit, plan.to);
    return ok === false ? null : plan;
}

/** Open the lid (to `opts.to`, default upright). Resolves with the plan (null if stopped). */
export function openLid(unit, opts = {}) {
    return swing(unit, opts.to ?? 1, opts);
}

/** Close the lid (to `opts.to`, default shut). */
export function closeLid(unit, opts = {}) {
    return swing(unit, opts.to ?? 0, opts);
}
