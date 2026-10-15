/**
 * deck/box: the deck's tuck box and its own moves, open the flap and close
 * the flap, wherever the box is.
 *
 *   import { deck } from "demos/anim/index.js";
 *   await deck.box.openFlap(rig, { solids });  // rig: { group, setFlap(fraction) }
 *   await deck.box.closeFlap(rig, { solids });
 *
 * The box's pose is read from rig.group; `solids` is what is around it
 * (anim/shared/room.js roomSolids(), other toys); its own body is added
 * here. `run(ms, step)` plays it on another clock (default: real time).
 * planFlap / checkFlap are the same move as a plan, for checks and tests.
 *
 * Audited by demos/micro/deck/box/open-close-flap/, pinned by
 * ../../library.test.mjs.
 */
import settings from "./settings.js";
import { obbOf, quatAxisAngle, quatMul } from "../../shared/geom.js";
import { planSwing, checkSwing } from "../../shared/swing.js";
import { rafRun, worldPose } from "../../shared/run.js";

export { settings };
export const timing = settings.timing;
export const flap = settings.flap;
export const slots = [];

// The tuck box (unbox-rig.js): 67 × 92 × 20 mm, walls 1.6 mm.
export const BW = 0.067, BH = 0.092, BD = 0.020, WALL = 0.0016;
/** Drawn local bounds of the tuck box with its flap shut (the flap stands 2.8 mm proud of the rim, 1.2 mm past the front). */
export const TUCK_BOX = { min: [-BW / 2, -BH / 2, -BD / 2], max: [BW / 2, BH / 2 + 0.0028, BD / 2 + 0.0012] };
/** The flap's hinge (unbox-rig flapPivot) and its drawn bounds in the hinge frame. */
export const FLAP = {
    pivot: [0, BH / 2 - 0.0004, -BD / 2 + WALL],
    bounds: { min: [-(BW * 0.97) / 2, 0, 0], max: [(BW * 0.97) / 2, 0.0032, BD * 0.98] },
};
/** The box's own body under the flap (the flap must not swing into it; 2 mm at the hinge edge is the fold). */
export const BODY = { min: [-BW / 2, -BH / 2, -BD / 2], max: [BW / 2, BH / 2 - 0.0005, BD / 2 + 0.0005] };
export const FLAP_FOLD = { min: [FLAP.bounds.min[0], 0, 0.002], max: FLAP.bounds.max };

/** The flap's box at `angle` with the tuck box at `pose`. */
export function flapObb(pose, angle, bounds = FLAP.bounds) {
    const pivot = obbOf({ p: pose.p, q: pose.q }, { min: FLAP.pivot, max: FLAP.pivot }).c;
    return obbOf({ p: pivot, q: quatMul(pose.q, quatAxisAngle([1, 0, 0], -angle)) }, bounds);
}

/** What the flap must not swing into at `pose`: `solids` around it plus the box's own body (the fold excluded). */
export function flapSolids(pose, solids = []) {
    return [...solids, { ...obbOf(pose, BODY), kind: "box", name: "its own box" }];
}

/** The flap swinging from `from` to `to` (fractions of openRad) with the box at `pose`. */
export function planFlap({ pose, from = 0, to = 1, solids = [], tempo = timing.tempo }) {
    const all = flapSolids(pose, solids);
    const sweep = (a) => flapObb(pose, a, FLAP_FOLD);
    const plan = planSwing({ part: flap, from, to, sweep, solids: all, tempo });
    plan.sweep = sweep;
    plan.solids = all;
    return plan;
}

/** The plan's checks: no overlap, exact ends, duration and peak on the law. */
export function checkFlap(plan, tempo = timing.tempo) {
    return checkSwing(plan, { sweep: plan.sweep, solids: plan.solids, tempo });
}

const flapAt = new WeakMap();

async function swingFlap(box, to, { from, solids = [], tempo = timing.tempo, run = rafRun } = {}) {
    const plan = planFlap({ pose: worldPose(box.group), from: from ?? flapAt.get(box) ?? 0, to, solids, tempo });
    const ok = await run(plan.ms, (t) => box.setFlap(plan.at(t) / flap.openRad));
    if (ok === false) return null;
    flapAt.set(box, plan.to / flap.openRad);
    return plan;
}

/** Open the box's flap (to `opts.to`, default fully). Resolves with the plan (null if stopped). */
export function openFlap(box, opts = {}) {
    return swingFlap(box, opts.to ?? 1, opts);
}

/** Close the box's flap (to `opts.to`, default shut). */
export function closeFlap(box, opts = {}) {
    return swingFlap(box, opts.to ?? 0, opts);
}
