/**
 * chest: the toy chest and its own moves, open the lid and close the lid,
 * wherever the chest stands.
 *
 *   import { chest } from "demos/anim/index.js";
 *   await chest.openLid(rig, { at });   // rig: { setLid(fraction) }
 *   await chest.closeLid(rig, { at });
 *
 * `at` is where the chest stands (anim/shared/room.js chestAt(centre,
 * yaw); default CHEST, its spot in the playroom corner). `solids` is what
 * is around it (default: the room, chestAround(at)); its own body is
 * added here. `run(ms, step)` plays it on another clock (default: real
 * time). planLid / checkLid are the same move as a plan.
 *
 * Audited by demos/micro/chest/open-close-lid/, pinned by
 * ../library.test.mjs.
 */
import settings from "./settings.js";
import { CHEST, ROOM, chestAt, chestBodyObb, chestLidObb } from "../shared/room.js";
import { planSwing, checkSwing } from "../shared/swing.js";
import { rafRun } from "../shared/run.js";

export { settings, CHEST, chestAt };
export const timing = settings.timing;
export const lid = settings.lid;
export const slots = [];

/** The room around a chest standing at `at` (everything but the chest itself). */
export function chestAround(at = CHEST) {
    return ROOM.filter((s) => !s.name.startsWith("chest-"));
}

/** The lid's box at `angle` with the chest at `at`. */
export function lidObb(at, angle) {
    return { ...chestLidObb(angle, at), kind: "box", name: "chest-lid" };
}

/** The lid swinging from `from` to `to` (fractions of openRad) with the chest at `at`. */
export function planLid({ at = CHEST, from = 0, to = 1, solids = chestAround(at), tempo = timing.tempo }) {
    // Its own body is in the sweep too: shut, the lid rests on it (the baseline).
    const all = [...solids, { ...chestBodyObb(at), kind: "box", name: "chest-body" }];
    const sweep = (a) => lidObb(at, a);
    const plan = planSwing({ part: lid, from, to, sweep, solids: all, tempo });
    plan.sweep = sweep;
    plan.solids = all;
    return plan;
}

/** The plan's checks: no overlap, exact ends, duration and peak on the law. */
export function checkLid(plan, tempo = timing.tempo) {
    return checkSwing(plan, { sweep: plan.sweep, solids: plan.solids, tempo });
}

const lidAt = new WeakMap();

async function swingLid(rig, to, { at = CHEST, from, solids, tempo = timing.tempo, run = rafRun } = {}) {
    const plan = planLid({ at, from: from ?? lidAt.get(rig) ?? 0, to, solids: solids ?? chestAround(at), tempo });
    const ok = await run(plan.ms, (t) => rig.setLid(plan.at(t) / lid.openRad));
    if (ok === false) return null;
    lidAt.set(rig, plan.to / lid.openRad);
    return plan;
}

/** Open the chest's lid (to `opts.to`, default fully). Resolves with the plan (null if stopped). */
export function openLid(rig, opts = {}) {
    return swingLid(rig, opts.to ?? 1, opts);
}

/** Close the chest's lid (to `opts.to`, default shut). */
export function closeLid(rig, opts = {}) {
    return swingLid(rig, opts.to ?? 0, opts);
}
