/**
 * ship: a Battleship piece and its own moves, wherever its grid is.
 *
 *   import { ship } from "demos/anim/index.js";
 *   await ship.place(mesh, at);   // straight down onto its holes
 *   await ship.lift(mesh);        // straight up; hidden after
 *   await ship.move(mesh, to);    // slide along the frame (the walk cursor)
 *
 * `mesh` is the piece (origin on the hull bottom at the middle of its hole
 * run, +y up); poses are in its parent frame, which is level (a grid lying
 * on the table). `tempo` scales the durations; `run(ms, step)` plays it on
 * another clock. The values live in ./settings.js (NOT YET APPROVED).
 */
import settings from "./settings.js";
import { rafRun } from "../shared/run.js";

export { settings };
export const timing = settings.timing;
export const slots = [];

const easeInOutCubic = (t) => (t < 0.5 ? 4 * t * t * t : 1 - ((-2 * t + 2) ** 3) / 2);
const easeOutCubic = (t) => 1 - (1 - t) ** 3;
const easeInOutQuad = (t) => (t < 0.5 ? 2 * t * t : 1 - ((-2 * t + 2) ** 2) / 2);

export function planPlace({ tempo = timing.tempo } = {}) {
    const ms = settings.place.ms / Math.max(0.05, tempo);
    return { ms, at: (t) => settings.place.dropM * (1 - easeInOutCubic(Math.min(1, t / ms))) };
}

export function planLift({ tempo = timing.tempo } = {}) {
    const ms = settings.lift.ms / Math.max(0.05, tempo);
    return { ms, at: (t) => settings.lift.dropM * easeOutCubic(Math.min(1, t / ms)) };
}

/** Lower the piece onto `at` (Vector3, its seated origin). */
export async function place(mesh, at, { tempo = timing.tempo, run = rafRun } = {}) {
    const plan = planPlace({ tempo });
    mesh.visible = true;
    const ok = await run(plan.ms, (t) => mesh.position.set(at.x, at.y + plan.at(t), at.z));
    mesh.position.copy(at);
    return ok !== false;
}

/** Lift the piece straight up off its holes; it is hidden at the end. */
export async function lift(mesh, { tempo = timing.tempo, run = rafRun } = {}) {
    const plan = planLift({ tempo });
    const at = mesh.position.clone();
    const ok = await run(plan.ms, (t) => mesh.position.set(at.x, at.y + plan.at(t), at.z));
    mesh.visible = false;
    mesh.position.copy(at);
    return ok !== false;
}

/** Slide the piece to `to` (Vector3) along its frame, no hop. */
export async function move(mesh, to, { tempo = timing.tempo, run = rafRun } = {}) {
    const ms = settings.move.ms / Math.max(0.05, tempo);
    const from = mesh.position.clone();
    mesh.visible = true;
    const ok = await run(ms, (t) => mesh.position.lerpVectors(from, to, easeInOutQuad(Math.min(1, t / ms))));
    mesh.position.copy(to);
    return ok !== false;
}
