/**
 * peg: a Battleship peg and its own moves, wherever its hole is.
 *
 *   import { peg } from "demos/anim/index.js";
 *   await peg.insert(mesh, seat, axis);   // down its hole's axis into the seat
 *   await peg.remove(mesh, axis);         // pull out along the axis; hidden after
 *   await peg.slide(mesh, fromSeat, toSeat, axis);  // out, arc, into another hole
 *
 * `mesh` is the peg (origin at the underside of its head, +y up the head);
 * `seat` its seated position and `axis` the unit vector out of the hole
 * (both in the mesh's parent frame). `tempo` scales every duration;
 * `run(ms, step)` plays it on another clock (default: real time); it
 * resolves false if stopped. The values live in ./settings.js (NOT YET
 * APPROVED).
 */
import settings from "./settings.js";
import { rafRun } from "../shared/run.js";
import { easeInOutCubic, easeInCubic, easeOutCubic, easeInOutQuad } from "../shared/geom.js";

export { settings };
export const timing = settings.timing;
export const slots = [];


/** Insert plan: duration and the peg's height above its seat at time t (ms). */
export function planInsert({ tempo = timing.tempo } = {}) {
    const k = Math.max(0.05, tempo);
    const { approachMs, pushMs, hoverM, seatM } = settings.insert;
    const a = approachMs / k;
    const p = pushMs / k;
    return {
        ms: a + p,
        at(t) {
            if (t <= a) return seatM + (hoverM - seatM) * (1 - easeInOutCubic(Math.min(1, t / a)));
            return seatM * (1 - easeInCubic(Math.min(1, (t - a) / Math.max(1e-6, p))));
        },
    };
}

/** Remove plan: duration and the peg's height above its seat at time t (ms). */
export function planRemove({ tempo = timing.tempo } = {}) {
    const ms = settings.remove.ms / Math.max(0.05, tempo);
    return { ms, at: (t) => settings.remove.hoverM * easeOutCubic(Math.min(1, t / ms)) };
}

/** Slide plan: out, arc, in; progress s along the way and the height off the line at time t (ms). */
export function planSlide({ tempo = timing.tempo } = {}) {
    const ms = settings.slide.ms / Math.max(0.05, tempo);
    return {
        ms,
        at(t) {
            const u = Math.min(1, t / ms);
            return { s: easeInOutQuad(u), lift: Math.sin(Math.PI * u) * settings.slide.hopM };
        },
    };
}

function along(mesh, seat, axis, h) {
    mesh.position.set(seat.x + axis.x * h, seat.y + axis.y * h, seat.z + axis.z * h);
}

/** Bring the peg down its hole's axis into `seat`. Resolves true when seated. */
export async function insert(mesh, seat, axis, { tempo = timing.tempo, run = rafRun } = {}) {
    const plan = planInsert({ tempo });
    mesh.visible = true;
    along(mesh, seat, axis, settings.insert.hoverM);
    const ok = await run(plan.ms, (t) => along(mesh, seat, axis, plan.at(t)));
    along(mesh, seat, axis, 0);
    return ok !== false;
}

/** Pull the peg straight out of its hole along `axis`; it is hidden at the end. */
export async function remove(mesh, axis, { tempo = timing.tempo, run = rafRun } = {}) {
    const plan = planRemove({ tempo });
    const seat = mesh.position.clone();
    const ok = await run(plan.ms, (t) => along(mesh, seat, axis, plan.at(t)));
    mesh.visible = false;
    along(mesh, seat, axis, 0);
    return ok !== false;
}

/** Move the peg from `from` to `to` (seats in its parent frame): out, an arc, in. */
export async function slide(mesh, from, to, axis, { tempo = timing.tempo, run = rafRun } = {}) {
    const plan = planSlide({ tempo });
    mesh.visible = true;
    const ok = await run(plan.ms, (t) => {
        const { s, lift } = plan.at(t);
        mesh.position.set(
            from.x + (to.x - from.x) * s + axis.x * lift,
            from.y + (to.y - from.y) * s + axis.y * lift,
            from.z + (to.z - from.z) * s + axis.z * lift,
        );
    });
    mesh.position.copy(to);
    return ok !== false;
}
