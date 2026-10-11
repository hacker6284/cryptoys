/**
 * deck/card: a single card of the deck and its own moves, wherever it is.
 *
 *   import { deck } from "demos/anim/index.js";
 *   await deck.card.turnOver(mesh, { faceUp: true });  // roll it over on its seat
 *   await deck.card.move(mesh, toPosition, toQuaternion);  // slide-and-hop to a pose
 *   await deck.card.straight(mesh, toPosition);  // slide out of / into its box
 *
 * `mesh` is a three.js card lying flat (its 63 mm side along x, 88 mm
 * along z, face on +y when face up). Poses are in the mesh's parent frame.
 * `run(ms, step)` plays it on another clock (default: real time); it
 * resolves false if stopped. The values live in ./settings.js
 * (NOT YET APPROVED). Extract, insert and peel are not built yet.
 */
import settings from "./settings.js";
import { rafRun } from "../../shared/run.js";

export { settings };
export const timing = settings.timing;
export const slots = [];

/** Half the card's width: how high its centre must rise to roll over without touching its seat. */
export const HALF_W = 0.0315;

function easeInOutCubic(t) {
    return t < 0.5 ? 4 * t * t * t : 1 - ((-2 * t + 2) ** 3) / 2;
}

function easeInOutQuad(t) {
    return t < 0.5 ? 2 * t * t : 1 - ((-2 * t + 2) ** 2) / 2;
}

/** Turn-over plan: duration and the card's (height, roll) at time t (ms). */
export function planTurnOver({ tempo = timing.tempo } = {}) {
    const ms = settings.turnOver.ms / Math.max(0.25, tempo);
    const top = HALF_W + settings.turnOver.clearM;
    return {
        ms,
        top,
        at(t) {
            const u = Math.min(1, Math.max(0, t / ms));
            return { lift: Math.sin(Math.PI * u) * top, roll: Math.PI * easeInOutCubic(u) };
        },
    };
}

/**
 * Roll the card over on its seat: face up (faceUp true) or face down.
 * Resolves true when done (false if stopped).
 */
export async function turnOver(mesh, { faceUp = true, tempo = timing.tempo, run = rafRun } = {}) {
    const plan = planTurnOver({ tempo });
    const Q = mesh.quaternion.constructor;
    const V = mesh.position.constructor;
    const seatY = mesh.position.y;
    const from = mesh.quaternion.clone();
    // Face up = identity roll; face down = π about z (the card's long axis).
    const to = new Q().setFromAxisAngle(new V(0, 0, 1), faceUp ? 0 : Math.PI);
    if (from.angleTo(to) < 1e-3) return true;
    const axis = new V(0, 0, 1);
    const roll = new Q();
    const ok = await run(plan.ms, (t) => {
        const { lift, roll: a } = plan.at(t);
        mesh.position.y = seatY + lift;
        roll.setFromAxisAngle(axis, a);
        mesh.quaternion.copy(from).premultiply(roll);
    });
    mesh.position.y = seatY;
    if (ok !== false) mesh.quaternion.copy(to);
    return ok !== false;
}

/** Move plan: duration and the card's progress (slide, hop) at time t (ms). */
export function planMove({ tempo = timing.tempo } = {}) {
    const ms = settings.move.ms / Math.max(0.25, tempo);
    return {
        ms,
        at(t) {
            const u = Math.min(1, Math.max(0, t / ms));
            return { s: easeInOutQuad(u), hop: Math.sin(Math.PI * u) * settings.move.hopM };
        },
    };
}

/** Slide-and-hop the card to `to` (Vector3) and `toQ` (Quaternion, default: as it is). */
export async function move(mesh, to, toQ = null, { tempo = timing.tempo, run = rafRun } = {}) {
    const plan = planMove({ tempo });
    const from = mesh.position.clone();
    const fromQ = mesh.quaternion.clone();
    const endQ = toQ ? toQ.clone() : fromQ.clone();
    const ok = await run(plan.ms, (t) => {
        const { s, hop } = plan.at(t);
        mesh.position.lerpVectors(from, to, s);
        mesh.position.y += hop;
        mesh.quaternion.slerpQuaternions(fromQ, endQ, s);
    });
    if (ok !== false) {
        mesh.position.copy(to);
        mesh.quaternion.copy(endQ);
    }
    return ok !== false;
}

/** Slide the card straight to `to` (no hop, no turn): out of or into its box. */
export async function straight(mesh, to, { tempo = timing.tempo, run = rafRun } = {}) {
    const ms = settings.straight.ms / Math.max(0.25, tempo);
    const from = mesh.position.clone();
    const ok = await run(ms, (t) => mesh.position.lerpVectors(from, to, easeInOutQuad(Math.min(1, t / ms))));
    if (ok !== false) mesh.position.copy(to);
    return ok !== false;
}
