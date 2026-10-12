/**
 * dice: one die and its roll, wherever it lies.
 *
 *   import { dice } from "demos/anim/index.js";
 *   await dice.roll(mesh, "d10", 7, { landY });   // tumble and land showing 7
 *   mesh.quaternion.copy(dice.restQuaternion("d10", 7, 0, THREE.Quaternion, THREE.Vector3));
 *   mesh.position.y = dice.restHeight(dieMesh, "d10", 7, THREE.Quaternion, THREE.Vector3);
 *
 * `mesh` is the die resting on the felt (origin at its centre; restHeight
 * is the height of its centre above the felt for the face it lands on). The face
 * normals of the Facehunter dice (CC0, demos/bs/assets/LICENSE.md) are in
 * ./faces.js. `tempo` scales the duration; `run(ms, step)` plays it on
 * another clock. The values live in ./settings.js (NOT YET APPROVED).
 *
 *   await dice.place(mesh, "d10", to, { clearY, solids });   // lift it and set it down at `to`
 *
 * place: `to` is a world pose { p, q } (restQuaternion and restHeight give
 * the one for a face on the felt); clearY the height its bottom must clear
 * first (a box's rim, a cup it passes over). The die keeps its parent. planPlace is the same
 * move as a plan, for checks (checkHop).
 */
import settings from "./settings.js";
import { FACES } from "./faces.js";
import { rafRun, playPose, worldPose } from "../shared/run.js";
import { planHop, checkHop } from "../shared/hop.js";

export { settings, FACES, checkHop };

/** Each die's drawn bounds about its centre (the Facehunter GLBs, MEASURED). */
export const SHAPES = {
    d10: { min: [-0.0101, -0.011, -0.01055], max: [0.0101, 0.011, 0.01055] },
    d12: { min: [-0.0095, -0.0095, -0.0095], max: [0.0095, 0.0095, 0.0095] },
    d6: { min: [-0.008, -0.008, -0.008], max: [0.008, 0.008, 0.008] },
};
export const timing = settings.timing;
export const slots = [];

/** The rotation that turns face `face` of a `kind` die ("d10", "d12", "d6") straight up, yawed by `yaw`. */
export function restQuaternion(kind, face, yaw = 0, Q, V) {
    const n = FACES[kind]?.[face];
    if (!n) throw new Error(`no face ${face} on a ${kind}`);
    const from = new V(n[0], n[1], n[2]).normalize();
    const q = new Q().setFromUnitVectors(from, new V(0, 1, 0));
    return new Q().setFromAxisAngle(new V(0, 1, 0), yaw).multiply(q);
}

/**
 * The height of a die's centre above the felt when it rests showing `face`:
 * the lowest vertex of `dieMesh` (its geometry, scale and own rotation)
 * turned by restQuaternion. Q, V: three's Quaternion and Vector3.
 */
export function restHeight(dieMesh, kind, face, Q, V) {
    const q = restQuaternion(kind, face, 0, Q, V);
    const pos = dieMesh.geometry.attributes.position;
    const v = new V();
    let min = Infinity;
    for (let i = 0; i < pos.count; i++) {
        v.fromBufferAttribute(pos, i).multiply(dieMesh.scale).applyQuaternion(dieMesh.quaternion).applyQuaternion(q);
        min = Math.min(min, v.y);
    }
    return -min;
}

export function planRoll({ tempo = timing.tempo } = {}) {
    const ms = settings.roll.ms / Math.max(0.05, tempo);
    return {
        ms,
        at(t) {
            const u = Math.min(1, Math.max(0, t / ms));
            return { u, hop: Math.sin(Math.PI * u) * settings.roll.hopM, spin: u * settings.roll.turns * 2 * Math.PI };
        },
    };
}

/**
 * Roll the die: it hops off its spot, tumbles and lands on the same spot
 * showing `face`. kind: "d10" | "d12" | "d6"; yaw: the landing yaw; landY:
 * the height of its centre resting on that face (default: where it is).
 */
export async function roll(mesh, kind, face, { yaw = 0, landY, tempo = timing.tempo, run = rafRun } = {}) {
    const Q = mesh.quaternion.constructor;
    const V = mesh.position.constructor;
    const plan = planRoll({ tempo });
    const base = mesh.position.clone();
    const y1 = landY ?? base.y;
    const start = mesh.quaternion.clone();
    const end = restQuaternion(kind, face, yaw, Q, V);
    const axis = new V(1, 0.35, 0.6).normalize();
    const tumble = new Q();
    const tmp = new Q();
    const ok = await run(plan.ms, (t) => {
        const { u, hop, spin } = plan.at(t);
        mesh.position.set(base.x, base.y + (y1 - base.y) * u + hop, base.z);
        tumble.setFromAxisAngle(axis, spin);
        tmp.copy(start).premultiply(tumble);
        const land = Math.max(0, (u - 0.75) / 0.25);
        mesh.quaternion.slerpQuaternions(tmp, end, land * land * (3 - 2 * land));
    });
    mesh.position.set(base.x, y1, base.z);
    mesh.quaternion.copy(end);
    return ok !== false;
}

/** The die from world pose `from` to `to`, its bottom clearing `clearY` on the way. */
export function planPlace({ kind, from, to, clearY = -Infinity, solids = [], tempo = timing.tempo }) {
    const law = settings.place;
    return planHop({ from, to, parts: [SHAPES[kind]], clearY: clearY + law.clearM, solids, law, tempo });
}

/** Lift the die from where it is and set it down at world pose `to`. Resolves with the plan (null if stopped). */
export function place(mesh, kind, to, { clearY, solids = [], tempo = timing.tempo, run = rafRun } = {}) {
    const plan = planPlace({ kind, from: worldPose(mesh), to, clearY, solids, tempo });
    return playPose(mesh, plan, run);
}
