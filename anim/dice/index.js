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
 */
import settings from "./settings.js";
import { FACES } from "./faces.js";
import { rafRun } from "../shared/run.js";

export { settings, FACES };
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
