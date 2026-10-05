/**
 * The open-close-lid microdemo's placement: the chest standing at one
 * fixed spot per seed (?seed=N), its lid opened and closed there on a
 * loop. Seeds: 1 its playroom corner turned to the room (yaw π, the
 * microdemos' proposed turn); 2 turned as the live playroom has it
 * (yaw π/2: the lid meets the wall); 3 a step in front of the shelf, hinge
 * toward it (the lid meets the shelf); 4+ random spots on the floor. Every
 * spot is in view of the page's fixed camera direction (the table is not
 * between them).
 *
 *   lidPlacement(seed) → { seed, kind, label, at, solids, open, close, checks }
 */
import { rng, worstDepth } from "../shared/geom.js";
import { CHEST, DEN, chestAt, chestBodyObb } from "../shared/room.js";
import { chestAround, lidObb, planLid, checkLid, lid } from "./index.js";

export const DEFAULT_SEED = 1;
/** The page's camera: from this position looking at this target (the view direction is what matters). */
export const CAMERA = { position: [0.9, 2.3, 3.1], target: [-1.15, 0.8, -0.25], fov: 40, fill: 0.92 };

const TABLE_R = 1.033;
const HALF_DIAG = Math.hypot(CHEST.outer.max[0] - CHEST.outer.min[0], CHEST.outer.max[2] - CHEST.outer.min[2]) / 2;

/** The table is not between the chest and the camera (looking along the camera's direction, flat). */
export function inView(at) {
    const d = [CAMERA.position[0] - CAMERA.target[0], CAMERA.position[2] - CAMERA.target[2]];
    const n = Math.hypot(...d);
    const u = [d[0] / n, d[1] / n];
    const w = [DEN.x - at.centre[0], DEN.z - at.centre[1]];
    const along = w[0] * u[0] + w[1] * u[1];
    const across = Math.abs(w[0] * u[1] - w[1] * u[0]);
    return along <= 0 || across > TABLE_R + HALF_DIAG;
}

/** Standing on the floor, 2 cm clear of everything, its shut lid clear too. */
function clear(at) {
    const solids = chestAround(at).filter((s) => s.name !== "floor");
    if (worstDepth(chestBodyObb(at), solids, 0.02).depth > 0) return false;
    return worstDepth(lidObb(at, 0), solids, 0.01).depth <= 0;
}

const FIXED = [
    ["real", "in its corner, turned to the room", CHEST],
    ["edge", "turned as the live playroom has it (yaw π/2): the lid meets the wall", chestAt(CHEST.centre, Math.PI / 2)],
    ["edge", "a step in front of the shelf, hinge toward it: the lid meets the shelf", chestAt([1.4, -1.25], 0)],
];

export function lidPlacement(seed = DEFAULT_SEED) {
    let kind, label, at;
    if (seed >= 1 && seed <= FIXED.length) {
        [kind, label, at] = FIXED[seed - 1];
        if (!clear(at)) throw new Error(`lid seed ${seed} (${label}): spot not clear`);
    } else {
        const r = rng(seed * 7907 + 11);
        for (let k = 0; k < 800 && !at; k++) {
            const c = chestAt([-2.3 + r() * 4.6, -1.85 + r() * 3.15], r() * Math.PI * 2);
            if (clear(c) && inView(c)) at = c;
        }
        if (!at) throw new Error(`lid seed ${seed}: no random spot`);
        kind = "random";
        label = "a random spot on the floor";
    }
    const solids = chestAround(at);
    const open = planLid({ at, from: 0, to: 1, solids });
    const close = planLid({ at, from: open.to / lid.openRad, to: 0, solids });
    return { seed, kind, label, at, solids, open, close, checks: [checkLid(open), checkLid(close)] };
}
