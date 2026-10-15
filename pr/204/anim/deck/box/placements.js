/**
 * The open-close-flap microdemo's placement: one tuck box, one fixed pose
 * per seed (?seed=N), its flap opened and closed there on a loop. Seeds
 * 1–7 are the real poses and the edge cases, larger seeds random poses:
 *   1 table centre, standing (real: KEY borrowed)   2 its shelf slot (real)
 *   3 lying on its back (the felt stops the flap)    4 on the shelf, its
 *   back 5 mm from the backboard (the backboard stops it)   5 face down
 *   6 on its side   7 half turn at the felt's edge   8+ random.
 *
 *   flapPlacement(seed) → { seed, kind, label, target, pose, surfaceY,
 *     solids, open, close, checks }
 */
import { rng, obbOf, obbCorners, worstDepth } from "../../shared/geom.js";
import { roomSolids, SURFACES, REAL_POSES, DEN } from "../../shared/room.js";
import { STAND, FACE_UP, FACE_DOWN, SIDE, orient, seatPose, orientName } from "../../shared/poses.js";
import { TUCK_BOX, BD, planFlap, checkFlap, flap } from "./index.js";

export const DEFAULT_SEED = 1;

const SUPPORT = { felt: "table", shelf: "shelf-top" };

/** The fixed placements: [kind, label, target]. */
const FIXED = [
    ["real", "KEY borrowed: standing at the table centre", { ...REAL_POSES.tableCentre, o: STAND }],
    ["real", "in its shelf slot", { ...REAL_POSES.shelfSlot, o: STAND }],
    ["edge", "lying on its back: the flap swings down to the felt", { surface: "felt", x: DEN.x + 0.25, z: DEN.z + 0.2, yaw: 0.6, o: FACE_UP }],
    ["edge", "on the shelf, its back 5 mm from the backboard: the flap meets it", { surface: "shelf", x: -1.0, z: -2.28 + 0.005 + BD / 2, yaw: 0, o: STAND, minGap: 0.004 }],
    ["edge", "lying face down", { surface: "felt", x: DEN.x - 0.3, z: DEN.z + 0.25, yaw: 2.2, o: FACE_DOWN }],
    ["edge", "on its side", { surface: "felt", x: DEN.x + 0.35, z: DEN.z - 0.3, yaw: -0.9, o: SIDE }],
    ["edge", "half turn, at the felt's edge", { surface: "felt", x: DEN.x + 0.8, z: DEN.z + 0.1, yaw: Math.PI / 2 + Math.PI, o: STAND }],
];

function seat(t) {
    return seatPose({ x: t.x, z: t.z, q: orient(t.o, t.yaw), surfaceY: SURFACES[t.surface].y }, TUCK_BOX);
}

/** Inside its surface, not into anything, 10 mm clear of everything but what it stands on. */
function clear(t, pose, solids) {
    const o = obbOf(pose, TUCK_BOX);
    if (!obbCorners(o).every((c) => SURFACES[t.surface].inside(c[0], c[2], 0))) return false;
    if (worstDepth(o, solids, 0).depth > 0.0005) return false;
    return worstDepth(o, solids.filter((s) => s.name !== SUPPORT[t.surface]), t.minGap ?? 0.01).depth <= 0;
}

function randomTarget(r) {
    if (r() < 0.25) return { surface: "shelf", x: -2.1 + r() * 2.3, z: -2.2 + r() * 0.13, yaw: (r() - 0.5) * 1.2, o: STAND };
    const a = r() * Math.PI * 2, d = Math.sqrt(r()) * 0.78;
    const o = r();
    return { surface: "felt", x: DEN.x + Math.cos(a) * d, z: DEN.z + Math.sin(a) * d, yaw: r() * Math.PI * 2, o: o < 0.55 ? STAND : o < 0.7 ? FACE_UP : o < 0.85 ? FACE_DOWN : SIDE };
}

export function flapPlacement(seed = DEFAULT_SEED) {
    const solids = roomSolids();
    let kind, label, target;
    if (seed >= 1 && seed <= FIXED.length) {
        [kind, label, target] = FIXED[seed - 1];
        if (!clear(target, seat(target), solids)) throw new Error(`flap seed ${seed} (${label}): pose not clear`);
    } else {
        const r = rng(seed * 104729 + 3);
        for (let k = 0; k < 400 && !target; k++) {
            const t = randomTarget(r);
            if (clear(t, seat(t), solids)) target = t;
        }
        if (!target) throw new Error(`flap seed ${seed}: no random pose`);
        kind = "random";
        label = `${target.surface === "felt" ? "on the felt" : "on the shelf"}, ${orientName(target.o)}`;
    }
    const pose = seat(target);
    const open = planFlap({ pose, from: 0, to: 1, solids });
    const close = planFlap({ pose, from: open.to / flap.openRad, to: 0, solids });
    return { seed, kind, label, target, pose, surfaceY: SURFACES[target.surface].y, solids, open, close, checks: [checkFlap(open), checkFlap(close)] };
}
