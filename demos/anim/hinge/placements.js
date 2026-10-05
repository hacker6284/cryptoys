/**
 * The hinge microdemo's placements: a seeded loop of CYCLES swings, one
 * primitive and nothing else moving. Each cycle is a fresh placement (a
 * clean cut, not motion): the KEY tuck box (playroom/unbox-rig.js, the
 * real hinged flap) set down at a new pose, then only its flap swings;
 * every fourth cycle the toy chest set down at a new spot on the floor,
 * then only its lid swings. Flap poses: the real ones (table centre, the
 * shelf slot), edge cases (lying on its back so the flap swings down to
 * the felt, face down, on its side, its back 5 mm from the shelf's
 * backboard so the flap meets it, 6 mm from the MSG box so it swings just
 * over it, half-open swings, open/half-shut/reopen) and random ones. Chest
 * spots: its corner (turned to the room), turned as the live playroom has
 * it (the lid meets the wall), a step in front of the shelf (the lid
 * meets the shelf board), random spots.
 *
 * Independent of every other primitive: only geom.js, room.js, poses.js
 * and hinge itself.
 */
import { rng, quatAxisAngle, quatMul, obbOf, obbCorners, worstDepth } from "../geom.js";
import { roomSolids, roomSolidsWithChest, chestAt, chestBodyObb, SURFACES, REAL_POSES, DEN, CHEST } from "../room.js";
import { DECK_BOX, STAND, FACE_UP, FACE_DOWN, SIDE, orient, seatPose, orientName } from "../poses.js";
import { planHinge, checkHinge, parts } from "./index.js";

export const CYCLES = 24;
export const DEFAULT_SEED = 1;

// The tuck box (unbox-rig.js): 67 × 92 × 20 mm, walls 1.6 mm.
const BW = 0.067, BH = 0.092, BD = 0.020, WALL = 0.0016;
/** Drawn local bounds of the tuck box with its flap shut (the flap stands 2.8 mm proud of the rim, 1.2 mm past the front). */
export const TUCK_BOX = { min: [-BW / 2, -BH / 2, -BD / 2], max: [BW / 2, BH / 2 + 0.0028, BD / 2 + 0.0012] };
/** The flap's hinge (unbox-rig flapPivot) and its drawn bounds in the hinge frame. */
export const FLAP = {
    pivot: [0, BH / 2 - 0.0004, -BD / 2 + WALL],
    bounds: { min: [-(BW * 0.97) / 2, 0, 0], max: [(BW * 0.97) / 2, 0.0032, BD * 0.98] },
};
/** The box's own body under the flap (the flap must not swing into it; 2 mm at the hinge edge is the fold). */
const BODY = { min: [-BW / 2, -BH / 2, -BD / 2], max: [BW / 2, BH / 2 - 0.0005, BD / 2 + 0.0005] };
const FLAP_FOLD = { min: [FLAP.bounds.min[0], 0, 0.002], max: FLAP.bounds.max };

/** The flap's box at `angle` with the tuck box at `pose`. */
export function flapObb(pose, angle, bounds = FLAP.bounds) {
    const pivot = obbOf({ p: pose.p, q: pose.q }, { min: FLAP.pivot, max: FLAP.pivot }).c;
    return obbOf({ p: pivot, q: quatMul(pose.q, quatAxisAngle([1, 0, 0], -angle)) }, bounds);
}

/** What the flap must not swing into at `pose`: the room, the MSG box, the box's own body (the fold excluded). */
export function flapSolids(pose, others) {
    return [...roomSolids({ lidAngle: 0 }), ...others, { ...obbOf(pose, BODY), kind: "box", name: "its own box" }];
}

const SUPPORT = { felt: "table", shelf: "shelf-top", chest: "chest-floor" };

function seat(t) {
    return seatPose({ x: t.x, z: t.z, q: orient(t.o, t.yaw), surfaceY: SURFACES[t.surface].y }, TUCK_BOX);
}

function clear(t, pose, solids) {
    const o = obbOf(pose, TUCK_BOX);
    // Every corner of its footprint on the surface.
    if (!obbCorners(o).every((c) => SURFACES[t.surface].inside(c[0], c[2], 0))) return false;
    if (worstDepth(o, solids, 0).depth > 0.0005) return false;
    return worstDepth(o, solids.filter((s) => s.name !== SUPPORT[t.surface]), t.minGap ?? 0.01).depth <= 0;
}

// MSG stays at its borrowed rest pose all loop (world.js makeDeckBox).
const MSG_AT = { ...REAL_POSES.restLeft, o: STAND };
const MSG_POSE = seatPose({ x: MSG_AT.x, z: MSG_AT.z, q: orient(STAND, MSG_AT.yaw), surfaceY: SURFACES.felt.y }, DECK_BOX);
const MSG_SOLID = { ...obbOf(MSG_POSE, DECK_BOX), kind: "box", name: "MSG box" };

function program() {
    const flap = (label, kind, target, swings = [[0, 1], [1, 0]]) => ({ kind, label, what: "flap", target, swings });
    const lid = (label, kind, spot, swings = [[0, 1], [1, 0]]) => ({ kind, label, what: "lid", spot, swings });
    return [
        flap("KEY borrowed: flap at the table centre", "real", () => ({ ...REAL_POSES.tableCentre, o: STAND })),
        flap("random", "random", "random"),
        flap("lying on its back: the flap swings down to the felt", "edge", (r) => ({ ...spot(r), o: FACE_UP })),
        lid("chest in its corner, turned to the room: the lid opens and drops shut", "real", () => CHEST),
        flap("on the shelf, its back 5 mm from the backboard: the flap meets it", "edge", () => ({ surface: "shelf", x: -1.0, z: -2.28 + 0.005 + BD / 2, yaw: 0, o: STAND, minGap: 0.004 })),
        flap("random", "random", "random"),
        flap("its back 6 mm from the MSG box: the flap swings back over it", "edge", () => behind(MSG_AT, 0.006)),
        lid("chest turned as the live playroom has it (yaw π/2): the lid meets the wall", "edge", () => chestAt(CHEST.centre, Math.PI / 2)),
        flap("lying face down", "edge", (r) => ({ ...spot(r), o: FACE_DOWN })),
        flap("random", "random", "random"),
        flap("half turn, at the felt's edge", "edge", () => ({ surface: "felt", x: DEN.x + 0.8, z: DEN.z + 0.1, yaw: Math.PI / 2 + Math.PI, o: STAND })),
        lid("chest at a random spot: the lid opens, drops part-way, reopened, shut", "random", "random", [[0, 1], [1, 0.45], [0.45, 1], [1, 0]]),
        flap("on its side", "edge", (r) => ({ ...spot(r), o: SIDE })),
        flap("random", "random", "random"),
        flap("side by side with the MSG box (12 mm)", "edge", () => ({ surface: "felt", x: MSG_AT.x + (BW + 0.012) * Math.cos(MSG_AT.yaw), z: MSG_AT.z - (BW + 0.012) * Math.sin(MSG_AT.yaw), yaw: MSG_AT.yaw, o: STAND })),
        lid("chest a step in front of the shelf, hinge toward it: the lid meets the shelf board", "edge", () => chestAt([-1.38, -1.25], 0)),
        flap("random, on the shelf", "random", "random-shelf"),
        flap("flap half open and shut", "edge", (r) => ({ ...spot(r), o: STAND }), [[0, 0.5], [0.5, 0]]),
        flap("random", "random", "random"),
        lid("chest at a random spot: the lid opens half way and drops shut", "random", "random", [[0, 0.5], [0.5, 0]]),
        flap("random", "random", "random"),
        flap("flap opened, half shut, reopened, shut", "edge", (r) => ({ ...spot(r), o: STAND }), [[0, 1], [1, 0.5], [0.5, 1], [1, 0]]),
        flap("random", "random", "random"),
        flap("KEY home: flap in its shelf slot", "real", () => ({ ...REAL_POSES.shelfSlot, o: STAND })),
    ];
}

/** The room the chest is set down in: everything but the floor it stands on and its own home body. */
function chestClear(chest) {
    const solids = [...roomSolidsWithChest(chest).filter((s) => !s.name.startsWith("chest-") && s.name !== "floor"), MSG_SOLID];
    if (worstDepth(chestBodyObb(chest), solids, 0.02).depth > 0) return false;
    const shut = roomSolidsWithChest(chest).find((s) => s.name === "chest-lid");
    return worstDepth(shut, solids, 0.01).depth <= 0;
}

function randomChest(r) {
    return chestAt([-2.3 + r() * 4.6, -1.85 + r() * 3.15], r() * Math.PI * 2);
}

/** Standing in front of `m` (same yaw), its back `gap` from m's front. */
function behind(m, gap) {
    const d = 0.0104 + gap + BD / 2; // MSG's front (label 0.4 mm proud) to KEY's centre
    return { surface: "felt", x: m.x + d * Math.sin(m.yaw), z: m.z + d * Math.cos(m.yaw), yaw: m.yaw, o: STAND, minGap: gap - 0.001 };
}

function spot(r) {
    for (let k = 0; k < 400; k++) {
        const a = r() * Math.PI * 2, d = Math.sqrt(r()) * 0.78;
        const x = DEN.x + Math.cos(a) * d, z = DEN.z + Math.sin(a) * d;
        if (Math.hypot(x - MSG_AT.x, z - MSG_AT.z) > 0.25) return { surface: "felt", x, z, yaw: r() * Math.PI * 2 };
    }
    return { surface: "felt", x: DEN.x, z: DEN.z, yaw: 0 };
}

function randomTarget(r, shelf) {
    if (shelf || r() < 0.2) return { surface: "shelf", x: -2.1 + r() * 2.3, z: -2.2 + r() * 0.13, yaw: (r() - 0.5) * 1.2, o: STAND };
    const o = r();
    return { ...spot(r), o: o < 0.6 ? STAND : o < 0.75 ? FACE_UP : o < 0.9 ? FACE_DOWN : SIDE };
}

/** The seeded loop: per cycle the placement (box pose or chest spot), the swings, their plans and checks. */
export function hingeSchedule(seed = DEFAULT_SEED) {
    const r = rng(seed * 104729 + 3);
    const cycles = [];
    const roomForBox = [...roomSolids(), MSG_SOLID];
    let last = null;
    program().forEach((step, i) => {
        const c = { n: i + 1, kind: step.kind, label: step.label, what: step.what, swings: [] };
        if (step.what === "flap") {
            let t = null;
            if (typeof step.target === "function") {
                t = step.target(r);
                if (!clear(t, seat(t), roomForBox)) throw new Error(`hinge cycle ${c.n} (${c.label}): pose not clear`);
            } else {
                for (let k = 0; k < 400 && !t; k++) {
                    const cand = randomTarget(r, step.target === "random-shelf");
                    if (last && Math.hypot(cand.x - last.x, cand.z - last.z) < 0.15) continue;
                    if (clear(cand, seat(cand), roomForBox)) t = cand;
                }
                if (!t) throw new Error(`hinge cycle ${c.n}: no random pose`);
                c.label = `${t.surface}, ${orientName(t.o)}`;
            }
            c.pose = seat(t);
            c.target = t;
            c.surfaceY = SURFACES[t.surface].y;
            c.solids = flapSolids(c.pose, [MSG_SOLID]);
            const sweep = (a) => flapObb(c.pose, a, FLAP_FOLD);
            let frac = 0;
            for (const [, b] of step.swings) {
                const plan = planHinge({ part: "tuck-flap", from: frac, to: b, sweep, solids: c.solids });
                c.swings.push({ plan, check: checkHinge(plan, { sweep, solids: c.solids }) });
                frac = plan.to / parts["tuck-flap"].openRad;
            }
            last = t;
        } else {
            let chest = null;
            if (step.spot === "random") {
                for (let k = 0; k < 400 && !chest; k++) {
                    const cand = randomChest(r);
                    if (chestClear(cand)) chest = cand;
                }
                if (!chest) throw new Error(`hinge cycle ${c.n}: no random chest spot`);
            } else {
                chest = step.spot();
                if (!chestClear(chest)) throw new Error(`hinge cycle ${c.n} (${c.label}): chest spot not clear`);
            }
            c.chest = chest;
            // What the lid must not swing into: the room, the MSG box, its own body (touching it shut is the baseline).
            c.solids = [...roomSolidsWithChest(chest).filter((s) => s.name !== "chest-lid" && (s.name === "chest-body" || !s.name.startsWith("chest-"))), MSG_SOLID];
            const sweep = (a) => roomLid(chest, a);
            let frac = 0;
            for (const [, b] of step.swings) {
                const plan = planHinge({ part: "chest-lid", from: frac, to: b, sweep, solids: c.solids });
                c.swings.push({ plan, check: checkHinge(plan, { sweep, solids: c.solids }) });
                frac = plan.to / CHEST.lidOpenAngle;
            }
        }
        cycles.push(c);
    });
    return { seed, cycles, msg: MSG_AT, msgPose: MSG_POSE };
}

/** The chest lid's box at `angle` with the chest at `chest`. */
export function roomLid(chest, angle) {
    return roomSolidsWithChest(chest, { lidAngle: angle }).find((s) => s.name === "chest-lid");
}

export { BW, BH, BD, BODY, FLAP_FOLD, MSG_AT, MSG_POSE, MSG_SOLID };
