/**
 * The carry microdemo's placements: a seeded, deterministic loop of
 * CYCLES carries of the two deck boxes (KEY, MSG) around the playroom.
 * Every cycle starts where the last one ended (nothing jumps) and has a
 * different end: the real playroom poses (borrow, aside, home), edge
 * cases (shortest hop, longest flight, 180° turn, flips, on its side,
 * up to the shelf, into the chest, next to the other box) and random
 * ones. The loop ends where it starts (both boxes home), so it repeats.
 *
 *   carrySchedule(seed) → { seed, start, cycles: [{ n, kind, label,
 *     mover, from, to, surfaceFrom, surfaceTo, chest, plan, check }] }
 */
import { rng, quatFromEuler, quatMul, obbOf, obbCorners, worstDepth } from "../geom.js";
import { roomSolids, SURFACES, REAL_POSES, DEN, CHEST } from "../room.js";
import { planCarry, checkPlan, seatPose } from "./index.js";

/** Drawn local bounds of the playroom deck box (world.js makeDeckBox: 67 × 92 × 20 mm, label 0.4 mm proud). */
export const DECK_BOX = { min: [-0.0335, -0.046, -0.01], max: [0.0335, 0.046, 0.0104] };
export const CYCLES = 24;
export const DEFAULT_SEED = 1;

// Orientations, as Euler XYZ before the yaw: standing, lying face up
// (label up), face down, on its long side.
const STAND = [0, 0, 0], FACE_UP = [-Math.PI / 2, 0, 0], FACE_DOWN = [Math.PI / 2, 0, 0], SIDE = [0, 0, Math.PI / 2];
function orient(o, yaw) {
    return quatMul(quatFromEuler(0, yaw, 0), quatFromEuler(...o));
}

function poseAt(surface, x, z, q) {
    return seatPose({ x, z, q, surfaceY: SURFACES[surface].y }, DECK_BOX);
}

/** The 24 kinds, in order: [kind, label, mover, target(state, r)]. */
function program() {
    const real = (name) => () => ({ ...REAL_POSES[name], o: STAND });
    return [
        ["real", "KEY borrowed: shelf slot → table centre", "deck", real("tableCentre")],
        ["real", "MSG borrowed: chest → its rest pose", "deck2", real("restLeft")],
        ["random", "KEY → random", "deck", "random"],
        ["edge", "MSG: shortest hop (5 cm, quarter turn)", "deck2", (s) => ({ surface: s.deck2.surface, x: s.deck2.x + 0.05, z: s.deck2.z + 0.012, yaw: s.deck2.yaw + Math.PI / 2, o: s.deck2.o })],
        ["random", "KEY → random", "deck", "random"],
        ["edge", "MSG: flips face down", "deck2", (s, r) => ({ ...feltSpot(s, "deck2", r), o: FACE_DOWN })],
        ["edge", "KEY: half turn (180°) 15 cm along", "deck", (s) => ({ surface: s.deck.surface, x: s.deck.x - 0.15 * Math.sign(s.deck.x - DEN.x || 1), z: s.deck.z, yaw: s.deck.yaw + Math.PI, o: s.deck.o })],
        ["random", "MSG → random", "deck2", "random"],
        ["edge", "KEY: across the felt to its far edge", "deck", (s) => farFelt(s.deck)],
        ["edge", "MSG: up onto the shelf", "deck2", () => ({ surface: "shelf", x: -0.3, z: -2.16, yaw: 0.05, o: STAND })],
        ["edge", "KEY: onto the shelf right beside MSG (12 mm gap)", "deck", (s) => ({ surface: "shelf", x: s.deck2.x - 0.067 - 0.012, z: s.deck2.z, yaw: s.deck2.yaw, o: STAND })],
        ["random", "KEY → random", "deck", "random"],
        ["edge", "MSG: shelf → chest (the longest flight)", "deck2", () => ({ surface: "chest", x: CHEST.inner.max[0] - 0.08, z: CHEST.inner.max[2] - 0.08, yaw: 0.6, o: STAND })],
        ["edge", "KEY: onto its long side", "deck", (s, r) => ({ ...feltSpot(s, "deck", r), o: SIDE })],
        ["random", "KEY → random", "deck", "random"],
        ["edge", "KEY: back upright at the table centre, 45°", "deck", () => ({ ...REAL_POSES.tableCentre, yaw: Math.PI / 4, o: STAND })],
        ["real", "KEY sleeve set aside: table centre → right rest", "deck", (s) => ({ ...REAL_POSES.tableCentre, o: STAND, _via: true })],
        ["random", "MSG → random", "deck2", "random"],
        ["edge", "MSG: beside KEY at the right rest (12 mm gap)", "deck2", (s) => ({ surface: "felt", x: s.deck.x, z: s.deck.z + 0.02 + 0.092 / 2 + 0.012 + 0.046, yaw: s.deck.yaw, o: STAND })],
        ["random", "KEY → random", "deck", "random"],
        ["random", "MSG → random", "deck2", "random"],
        ["edge", "KEY: into the chest corner", "deck", () => ({ surface: "chest", x: CHEST.inner.min[0] + 0.07, z: CHEST.inner.min[2] + 0.07, yaw: -0.4, o: STAND })],
        ["real", "MSG home: back into the chest", "deck2", real("chestSeat")],
        ["real", "KEY home: chest → its shelf slot", "deck", real("shelfSlot")],
    ];
}

function feltSpot(s, who, r) {
    const other = s[who === "deck" ? "deck2" : "deck"];
    for (let k = 0; k < 200; k++) {
        const a = r() * Math.PI * 2, d = Math.sqrt(r()) * 0.75;
        const x = DEN.x + Math.cos(a) * d, z = DEN.z + Math.sin(a) * d;
        if (Math.hypot(x - other.x, z - other.z) > 0.2 && Math.hypot(x - s[who].x, z - s[who].z) > 0.15) return { surface: "felt", x, z, yaw: r() * Math.PI * 2 };
    }
    return { surface: "felt", x: DEN.x, z: DEN.z, yaw: 0 };
}

function farFelt(me) {
    const a = Math.atan2(me.z - DEN.z, me.x - DEN.x) + Math.PI;
    const d = 0.86;
    return { surface: "felt", x: DEN.x + Math.cos(a) * d, z: DEN.z + Math.sin(a) * d, yaw: a + Math.PI / 2, o: STAND };
}

function randomTarget(s, who, r) {
    const roll = r();
    const surface = roll < 0.68 ? "felt" : roll < 0.9 ? "shelf" : "chest";
    const oRoll = r();
    const o = surface === "shelf" ? (oRoll < 0.8 ? STAND : FACE_UP) : oRoll < 0.55 ? STAND : oRoll < 0.72 ? FACE_UP : oRoll < 0.88 ? FACE_DOWN : SIDE;
    const yaw = r() * Math.PI * 2;
    let x, z;
    if (surface === "felt") {
        const a = r() * Math.PI * 2, d = Math.sqrt(r()) * 0.84;
        x = DEN.x + Math.cos(a) * d; z = DEN.z + Math.sin(a) * d;
    } else if (surface === "shelf") {
        x = -2.1 + r() * 2.3; z = -2.2 + r() * 0.13;
    } else {
        x = CHEST.inner.min[0] + 0.07 + r() * (CHEST.inner.max[0] - CHEST.inner.min[0] - 0.14);
        z = CHEST.inner.min[2] + 0.07 + r() * (CHEST.inner.max[2] - CHEST.inner.min[2] - 0.14);
    }
    return { surface, x, z, yaw, o };
}

/** The solid each surface is the top of (a seated box touches it). */
const SUPPORT = { felt: "table", shelf: "shelf-top", chest: "chest-floor" };

/** The other toy as a solid. */
function toySolid(pose, name) {
    return { ...obbOf(pose, DECK_BOX), kind: "box", name };
}

/** A target is valid if the box sits inside its surface and clear of every solid by 10 mm (lid open if it is the chest). */
function valid(t, pose, otherPose) {
    // Every corner of its footprint on the surface.
    if (!obbCorners(obbOf(pose, DECK_BOX)).every((c) => SURFACES[t.surface].inside(c[0], c[2], 0))) return false;
    const solids = [...roomSolids({ lidAngle: t.surface === "chest" ? CHEST.lidOpenAngle : 0 }), toySolid(otherPose, "other toy")];
    const o = obbOf(pose, DECK_BOX);
    if (worstDepth(o, solids, 0).depth > 0.0005) return false;
    const support = SUPPORT[t.surface];
    return worstDepth(o, solids.filter((s) => s.name !== support), 0.01).depth <= 0;
}

/** The seeded loop. Cycles that touch the chest open its lid (the hinge) around the carry. */
export function carrySchedule(seed = DEFAULT_SEED, { plan = true } = {}) {
    const r = rng(seed * 7919 + 17);
    const start = {
        deck: { ...REAL_POSES.shelfSlot, o: STAND },
        deck2: { ...REAL_POSES.chestSeat, o: STAND },
    };
    const state = { deck: { ...start.deck }, deck2: { ...start.deck2 } };
    const poseOf = (t) => poseAt(t.surface, t.x, t.z, orient(t.o, t.yaw));
    const cycles = [];
    program().forEach(([kind, label, mover, target], i) => {
        const other = mover === "deck" ? "deck2" : "deck";
        const otherPose = poseOf(state[other]);
        let t = null;
        if (target === "random") {
            for (let k = 0; k < 400 && !t; k++) {
                const c = randomTarget(state, mover, r);
                if (Math.hypot(c.x - state[mover].x, c.z - state[mover].z) < 0.12) continue;
                if (valid(c, poseOf(c), otherPose)) t = c;
            }
            if (!t) throw new Error(`cycle ${i + 1}: no random target`);
        } else {
            t = target(state, r);
            if (t._via) t = { ...REAL_POSES.restRight, o: STAND };
            if (!valid(t, poseOf(t), otherPose)) throw new Error(`cycle ${i + 1} (${label}): target not clear`);
        }
        const from = poseOf(state[mover]), to = poseOf(t);
        const chest = state[mover].surface === "chest" || t.surface === "chest";
        const solids = [...roomSolids({ lidAngle: chest ? CHEST.lidOpenAngle : 0 }), toySolid(otherPose, other === "deck" ? "KEY" : "MSG")];
        const c = { n: i + 1, kind, label, mover, other, from, to, surfaceFrom: SURFACES[state[mover].surface].y, surfaceTo: SURFACES[t.surface].y, chest, solids, target: t };
        if (plan) {
            c.plan = planCarry({ from, to, shape: DECK_BOX, solids });
            c.check = checkPlan(c.plan, { shape: DECK_BOX, solids, surfaceFrom: c.surfaceFrom, surfaceTo: c.surfaceTo });
        }
        cycles.push(c);
        state[mover] = t;
    });
    return { seed, start, cycles, end: state, poseOf };
}

export { STAND, FACE_UP, FACE_DOWN, SIDE, orient, poseAt };
