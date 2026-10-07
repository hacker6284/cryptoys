/**
 * P1 carry: a rigid toy from pose A to pose B, clearing whatever is
 * under and around the path. Placement (from, to, the solids) is always
 * an input; the laws in ./settings.js are what Zachary approves.
 *
 *   const plan = planCarry({ from, to, shape, solids })
 *   plan.at(ms) → { p, q }   (0 … plan.ms; holds the ends outside)
 *
 * from / to: { p: [x, y, z], q: [x, y, z, w] } (seated poses: see
 * seatPose). shape: the toy's drawn local bounds { min, max }. solids:
 * anim/shared/room.js roomSolids() plus the other toys' boxes.
 *
 * Audited by demos/micro/deck/carry/ (a seeded loop of placements:
 * ./placements.js), pinned by ../../library.test.mjs.
 */
import settings from "./settings.js";
import { seatPose, DECK_BOX } from "../../shared/poses.js";
import { rafRun, worldPose } from "../../shared/run.js";
import {
    add, clamp01, lerp3, obbOf, quatAngle, quatDot, slerp, smootherStep, smootherStepD, worstDepth,
} from "../../shared/geom.js";

export { settings };
export const timing = settings.timing;
export const slots = [];

/** Peak speed of smootherstep relative to the mean (at exactly half way). */
export const PEAK_RATIO = 1.875;
export const PEAK_AT = 0.5;

const N = 160; // path samples for length, pace and clearance

/** Duration law (ms at tempo 1 → ÷ tempo). */
export function carryMs(pathM, t = timing) {
    const ms = t.baseMs + t.perSqrtM * Math.sqrt(Math.max(0, pathM));
    return Math.min(t.maxMs, Math.max(t.minMs, ms)) / (t.tempo || 1);
}

/** Arc top law: metres above the higher end before clearance raises it. */
export function riseFor(horizM, t = timing) {
    return Math.min(t.riseMaxM, t.riseM + t.risePerM * horizM);
}

// A seated pose (from ../poses.js, re-exported for callers of carry).
export { seatPose };

function bez(P, u) {
    const s = 1 - u;
    const a = s * s * s, b = 3 * s * s * u, c = 3 * s * u * u, d = u * u * u;
    return [0, 1, 2].map((k) => a * P[0][k] + b * P[1][k] + c * P[2][k] + d * P[3][k]);
}

/**
 * The path: straight up `lift0` off the start seat, a cubic Bézier with
 * vertical end handles (a up from the lifted start, b up from the
 * lifted end), straight down `lift1` onto the end seat. Returned as a
 * dense polyline with its cumulative length (arc-length lookup).
 */
function buildPath(from, to, { lift0, lift1, a, b }) {
    const L0 = add(from.p, [0, lift0, 0]), L1 = add(to.p, [0, lift1, 0]);
    const P = [L0, add(L0, [0, a, 0]), add(L1, [0, b, 0]), L1];
    const pts = [];
    const nUp = 12;
    for (let i = 0; i < nUp; i++) pts.push(lerp3(from.p, L0, i / nUp));
    for (let i = 0; i <= N; i++) pts.push(bez(P, i / N));
    for (let i = 1; i <= nUp; i++) pts.push(lerp3(L1, to.p, i / nUp));
    const cum = [0];
    for (let i = 1; i < pts.length; i++) cum.push(cum[i - 1] + Math.hypot(pts[i][0] - pts[i - 1][0], pts[i][1] - pts[i - 1][1], pts[i][2] - pts[i - 1][2]));
    return { P, pts, cum, L: cum[cum.length - 1], lift0, lift1, a, b };
}

/** Point at arc-length fraction f of the path. */
function pointAt(path, f) {
    const target = clamp01(f) * path.L;
    const { cum, pts } = path;
    let lo = 0, hi = cum.length - 1;
    while (hi - lo > 1) {
        const mid = (lo + hi) >> 1;
        if (cum[mid] < target) lo = mid; else hi = mid;
    }
    const span = cum[hi] - cum[lo];
    return span > 0 ? lerp3(pts[lo], pts[hi], (target - cum[lo]) / span) : pts[lo].slice();
}

function turnAt(f, t) {
    return smootherStep((f - t.turnFrom) / (t.turnTo - t.turnFrom));
}

/** Pose at arc-length fraction f (0 … 1). */
function poseAtFraction(path, from, to, f, t) {
    return { p: pointAt(path, f), q: slerp(from.q, to.q, turnAt(f, t)) };
}

// The clearance margin ramps in with horizontal distance from either
// end: straight up off a seat and straight down onto one, the toy only
// has to miss its neighbours (it may be set 1 cm from another box); once
// it travels it keeps clearM from everything.
function margin(p, from, to, t) {
    const dFrom = Math.hypot(p[0] - from.p[0], p[2] - from.p[2]);
    const dTo = Math.hypot(p[0] - to.p[0], p[2] - to.p[2]);
    return Math.max(0, Math.min(t.clearM, dFrom, dTo));
}

/**
 * Clearance along the path: the worst depth of the toy's drawn box in
 * any solid (with the ramped margin), sampled over arc length.
 */
export function pathClearance(path, from, to, shape, solids, t = timing, samples = 120) {
    let worst = { depth: -Infinity, f: 0, solid: null, raw: -Infinity };
    for (let i = 0; i <= samples; i++) {
        const f = i / samples;
        const pose = poseAtFraction(path, from, to, f, t);
        const o = obbOf(pose, shape);
        const m = margin(pose.p, from, to, t);
        const w = worstDepth(o, solids, m);
        const raw = m > 0 ? worstDepth(o, solids, 0).depth : w.depth;
        if (w.depth > worst.depth) worst = { depth: w.depth, f, solid: w.solid?.name, raw: Math.max(worst.raw, raw) };
        else worst.raw = Math.max(worst.raw, raw);
    }
    return worst;
}

const TOL = 0.0005; // 0.5 mm: touching a seat is not overlapping

/**
 * Plan a carry. The Bézier's handles are scaled so its top is the law's
 * (riseFor the horizontal distance above the higher end); then, while
 * the toy's box would come within the margin of a solid, the planner
 * lifts it further straight up off the start (a conflict in the first
 * half) or straight down onto the end (second half), and raises the arc
 * by the same amount. Throws if no clear path is found.
 */
export function planCarry({ from, to, shape, solids = [], t = timing, debug = null }) {
    const horiz = Math.hypot(to.p[0] - from.p[0], to.p[2] - from.p[2]);
    const shaped = (lift0, lift1, extra) => {
        const y0 = from.p[1] + lift0, y1 = to.p[1] + lift1;
        const top = Math.max(Math.max(from.p[1], to.p[1]) + riseFor(horiz, t), Math.max(y0, y1) + t.riseM) + extra;
        const da = top - y0, db = top - y1;
        const peakOf = (k) => {
            const path = buildPath(from, to, { lift0, lift1, a: k * da, b: k * db });
            return Math.max(...path.P.length ? [0, 1, 2, 3, 4, 5, 6, 7, 8].map((i) => bez(path.P, i / 8)[1]) : [0]);
        };
        let lo = 0, hi = 8;
        for (let k = 0; k < 40; k++) {
            const m = (lo + hi) / 2;
            if (peakOf(m) < top) lo = m; else hi = m;
        }
        return buildPath(from, to, { lift0, lift1, a: hi * da, b: hi * db });
    };
    let lift0 = 0, lift1 = 0, extra = 0;
    let path = shaped(lift0, lift1, extra);
    let clear = pathClearance(path, from, to, shape, solids, t);
    let raises = 0;
    while (clear.depth > TOL && raises < 120) {
        debug?.({ raises, lift0, lift1, extra, ...clear });
        const step = Math.max(0.01, Math.min(0.08, clear.depth + 0.004));
        if (clear.f < 0.35) lift0 += step;
        else if (clear.f > 0.65) lift1 += step;
        else extra += step;
        path = shaped(lift0, lift1, extra);
        clear = pathClearance(path, from, to, shape, solids, t);
        raises += 1;
    }
    if (clear.depth > TOL) throw new Error(`carry: no clear path (${clear.solid} at ${clear.f.toFixed(2)}, ${(clear.depth * 1000).toFixed(1)} mm)`);
    const ms = carryMs(path.L, t);
    return {
        from, to, path, L: path.L, horiz, top: Math.max(...path.pts.map((p) => p[1])), raises, clearance: clear,
        lift0, lift1,
        ms,
        peakMs: PEAK_AT * ms,
        peakSpeed: (PEAK_RATIO * path.L) / (ms / 1000),
        turn: quatAngle(from.q, to.q),
        /** Pose at `ms` after the start (holds the ends outside 0 … ms). */
        at(msNow) {
            return poseAtFraction(path, from, to, smootherStep(msNow / ms), t);
        },
        /** Speed (m/s) at `ms` after the start, from the law. */
        speedAt(msNow) {
            return (path.L * smootherStepD(msNow / ms)) / (ms / 1000);
        },
        fraction: (f) => poseAtFraction(path, from, to, f, t),
    };
}

/** The checks a carry must pass (run on the plan; the page also runs them on what it drew). */
export function checkPlan(plan, { shape, solids, surfaceTo, surfaceFrom, t = timing, samples = 400 }) {
    const fail = [];
    // No overlap anywhere along the path, sampled densely in time.
    let worst = -Infinity, where = null;
    for (let i = 0; i <= samples; i++) {
        const pose = plan.at((i / samples) * plan.ms);
        const w = worstDepth(obbOf(pose, shape), solids, 0);
        if (w.depth > worst) { worst = w.depth; where = `${w.solid?.name} at ${((i / samples) * plan.ms).toFixed(0)} ms`; }
    }
    if (worst > TOL) fail.push(`overlap ${(worst * 1000).toFixed(1)} mm (${where})`);
    // Seated by drawn geometry at both ends.
    for (const [pose, y, name] of [[plan.to, surfaceTo, "end"], [plan.from, surfaceFrom, "start"]]) {
        if (y == null) continue;
        const bottom = obbOf(pose, shape);
        const minY = bottom.c[1] - (Math.abs(bottom.axes[0][1]) * bottom.he[0] + Math.abs(bottom.axes[1][1]) * bottom.he[1] + Math.abs(bottom.axes[2][1]) * bottom.he[2]);
        if (Math.abs(minY - (y + 0.001)) > TOL) fail.push(`${name} not seated: bottom ${(minY - y).toFixed(4)} m above its surface`);
    }
    // The ends are exact.
    const end = plan.at(plan.ms), start = plan.at(0);
    if (Math.hypot(...end.p.map((v, k) => v - plan.to.p[k])) > 1e-6 || quatAngle(end.q, plan.to.q) > 1e-4) fail.push("does not end on its target pose");
    if (Math.hypot(...start.p.map((v, k) => v - plan.from.p[k])) > 1e-6 || quatAngle(start.q, plan.from.q) > 1e-4) fail.push("does not start from its pose");
    // Duration law and peak speed half way.
    if (Math.abs(plan.ms - carryMs(plan.L, t)) > 1e-6) fail.push("duration off the law");
    let peak = 0, peakAt = 0;
    const dt = plan.ms / samples;
    let prev = plan.at(0).p;
    for (let i = 1; i <= samples; i++) {
        const p = plan.at(i * dt).p;
        const v = Math.hypot(p[0] - prev[0], p[1] - prev[1], p[2] - prev[2]) / (dt / 1000);
        if (v > peak) { peak = v; peakAt = (i - 0.5) * dt; }
        prev = p;
    }
    if (Math.abs(peakAt / plan.ms - PEAK_AT) > 0.02) fail.push(`peak speed at ${(peakAt / plan.ms).toFixed(3)} of the move, not half way`);
    if (Math.abs(peak / plan.peakSpeed - 1) > 0.03) fail.push(`peak speed ${peak.toFixed(2)} m/s, law ${plan.peakSpeed.toFixed(2)}`);
    // Rotation: unit quaternions, the shorter arc, monotone.
    let last = 0;
    for (let i = 0; i <= 40; i++) {
        const q = plan.at((i / 40) * plan.ms).q;
        if (Math.abs(Math.hypot(...q) - 1) > 1e-6) fail.push("rotation not a unit quaternion");
        const done = quatAngle(plan.from.q, q);
        if (done + 1e-6 < last) { fail.push("rotation not monotone (slerp)"); break; }
        last = done;
    }
    return { ok: fail.length === 0, fail, worstDepth: worst, peakSpeed: peak, peakAt };
}

export { quatDot, lerp3 };

/**
 * Carry `toy` (a three.js object whose parent is the world) from where it
 * is to the seated pose `to` ({ p, q }). shape: its drawn local bounds
 * (default the deck box); solids: what is around the path. `run(ms, step)`
 * plays it on another clock (default: real time). Resolves with the plan
 * (null if stopped).
 */
export async function carry(toy, to, { shape = DECK_BOX, solids = [], run = rafRun, t = timing } = {}) {
    const plan = planCarry({ from: worldPose(toy), to, shape, solids, t });
    const ok = await run(plan.ms, (ms) => {
        const at = plan.at(ms);
        toy.position.set(at.p[0], at.p[1], at.p[2]);
        toy.quaternion.set(at.q[0], at.q[1], at.q[2], at.q[3]);
    });
    return ok === false ? null : plan;
}
