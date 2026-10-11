/**
 * Private helper for a rigid object lifted out of where it sits and set
 * down somewhere else (a box's lid, a unit out of its box, the cup out of
 * its box, a die out of the cup): straight up until its drawn bottom is
 * `clearY` up and every solid under the way across is `clearM` below it,
 * straight across at that height (turning on the way: slerp), straight
 * down onto `to`. Each leg eases in and out (easeInOutSine), so it stops
 * at each corner like a hand lifting, carrying and setting down. It holds
 * no constants and is not an entry: each object passes its own law.
 *
 *   const plan = planHop({ from, to, parts, clearY, solids, law, tempo })
 *   plan.at(ms) → { p, q }    (0 … plan.ms; holds the ends outside)
 *   checkHop(plan, { solids }) → { ok, fail, worst }
 *
 * from / to: world poses { p: [x, y, z], q: [x, y, z, w] }. parts: the
 * object's drawn local bounds as one or more boxes [{ min, max }] (a lid
 * is its top and four walls, so it can sit over a box). solids: oriented
 * boxes (geom.js obbOf, with a name) or vertical rings ({ kind: "cyl" })
 * it must not pass through. law: { clearM, baseMs, perSqrtM, minMs, maxMs }:
 * a leg of d metres takes baseMs + perSqrtM × √d ms (clamped), ÷ tempo.
 */
import { clamp01, easeInOutSine, lerp3, obbMinY, obbOf, quatAngle, slerp, worstDepth } from "./geom.js";

const TOL = 0.0005; // touching is not overlapping (a box set down on the felt, a unit on the box floor)

/** A leg's duration on the law. */
export function legMs(d, law, tempo = 1) {
    const ms = law.baseMs + law.perSqrtM * Math.sqrt(Math.max(0, d));
    return Math.min(law.maxMs ?? Infinity, Math.max(law.minMs ?? 0, ms)) / (tempo || 1);
}

/** The parts' oriented boxes at a pose. */
export function partsAt(pose, parts) {
    return parts.map((s) => obbOf(pose, s));
}

function lowest(pose, parts) {
    return Math.min(...partsAt(pose, parts).map(obbMinY));
}

export function planHop({ from, to, parts, clearY = -Infinity, solids = [], law, tempo = 1 }) {
    const N = 24;
    // The height the object's origin crosses at: its bottom clearY up (at
    // every turn of the slerp), never below either end.
    let topY = Math.max(from.p[1], to.p[1]);
    for (let i = 0; i <= N; i++) {
        const q = slerp(from.q, to.q, i / N);
        const drop = lowest({ p: [0, 0, 0], q }, parts);
        topY = Math.max(topY, clearY - drop);
    }
    // Raised until the way across clears every solid by clearM.
    const across = (y, u) => ({ p: lerp3([from.p[0], y, from.p[2]], [to.p[0], y, to.p[2]], u), q: slerp(from.q, to.q, u) });
    const clearAt = (y) => {
        let worst = -Infinity;
        for (let i = 0; i <= N; i++) for (const o of partsAt(across(y, i / N), parts)) worst = Math.max(worst, worstDepth(o, solids, law.clearM).depth);
        return worst <= 0;
    };
    for (let k = 0; k < 100 && solids.length && !clearAt(topY); k++) topY += 0.005;
    const A = from.p, B = [from.p[0], topY, from.p[2]], C = [to.p[0], topY, to.p[2]], D = to.p;
    const dist = (a, b) => Math.hypot(b[0] - a[0], b[1] - a[1], b[2] - a[2]);
    const legs = [
        { a: A, b: B, ms: legMs(dist(A, B), law, tempo), turn: false },
        { a: B, b: C, ms: legMs(dist(B, C), law, tempo), turn: true },
        { a: C, b: D, ms: legMs(dist(C, D), law, tempo), turn: false },
    ];
    let t0 = 0;
    for (const leg of legs) {
        leg.t0 = t0;
        t0 += leg.ms;
    }
    const ms = t0;
    const plan = {
        from, to, parts, topY, legs, ms, law, tempo,
        at(t) {
            t = Math.min(ms, Math.max(0, t));
            let i = 0;
            while (i < 2 && t > legs[i].t0 + legs[i].ms) i++;
            const leg = legs[i];
            const u = easeInOutSine(clamp01(leg.ms ? (t - leg.t0) / leg.ms : 1));
            const q = i === 0 ? from.q : i === 2 ? to.q : slerp(from.q, to.q, u);
            return { p: lerp3(leg.a, leg.b, u), q };
        },
    };
    return plan;
}

/**
 * The checks a hop must pass: it starts and ends exactly on its poses,
 * nothing jumps (no step between samples faster than the legs allow), its
 * duration is on the law, and its parts overlap no solid (TOL: touching).
 */
export function checkHop(plan, { solids = [], samples = 360 } = {}) {
    const fail = [];
    const near = (a, b) => Math.hypot(a[0] - b[0], a[1] - b[1], a[2] - b[2]) < 1e-9;
    const s = plan.at(0), e = plan.at(plan.ms);
    if (!near(s.p, plan.from.p) || quatAngle(s.q, plan.from.q) > 1e-6) fail.push("does not start on its pose");
    if (!near(e.p, plan.to.p) || quatAngle(e.q, plan.to.q) > 1e-6) fail.push("does not end on its pose");
    const law = plan.legs.reduce((sum, leg) => sum + legMs(Math.hypot(...leg.b.map((v, k) => v - leg.a[k])), plan.law, plan.tempo), 0);
    if (Math.abs(law - plan.ms) > 1e-6) fail.push("duration off the law");
    let worst = -Infinity, where = "", prev = s, jump = 0;
    for (let i = 0; i <= samples; i++) {
        const t = (i / samples) * plan.ms;
        const pose = plan.at(t);
        for (const o of partsAt(pose, plan.parts)) {
            const w = worstDepth(o, solids, 0);
            if (w.depth > worst) { worst = w.depth; where = `${w.solid?.name ?? "a solid"} at ${t.toFixed(0)} ms`; }
        }
        jump = Math.max(jump, Math.hypot(...pose.p.map((v, k) => v - prev.p[k])));
        prev = pose;
    }
    if (worst > TOL) fail.push(`overlap ${(worst * 1000).toFixed(1)} mm (${where})`);
    // easeInOutSine is fastest half way, π/2 × its mean speed: no sample may step further.
    const step = plan.ms / samples;
    const most = Math.max(...plan.legs.map((leg) => (leg.ms ? (Math.hypot(...leg.b.map((v, k) => v - leg.a[k])) * Math.PI / 2 * step) / leg.ms : 0)));
    if (jump > most * 1.05 + 1e-9) fail.push(`jumps ${(jump * 1000).toFixed(1)} mm between samples`);
    return { ok: fail.length === 0, fail, worst };
}
