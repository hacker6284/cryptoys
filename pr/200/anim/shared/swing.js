/**
 * Private helper for the objects' hinged parts (deck/box's flap, chest's
 * lid): the swing curves, the duration law and the stop-short scan. It
 * holds no constants and is not an entry: each object calls it with its
 * own part spec { openRad, stopGapM, open, close } and tempo.
 *
 *   const plan = planSwing({ part, from: 0, to: 1, sweep, solids, tempo })
 *   plan.at(ms) → angle (rad, 0 shut, + open)
 *
 * from / to: fractions of the part's open angle (0 shut, 1 open).
 * sweep(angle) → the part's oriented box at that angle (world). solids:
 * what it must not swing into.
 */
import { clamp01, depthIn, easeInOutCubic, easeInOutSine, worstDepth } from "./geom.js";

const TOL = 0.0005;

/** Progress g(u) of a curve (0 at the start, 1 at the end angle; may pass 1 by the overshoot). */
export function curveAt(spec, u) {
    u = clamp01(u);
    const settle = spec.settle || 0;
    const pA = 1 - settle;
    if (spec.curve === "fall") {
        if (u <= pA) return (u / pA) ** 2;
        return 1 - (spec.bounce || 0) * Math.sin(Math.PI * ((u - pA) / settle));
    }
    const o = spec.overshoot || 0;
    if (u <= pA) return (1 + o) * easeInOutCubic(u / pA);
    return 1 + o - o * easeInOutSine((u - pA) / settle);
}

/** Where (fraction of ms) a curve turns fastest. */
export function curvePeakAt(spec) {
    const pA = 1 - (spec.settle || 0);
    return spec.curve === "fall" ? pA : pA / 2;
}

/** Duration law: ms × √(fraction of the sweep), ÷ tempo. */
export function swingMs(spec, fraction, tempo = 1) {
    return (spec.ms * Math.sqrt(Math.min(1, Math.abs(fraction)))) / (tempo || 1);
}

/**
 * Plan a swing from `from` to `to` (fractions of openRad). If a solid is
 * in the way, the swing stops stopGapM short of it (no overshoot).
 */
export function planSwing({ part, from = 0, to = 1, sweep, solids = [], tempo = 1 }) {
    const p = part;
    const opening = to > from;
    let spec = opening ? p.open : p.close;
    const a0 = from * p.openRad;
    let a1 = to * p.openRad;
    let stopped = null;
    if (sweep && opening) {
        // Scan the sweep including the overshoot. A solid stops it when the
        // part comes within the part's stopGapM of it, closer than it is
        // when shut (a shut lid rests on its chest, a shut flap on its box).
        const gap = p.stopGapM;
        const over = a1 + (a1 - a0) * (spec.overshoot || 0);
        const shut = sweep(0);
        const base = solids.map((sol) => Math.max(0, depthIn(shut, sol, gap)));
        const blocked = (a) => {
            const o = sweep(a);
            for (let k = 0; k < solids.length; k++) if (depthIn(o, solids[k], gap) > base[k] + 1e-4) return solids[k].name || "a solid";
            return null;
        };
        const steps = 120;
        let last = a0;
        for (let i = 1; i <= steps && !stopped; i++) {
            const a = a0 + ((over - a0) * i) / steps;
            stopped = blocked(a);
            if (!stopped) last = a;
        }
        if (stopped) {
            let lo = last, hi = Math.min(over, last + (over - a0) / steps);
            for (let k = 0; k < 24; k++) {
                const m = (lo + hi) / 2;
                if (blocked(m)) hi = m; else lo = m;
            }
            // It stops there, without the overshoot; if only the overshoot
            // would have touched, it still reaches its end, just without it.
            spec = { ...spec, overshoot: 0, settle: 0 };
            if (lo < a1) a1 = lo;
            else stopped = null;
        }
    }
    const fraction = (a1 - a0) / p.openRad;
    const ms = swingMs(opening ? p.open : p.close, fraction, tempo);
    const peakAt = curvePeakAt(spec);
    const plan = {
        part, from: a0, to: a1, spec, ms, stopped, fraction,
        peakMs: peakAt * ms,
        at(msNow) {
            return a0 + (a1 - a0) * curveAt(spec, msNow / ms);
        },
        /** Angular speed (rad/s) at `ms`, numerically from the curve. */
        rateAt(msNow) {
            const h = 0.25;
            return Math.abs(plan.at(msNow + h) - plan.at(msNow - h)) / (2 * h / 1000);
        },
    };
    return plan;
}

/** The checks a swing must pass (on the plan; the page also checks what it drew). */
export function checkSwing(plan, { sweep, solids = [], tempo = 1, samples = 240 }) {
    const fail = [];
    if (sweep) {
        let worst = -Infinity, where = "";
        for (let i = 0; i <= samples; i++) {
            const ms = (i / samples) * plan.ms;
            const w = worstDepth(sweep(plan.at(ms)), solids, 0);
            if (w.depth > worst) { worst = w.depth; where = `${w.solid?.name} at ${ms.toFixed(0)} ms`; }
        }
        if (worst > TOL) fail.push(`overlap ${(worst * 1000).toFixed(1)} mm (${where})`);
    }
    if (Math.abs(plan.at(0) - plan.from) > 1e-9 || Math.abs(plan.at(plan.ms) - plan.to) > 1e-9) fail.push("does not start and end on its angles");
    const p = plan.part;
    const law = swingMs(plan.to > plan.from ? p.open : p.close, (plan.to - plan.from) / p.openRad, tempo);
    if (Math.abs(plan.ms - law) > 1e-6) fail.push("duration off the law");
    let peak = 0, peakAt = 0;
    for (let i = 1; i < samples; i++) {
        const ms = (i / samples) * plan.ms;
        const r = plan.rateAt(ms);
        if (r > peak + 1e-9) { peak = r; peakAt = ms; }
    }
    if (Math.abs(peakAt - plan.peakMs) / plan.ms > 0.02) fail.push(`fastest at ${(peakAt / plan.ms).toFixed(3)} of the swing, law ${(plan.peakMs / plan.ms).toFixed(3)}`);
    return { ok: fail.length === 0, fail, peakRate: peak, peakAt };
}
