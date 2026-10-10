/**
 * BS off the main thread. Everything here calls the sudoc-generated module
 * built from primitives/key_exchange/bs/bs.sudo (no hand-written step):
 *
 * - `show`: the dice for a seed (trace.js diceFromSeed), or a known-answer
 *   vector's dice, through the generated trace_exchange (BUILD both key
 *   grids, both public walks, the calls, the checks and both shared walks),
 *   ordered into one beat per summary by trace.js buildShow. T1 only: its
 *   workspace fits one lid grid (SPEC §6).
 * - `check`: a known-answer vector of any tier through the generated host
 *   API (build_key_grid on each player's dice, then exchange): A, B and K
 *   to compare with the file, no show.
 */
import * as host from "./generated/bs.mjs";
import * as raw from "./generated/_bs_impl.mjs";
import * as rt from "./generated/_sudo_rt.mjs";
import { buildShow, diceFromSeed, regString, runTrace } from "./trace.js";

export const SHOW_TIER = "T1";

/** True when the generated module has the demo's trace. */
export function hasTrace() {
    return typeof raw.trace_exchange === "function";
}

function showFor(tier, a, b, meta) {
    const { field, trace } = runTrace(raw, rt, tier, a, b);
    const show = buildShow({ field, trace }, meta);
    if (!show.ok) throw new Error(show.error || "The exchange failed.");
    return {
        ...show,
        A: regString(show.publicA),
        B: regString(show.publicB),
        K: regString(show.secretA),
        Kb: regString(show.secretB),
    };
}

function checkVector(v) {
    const built = (d) => host.build_key_grid({ ...d, next12: 0, next6: 0, next10: 0 }).grid;
    const ex = host.exchange(host.tier(v.tier), [built(v.dice_a)], [built(v.dice_b)]);
    return { A: regString(ex.public_a), B: regString(ex.public_b), K: regString(ex.secret_a), Kb: regString(ex.secret_b) };
}

/** One request: { op: "show", seed } | { op: "show", vector } | { op: "check", vector }. */
export function answer({ op, seed, vector }) {
    if (op === "show") {
        if (!hasTrace()) return { show: null, reason: "no-trace" };
        if (vector) return { show: showFor(vector.tier, vector.dice_a, vector.dice_b, { tier: vector.tier, kat: vector.name }) };
        const dice = diceFromSeed(String(seed ?? ""));
        return { show: showFor(SHOW_TIER, dice.a, dice.b, { tier: SHOW_TIER, seed: String(seed ?? "") }) };
    }
    if (op === "check") return checkVector(vector);
    throw new Error(`unknown op ${op}`);
}

if (typeof self !== "undefined" && typeof self.postMessage === "function" && typeof window === "undefined") {
    self.onmessage = ({ data }) => {
        try {
            self.postMessage({ id: data.id, ...answer(data) });
        } catch (err) {
            self.postMessage({ id: data.id, error: err?.message || String(err) });
        }
    };
}
