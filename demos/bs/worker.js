/**
 * BS off the main thread. Everything here calls the sudoc-generated module
 * built from primitives/key_exchange/bs/bs.sudo (no hand-written step):
 *
 * - `show`: the dice for a seed (trace.js diceFromSeed), or a known-answer
 *   vector's dice, through the generated trace_exchange (BUILD both key
 *   grids with every hole's moves, both public walks, the calls, the checks
 *   and both shared walks), ordered into one beat per summary by trace.js
 *   buildShow. T1 only: its workspace fits one lid grid (SPEC §6).
 * - `moves`: one exchange step's peg moves, from the generated step_moves on
 *   the last show's trace (the player's registers before the step, then the
 *   step). One step at a time: T1's exchange is about 951k peg moves.
 * - `check`: a known-answer vector of any tier through the generated host
 *   API (build_key_grid on each player's dice, then exchange): A, B and K
 *   to compare with the file, no show.
 */
import * as host from "./generated/bs.mjs";
import * as raw from "./generated/_bs_impl.mjs";
import * as rt from "./generated/_sudo_rt.mjs";
import { plain } from "../shared/sudo-plain.js";
import { buildShow, diceFromSeed, regString, runTrace } from "./trace.js";

export const SHOW_TIER = "T1";

// The last show's generated field and steps, for `moves`.
let last = null;

function showFor(tier, a, b, meta) {
    const { field, trace, generated } = runTrace(raw, rt, tier, a, b);
    const show = buildShow({ field, trace }, meta);
    if (!show.ok) throw new Error(show.error || "The exchange failed.");
    last = { field: generated.field, steps: Array.from(generated.trace.steps) };
    return {
        ...show,
        A: regString(show.publicA),
        B: regString(show.publicB),
        K: regString(show.secretA),
        Kb: regString(show.secretB),
    };
}

/** Step `i`'s peg moves: generated step_moves on the player's X, Y and C after their previous step. */
function movesFor(i) {
    if (!last || !(i >= 0 && i < last.steps.length)) throw new Error(`no step ${i}`);
    const st = last.steps[i];
    let prev = null;
    for (let j = i - 1; j >= 0 && !prev; j--) if (last.steps[j].player === st.player) prev = last.steps[j];
    const empty = raw.empty_register(last.field);
    const [x, y, c] = prev ? [prev.x, prev.y, prev.c] : [empty, empty, empty];
    return plain(raw.step_moves(last.field, x, y, c, st));
}

function checkVector(v) {
    const built = (d) => host.build_key_grid({ ...d, next12: 0, next6: 0, next10: 0 }).grid;
    const ex = host.exchange(host.tier(v.tier), [built(v.dice_a)], [built(v.dice_b)]);
    return { A: regString(ex.public_a), B: regString(ex.public_b), K: regString(ex.secret_a), Kb: regString(ex.secret_b) };
}

/** One request: { op: "show", seed } | { op: "show", vector } | { op: "moves", step } | { op: "check", vector }. */
export function answer({ op, seed, vector, step }) {
    if (op === "show") {
        if (vector) return { show: showFor(vector.tier, vector.dice_a, vector.dice_b, { tier: vector.tier, kat: vector.name }) };
        const dice = diceFromSeed(String(seed ?? ""));
        return { show: showFor(SHOW_TIER, dice.a, dice.b, { tier: SHOW_TIER, seed: String(seed ?? "") }) };
    }
    if (op === "moves") return { step, moves: movesFor(step) };
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
