/**
 * BS: the show from the generated trace. Everything about the exchange
 * comes from the sudoc-generated module of primitives/key_exchange/bs/
 * bs.sudo: the keys from BUILD (trace_build inside trace_exchange), every
 * multiplication, start, tidy, clear and shot from trace_exchange, and the
 * outputs A, B and K. This file only turns its records into plain numbers
 * and orders them into beats (one beat per summary), and turns a seed into
 * the dice faces BUILD reads (the seed is the input, like a cup of dice).
 */
import { OP } from "./expand.js";

/** A generated value as plain numbers, arrays and objects (records by their sudo field list, enum cases by name). */
export function plain(v) {
    if (typeof v === "bigint") return Number(v);
    const kind = v?.constructor?._sudoKind;
    if (kind && kind[0] === "e" && !v.constructor._sudoFields.length) return kind[1].split(".").pop();
    if (v && v.constructor && Array.isArray(v.constructor._sudoFields)) {
        const out = {};
        for (const f of v.constructor._sudoFields) out[f] = plain(v[f]);
        return out;
    }
    if (v && typeof v !== "string" && typeof v[Symbol.iterator] === "function") return Array.from(v, plain);
    return v;
}

/** '.WR' string of a register (hole 0 first), the vectors' notation. */
export function regString(r) {
    return r.map((t) => ".WR"[t]).join("");
}

export function regOf(s) {
    return Array.from(s, (ch) => ".WR".indexOf(ch));
}

// ---- seed → dice --------------------------------------------------------

// cyrb128 string hash and sfc32: a small seeded generator for the dice faces.
function cyrb128(str) {
    let h1 = 1779033703, h2 = 3144134277, h3 = 1013904242, h4 = 2773480762;
    for (let i = 0; i < str.length; i++) {
        const k = str.charCodeAt(i);
        h1 = h2 ^ Math.imul(h1 ^ k, 597399067);
        h2 = h3 ^ Math.imul(h2 ^ k, 2869860233);
        h3 = h4 ^ Math.imul(h3 ^ k, 951274213);
        h4 = h1 ^ Math.imul(h4 ^ k, 2716044179);
    }
    h1 = Math.imul(h3 ^ (h1 >>> 18), 597399067);
    h2 = Math.imul(h4 ^ (h2 >>> 22), 2869860233);
    h3 = Math.imul(h1 ^ (h3 >>> 17), 951274213);
    h4 = Math.imul(h2 ^ (h4 >>> 19), 2716044179);
    return [(h1 ^ h2 ^ h3 ^ h4) >>> 0, (h2 ^ h1) >>> 0, (h3 ^ h1) >>> 0, (h4 ^ h1) >>> 0];
}

function sfc32([a, b, c, d]) {
    return () => {
        a >>>= 0; b >>>= 0; c >>>= 0; d >>>= 0;
        const t = (a + b | 0) + d | 0;
        d = d + 1 | 0;
        a = b ^ (b >>> 9);
        b = c + (c << 3) | 0;
        c = (c << 21) | (c >>> 11);
        c = c + t | 0;
        return (t >>> 0) / 4294967296;
    };
}

// More faces than a build can read: d12 at most 100, d6 at most 4 per ship
// (50 ships at most), d10 50 dice plus their zero faces.
export const STREAM = { d12: 120, d6: 240, d10: 300 };

/** Each player's dice faces for a seed: { a: { d12, d6, d10 }, b: … } (d10 0-9, 0 the zero face). */
export function diceFromSeed(seed) {
    const out = {};
    for (const who of ["a", "b"]) {
        const rnd = sfc32(cyrb128(`bs:${seed}:${who}`));
        const roll = (sides, from) => Math.floor(rnd() * sides) + from;
        out[who] = {
            d12: Array.from({ length: STREAM.d12 }, () => roll(12, 1)),
            d6: Array.from({ length: STREAM.d6 }, () => roll(6, 1)),
            d10: Array.from({ length: STREAM.d10 }, () => roll(10, 0)),
        };
    }
    return out;
}

/** A fresh seed for "Roll keys" (8 hex digits). */
export function randomSeed() {
    const b = new Uint32Array(1);
    globalThis.crypto.getRandomValues(b);
    return b[0].toString(16).padStart(8, "0");
}

// ---- trace → show -----------------------------------------------------------

/**
 * Run the generated trace_exchange on two players' dice. raw/rt: the
 * generated _bs_impl.mjs and _sudo_rt.mjs; tierName "T1" | "T2" | "T6".
 */
export function runTrace(raw, rt, tierName, diceA, diceB) {
    const list = (xs) => rt.host_list(xs, (v) => rt.host_int(v));
    const dz = (d) => raw.dice(list(d.d12), list(d.d6), list(d.d10));
    const field = raw[tierName.toLowerCase()];
    if (!field) throw new Error(`unknown tier ${tierName}`);
    const generated = raw.trace_exchange(field, dz(diceA), dz(diceB));
    const trace = plain(generated);
    trace.error = rt.text_str(generated.error);
    return { field: plain(field), trace };
}

/**
 * The show: one beat per summary. BUILD gives a beat per key-grid hole
 * (Alice's 100, then Bob's); the exchange a beat per trace step. Each
 * exchange beat carries the key cell it walks (`cellValue`, `keyHole`) and
 * whether it is in the shared walk.
 */
export function buildShow({ field, trace }, meta = {}) {
    const beats = [];
    const reads = [trace.reads_a, trace.reads_b];
    const cells = [trace.cells_a, trace.cells_b];
    const holes = [trace.holes_a, trace.holes_b];
    for (const p of [0, 1]) {
        reads[p].forEach((read, i) => beats.push({ kind: "build", player: p, read: i, stage: `build-${p}` }));
    }
    const starts = [0, 0];
    trace.steps.forEach((st, i) => {
        if (st.op === OP.start) starts[st.player] += 1;
        const shared = starts[st.player] > 1;
        const cell = st.cell >= 0 ? cells[st.player][st.cell] : -1;
        const keyHole = st.cell >= 0 ? holes[st.player][st.cell] : null;
        let stage;
        if (st.op === OP.clear || st.op === OP.shot) stage = `call-${st.player}`;
        else if (st.op === OP.check || st.op === OP.checkTidy) stage = `check-${st.player}`;
        else stage = `${shared ? "shared" : "public"}-${st.player}`;
        beats.push({ kind: "step", step: i, player: st.player, op: st.op, shared, cellValue: cell, keyHole, stage });
    });
    return {
        ...meta,
        n: field.n,
        toll: field.toll,
        grids: [trace.grid_a, trace.grid_b],
        reads,
        cells,
        holes,
        steps: trace.steps,
        beats,
        ok: trace.ok,
        error: trace.error,
        publicA: trace.public_a,
        publicB: trace.public_b,
        secretA: trace.secret_a,
        secretB: trace.secret_b,
    };
}
