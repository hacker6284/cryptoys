/**
 * MegaDreifach v3 hashing off the main thread. Everything here calls the
 * sudoc-generated module built from primitives/hash/megadreifach/v3/
 * megadreifach.sudo (no hand-written hash, no copy of any step):
 *
 * - `digest`: the generated Hash, so typing never stalls the room.
 * - `show`: the generated trace_hash (one pass, as long as Hash), turned
 *   into the show's move lists by plan.js when present. Otherwise
 *   { show: null, reason: "no-trace" } (this build has no trace) or
 *   { show: null, reason: "too-long" } (message longer than TRACE_BLOCKS
 *   blocks; too long to animate turn for turn). The digest and the KAT
 *   check still run on the generated Hash either way.
 *
 * The marks the view draws (where the card's edge and corner are when the
 * step names them, where the held edge and corner are when an echo looks)
 * are read off the generated position with the generated edge_face_of /
 * corner_face_of after replaying the trace's own turns with the generated
 * face_turn. They place highlights only; no turn comes from them.
 */
import { Hash, pad_message } from "./generated/megadreifach.mjs";
import * as raw from "./generated/_megadreifach_impl.mjs";
import * as rt from "./generated/_sudo_rt.mjs";
import { BLOCK_BYTES, TRACE_BLOCKS, buildShow } from "./plan.js";

let faceTurns = null;
let oneBlock = null;

/** True when the generated module exports trace_hash. */
export function hasTrace() {
    return typeof raw.trace_hash === "function";
}

/** The longest message that pads to one block, asked of the generated pad_message. */
export function oneBlockBytes() {
    if (oneBlock !== null) return oneBlock;
    let n = 0;
    while (pad_message(new Array(n + 1).fill(0)).length === BLOCK_BYTES) n += 1;
    oneBlock = n;
    return n;
}

/** A generated value as plain numbers, arrays and objects (records by their sudo field list). */
export function plain(v) {
    if (typeof v === "bigint") return Number(v);
    if (v && v.constructor && Array.isArray(v.constructor._sudoFields)) {
        const out = {};
        for (const f of v.constructor._sudoFields) out[f] = plain(v[f]);
        return out;
    }
    if (v && typeof v !== "string" && typeof v[Symbol.iterator] === "function") return Array.from(v, plain);
    return v;
}

const big = (n) => BigInt(n);
const toPos = (p) => rt.rec(new raw.Position(...["cp", "co", "ep", "eo"].map((k) => rt.lst(p[k].map(big)))));

/** Generated face_turn(identity, f, +1) for each face, as plain numbers (for checks). */
export function generatedFaceTurns() {
    if (faceTurns) return faceTurns;
    faceTurns = [];
    for (let f = 0; f < 12; f++) faceTurns.push(plain(raw.face_turn(raw.identity(), big(f), 1n)));
    return faceTurns;
}

function turnOn(g, face, clicks) {
    return raw.face_turn(g, big(face), big(((clicks % 5) + 5) % 5));
}

function edgeFaces(g, a, b) {
    return [plain(raw.edge_face_of(g, big(a), big(b), big(a))), plain(raw.edge_face_of(g, big(a), big(b), big(b)))];
}

function cornerFaces(g, a, b, c) {
    return [a, b, c].map((x) => plain(raw.corner_face_of(g, big(a), big(b), big(c), big(x))));
}

/**
 * Where the named pieces are, for the view's marks: per step, the faces
 * of the slot holding the card's edge and corner right after the step's
 * first turn (when step 2 names them), and for an echo the slots of the
 * held edge and corner before it (the look). Replays only the trace's turns.
 */
function marksFor(trace) {
    const out = [];
    for (const blk of trace.blocks) {
        let g = toPos(blk.h);
        const held = blk.deal[51];
        const marks = [];
        for (const st of blk.steps) {
            const mark = {};
            if (st.pos > 52) {
                // The held card's colour and suit neighbours, from the generated helpers.
                const hc = plain(raw.card_colour(big(held)));
                const [hn, hn2] = plain(raw.suit_nbrs(big(hc), big((held % 4) + 1)));
                mark.lookEdge = edgeFaces(g, hc, hn);
                mark.lookCorner = cornerFaces(g, hc, hn, hn2);
            }
            g = turnOn(g, st.turns[0], st.turns[1]);
            mark.edge = edgeFaces(g, st.colour, st.n);
            mark.corner = cornerFaces(g, st.colour, st.n, st.n2);
            for (let i = 2; i < st.turns.length; i += 2) g = turnOn(g, st.turns[i], st.turns[i + 1]);
            marks.push(mark);
        }
        out.push(marks);
    }
    return out;
}

export function answer({ op, bytes }) {
    const blocks = pad_message(bytes).length / BLOCK_BYTES;
    const base = { blocks, oneBlock: oneBlockBytes(), traceBlocks: TRACE_BLOCKS, traced: hasTrace() };
    if (op === "digest") return { ...base, digest: Hash(bytes) };
    if (op === "show") {
        if (!hasTrace()) return { ...base, digest: Hash(bytes), show: null, reason: "no-trace" };
        if (blocks > TRACE_BLOCKS) return { ...base, digest: Hash(bytes), show: null, reason: "too-long" };
        const msg = rt.host_list(bytes, (v) => rt.host_int(v));
        const generated = raw.trace_hash(msg);
        const trace = plain(generated);
        const show = buildShow(trace, marksFor(trace));
        show.faceTurns = generatedFaceTurns();
        return { ...base, digest: trace.digest, show };
    }
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
