/**
 * MegaDreifach hashing off the main thread. Imports the same
 * sudoc-generated module as everything else (no hand-written hash), so
 * typing never stalls the room: a 4 KiB message is 147 blocks, about
 * 0.7 s of Hash. `show` runs the generated trace_hash (one pass, as long
 * as Hash: 88 steps a block) and turns block 1 into the show's move lists
 * (plan.js); later blocks only lend their final h and h⁻¹ for the
 * fast-forward. The reply also carries the generated +1 turn of each
 * face, which pattern.js uses to put those final positions on cubing.js.
 */
import { Hash, pad_message, trace_hash } from "./generated/megadreifach.mjs";
import * as raw from "./generated/_megadreifach_impl.mjs";
import { BLOCK_BYTES, buildShow } from "./plan.js";

let faceTurns = null;

/** Generated face_turn(identity, f, +1) for each face, as plain numbers. */
export function generatedFaceTurns() {
    if (faceTurns) return faceTurns;
    const plain = (p) => ({
        cp: [...p.cp].map(Number), co: [...p.co].map(Number),
        ep: [...p.ep].map(Number), eo: [...p.eo].map(Number),
    });
    faceTurns = [];
    for (let f = 0; f < 12; f++) faceTurns.push(plain(raw.face_turn(raw.identity(), BigInt(f), 1n)));
    return faceTurns;
}

export function answer({ op, bytes }) {
    const blocks = pad_message(bytes).length / BLOCK_BYTES;
    if (op === "digest") return { digest: Hash(bytes), blocks };
    if (op === "show") {
        const trace = trace_hash(bytes);
        const show = buildShow(trace);
        if (show.final) show.faceTurns = generatedFaceTurns();
        return { digest: trace.digest, blocks, show };
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
