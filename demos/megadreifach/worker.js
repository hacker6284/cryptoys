/**
 * MegaDreifach hashing off the main thread. Imports the same
 * sudoc-generated module as everything else (no hand-written hash), so
 * typing never stalls the room: a 4 KiB message is 147 blocks, about
 * 1.1 s of Hash. `show` also runs the generated trace_hash and turns it
 * into the show's move lists (plan.js) when the message is short enough
 * to animate.
 */
import { Hash, pad_message, trace_hash } from "./generated/megadreifach.mjs";
import { BLOCK_BYTES, MAX_ANIM_BLOCKS, buildShow } from "./plan.js";

export function answer({ op, bytes }) {
    const blocks = pad_message(bytes).length / BLOCK_BYTES;
    if (op === "digest") return { digest: Hash(bytes), blocks };
    if (op === "show") {
        if (blocks > MAX_ANIM_BLOCKS) return { digest: Hash(bytes), blocks, show: null };
        const trace = trace_hash(bytes);
        return { digest: trace.digest, blocks, show: buildShow(trace) };
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
