/**
 * Incremental Scramble hash. Main thread streams file chunks; this
 * worker updates the generated impl cube and drops the teach list so a
 * multi-MB file cannot freeze the dock or build a leave list.
 *
 * Uses `_scramble_impl.mjs` (not the host wrapper) so each chunk does
 * not convert thousands of Step records to plain objects.
 */
import * as impl from "./generated/_scramble_impl.mjs";
import * as rt from "./generated/_sudo_rt.mjs";
import { createGeneratedHasher } from "../shared/file-hash.js";

const hasher = createGeneratedHasher({ impl, rt });

function reply(data) {
    self.postMessage(data);
}

self.onmessage = (event) => {
    const msg = event.data || {};
    try {
        if (msg.type === "start") {
            hasher.start(msg.version);
            reply({ type: "ready" });
            return;
        }
        if (msg.type === "chunk") {
            hasher.push(msg.bytes);
            reply({ type: "progress" });
            return;
        }
        if (msg.type === "finish") {
            const { digest } = hasher.finish();
            reply({ type: "done", digest });
        }
    } catch (err) {
        reply({ type: "error", message: err?.message || "Could not hash this file." });
    }
};
