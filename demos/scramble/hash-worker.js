/**
 * Incremental Scramble hash. Main thread streams file chunks; this
 * worker `update`s the cube and drops the teach trace so a multi-MB
 * file cannot freeze the dock or build a leave list.
 */
import { scramble_v1, scramble_v2, update, evaluate } from "./generated/scramble.mjs";
import { createIncrementalHasher } from "../shared/file-hash.js";

const hasher = createIncrementalHasher({ scramble_v1, scramble_v2, update, evaluate });

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
