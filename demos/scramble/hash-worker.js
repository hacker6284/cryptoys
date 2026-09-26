/**
 * Incremental Scramble hash. Fast JS cube (no generated CowList), so a
 * JPEG can finish and post `done` on GitHub Pages without importing
 * `.mjs` from the worker.
 */
import { createFastHasher } from "../shared/file-hash.js";

const hasher = createFastHasher();

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
