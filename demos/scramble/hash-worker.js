/**
 * Incremental Scramble hash. Fast JS cube (no generated CowList), so a
 * JPEG can finish and post `done` on GitHub Pages without importing
 * `.mjs` from the worker.
 *
 * Product path posts one `hash` with the whole file. The worker walks
 * internally and posts `progress` + `done`, so Digest cannot stall on
 * a dropped per-chunk reply.
 */
import { createFastHasher } from "../shared/file-hash.js";

const hasher = createFastHasher();
const STEP = 32 * 1024;

function reply(data) {
    self.postMessage(data);
}

async function hashBytes(bytes) {
    const total = bytes.length;
    if (!total) {
        reply({ type: "progress", processed: 0, total: 0 });
    }
    for (let i = 0; i < total; i += STEP) {
        const end = Math.min(i + STEP, total);
        hasher.push(bytes.subarray(i, end));
        reply({ type: "progress", processed: end, total });
        await new Promise((resolve) => setTimeout(resolve, 0));
    }
    const { digest } = hasher.finish();
    reply({ type: "done", digest });
}

self.onmessage = (event) => {
    const msg = event.data || {};
    try {
        if (msg.type === "start") {
            hasher.start(msg.version);
            reply({ type: "ready" });
            return;
        }
        if (msg.type === "hash") {
            hasher.start(msg.version);
            const raw = msg.bytes;
            const bytes = raw instanceof Uint8Array ? raw : new Uint8Array(raw || []);
            void hashBytes(bytes).catch((err) => {
                reply({ type: "error", message: err?.message || "Could not hash this file." });
            });
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
