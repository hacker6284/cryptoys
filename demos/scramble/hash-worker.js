/**
 * Incremental Scramble hash. Main thread streams file chunks; this
 * worker walks the cube without teach steps so a JPEG / PNG can finish
 * and post `done` (host/impl `update` stalls on `push_step`).
 *
 * Prefer the silent impl walk. Fall back to the host Message API.
 */
import { createSilentHasher, createIncrementalHasher } from "../shared/file-hash.js";

async function makeHasher() {
    try {
        const impl = await import("./generated/_scramble_impl.mjs");
        const rt = await import("./generated/_sudo_rt.mjs");
        return createSilentHasher({ impl, rt });
    } catch {
        const api = await import("./generated/scramble.mjs");
        return createIncrementalHasher(api);
    }
}

const hasherPromise = makeHasher();

function reply(data) {
    self.postMessage(data);
}

self.onmessage = async (event) => {
    const msg = event.data || {};
    try {
        const hasher = await hasherPromise;
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
