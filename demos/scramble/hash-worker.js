/**
 * Incremental Scramble hash. Main thread streams file chunks; this
 * worker updates the cube and drops the teach list so a multi-MB file
 * cannot freeze the dock or build a leave list.
 *
 * Prefer the generated impl (no host conversion of Step records).
 * Fall back to the same host API typed Message uses.
 */
import { createGeneratedHasher, createIncrementalHasher } from "../shared/file-hash.js";

async function makeHasher() {
    try {
        const impl = await import("./generated/_scramble_impl.mjs");
        const rt = await import("./generated/_sudo_rt.mjs");
        return createGeneratedHasher({ impl, rt });
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
