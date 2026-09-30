/**
 * Scramble file hash off the main thread, on the fast JS cube
 * (`fast-hash.js`), so it does not import the generated `.mjs`.
 *
 * `start` answers `ready`. `hash` walks the whole file, posting
 * `progress` per chunk and then `done` with the digest.
 */
import { DEMO_FILE_CHUNK_BYTES } from "../shared/file-hash.js";
import { createFastHasher } from "./fast-hash.js";

function reply(data) {
    self.postMessage(data);
}

async function hashBytes(version, bytes) {
    const hasher = createFastHasher();
    hasher.start(version);
    const total = bytes.length;
    reply({ type: "progress", processed: 0, total });
    for (let i = 0; i < total; i += DEMO_FILE_CHUNK_BYTES) {
        const end = Math.min(i + DEMO_FILE_CHUNK_BYTES, total);
        hasher.push(bytes.subarray(i, end));
        reply({ type: "progress", processed: end, total });
        await new Promise((resolve) => setTimeout(resolve, 0));
    }
    reply({ type: "done", digest: hasher.finish().digest });
}

self.onmessage = (event) => {
    const msg = event.data || {};
    if (msg.type === "start") {
        reply({ type: "ready" });
        return;
    }
    if (msg.type === "hash") {
        const raw = msg.bytes;
        const bytes = raw instanceof Uint8Array ? raw : new Uint8Array(raw || []);
        hashBytes(msg.version, bytes).catch((err) => {
            reply({ type: "error", message: err?.message || "Could not hash this file." });
        });
    }
};
