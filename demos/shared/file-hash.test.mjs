import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import {
    DEMO_FILE_MAX_BYTES,
    DEMO_FILE_TEACH_MAX_BYTES,
    canWalkFile,
    checkFileSize,
    formatFileLabel,
    formatFileSize,
    hashFile,
    readFileChunks,
} from "./file-hash.js";
import { DEMO_INPUT_MAX_CHARS } from "./input-cap.js";

assert.equal(DEMO_FILE_MAX_BYTES, 10 * 1024 * 1024, "first file ceiling is 10 MB");
assert.equal(DEMO_FILE_TEACH_MAX_BYTES, DEMO_INPUT_MAX_CHARS, "Play/teach cap matches typed Message");

assert.equal(formatFileSize(0), "0 B");
assert.equal(formatFileSize(512), "512 B");
assert.equal(formatFileSize(2048), "2.0 KB");
assert.equal(formatFileSize(12 * 1024), "12 KB");
assert.equal(formatFileSize(DEMO_FILE_MAX_BYTES), "10 MB");
assert.equal(formatFileLabel({ name: "notes.txt", size: 2048 }), "notes.txt · 2.0 KB");

assert.deepEqual(checkFileSize({ size: 100 }), { ok: true, size: 100 });
const over = checkFileSize({ name: "big.bin", size: DEMO_FILE_MAX_BYTES + 1 });
assert.equal(over.ok, false);
assert.match(over.message, /10 MB/);
assert.equal(canWalkFile({ size: DEMO_FILE_TEACH_MAX_BYTES }), true);
assert.equal(canWalkFile({ size: DEMO_FILE_TEACH_MAX_BYTES + 1 }), false);

const file = new File([new Uint8Array([9, 8, 7, 6])], "nibble.bin");
const seen = [];
await readFileChunks(file, {
    chunkBytes: 3,
    onChunk(bytes, progress) {
        seen.push({ bytes: Array.from(bytes), processed: progress.processed, total: progress.total });
    },
});
assert.deepEqual(seen, [
    { bytes: [9, 8, 7], processed: 3, total: 4 },
    { bytes: [6], processed: 4, total: 4 },
]);

await assert.rejects(hashFile({ name: "huge.bin", size: DEMO_FILE_MAX_BYTES + 1 }), /10 MB/, "oversized file is rejected");

// A fake module Worker speaking the hash-worker.js protocol.
function installWorker(respond) {
    const made = [];
    globalThis.Worker = function Worker(url, opts) {
        const listeners = { message: [], error: [] };
        const worker = {
            url,
            opts,
            terminated: false,
            sent: [],
            addEventListener(type, fn) { listeners[type].push(fn); },
            removeEventListener(type, fn) { listeners[type] = listeners[type].filter((item) => item !== fn); },
            terminate() { this.terminated = true; },
            postMessage(data) {
                worker.sent.push(data);
                queueMicrotask(() => {
                    for (const reply of respond(data)) {
                        for (const fn of listeners.message) fn({ data: reply });
                    }
                });
            },
        };
        made.push(worker);
        return worker;
    };
    return made;
}

const fallbackDigest = async () => ({ digest: [7, 7] });

{
    const made = installWorker((data) => {
        if (data.type === "start") return [{ type: "ready" }];
        if (data.type === "hash") {
            return [
                { type: "progress", processed: data.bytes.length, total: data.bytes.length },
                { type: "done", digest: [data.version, ...data.bytes] },
            ];
        }
        return [];
    });
    const progress = [];
    const got = await hashFile(file, {
        version: 1,
        workerUrl: "mock:hash-worker",
        fallback: fallbackDigest,
        onProgress(info) { progress.push(info.processed); },
    });
    assert.deepEqual(got.digest, [1, 9, 8, 7, 6], "worker gets the file's raw bytes and version; done is the digest");
    assert.deepEqual(progress, [4], "worker progress reaches onProgress");
    assert.equal(made[0].opts.type, "module", "worker is a module worker");
    assert.equal(made[0].terminated, true, "worker is terminated after done");
}

{
    installWorker((data) => (data.type === "start" ? [{ type: "ready" }] : [{ type: "error", message: "boom" }]));
    const got = await hashFile(file, { workerUrl: "mock:hash-worker", fallback: fallbackDigest });
    assert.deepEqual(got.digest, [7, 7], "worker error falls back to the host hash");
}

{
    installWorker(() => []);
    const started = Date.now();
    const got = await hashFile(file, { workerUrl: "mock:hash-worker", readyMs: 40, fallback: fallbackDigest });
    assert.deepEqual(got.digest, [7, 7], "no worker ready → host fallback still writes Digest");
    assert.ok(Date.now() - started < 400, "ready timeout does not sit on a multi-second stall");
}

{
    installWorker((data) => (data.type === "start" ? [{ type: "ready" }] : []));
    const abort = new AbortController();
    const pending = hashFile(file, { workerUrl: "mock:hash-worker", signal: abort.signal, readyMs: 0, fallback: fallbackDigest });
    setTimeout(() => abort.abort(), 20);
    await assert.rejects(pending, { name: "AbortError" }, "abort does not fall back");
}

delete globalThis.Worker;
assert.deepEqual(
    (await hashFile(file, { workerUrl: "mock:hash-worker", fallback: fallbackDigest })).digest,
    [7, 7],
    "no Worker → host fallback",
);

// Markup: paperclip on the Message line, name/progress on the next row,
// in the Scramble dock and the standalone page. DoubleDeal has none.
const adapters = readFileSync(new URL("../playroom/adapters.js", import.meta.url), "utf8");
const scrambleStart = adapters.indexOf('createDock("scramble"');
const doubledealStart = adapters.indexOf('createDock("doubledeal"');
assert.ok(scrambleStart >= 0 && doubledealStart > scrambleStart, "both docks come from createDock");
const scrambleDock = adapters.slice(scrambleStart, doubledealStart);
const doubleDealDock = adapters.slice(doubledealStart);
const standalone = readFileSync(new URL("../scramble/index.html", import.meta.url), "utf8");
for (const [name, html] of [["dock", scrambleDock], ["standalone", standalone]]) {
    const row = html.match(/<div class="playroom-message-row">[\s\S]*?<\/div>/);
    assert.ok(row, `${name}: Message line is its own row`);
    assert.match(row[0], /id="message"[\s\S]*id="message-file-btn"/, `${name}: paperclip ends the Message line`);
    assert.doesNotMatch(row[0], /id="message-file"/, `${name}: filename chip is not beside the paperclip`);
    assert.match(html, /playroom-message-row[\s\S]*message-file-stack[\s\S]*id="message-file"[\s\S]*id="message-file-progress"/, `${name}: name and progress sit under Message`);
    assert.match(html, /id="message-file-input" type="file"/, `${name}: has the file input`);
}
assert.doesNotMatch(doubleDealDock, /message-file/, "DoubleDeal Message is not a hash file input");

console.log("file-hash tests ok");
