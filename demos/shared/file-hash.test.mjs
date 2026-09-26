import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { existsSync } from "node:fs";
import {
    DEMO_FILE_CHUNK_BYTES,
    DEMO_FILE_MAX_BYTES,
    DEMO_FILE_TEACH_MAX_BYTES,
    canWalkFile,
    checkFileSize,
    createGeneratedHasher,
    createIncrementalHasher,
    dropTeachTrace,
    formatFileLabel,
    formatFileSize,
    hashFile,
    readFileChunks,
} from "./file-hash.js";
import { DEMO_INPUT_MAX_CHARS } from "./input-cap.js";

assert.equal(DEMO_FILE_MAX_BYTES, 10 * 1024 * 1024, "first file ceiling is 10 MB");
assert.equal(DEMO_FILE_TEACH_MAX_BYTES, DEMO_INPUT_MAX_CHARS, "Play/teach cap matches typed Message");
assert.ok(DEMO_FILE_CHUNK_BYTES >= 4 * 1024);

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

const state = { steps: [{ kind: "move" }, { kind: "move" }] };
dropTeachTrace(state);
assert.deepEqual(state.steps, []);

function stubApi() {
    return {
        scramble_v1() { return { v: 1, bytes: [], steps: [] }; },
        scramble_v2() { return { v: 2, bytes: [], steps: [] }; },
        update(s, bytes) {
            s.bytes.push(...bytes);
            for (const b of bytes) s.steps.push({ b });
        },
        evaluate(s) {
            return { digest: [0, s.v, s.bytes.length], trace: s.steps.slice() };
        },
    };
}

const hasher = createIncrementalHasher(stubApi());
hasher.start(2);
hasher.push(new Uint8Array([1, 2, 3]));
hasher.push(new Uint8Array([4, 5]));
const got = hasher.finish();
assert.deepEqual(got.digest, [0, 2, 5], "chunked update matches one-shot length");

const file = new File([new Uint8Array([9, 8, 7, 6])], "nibble.bin");
const seen = [];
await readFileChunks(file, {
    chunkBytes: 2,
    onChunk(bytes, progress) {
        seen.push({ n: bytes.length, processed: progress.processed, total: progress.total });
    },
});
assert.deepEqual(seen, [
    { n: 2, processed: 2, total: 4 },
    { n: 2, processed: 4, total: 4 },
]);

const progress = [];
const hashed = await hashFile(file, {
    version: 2,
    hashInline: async ({ file: next, onProgress }) => {
        const bytes = new Uint8Array(await next.arrayBuffer());
        onProgress?.({ processed: bytes.length, total: bytes.length });
        const inc = createIncrementalHasher(stubApi());
        inc.start(2);
        inc.push(bytes);
        return inc.finish();
    },
    onProgress(info) { progress.push(info); },
});
assert.deepEqual(hashed.digest, [0, 2, 4]);
assert.equal(progress.length, 1);

function mockWorker() {
    const inc = createIncrementalHasher(stubApi());
    const listeners = { message: [], error: [] };
    return {
        addEventListener(type, fn) { (listeners[type] ||= []).push(fn); },
        removeEventListener(type, fn) {
            listeners[type] = (listeners[type] || []).filter((item) => item !== fn);
        },
        terminate() {},
        postMessage(data) {
            queueMicrotask(() => {
                let reply;
                if (data.type === "start") {
                    inc.start(data.version);
                    reply = { type: "ready" };
                } else if (data.type === "chunk") {
                    inc.push(data.bytes);
                    reply = { type: "progress" };
                } else if (data.type === "finish") {
                    reply = { type: "done", digest: inc.finish().digest };
                }
                for (const fn of listeners.message) fn({ data: reply });
            });
        },
    };
}

const workerProgress = [];
const viaWorker = await hashFile(file, {
    version: 2,
    workerUrl: "mock:hash-worker",
    chunkBytes: 2,
    createWorker: () => mockWorker(),
    onProgress(info) { workerProgress.push(info.processed); },
});
assert.deepEqual(viaWorker.digest, [0, 2, 4], "worker protocol returns the incremental digest");
assert.deepEqual(workerProgress, [2, 4], "main thread only hears progress, never setAlg");

const implUrl = new URL("../scramble/generated/_scramble_impl.mjs", import.meta.url);
if (existsSync(implUrl)) {
    const impl = await import(implUrl);
    const rt = await import(new URL("../scramble/generated/_sudo_rt.mjs", import.meta.url));
    const hello = [104, 101, 108, 108, 111];
    const gen = createGeneratedHasher({ impl, rt });
    gen.start(2);
    gen.push(hello.slice(0, 2));
    gen.push(hello.slice(2));
    assert.deepEqual(
        gen.finish().digest,
        [0, 82, 163, 199, 209, 34, 145, 209, 64],
        "generated impl hasher matches SPEC hello v2",
    );
}

const src = readFileSync(new URL("./file-hash.js", import.meta.url), "utf8");
assert.match(src, /createIncrementalHasher/);
assert.match(src, /createGeneratedHasher/);
assert.match(src, /dropTeachTrace/);
assert.match(src, /new Worker/);

const worker = readFileSync(new URL("../scramble/hash-worker.js", import.meta.url), "utf8");
assert.match(worker, /createGeneratedHasher/, "worker hashes on the generated impl");
assert.match(worker, /_scramble_impl\.mjs/);
assert.doesNotMatch(worker, /setAlg/);
assert.doesNotMatch(worker, /mapTraceToAlg/);

const scramble = readFileSync(new URL("../scramble/session.js", import.meta.url), "utf8");
assert.match(scramble, /hashFile\(/);
assert.match(scramble, /function applyFile\(/);
assert.match(scramble, /function hashSelectedFile\(\)/);
const hashFn = scramble.match(/async function hashSelectedFile\(\) \{[\s\S]*?\n    \}/);
assert.ok(hashFn, "hashSelectedFile is the file Digest path");
assert.doesNotMatch(hashFn[0], /view\.setAlg/, "file hash must not call setAlg while hashing");
assert.doesNotMatch(hashFn[0], /bindAlg\(/);
assert.doesNotMatch(hashFn[0], /mapTraceToAlg/);
assert.match(scramble, /function play\(\) \{[\s\S]*?ensureTimeline\(\)/);
assert.match(scramble, /canWalkPayload/);

const adapters = readFileSync(new URL("../playroom/adapters.js", import.meta.url), "utf8");
assert.match(adapters, /id="message-file-btn"/);
assert.match(adapters, /id="message-file"/);
const doubleDealDock = adapters.slice(adapters.indexOf("function mountDoubleDealDock"));
assert.doesNotMatch(doubleDealDock, /message-file/, "DoubleDeal Message is not a hash file input");

console.log("file-hash tests ok");
