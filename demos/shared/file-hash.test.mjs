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
    createSilentHasher,
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

const viaFallback = await hashFile(file, {
    version: 2,
    workerUrl: "",
    fallback: async () => ({ digest: [9, 9] }),
});
assert.deepEqual(viaFallback.digest, [9, 9], "hashFile falls back when a worker cannot start");

const implUrl = new URL("../scramble/generated/_scramble_impl.mjs", import.meta.url);
if (existsSync(implUrl)) {
    const impl = await import(implUrl);
    const rt = await import(new URL("../scramble/generated/_sudo_rt.mjs", import.meta.url));
    const host = await import(new URL("../scramble/generated/scramble.mjs", import.meta.url));
    const hello = [104, 101, 108, 108, 111];
    const helloV2 = [0, 82, 163, 199, 209, 34, 145, 209, 64];
    const gen = createGeneratedHasher({ impl, rt });
    gen.start(2);
    gen.push(hello.slice(0, 2));
    gen.push(hello.slice(2));
    assert.deepEqual(gen.finish().digest, helloV2, "generated impl hasher matches SPEC hello v2");

    const silent = createSilentHasher({ impl, rt });
    silent.start(2);
    silent.push(new Uint8Array(hello.slice(0, 2)));
    silent.push(new ArrayBuffer(0));
    silent.push(new Uint8Array(hello.slice(2)));
    assert.deepEqual(silent.finish().digest, helloV2, "silent hasher matches SPEC hello v2");

    const pngish = new Uint8Array([0x89, 0x50, 0x4e, 0x47, 0x0d, 0x0a, 0x1a, 0x0a, 0xff, 0x00, 0x7f, 0x80]);
    const state = host.scramble_v2();
    host.update(state, Array.from(pngish));
    const expected = host.evaluate(state).digest;
    const fromBuf = createSilentHasher({ impl, rt });
    fromBuf.start(2);
    fromBuf.push(pngish.buffer);
    assert.deepEqual(fromBuf.finish().digest, expected, "silent hasher treats ArrayBuffer as raw bytes, not text");

    const imageSized = new Uint8Array(8 * 1024);
    imageSized[0] = 0xff;
    imageSized[1] = 0xd8;
    imageSized[2] = 0xff;
    const t0 = Date.now();
    const jpeg = createSilentHasher({ impl, rt });
    jpeg.start(2);
    jpeg.push(imageSized.subarray(0, 4096));
    jpeg.push(imageSized.subarray(4096));
    const jpegDigest = jpeg.finish().digest;
    assert.equal(jpegDigest.length, 9, "image-sized file still produces a 9-byte digest");
    assert.ok(Date.now() - t0 < 8000, "silent 8 KiB JPEG-shaped hash finishes without push_step stall");
}

const src = readFileSync(new URL("./file-hash.js", import.meta.url), "utf8");
assert.match(src, /createIncrementalHasher/);
assert.match(src, /createGeneratedHasher/);
assert.match(src, /createSilentHasher/);
assert.match(src, /dropTeachTrace/);
assert.match(src, /new Worker/);

const worker = readFileSync(new URL("../scramble/hash-worker.js", import.meta.url), "utf8");
assert.match(worker, /createSilentHasher/, "worker prefers the silent digest walk");
assert.match(worker, /createIncrementalHasher/, "worker falls back to the host Message API");
assert.match(worker, /_scramble_impl\.mjs/);
assert.doesNotMatch(worker, /setAlg/);
assert.doesNotMatch(worker, /mapTraceToAlg/);

const scramble = readFileSync(new URL("../scramble/session.js", import.meta.url), "utf8");
assert.match(scramble, /hashFile\(/);
assert.match(scramble, /function applyFile\(/);
assert.match(scramble, /function hashSelectedFile\(\)/);
assert.match(scramble, /function hashSilentOnHost\(/, "host fallback is the silent walk, not text update");
assert.doesNotMatch(scramble, /if \(modest\) \{\s*got = await hashWithPublicApi/);
const hashFn = scramble.match(/async function hashSelectedFile\(\) \{[\s\S]*?\n    \}/);
assert.ok(hashFn, "hashSelectedFile is the file Digest path");
assert.match(hashFn[0], /hashFile\(/, "every file size auto-hashes on pick");
assert.match(hashFn[0], /applyFileDigest\(digest/, "Digest hex is written when the hasher finishes");
assert.doesNotMatch(hashFn[0], /view\.setAlg/, "file hash must not call setAlg while hashing");
assert.doesNotMatch(hashFn[0], /bindAlg\(/);
assert.doesNotMatch(hashFn[0], /mapTraceToAlg/);
assert.doesNotMatch(hashFn[0], /bytesOf\(/, "file path must not encode bytes as typed Message text");
assert.match(scramble, /function play\(\) \{[\s\S]*?ensureTimeline\(\)/);
assert.match(scramble, /canWalkPayload/);

const adapters = readFileSync(new URL("../playroom/adapters.js", import.meta.url), "utf8");
assert.match(adapters, /id="message-file-btn"/);
assert.match(adapters, /class="file-btn"/);
assert.match(adapters, /lucideSvg\("paperclip"/);
assert.match(adapters, /id="message-file"/);
const scrambleDock = adapters.slice(0, adapters.indexOf("function mountDoubleDealDock"));
const messageRow = scrambleDock.match(/<div class="playroom-message-row">[\s\S]*?<\/div>/);
assert.ok(messageRow, "Message line is its own row");
assert.match(messageRow[0], /id="message"/);
assert.match(messageRow[0], /file-btn/);
assert.doesNotMatch(messageRow[0], /id="message-file"/, "filename chip is not between Message and paperclip");
assert.match(scrambleDock, /playroom-message-row[\s\S]*file-btn[\s\S]*id="message-file"/);
const standalone = readFileSync(new URL("../scramble/index.html", import.meta.url), "utf8");
const standaloneRow = standalone.match(/<div class="playroom-message-row">[\s\S]*?<\/div>/);
assert.doesNotMatch(standaloneRow[0], /id="message-file"/, "standalone filename chip is also on the next row");
const doubleDealDock = adapters.slice(adapters.indexOf("function mountDoubleDealDock"));
assert.doesNotMatch(doubleDealDock, /message-file/, "DoubleDeal Message is not a hash file input");

console.log("file-hash tests ok");
