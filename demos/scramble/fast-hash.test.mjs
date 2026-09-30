import assert from "node:assert/strict";
import { scramble_v1, scramble_v2, update, evaluate } from "./generated/scramble.mjs";
import { DEMO_FILE_CHUNK_BYTES } from "../shared/file-hash.js";
import { createFastHasher } from "./fast-hash.js";

// The file path must give the same Digest as the generated module for
// the same bytes: Gen 1 and Gen 2, any chunking, padding boundaries.
function generated(version, bytes) {
    const state = version === 1 ? scramble_v1() : scramble_v2();
    update(state, Array.from(bytes));
    return Array.from(evaluate(state).digest);
}

function fast(version, bytes, cuts = []) {
    const hasher = createFastHasher();
    hasher.start(version);
    let at = 0;
    for (const cut of cuts) {
        hasher.push(bytes.subarray(at, at + cut));
        at += cut;
    }
    hasher.push(bytes.subarray(at));
    return hasher.finish().digest;
}

let seed = 6284;
const rand = () => {
    seed = (seed * 1103515245 + 12345) >>> 0;
    return seed >>> 24;
};

const hello = new TextEncoder().encode("hello");
assert.deepEqual(fast(2, hello), [0, 82, 163, 199, 209, 34, 145, 209, 64], "hello v2 matches the SPEC vector");

let cases = 0;
for (const version of [1, 2]) {
    for (const length of [0, 1, 2, 3, 4, 5, 6, 7, 8, 11, 12, 13, 16, 17, 31, 32, 33, 64, 127, 200]) {
        const bytes = Uint8Array.from({ length }, rand);
        const want = generated(version, bytes);
        assert.deepEqual(fast(version, bytes), want, `Gen ${version}, ${length} bytes, one push`);
        const cuts = [1, 0, 3, 2, 5].filter((_, i) => i < length);
        assert.deepEqual(fast(version, bytes, cuts), want, `Gen ${version}, ${length} bytes, chunked`);
        cases += 1;
    }
}

// The worker walks in DEMO_FILE_CHUNK_BYTES pieces and posts the same digest.
const posted = [];
globalThis.self = { postMessage: (msg) => posted.push(msg) };
await import("./hash-worker.js");
const done = new Promise((resolve) => {
    self.postMessage = (msg) => {
        posted.push(msg);
        if (msg.type === "done" || msg.type === "error") resolve(msg);
    };
});
self.onmessage({ data: { type: "start" } });
assert.deepEqual(posted, [{ type: "ready" }], "worker answers start with ready");
const big = Uint8Array.from({ length: DEMO_FILE_CHUNK_BYTES + 7 }, rand);
self.onmessage({ data: { type: "hash", version: 2, bytes: big } });
const reply = await done;
assert.equal(reply.type, "done");
assert.deepEqual(reply.digest, fast(2, big), "worker digest is the one-shot digest");
const progress = posted.filter((msg) => msg.type === "progress").map((msg) => msg.processed);
assert.deepEqual(progress, [0, DEMO_FILE_CHUNK_BYTES, big.length], "worker reports chunk progress");

const doneV1 = new Promise((resolve) => {
    self.postMessage = (msg) => {
        if (msg.type === "done" || msg.type === "error") resolve(msg);
    };
});
self.onmessage({ data: { type: "hash", version: 1, bytes: hello } });
assert.deepEqual((await doneV1).digest, generated(1, hello), "worker hashes Gen 1 when asked");

console.log(`fast-hash tests ok (${cases * 2} generated comparisons)`);
