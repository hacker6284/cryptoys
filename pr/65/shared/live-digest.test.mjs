import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { createLiveDigest } from "./live-digest.js";

const live = createLiveDigest();
assert.equal(live.stale(), true, "timeline starts unbound");

let binds = 0;
live.afterDigest();
assert.equal(live.stale(), true);
assert.equal(live.ensureTimeline(() => { binds += 1; }), true);
assert.equal(binds, 1);
assert.equal(live.stale(), false);
assert.equal(live.ensureTimeline(() => { binds += 1; }), false, "second Play does not rebuild");
assert.equal(binds, 1);

live.afterDigest();
assert.equal(live.stale(), true, "typing marks the timeline stale");
assert.equal(live.ensureTimeline(() => { binds += 1; }), true);
assert.equal(binds, 2);

live.dropTimeline();
assert.equal(live.stale(), true, "puzzle swap drops the bound alg");
assert.equal(live.ensureTimeline(() => { binds += 1; }), true);
assert.equal(binds, 3);

const scramble = readFileSync(new URL("../scramble/session.js", import.meta.url), "utf8");
assert.match(scramble, /createLiveDigest/, "Scramble uses the shared digest/timeline gate");
assert.match(scramble, /afterDigest\(\)/);
assert.match(scramble, /ensureTimeline/);
assert.doesNotMatch(
    scramble,
    /onChange:\s*\(\)\s*=>\s*recompute\(\)/,
    "Message input must not call full recompute / setAlg",
);
assert.match(
    scramble,
    /onChange:\s*\(\)\s*=>\s*refreshDigest\(\)/,
    "Message input updates Digest only",
);

const digestFn = scramble.match(/function refreshDigest\(\) \{[\s\S]*?\n    \}/);
assert.ok(digestFn, "refreshDigest is the live Message path");
assert.doesNotMatch(digestFn[0], /view\.setAlg/, "Digest path must not call setAlg");
assert.doesNotMatch(digestFn[0], /bindAlg\(/, "Digest path must not bind the move timeline");
assert.doesNotMatch(digestFn[0], /mapTraceToAlg/, "leave-trace mapping waits for Play / Step / teach");

assert.match(scramble, /function play\(\) \{[\s\S]*?ensureTimeline\(\)/, "Play binds the timeline");
assert.match(scramble, /function enterTeach\(\) \{[\s\S]*?ensureTimeline\(\)/, "Step / teach binds the timeline");
assert.match(scramble, /async function solve\(\) \{[\s\S]*?ensureTimeline\(\)/, "Solve binds the current Message first");
assert.match(scramble, /hashSelectedFile/, "file hash is a separate Digest path");
assert.match(scramble, /hashSilentOnHost/, "file Digest fallback is the silent walk, not text update");

const doubledeal = readFileSync(new URL("../doubledeal/session.js", import.meta.url), "utf8");
assert.match(doubledeal, /function preview\(\)/, "DoubleDeal keeps a Digest-friendly input path");
assert.match(doubledeal, /function computeTrace\(\)/, "teach / play trace stays on Play / Step");
const previewFn = doubledeal.match(/function preview\(\) \{[\s\S]*?\n    \}/);
assert.ok(previewFn, "preview is the live input path");
assert.doesNotMatch(previewFn[0], /computeTrace\(/, "preview must not build the play trace");
assert.doesNotMatch(previewFn[0], /trace_ecb|trace_ctr|trace_decrypt/, "preview must not walk the teach trace");

console.log("live-digest tests ok");
