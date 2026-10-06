// plan.js on the generated v3 module. Without trace_hash in the generated
// build (the committed v3 sudo has none yet), only the trace-free parts run
// and the worker must say "no-trace". With it (the proposed sudo), every
// KAT that is short enough to trace is replayed move by move with the
// generated face turns, against the trace's h, W·h, h′, h′⁻¹ and solved.
import assert from "node:assert/strict";
import { FACE_MOVE } from "./minx.js";
import { CARD_STEPS, ECHOES, PUZZLES, TRACE_BLOCKS, buildShow, pairs, undo } from "./plan.js";
import { bytesOfHex, loadGenerated, samePos } from "./gen.test-helper.mjs";

assert.deepEqual(undo([[1, 2], [3, -4]]), [[3, 4], [1, -2]]);
assert.deepEqual(pairs([1, 2, 3, 4]), [[1, 2], [3, 4]]);
assert.equal(TRACE_BLOCKS, 1);

const gen = await loadGenerated();
if (!gen) {
    console.log("plan.test: SKIP (run tools/build.sh)");
    process.exit(0);
}

const { answer, hasTrace, oneBlockBytes, plain } = await import("./worker.js");
// The dock's one-block size comes from the generated padding.
assert.equal(gen.host.pad_message(new Array(oneBlockBytes()).fill(1)).length / 28, 1);
assert.equal(gen.host.pad_message(new Array(oneBlockBytes() + 1).fill(1)).length / 28, 2);
assert.equal(oneBlockBytes(), 19);

const kats = gen.kats();
const hexOf = (bytes) => bytes.map((b) => b.toString(16).padStart(2, "0")).join("");
// The digest path is the generated Hash on every KAT, traced or not.
for (const kat of kats.vectors) {
    const reply = answer({ op: "digest", bytes: bytesOfHex(kat.msg_hex) });
    assert.equal(hexOf(reply.digest), kat.digest_hex, `${kat.name}: generated Hash = KAT`);
    assert.equal(reply.blocks, kat.n_blocks);
}

if (!hasTrace()) {
    const reply = answer({ op: "show", bytes: [0x61, 0x62, 0x63] });
    assert.equal(reply.show, null);
    assert.equal(reply.reason, "no-trace");
    assert.equal(hexOf(reply.digest), kats.vectors.find((v) => v.name === "short_abc").digest_hex);
    console.log("plan.test: ok (no trace_hash in the generated build: digest and KAT checks only)");
    process.exit(0);
}

function parseMove(move) {
    const m = /^([A-Z]+)(\d?)('?)$/.exec(move);
    const face = FACE_MOVE.indexOf(m[1]);
    const n = Number(m[2] || 1);
    return [face, m[3] ? -n : n];
}

let traced = 0;
for (const kat of kats.vectors) {
    const msg = bytesOfHex(kat.msg_hex);
    const reply = answer({ op: "show", bytes: msg });
    assert.equal(hexOf(reply.digest), kat.digest_hex, `${kat.name}: traced digest = KAT`);
    if (kat.n_blocks > TRACE_BLOCKS) {
        assert.equal(reply.show, null);
        assert.equal(reply.reason, "too-long");
        continue;
    }
    traced += 1;
    const show = reply.show;
    const trace = plain(gen.raw.trace_hash(gen.rtList(msg)));
    assert.equal(hexOf(trace.digest), kat.digest_hex);
    const pos = { A: gen.identity(), B: gen.identity(), C: gen.identity() };
    const done = { A: 0, B: 0, C: 0 };
    let block = 0;
    const stepTurns = {};
    for (const beat of show.beats) {
        for (const p of PUZZLES) {
            const r = beat.ranges[p];
            if (!r) continue;
            assert.equal(r[0], done[p], `${kat.name}: ${p} plays in order`);
            for (let i = r[0]; i < r[1]; i++) {
                const [face, clicks] = parseMove(show.moves[p][i]);
                pos[p] = gen.faceTurn(pos[p], face, clicks);
            }
            done[p] = r[1];
        }
        const blk = trace.blocks[block];
        if (beat.kind === "deal") {
            assert.ok(samePos(pos.A, blk.h), `${kat.name}: A = h at block ${block}`);
            assert.ok(samePos(pos.B, blk.h_inv), `${kat.name}: B = h⁻¹ at block ${block}`);
            assert.ok(samePos(pos.C, gen.identity()));
            assert.deepEqual(beat.deal, blk.deal);
        }
        if (beat.step) {
            const step = blk.steps[beat.pos - 1];
            const got = (stepTurns[beat.step] ??= []);
            if (beat.face !== undefined) got.push(beat.face, beat.clicks);
            if (beat.kind === "name") {
                assert.equal(beat.marks.edge.length, 2);
                assert.equal(beat.marks.corner.length, 3);
                // The named edge carries its card-coloured sticker on the face the next turn turns.
                const next = show.beats[show.beats.indexOf(beat) + 1];
                assert.equal(next.face, beat.marks.edge[0], `${kat.name}: step ${beat.step} edge mark`);
            }
            if (beat.kind === "look") {
                // X and Y are where the held edge's and corner's n-stickers are.
                assert.equal(beat.marks.edge[1], step.x);
                assert.equal(beat.marks.corner[1], step.y);
            }
        }
        if (beat.kind === "done-w") {
            assert.ok(samePos(pos.A, blk.e), `${kat.name}: A = W·h after E_m`);
            for (const st of blk.steps) {
                // Literal clicks, exactly the trace's six turns per step, one per beat.
                assert.deepEqual(stepTurns[`${block}:${st.pos}`], st.turns, `${kat.name}: step ${st.pos} turns`);
                const kinds = show.beats.filter((x) => x.step === `${block}:${st.pos}`).map((x) => x.kind);
                const want = st.pos > CARD_STEPS
                    ? ["count", "look", "echo", "name", "turn", "turn", "turn", "turn", "turn"]
                    : ["card", "name", "turn", "turn", "turn", "turn", "turn", ...(st.pos === CARD_STEPS ? ["hold"] : [])];
                assert.deepEqual(kinds, want, `${kat.name}: step ${st.pos} sub-beats`);
            }
        }
        if (beat.kind === "gather") {
            assert.ok(samePos(pos.A, blk.h_next), `${kat.name}: A = h′ after the 3-solve`);
            assert.ok(samePos(pos.B, blk.h_next_inv), `${kat.name}: B = h′⁻¹`);
            assert.ok(samePos(pos.C, gen.identity()), `${kat.name}: C solved`);
            if (block + 1 === trace.blocks.length) assert.equal(hexOf(gen.host.position_to_bytes(pos.A)), kat.digest_hex, `${kat.name}: A reads the digest`);
            block += 1;
        }
    }
    assert.equal(block, trace.blocks.length);
    for (const p of PUZZLES) assert.equal(done[p], show.moves[p].length);
    // 12 + 468 + 12 + 492 turns on A in a one-block show, never cut short.
    assert.deepEqual(PUZZLES.map((p) => show.moves[p].length), [12 + 468 + 12 + 492 + 492, 12 + 12 + 492, 492 + 492]);
    assert.equal(show.beats.filter((b) => b.kind === "count").length, ECHOES);
    for (const s of [1, 2, 3]) assert.ok(show.beats.some((x) => x.kind === "solve" && x.solve === s));
}
assert.equal(traced, 3);
console.log("plan.test: ok (trace_hash present: 3 KATs replayed turn for turn)");
