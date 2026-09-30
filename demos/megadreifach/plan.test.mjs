import assert from "node:assert/strict";
import { FACE_MOVE, gripMatrix, mulMatrix, spinMatrix } from "./minx.js";
import { MAX_ANIM_BLOCKS, PUZZLES, buildShow, maxAnimBytes, undo } from "./plan.js";
import { bytesOfHex, loadGenerated, samePos } from "./gen.test-helper.mjs";

assert.deepEqual(undo([[1, 2], [3, -4]]), [[3, 4], [1, -2]]);
assert.equal(maxAnimBytes(), 47);

const gen = await loadGenerated();
if (!gen) {
    console.log("plan.test: SKIP (run tools/build.sh)");
    process.exit(0);
}

// The dock's byte limit is the generated padding's two-block limit.
assert.equal(gen.host.pad_message(new Array(47).fill(1)).length / 28, 2);
assert.equal(gen.host.pad_message(new Array(48).fill(1)).length / 28, 3);

function parseMove(move) {
    const m = /^([A-Z]+)(\d?)('?)$/.exec(move);
    const face = FACE_MOVE.indexOf(m[1]);
    const n = Number(m[2] || 1);
    return [face, m[3] ? -n : n];
}

const close = (a, b) => a.every((row, i) => row.every((v, j) => Math.abs(v - b[i][j]) < 1e-9));
const kats = gen.kats().vectors;
let animated = 0;
for (const kat of kats) {
    const msg = bytesOfHex(kat.msg_hex);
    const trace = gen.host.trace_hash(msg);
    assert.equal(trace.blocks.length, kat.n_blocks);
    assert.equal(trace.digest.map((b) => b.toString(16).padStart(2, "0")).join(""), kat.digest_hex);
    if (trace.blocks.length > MAX_ANIM_BLOCKS) {
        assert.throws(() => buildShow(trace), RangeError);
        continue;
    }
    animated += 1;
    const show = buildShow(trace);
    const pos = { A: gen.identity(), B: gen.identity(), C: gen.identity() };
    const done = { A: 0, B: 0, C: 0 };
    let block = 0;
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
        if (beat.kind === "card" || beat.kind === "f3") {
            const step = blk.steps[beat.pos - 1];
            // Literal clicks, exactly the trace's turns.
            assert.deepEqual(beat.turns.flat(), step.turns);
            if (beat.spin) {
                assert.ok(close(mulMatrix(spinMatrix(beat.spin), gripMatrix(beat.grip.up, beat.grip.front)),
                    gripMatrix(beat.spunGrip.up, beat.spunGrip.front)), `${kat.name}: King spin ${beat.pos}`);
            }
        }
        if (beat.kind === "home") assert.ok(samePos(pos.A, blk.e), `${kat.name}: A = e after E_m`);
        if (beat.kind === "gather") {
            assert.ok(samePos(pos.A, blk.h_next), `${kat.name}: A = h' after the 3-solve`);
            assert.ok(samePos(pos.B, blk.h_next_inv), `${kat.name}: B = h'⁻¹`);
            assert.ok(samePos(pos.C, gen.identity()), `${kat.name}: C solved`);
            block += 1;
        }
    }
    for (const p of PUZZLES) assert.equal(done[p], show.moves[p].length);
    const counts = PUZZLES.map((p) => show.moves[p].length);
    if (trace.blocks.length === 1) assert.deepEqual(counts, [648, 12 + 12 + 216, 216 + 216]);
    if (trace.blocks.length === 2) assert.deepEqual(counts, [2304, 240 + 216 + 624, 432 + 624 + 624]);
    // Every block shows the full 3-solve, the last included.
    for (let b = 0; b < trace.blocks.length; b++) {
        for (const s of [1, 2, 3]) assert.ok(show.beats.some((x) => x.kind === "solve" && x.block === b && x.solve === s));
    }
}
assert.equal(animated, 6);
console.log("plan.test: ok");
