import assert from "node:assert/strict";
import { FACE_MOVE, gripMatrix, mulMatrix, spinMatrix } from "./minx.js";
import { FULL_BLOCKS, PUZZLES, buildShow, ffBlockAt, ffMillis, oneBlockBytes, undo } from "./plan.js";
import { bytesOfHex, loadGenerated, samePos } from "./gen.test-helper.mjs";

assert.deepEqual(undo([[1, 2], [3, -4]]), [[3, 4], [1, -2]]);
assert.equal(FULL_BLOCKS, 1);
assert.equal(oneBlockBytes(), 19);
assert.equal(ffBlockAt(0, 2, 147), 2);
assert.equal(ffBlockAt(0.5, 2, 147), 75);
assert.equal(ffBlockAt(1, 2, 147), 147);
assert.equal(ffBlockAt(1, 2, 2), 2);
assert.equal(ffMillis(2, 2), 1800);
assert.equal(ffMillis(2, 147), 5000);
assert.ok(ffMillis(2, 2, 12) >= 1400 && ffMillis(2, 147, 12) >= 1400);

const gen = await loadGenerated();
if (!gen) {
    console.log("plan.test: SKIP (run tools/build.sh)");
    process.exit(0);
}

// The dock's one-block size is the generated padding's.
assert.equal(gen.host.pad_message(new Array(19).fill(1)).length / 28, 1);
assert.equal(gen.host.pad_message(new Array(20).fill(1)).length / 28, 2);

function parseMove(move) {
    const m = /^([A-Z]+)(\d?)('?)$/.exec(move);
    const face = FACE_MOVE.indexOf(m[1]);
    const n = Number(m[2] || 1);
    return [face, m[3] ? -n : n];
}

const close = (a, b) => a.every((row, i) => row.every((v, j) => Math.abs(v - b[i][j]) < 1e-9));
const kats = gen.kats().vectors;
let fastForwarded = 0;
for (const kat of kats) {
    const msg = bytesOfHex(kat.msg_hex);
    const trace = gen.host.trace_hash(msg);
    assert.equal(trace.blocks.length, kat.n_blocks);
    assert.equal(trace.digest.map((b) => b.toString(16).padStart(2, "0")).join(""), kat.digest_hex);
    if (trace.blocks.length > FULL_BLOCKS) fastForwarded += 1;
    const show = buildShow(trace);
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
            if (beat.kind === "spin") {
                assert.equal(beat.spin, step.spin);
                assert.ok(close(mulMatrix(spinMatrix(beat.spin), gripMatrix(beat.grip.up, beat.grip.front)),
                    gripMatrix(beat.next.up, beat.next.front)), `${kat.name}: King spin ${beat.pos}`);
            }
            if (beat.kind === "grip") {
                // Literal clicks, exactly the trace's turns, one action per beat.
                assert.deepEqual(got, step.turns, `${kat.name}: step ${beat.step} turns`);
                assert.deepEqual(beat.next, { up: step.c1, front: step.c2 });
                const kinds = show.beats.filter((x) => x.step === beat.step).map((x) => x.kind);
                const want = step.card >= 0
                    ? ["card", ...(step.spin ? ["spin"] : []), "read", "turn", "turn", "grip"]
                    : ["turn", "read", ...Array(step.turns.length / 2 - 1).fill("turn"), "grip"];
                assert.deepEqual(kinds, want, `${kat.name}: step ${beat.step} sub-beats`);
            }
            // One short action per caption: no move lists.
            assert.ok(beat.caption.title.length <= 64, beat.caption.title);
            assert.ok(!beat.caption.math.includes(","), beat.caption.math);
        }
        if (beat.kind === "ff" || beat.kind === "done") {
            // No turns in the fast-forward: the view shows show.final, which
            // is the trace's last chaining value, its inverse, and solved.
            assert.deepEqual(beat.ranges, {});
            continue;
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
    // Block 1 is played in full at any length; later blocks add no turns.
    assert.deepEqual(counts, [648, 12 + 12 + 216, 216 + 216]);
    for (const s of [1, 2, 3]) assert.ok(show.beats.some((x) => x.kind === "solve" && x.block === 0 && x.solve === s));
    assert.equal(show.beats.filter((x) => x.kind === "deal").length, 1);
    const last = trace.blocks[trace.blocks.length - 1];
    if (trace.blocks.length === 1) {
        assert.equal(show.final, null);
        assert.equal(show.ffAt, -1);
        assert.equal(show.beats.at(-1).kind, "gather");
    } else {
        // A after block 1 really is block 2's h (the fast-forward starts there).
        assert.ok(samePos(pos.A, trace.blocks[1].h));
        assert.deepEqual(show.final, { A: last.h_next, B: last.h_next_inv });
        assert.equal(gen.host.position_to_bytes(show.final.A).map((b) => b.toString(16).padStart(2, "0")).join(""), kat.digest_hex);
        assert.equal(show.beats[show.ffAt].kind, "ff");
        assert.equal(show.beats[show.ffAt].from, 2);
        assert.equal(show.beats[show.ffAt].to, trace.blocks.length);
        assert.equal(show.beats.at(-1).kind, "done");
        assert.equal(show.ffAt, show.beats.length - 2);
        assert.match(show.beats[show.ffAt].caption.title, /^Fast-forward: blocks? /);
    }
}
assert.equal(fastForwarded, 5);
const one = buildShow(gen.host.trace_hash([0x61]));
assert.equal(one.beats.filter((b) => b.kind === "read").length, 88);
assert.ok(one.beats.filter((b) => b.kind === "solve").every((b) => / · turns \d+–\d+ of \d+$/.test(b.caption.short)));
console.log("plan.test: ok");
