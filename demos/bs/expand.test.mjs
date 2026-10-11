import assert from "node:assert/strict";
import { applyLidMoves, lidMoves } from "./expand.js";
import { diceFromSeed, regString } from "./trace.js";
import { loadGenerated } from "./gen.test-helper.mjs";
import { stubThree } from "../playroom/three-stub.mjs";

// Every exchange step's peg moves come from the generated step_moves (the
// worker's `moves`); expand.js only places them on the lid. Replayed on the
// lid from summary i, they land exactly on summary i + 1, at every step of
// the T1 vectors in bs_vectors.json and a seeded game. (bs.sudo's own tests
// replay them on the registers at every step of every vector, T2 and T6 too.)
const gen = await loadGenerated();
if (!gen) {
    console.log("bs expand tests skipped (no generated module; run tools/build.sh)");
    process.exit(0);
}
stubThree();
const { workspaceCell, workspaceCells } = await import("../playroom/bs-stage.js");
const worker = await import("./worker.js");

function checkShow(name, show) {
    // BUILD: each hole's generated moves end with its peg, cover its ship's holes.
    for (const p of [0, 1]) {
        for (const read of show.reads[p]) {
            const where = `${name} build ${p} hole ${read.hole}`;
            const put = read.moves.filter((m) => m.case === "PutPeg");
            assert.deepEqual(put.map((m) => [m.hole, m.colour]), read.peg ? [[read.hole, read.peg]] : [], `${where}: the peg`);
            assert.equal(read.moves.filter((m) => m.case === "Throw").length, read.cup.length, `${where}: every cup throw`);
            const last = read.moves.filter((m) => m.case === "Piece").pop();
            assert.deepEqual(last?.ship ?? null, read.ship[0] ?? null, `${where}: the piece left lying is the ship`);
            assert.deepEqual(last?.holes ?? [], read.covered, `${where}: it covers read.covered`);
        }
    }
    // The exchange: the lid after summary i, plus step i + 1's moves, is the lid after it.
    const lid = [workspaceCells({}), workspaceCells({})];
    const regs = [{}, {}];
    let count = 0;
    let overflow = 0;
    for (const beat of show.beats) {
        if (beat.kind !== "step") continue;
        const st = show.steps[beat.step];
        const p = st.player;
        const where = `${name} step ${beat.step} (${st.op}, player ${p})`;
        const { moves } = worker.answer({ op: "moves", step: beat.step });
        count += moves.length;
        for (const m of moves) {
            if (m.reg !== "Strip" || m.hole < 36) continue;
            // Strip holes 36–37 are C's holes 0–1 (row I): only while C is empty.
            overflow += 1;
            assert.ok(!regs[p].c?.some((v) => v), `${where}: strip hole ${m.hole} only while C is empty`);
            assert.ok(st.op !== "Check" && st.op !== "CheckTidy", `${where}: not while C is being filled`);
        }
        applyLidMoves(lid[p], lidMoves(moves, workspaceCell));
        assert.deepEqual(Array.from(lid[p]), Array.from(workspaceCells(st)), `${where}: the lid reaches the summary`);
        if (st.op === "Call") assert.ok(moves.length <= 1, `${where}: a call is one peg or a misfire`);
        if (["Square", "Cube", "TimesBase", "Check"].includes(st.op)) assert.ok(moves.length > 0, `${where}: a product moves pegs`);
        regs[p] = st;
    }
    return { count, overflow };
}

for (const v of gen.exchanges.filter((v) => v.tier === "T1")) {
    const t0 = performance.now();
    const { show } = worker.answer({ op: "show", vector: v });
    assert.equal(show.A, v.public_a, `${v.name}: A`);
    assert.equal(show.B, v.public_b, `${v.name}: B`);
    assert.equal(show.K, v.secret_a, `${v.name}: K`);
    const { count, overflow } = checkShow(v.name, show);
    console.log(`ok ${v.name}: ${show.beats.length} beats, ${count} peg moves, ${overflow} on strip holes 36–37 (${Math.round(performance.now() - t0)} ms)`);
}

// A seeded game (the dock's seed input), checked the same way.
const { show: seeded } = worker.answer({ op: "show", seed: "cryptoys" });
const dice = diceFromSeed("cryptoys");
const built = (d) => gen.host.build_key_grid({ ...d, next12: 0, next6: 0, next10: 0 }).grid;
const ex = gen.host.exchange(gen.host.tier("T1"), [built(dice.a)], [built(dice.b)]);
assert.equal(seeded.A, regString(ex.public_a));
assert.equal(seeded.K, regString(ex.secret_a));
assert.equal(seeded.K, seeded.Kb);
checkShow("seed cryptoys", seeded);
assert.notDeepEqual(diceFromSeed("a"), diceFromSeed("b"), "different seeds, different dice");
assert.deepEqual(diceFromSeed("x"), diceFromSeed("x"), "a seed always throws the same faces");

console.log("bs expand tests ok");
