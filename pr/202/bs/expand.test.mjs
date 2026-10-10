import assert from "node:assert/strict";
import { OP, applyMoves, cloneWorkspace, emptyGrid, emptyWorkspace, expandBuild, expandStep, shipHoles } from "./expand.js";
import { buildShow, diceFromSeed, regString, runTrace } from "./trace.js";
import { loadGenerated } from "./gen.test-helper.mjs";

// The expander turns one summary of the generated trace into its peg moves.
// Replayed from summary i, its moves land exactly on summary i + 1: on every
// exchange vector in bs_vectors.json (T1 ×2, T2, T6) and a seeded T1 game,
// at every BUILD hole and every exchange step.
const gen = await loadGenerated();
if (!gen) {
    console.log("bs expand tests skipped (no generated module; run tools/build.sh)");
    process.exit(0);
}

const same = (a, b) => a.length === b.length && a.every((v, i) => v === b[i]);

function checkShow(name, show) {
    const { n, toll } = show;
    const field = { n, toll };
    // BUILD: every hole's moves give the key grid so far; the last gives the generated grid.
    for (const p of [0, 1]) {
        const grid = emptyGrid();
        for (const read of show.reads[p]) {
            const moves = expandBuild(grid, read);
            assert.equal(grid.pegs[read.hole], read.peg, `${name} build ${p} hole ${read.hole}: peg`);
            const pegMove = moves.find((m) => m.t === "peg");
            assert.equal(pegMove?.colour ?? 0, read.peg, `${name} build ${p} hole ${read.hole}: peg move`);
            const d10 = moves.filter((m) => m.t === "d10");
            assert.equal(d10.length, read.cup.length, `${name} build ${p} hole ${read.hole}: every cup throw`);
            const last = moves.filter((m) => m.t === "ship").pop();
            if (read.ship.length) {
                assert.equal(last.kind, read.ship[0].kind, `${name} build ${p} hole ${read.hole}: the piece left lying is the ship`);
            } else {
                assert.equal(last, undefined);
            }
        }
        assert.deepEqual(grid.ships, show.grids[p].ships, `${name}: ${p} fleet`);
        assert.deepEqual(grid.pegs, show.grids[p].pegs, `${name}: ${p} pegs`);
        const covered = new Array(100).fill(false);
        for (const s of show.grids[p].ships) for (const h of shipHoles(s)) covered[h] = true;
        assert.deepEqual(grid.covered, covered, `${name}: ${p} covered holes`);
    }
    // The exchange: summary i + expansion = summary i + 1, the strip clear between steps.
    const ws = [emptyWorkspace(n), emptyWorkspace(n)];
    let moves = 0;
    for (const beat of show.beats) {
        if (beat.kind !== "step") continue;
        const st = show.steps[beat.step];
        const p = st.player;
        const before = cloneWorkspace(ws[p]);
        const out = expandStep(ws, st, field, { cellValue: beat.cellValue, shared: beat.shared });
        moves += out.length;
        const where = `${name} step ${beat.step} (op ${st.op}, player ${p})`;
        assert.ok(same(ws[p].x, st.x), `${where}: X`);
        assert.ok(same(ws[p].y, st.y), `${where}: Y`);
        assert.ok(same(ws[p].c, st.c), `${where}: C`);
        assert.ok(ws[p].s.every((t) => t === 0), `${where}: the strip ends clear`);
        // The moves alone, replayed on the summary before, give the same registers.
        const replay = applyMoves(cloneWorkspace(before), out);
        assert.ok(same(replay.x, st.x) && same(replay.y, st.y) && same(replay.c, st.c), `${where}: replay`);
        if (st.op === OP.shot) assert.ok(out.length <= 1, `${where}: a shot is one peg or a misfire`);
        if ([OP.square, OP.cube, OP.hit, OP.check].includes(st.op)) assert.ok(out.length > 0, `${where}: a multiplication moves pegs`);
    }
    return moves;
}

for (const v of gen.exchanges) {
    const t0 = performance.now();
    const show = buildShow(runTrace(gen.raw, gen.rt, v.tier, v.dice_a, v.dice_b));
    assert.equal(show.ok, true, v.name);
    assert.equal(regString(show.publicA), v.public_a, `${v.name}: A`);
    assert.equal(regString(show.publicB), v.public_b, `${v.name}: B`);
    assert.equal(regString(show.secretA), v.secret_a, `${v.name}: K`);
    assert.equal(regString(show.secretB), v.secret_b, `${v.name}: K (Bob)`);
    const moves = checkShow(v.name, show);
    console.log(`ok ${v.name}: ${show.beats.length} beats, ${moves} peg moves (${Math.round(performance.now() - t0)} ms)`);
}

// A seeded game (the dock's seed input), checked the same way.
const dice = diceFromSeed("cryptoys");
const seeded = buildShow(runTrace(gen.raw, gen.rt, "T1", dice.a, dice.b));
assert.equal(seeded.ok, true);
const built = (d) => gen.host.build_key_grid({ ...d, next12: 0, next6: 0, next10: 0 }).grid;
const ex = gen.host.exchange(gen.host.tier("T1"), [built(dice.a)], [built(dice.b)]);
assert.deepEqual(seeded.publicA, ex.public_a);
assert.deepEqual(seeded.secretA, ex.secret_a);
assert.deepEqual(seeded.secretA, seeded.secretB);
checkShow("seed cryptoys", seeded);
assert.notDeepEqual(diceFromSeed("a"), diceFromSeed("b"), "different seeds, different dice");
assert.deepEqual(diceFromSeed("x"), diceFromSeed("x"), "a seed always throws the same faces");

console.log("bs expand tests ok");
