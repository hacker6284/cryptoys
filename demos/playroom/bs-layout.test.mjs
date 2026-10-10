// BS on the table: the real-size layout (no overlap, on the felt, on the
// shelf clear of the room), the T1 workspace on the lid grid (SPEC §6) and
// the board marks the view draws from the generated trace.
import assert from "node:assert/strict";
import { existsSync } from "node:fs";
import { BS_DICE, BS_GAP, BS_SEAT_XZ, BS_SHELF, BS_UNIT_FOOT, DEN, REAL_SIZES, SHELF_TOP, TABLE_R } from "./constants.js";
import { ROOM } from "../anim/shared/room.js";
import { stubThree } from "./three-stub.mjs";

stubThree();
const { workspaceCell, laneCell, workspaceCells, boardMarks, diceFacesAt, settled } = await import("./bs-stage.js");

// ---- real sizes ----
assert.deepEqual([REAL_SIZES.bsUnit.w, REAL_SIZES.bsUnit.h, REAL_SIZES.bsUnit.d], [0.23, 0.035, 0.17], "unit 230 × 35 × 170 mm closed (measured)");
assert.ok(Math.abs(REAL_SIZES.bsPitch.m - 0.0133333) < 1e-6, "13.333 mm pitch");
assert.equal(REAL_SIZES.bsPeg.m, 0.018);
assert.equal(REAL_SIZES.d6.m, 0.016);
assert.equal(REAL_SIZES.d10.m, 0.022);
assert.equal(REAL_SIZES.d12.m, 0.0203);
assert.equal(REAL_SIZES.diceCup.m, 0.1016);

// ---- the table: footprints on the felt (x, z from DEN), no overlap ----
const rect = (name, [x, z], f) => ({ name, x0: x + f.x0, x1: x + f.x1, z0: z + f.z0, z1: z + f.z1 });
const cupR = 0.041 * (REAL_SIZES.diceCup.m / 0.0995); // the model: Ø 82 × 99.5 mm, scaled to 101.6 mm tall
const pieces = [rect("bs", BS_SEAT_XZ.bs, BS_UNIT_FOOT), rect("bsB", BS_SEAT_XZ.bsB, BS_UNIT_FOOT)];
const [dx, dz] = BS_SEAT_XZ.bsDice;
const disc = (name, x, r, z = 0) => ({ name, x0: dx + x - r, x1: dx + x + r, z0: dz + z - r, z1: dz + z + r });
pieces.push({ name: "cup", x0: BS_SEAT_XZ.bsCup[0] - cupR, x1: BS_SEAT_XZ.bsCup[0] + cupR, z0: BS_SEAT_XZ.bsCup[1] - cupR, z1: BS_SEAT_XZ.bsCup[1] + cupR });
BS_DICE.d10.forEach((x, k) => pieces.push(disc(`d10-${k}`, x, BS_DICE.reach.d10)));
pieces.push(disc("d12", BS_DICE.d12, BS_DICE.reach.d12), disc("d6", BS_DICE.d6, BS_DICE.reach.d6));
assert.ok(cupR <= BS_DICE.reach.cup + 1e-4, "the cup's reach covers its scaled rim");
for (let i = 0; i < pieces.length; i++) {
    for (let j = i + 1; j < pieces.length; j++) {
        const a = pieces[i];
        const b = pieces[j];
        const gap = Math.max(b.x0 - a.x1, a.x0 - b.x1, b.z0 - a.z1, a.z0 - b.z1);
        assert.ok(gap >= 0.0065, `${a.name} and ${b.name} are ${(gap * 1000).toFixed(1)} mm apart`);
    }
}
const units = pieces.slice(0, 2);
assert.ok(Math.abs(units[1].x0 - units[0].x1 - BS_GAP) < 1e-9, "the units 40 mm apart");
assert.ok(Math.abs(pieces[3].z0 - units[0].z1 - BS_GAP) < 1e-3, "the dice one gap in front");
assert.ok(Math.abs(units[0].x0 - pieces[2].x1 - BS_GAP) < 1e-3, "the cup one gap left of Alice's unit");
assert.ok(Math.abs(pieces[2].z1 - units[0].z1) < 1e-4, "the cup's front in line with the units'");
const felt = TABLE_R - 0.08;
for (const p of pieces) {
    for (const [x, z] of [[p.x0, p.z0], [p.x0, p.z1], [p.x1, p.z0], [p.x1, p.z1]]) {
        assert.ok(Math.hypot(x, z) < felt - 0.05, `${p.name} on the felt`);
    }
}

// ---- the shelf: the red unit between the plants, clear of the room ----
const shelf = { x0: BS_SHELF.x + BS_UNIT_FOOT.x0, x1: BS_SHELF.x + BS_UNIT_FOOT.x1, z0: BS_SHELF.z + BS_UNIT_FOOT.z0, z1: BS_SHELF.z + BS_UNIT_FOOT.z1, y0: SHELF_TOP, y1: SHELF_TOP + 0.177 };
for (const s of ROOM.filter((r) => r.kind === "box" && r.name !== "shelf-top")) {
    const lo = s.c.map((c, k) => c - s.he[k]);
    const hi = s.c.map((c, k) => c + s.he[k]);
    const apart = Math.max(lo[0] - shelf.x1, shelf.x0 - hi[0], lo[1] - shelf.y1, shelf.y0 - hi[1], lo[2] - shelf.z1, shelf.z0 - hi[2]);
    assert.ok(apart >= 0.015, `shelf unit clear of ${s.name} (${(apart * 1000).toFixed(0)} mm)`);
}
assert.ok(shelf.z0 > -2.28 && shelf.z1 < -2.0, "on the shelf board, in front of the backboard");

// ---- the T1 workspace on the lid grid (SPEC §6) ----
const row = (cell) => "ABCDEFGHIJ"[Math.floor(cell / 10)];
const col = (cell) => (cell % 10) + 1;
for (let h = 0; h < 18; h++) {
    assert.ok("AB".includes(row(workspaceCell("x", h))), "X in rows A–B");
    assert.ok("CD".includes(row(workspaceCell("y", h))), "Y in rows C–D");
    assert.ok("IJ".includes(row(workspaceCell("c", h))), "C in rows I–J");
    for (const r of ["x", "y", "c"]) assert.ok(col(workspaceCell(r, h)) <= 9, "registers in columns 1–9");
}
for (let h = 0; h < 36; h++) assert.ok("EFGH".includes(row(workspaceCell("s", h))) && col(workspaceCell("s", h)) <= 9, "the strip in E–H");
assert.deepEqual([36, 37].map((h) => [row(workspaceCell("s", h)), col(workspaceCell("s", h))]), [["I", 1], ["I", 2]], "overflow into row I");
for (let k = 1; k <= 10; k++) assert.equal(col(laneCell(k)), 10, "the control lane is column 10");
assert.equal(row(laneCell(5)), "E");
const all = [];
for (const r of ["x", "y", "c"]) for (let h = 0; h < 18; h++) all.push(workspaceCell(r, h));
for (let h = 0; h < 36; h++) all.push(workspaceCell("s", h));
for (let k = 1; k <= 10; k++) all.push(laneCell(k));
assert.equal(new Set(all).size, 100, "90 register holes and the 10-hole lane: every hole once (SPEC §6)");
const cells = workspaceCells({ x: [1, 2, ...new Array(16).fill(0)], y: new Array(18).fill(0), c: new Array(18).fill(0) }, 1, 2);
assert.deepEqual([cells[0], cells[1], cells[laneCell(5)], cells[laneCell(10)]], [1, 2, 1, 2]);

// ---- board marks from a generated show ----
const generated = new URL("../bs/generated/_bs_impl.mjs", import.meta.url);
if (!existsSync(generated)) {
    if (process.env.CI) throw new Error("demos/bs/generated missing: run tools/build.sh");
} else {
    const raw = await import(generated);
    const rt = await import(new URL("../bs/generated/_sudo_rt.mjs", import.meta.url));
    const { buildShow, diceFromSeed, runTrace } = await import("../bs/trace.js");
    const { OP } = await import("../bs/expand.js");
    const d = diceFromSeed("cryptoys");
    const show = buildShow(runTrace(raw, rt, "T1", d.a, d.b));
    const marks = boardMarks(show);
    const B = show.beats.length;
    show.beats.forEach((beat, i) => {
        const p = beat.player;
        if (beat.kind === "build") {
            const read = show.reads[p][beat.read];
            if (beat.read < 99) assert.equal(marks[p].cursor[i], read.hole, "BUILD: the cursor on the hole");
            assert.equal(marks[p].built[i], beat.read + 1);
            return;
        }
        const st = show.steps[beat.step];
        assert.equal(marks[p].step[i], beat.step);
        if (st.op === OP.shot) {
            const last = show.beats[i + 1]?.op !== OP.shot || show.beats[i + 1]?.player !== p;
            assert.equal(marks[p].lane5[i], last ? 0 : 1, "lane hole 5 while calling, lifted after the last call");
        } else if (st.op !== OP.clear) {
            assert.equal(marks[p].lane5[i], 0);
        }
        if (st.cell >= 0 && st.op !== OP.tidy) {
            const h = show.holes[p][st.cell];
            assert.equal(marks[p].lane10[i], h >= 100 ? 1 : h >= 0 && show.holes[p][st.cell + 1] === h ? 2 : 0, "lane hole 10: ship pass, 3-holer extra, peg pass");
        }
    });
    assert.ok(marks[0].lane10.includes(2) || marks[1].lane10.includes(2), "a 3-holer's extra cell shows red");
    assert.equal(marks[0].cursor[B - 1], -1, "the cursor leaves the grid at the end");
    // Dice: the last row cup's five settled faces, the last d12 and d6.
    const lastBuild = 199;
    const faces = diceFacesAt(show, lastBuild);
    assert.equal(faces.d10.length, 5);
    assert.ok(faces.d10.every((f) => f >= 1 && f <= 9));
    const cups = show.reads[1].filter((r) => r.cup.length);
    assert.deepEqual(faces.d10, settled(cups.at(-1).cup));
    assert.deepEqual(diceFacesAt(show, -1), { d10: [1, 2, 3, 4, 5], d12: 12, d6: 6 }, "at rest before BUILD");
}

console.log("bs layout tests ok");
