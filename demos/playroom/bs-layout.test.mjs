// BS on the table: the real-size layout (no overlap, on the felt, on the
// shelf clear of the room), the T1 workspace on the lid grid (SPEC §6) and
// the board marks the view draws from the generated trace.
import assert from "node:assert/strict";
import { existsSync, readFileSync } from "node:fs";
import { BS_DICE, BS_GAP, BS_GRID, BS_SEAT_XZ, BS_SHELF, BS_UNIT_FOOT, DEN, REAL_SIZES, SHELF_TOP, TABLE_R } from "./constants.js";
import { ROOM } from "../anim/shared/room.js";
import { stubThree } from "./three-stub.mjs";

stubThree();
const { BS_MODELS, workspaceCell, laneCell, workspaceCells, boardMarks, cursorPoses, diceFacesAt, settled } = await import("./bs-stage.js");

// ---- real sizes ----
assert.deepEqual([REAL_SIZES.bsUnit.w, REAL_SIZES.bsUnit.h, REAL_SIZES.bsUnit.d], [0.23, 0.035, 0.17], "unit 230 × 35 × 170 mm closed (measured)");
assert.ok(Math.abs(REAL_SIZES.bsPitch.m - 0.0133333) < 1e-6, "13.333 mm pitch");
assert.equal(REAL_SIZES.bsPeg.m, 0.018);
assert.equal(REAL_SIZES.d6.m, 0.016);
assert.equal(REAL_SIZES.d10.m, 0.022);
assert.equal(REAL_SIZES.d12.m, 0.0203);
assert.equal(REAL_SIZES.diceCup.m, 0.1016);

// ---- the models themselves at those sizes (POSITION min/max, node TRS applied) ----
function glbBounds(file, only = null) {
    const b = readFileSync(new URL(`../bs/assets/models/${file}`, import.meta.url));
    const json = JSON.parse(b.subarray(20, 20 + b.readUInt32LE(12)).toString("utf8"));
    const lo = [Infinity, Infinity, Infinity];
    const hi = [-Infinity, -Infinity, -Infinity];
    const rot = ([x, y, z, w], v) => {
        const t = [2 * (y * v[2] - z * v[1]), 2 * (z * v[0] - x * v[2]), 2 * (x * v[1] - y * v[0])];
        return [v[0] + w * t[0] + y * t[2] - z * t[1], v[1] + w * t[1] + z * t[0] - x * t[2], v[2] + w * t[2] + x * t[1] - y * t[0]];
    };
    const apply = (n, v) => {
        const s = n.scale ?? [1, 1, 1];
        const r = rot(n.rotation ?? [0, 0, 0, 1], [v[0] * s[0], v[1] * s[1], v[2] * s[2]]);
        const t = n.translation ?? [0, 0, 0];
        return [r[0] + t[0], r[1] + t[1], r[2] + t[2]];
    };
    const parent = new Map();
    json.nodes.forEach((n, i) => (n.children ?? []).forEach((c) => parent.set(c, i)));
    json.nodes.forEach((n, i) => {
        if (n.mesh === undefined || (only && n.name !== only)) return;
        for (const prim of json.meshes[n.mesh].primitives) {
            const a = json.accessors[prim.attributes.POSITION];
            for (const corner of [0, 1, 2, 3, 4, 5, 6, 7]) {
                let v = [0, 1, 2].map((k) => ((corner >> k) & 1 ? a.max[k] : a.min[k]));
                for (let at = i; at !== undefined; at = parent.get(at)) v = apply(json.nodes[at], v);
                for (let k = 0; k < 3; k++) {
                    lo[k] = Math.min(lo[k], v[k]);
                    hi[k] = Math.max(hi[k], v[k]);
                }
            }
        }
    });
    return hi.map((h, k) => Math.round((h - lo[k]) * 1e4) / 10); // mm, x × y × z
}
for (const unit of [BS_MODELS.red, BS_MODELS.blue]) assert.deepEqual(glbBounds(unit), [230, 177, 173.6], `${unit}: 230 × 177 × 173.6 mm open (w × h × d)`);
assert.equal(glbBounds(BS_MODELS.pegs, "peg_red")[1], 18, "pegs 18 mm long");
for (const [node, len] of [["ship_carrier_5", 65], ["ship_battleship_4", 52], ["ship_cruiser_3", 41], ["ship_submarine_3", 41], ["ship_destroyer_2", 27]]) {
    const [l, , w] = glbBounds(BS_MODELS.ships, node);
    assert.deepEqual([l, w], [len, 10], `${node}: ${len} × 10 mm`);
}
assert.equal(glbBounds(BS_MODELS.d10)[1], 22, "d10: 22 mm tip to tip");
assert.deepEqual(glbBounds(BS_MODELS.d12), [19, 19, 19], "d12: a 19 mm box");
assert.deepEqual(glbBounds(BS_MODELS.d6), [16, 16, 16], "d6: 16 mm");
assert.deepEqual(glbBounds(BS_MODELS.cup), [82.6, 101.6, 82.6], "cup: Ø 82.6 × 101.6 mm");

// ---- the table: footprints on the felt (x, z from DEN), no overlap ----
const rect = (name, [x, z], f) => ({ name, x0: x + f.x0, x1: x + f.x1, z0: z + f.z0, z1: z + f.z1 });
const cupR = REAL_SIZES.diceCup.w / 2; // the model, Ø 82.6 mm (checked above)
const pieces = [rect("bs", BS_SEAT_XZ.bs, BS_UNIT_FOOT), rect("bsB", BS_SEAT_XZ.bsB, BS_UNIT_FOOT)];
const [dx, dz] = BS_SEAT_XZ.bsDice;
const disc = (name, x, r, z = 0) => ({ name, x0: dx + x - r, x1: dx + x + r, z0: dz + z - r, z1: dz + z + r });
pieces.push({ name: "cup", x0: BS_SEAT_XZ.bsCup[0] - cupR, x1: BS_SEAT_XZ.bsCup[0] + cupR, z0: BS_SEAT_XZ.bsCup[1] - cupR, z1: BS_SEAT_XZ.bsCup[1] + cupR });
BS_DICE.d10.forEach((x, k) => pieces.push(disc(`d10-${k}`, x, BS_DICE.reach.d10)));
pieces.push(disc("d12", BS_DICE.d12, BS_DICE.reach.d12), disc("d6", BS_DICE.d6, BS_DICE.reach.d6));
assert.ok(cupR <= BS_DICE.reach.cup + 1e-4, "the cup's reach covers its rim");
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
    assert.ok("AB".includes(row(workspaceCell("X", h))), "X in rows A–B");
    assert.ok("CD".includes(row(workspaceCell("Y", h))), "Y in rows C–D");
    assert.ok("IJ".includes(row(workspaceCell("C", h))), "C in rows I–J");
    for (const r of ["X", "Y", "C"]) assert.ok(col(workspaceCell(r, h)) <= 9, "registers in columns 1–9");
}
for (let h = 0; h < 36; h++) assert.ok("EFGH".includes(row(workspaceCell("Strip", h))) && col(workspaceCell("Strip", h)) <= 9, "the strip in E–H");
assert.deepEqual([36, 37].map((h) => [row(workspaceCell("Strip", h)), col(workspaceCell("Strip", h))]), [["I", 1], ["I", 2]], "overflow into row I");
// The overlap, explicitly: strip holes 36–37 are C's holes 0–1 (the strip
// reaches them only while C is empty; bs/expand.test checks every step).
assert.equal(workspaceCell("Strip", 36), workspaceCell("C", 0), "strip hole 36 is C hole 0");
assert.equal(workspaceCell("Strip", 37), workspaceCell("C", 1), "strip hole 37 is C hole 1");
for (let k = 1; k <= 10; k++) assert.equal(col(laneCell(k)), 10, "the control lane is column 10");
assert.equal(row(laneCell(5)), "E");
const all = [];
for (const r of ["X", "Y", "C"]) for (let h = 0; h < 18; h++) all.push(workspaceCell(r, h));
for (let h = 0; h < 36; h++) all.push(workspaceCell("Strip", h));
for (let k = 1; k <= 10; k++) all.push(laneCell(k));
assert.equal(new Set(all).size, 100, "90 register holes and the 10-hole lane: every hole once (SPEC §6)");
const cells = workspaceCells({ x: [1, 2, ...new Array(16).fill(0)], y: new Array(18).fill(0), c: new Array(18).fill(0) }, 1, 2);
assert.deepEqual([cells[0], cells[1], cells[laneCell(5)], cells[laneCell(10)]], [1, 2, 1, 2]);

// ---- the walk cursor: two Destroyers, apart at every key-grid hole ----
const DESTROYER = REAL_SIZES.bsShip.destroyer;
for (let h = 0; h < 100; h++) {
    const { row: r, col: c } = cursorPoses(h);
    const gap = Math.max(c.foot.x0 - r.foot.x1, r.foot.x0 - c.foot.x1, c.foot.z0 - r.foot.z1, r.foot.z0 - c.foot.z1);
    assert.ok(gap > 0, `cursor at hole ${h}: the two Destroyers ${(gap * 1000).toFixed(1)} mm apart`);
    assert.ok(Math.abs(r.foot.z1 - r.foot.z0 - DESTROYER) < 1e-9 && Math.abs(c.foot.x1 - c.foot.x0 - DESTROYER) < 1e-9, "each 27 mm long");
    // Each still spans its own row's / column's hole centre.
    const zRow = BS_GRID.oceanZ0 + Math.floor(h / 10) * BS_GRID.pitch;
    const xCol = BS_GRID.x0 + (h % 10) * BS_GRID.pitch;
    assert.ok(r.foot.z0 < zRow && zRow < r.foot.z1 && c.foot.x0 < xCol && xCol < c.foot.x1, `cursor at hole ${h} marks its row and column`);
    // On the strips, clear of the grid's pegs (Ø 5 mm heads).
    assert.ok(r.foot.x1 < BS_GRID.x0 - 0.0025 && c.foot.z1 < BS_GRID.oceanZ0 - 0.0025, `cursor at hole ${h} off the grid`);
}

// ---- board marks from a generated show ----
const generated = new URL("../bs/generated/_bs_impl.mjs", import.meta.url);
if (!existsSync(generated)) {
    if (process.env.CI) throw new Error("demos/bs/generated missing: run tools/build.sh");
} else {
    const raw = await import(generated);
    const rt = await import(new URL("../bs/generated/_sudo_rt.mjs", import.meta.url));
    const { buildShow, diceFromSeed, runTrace } = await import("../bs/trace.js");
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
        if (st.op === "Call") {
            const after = show.beats[i + 1];
            const last = after?.kind !== "step" || show.steps[after.step].op !== "Call" || after.player !== p;
            assert.equal(marks[p].lane5[i], last ? 0 : 1, "lane hole 5 while calling, lifted after the last call");
        } else if (st.op !== "Clear") {
            assert.equal(marks[p].lane5[i], 0);
        }
        if (st.cell >= 0 && st.op !== "Tidy") {
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
