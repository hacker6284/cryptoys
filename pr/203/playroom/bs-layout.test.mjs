// BS on the table: the real-size layout (no overlap, on the felt, on the
// shelf clear of the room), the retail boxes and every move of their
// unboxing and repacking (real size, no overlap at any moment, the empty
// boxes at rest in view), the T1 workspace on the lid grid (SPEC §6) and
// the board marks the view draws from the generated trace.
import assert from "node:assert/strict";
import { existsSync, readFileSync } from "node:fs";
import { BS_BOX_REST, BS_CHEST, BS_DICE, BS_DIE_LIFT, BS_GAP, BS_GRID, BS_SEAT_XZ, BS_SHELF, BS_UNIT_FOOT, DEN, MINX_SPAN, REAL_SIZES, SHELF_TOP, TABLE_R } from "./constants.js";
import { Quaternion, Vector3, glbMesh } from "./three-mini.mjs";
import { CHEST as CHEST_DRAWN, ROOM } from "../anim/shared/room.js";
import { stubThree } from "./three-stub.mjs";

stubThree();
const { BS_MODELS, workspaceCell, laneCell, workspaceCells, boardMarks, cursorPoses, diceFacesAt, cupFaces } = await import("./bs-stage.js");

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
// The retail boxes, and the library's constants for them, from the models.
assert.deepEqual(glbBounds(BS_MODELS.navalBox), [400, 52.5, 265], "Battleship box: 400 × 265 × 52.5 mm closed");
assert.deepEqual(glbBounds(BS_MODELS.navalBox, "navalbox_lid"), [400, 52.5, 265], "its lid is the whole box's outside");
assert.deepEqual(glbBounds(BS_MODELS.navalBox, "navalbox_base"), [396.4, 50.7, 261.4], "its base, 1.5 mm inside the lid");
assert.deepEqual(glbBounds(BS_MODELS.diceBox), [248, 108, 163], "dice box: 248 × 163 × 108 mm closed");
assert.deepEqual(glbBounds(BS_MODELS.diceBox, "dicebox_base"), [245, 102.5, 160], "its base holds the 101.6 mm cup standing");
assert.deepEqual(glbBounds(BS_MODELS.diceBox, "dicebox_lid"), [248, 50, 163], "its lid, 50 mm deep");

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

// ---- the shelf: the Battleship box lying flat, clear of the room ----
// (15 mm from everything; 7.5 mm from the backboard: the board is 280 mm
// deep, the box 265 mm.)
const shelf = { x0: BS_SHELF.x - 0.2, x1: BS_SHELF.x + 0.2, z0: BS_SHELF.z - 0.1325, z1: BS_SHELF.z + 0.1325, y0: SHELF_TOP, y1: SHELF_TOP + 0.0525 };
for (const s of ROOM.filter((r) => r.kind === "box" && r.name !== "shelf-top")) {
    const lo = s.c.map((c, k) => c - s.he[k]);
    const hi = s.c.map((c, k) => c + s.he[k]);
    const apart = Math.max(lo[0] - shelf.x1, shelf.x0 - hi[0], lo[1] - shelf.y1, shelf.y0 - hi[1], lo[2] - shelf.z1, shelf.z0 - hi[2]);
    assert.ok(apart >= (s.name === "shelf-back" ? 0.0075 - 1e-9 : 0.015), `shelf box clear of ${s.name} (${(apart * 1000).toFixed(1)} mm)`);
}
assert.ok(shelf.z0 > -2.28 && shelf.z1 < -2.0, "on the shelf board, in front of the backboard");

// ---- the chest: the dice box waits in it, shut ----
// Where world.getChestPose lays it: the row's spot (42 % across the
// chest's drawn box in x, 52 % in z) moved by BS_CHEST, 55 mm up its
// floor, turned π/2 + 0.1. Inside the cavity (10 mm from its walls, under
// its rim, so the lid shuts over it) and clear of the row down the
// middle (half the widest toy in it, 15 mm more).
{
    const yahtzee = await import("../anim/yahtzee/index.js");
    const geom = await import("../anim/shared/geom.js");
    const { outer: o, inner: cav } = CHEST_DRAWN;
    const row = { x: o.min[0] * 0.42 + o.max[0] * 0.58, z: o.min[2] * 0.52 + o.max[2] * 0.48 };
    const yaw = Math.PI / 2 + 0.1;
    const at = { p: [row.x + BS_CHEST.dx, o.min[1] + 0.055, row.z + BS_CHEST.dz], q: [0, Math.sin(yaw / 2), 0, Math.cos(yaw / 2)] };
    const L = yahtzee.box.LID;
    const shut = geom.obbOf(at, { min: [-L.hx, 0, -L.hz], max: [L.hx, L.y1, L.hz] });
    const cs = geom.obbCorners(shut);
    for (const c of cs) {
        assert.ok(c[0] >= cav.min[0] + 0.01 && c[0] <= cav.max[0] - 0.01 && c[2] >= cav.min[2] + 0.01 && c[2] <= cav.max[2] - 0.01, `the dice box inside the chest's walls (${c[0].toFixed(3)}, ${c[2].toFixed(3)})`);
        assert.ok(c[1] >= cav.min[1] - 1e-9 && c[1] <= cav.max[1] - 0.01, `the dice box above the chest's floor, under its rim (${c[1].toFixed(3)})`);
    }
    const rowHalf = Math.max(MINX_SPAN, REAL_SIZES.deckBox.w, REAL_SIZES.deckBox.h, REAL_SIZES.deckBox.d) / 2;
    const gap = row.x - Math.max(...cs.map((c) => c[0]));
    assert.ok(gap >= rowHalf + 0.015, `the dice box clear of the chest's row (${(gap * 1000).toFixed(0)} mm from its line)`);
}

// ---- the unboxing: every move, at every moment ----
{
    const P = await import("./bs-unbox-plan.js");
    const { checkHop } = await import("../anim/shared/hop.js");
    const battleship = await import("../anim/battleship/index.js");
    const yahtzee = await import("../anim/yahtzee/index.js");
    const dice = await import("../anim/dice/index.js");
    const geom = await import("../anim/shared/geom.js");
    const { POSES } = await import("./poses.js");

    // The library's box constants are the models'.
    assert.deepEqual([battleship.box.LID.hx * 2, battleship.box.LID.h, battleship.box.LID.hz * 2].map((v) => +(v * 1000).toFixed(1)), [400, 52.5, 265]);
    assert.deepEqual([battleship.box.BASE.hx * 2, battleship.box.BASE.h, battleship.box.BASE.hz * 2].map((v) => +(v * 1000).toFixed(1)), [396.4, 50.7, 261.4]);
    assert.deepEqual([yahtzee.box.LID.hx * 2, yahtzee.box.LID.y1 - yahtzee.box.LID.y0, yahtzee.box.LID.hz * 2].map((v) => +(v * 1000).toFixed(1)), [248, 50, 163]);
    assert.deepEqual([yahtzee.box.BASE.hx * 2, yahtzee.box.BASE.h, yahtzee.box.BASE.hz * 2].map((v) => +(v * 1000).toFixed(1)), [245, 102.5, 160]);
    assert.deepEqual(battleship.box.UNIT, { min: [-0.115, 0, -0.0854], max: [0.115, 0.0351, 0.086] }, "a closed unit, 230 × 35.1 × 171.4 mm");
    assert.deepEqual(battleship.unit.OPEN, { min: [-0.115, 0, -0.0901], max: [0.115, 0.177, 0.0834] }, "an open unit, as its GLB");
    for (const [kind, mm] of [["d10", [20.2, 22, 21.1]], ["d12", [19, 19, 19]], ["d6", [16, 16, 16]]]) {
        assert.deepEqual(dice.SHAPES[kind].max.map((v, k) => +((v - dice.SHAPES[kind].min[k]) * 1000).toFixed(1)), mm, `${kind}: as its model`);
    }

    // Packed: each unit in the box, the cup in the dice box, the dice in the cup, nothing overlapping.
    const N = battleship.box;
    for (const k of [0, 1]) {
        const u = geom.obbOf(N.pocketPose(P.REST.navalBox, k), N.UNIT);
        assert.ok(geom.worstDepth(u, N.baseSolids(P.REST.navalBox), 0).depth <= 5e-4, `unit ${k} fits its pocket (on its floor)`);
        assert.ok(geom.obbMaxY(u) < P.REST.navalBox.p[1] + N.LID.h - N.LID.top, `unit ${k} under the lid`);
    }
    assert.ok(geom.obbDepth(geom.obbOf(N.pocketPose(P.REST.navalBox, 0), N.UNIT), geom.obbOf(N.pocketPose(P.REST.navalBox, 1), N.UNIT)) < 0, "the units apart in the box");
    const Y = yahtzee.box;
    const cupIn = Y.pocketPose(P.REST.diceBox);
    assert.ok(geom.worstDepth(geom.obbOf(cupIn, Y.CUP), Y.baseSolids(P.REST.diceBox), 0).depth <= 5e-4, "the cup stands in the dice box (on its floor)");
    assert.ok(cupIn.p[1] + Y.CUP.max[1] < P.REST.diceBox.p[1] + Y.LID.y1 - Y.LID.top, "the cup under the lid");
    const packed = P.DICE.map(([kind, k]) => ({ kind, k, o: geom.obbOf(P.packedDie(P.SEATS.cup, kind, k), dice.SHAPES[kind]) }));
    for (const a of packed) {
        assert.ok(geom.worstDepth(a.o, P.solids.cupRing(P.SEATS.cup), 0).depth <= 5e-4, `${a.kind}#${a.k} inside the cup`);
        for (const b of packed) if (a !== b) assert.ok(geom.obbDepth(a.o, b.o) <= 0, `${a.kind}#${a.k} and ${b.kind}#${b.k} apart in the cup`);
    }

    // A die's rest on its row: the stage's own rest(kind, k) (bs-unbox-plan.js
    // makeDieRest: dice.restHeight of the drawn die showing its face), on
    // the dice models themselves.
    const meshes = Object.fromEntries(["d10", "d12", "d6"].map((kind) => [kind, glbMesh(new URL(`../bs/assets/models/${BS_MODELS[kind]}`, import.meta.url))]));
    const rest = P.makeDieRest((kind) => meshes[kind], Quaternion, Vector3);
    for (const [kind, k] of P.DICE) {
        // Its lowest drawn point (every vertex turned to its rest) is BS_DIE_LIFT above the felt.
        const { p, q } = P.dieSpot(kind, k, rest);
        const m = meshes[kind];
        const mq = [m.quaternion.x, m.quaternion.y, m.quaternion.z, m.quaternion.w];
        const pos = m.geometry.attributes.position;
        let low = Infinity;
        for (let i = 0; i < pos.count; i++) {
            const v = geom.quatRotate(geom.quatMul(q, mq), [pos.getX(i) * m.scale.x, pos.getY(i) * m.scale.y, pos.getZ(i) * m.scale.z]);
            low = Math.min(low, p[1] + v[1]);
        }
        assert.ok(Math.abs(low - (P.FELT_Y + BS_DIE_LIFT)) < 1e-6, `${kind}#${k} rests on the felt by its drawn bottom (${((low - P.FELT_Y) * 1000).toFixed(3)} mm)`);
    }

    // Every move of the unboxing and the repacking, at the tempo it plays:
    // on its law, ends exact, nothing jumps, no overlap with anything that
    // stands around it then (touching, ≤ 0.5 mm, is not overlapping).
    const unit = battleship.unit;
    const steps = { unbox: P.unboxSteps(rest), repack: P.repackSteps(rest) };
    for (const [phase, list] of Object.entries(steps)) {
        assert.equal(list.length, 14, `${phase}: 14 moves`);
        for (const step of list) {
            const r = step.entry === "battleship/unit" ? unit.checkLid(step.plan, P.tempoOf(step.entry, phase)) : checkHop(step.plan, { solids: step.solids });
            assert.ok(r.ok, `${phase} ${step.name}: ${r.fail.join("; ")}`);
            if (step.entry === "battleship/unit") assert.equal(step.plan.stopped, null, `${step.name}: the lid swings all the way`);
        }
    }
    assert.deepEqual(steps.unbox.map((s) => s.name).slice(0, 7), ["naval-lid-off", "unit-0-out", "unit-1-out", "unit-0-open", "unit-1-open", "dice-lid-off", "cup-out"]);
    const at = (name) => steps.unbox.find((s) => s.name === name).plan;
    const near = (a, b) => Math.hypot(a[0] - b[0], a[1] - b[1], a[2] - b[2]) < 1e-9;
    assert.ok(near(at("unit-0-out").to.p, P.SEATS.units[0].p) && near(at("unit-1-out").to.p, P.SEATS.units[1].p), "the units go to their T1 seats");
    assert.ok(near(at("cup-out").to.p, P.SEATS.cup.p), "the cup to its spot");
    assert.ok(P.stepsMs(steps.unbox) < 10000 && P.stepsMs(steps.repack) < 7000, `unboxing ${P.stepsMs(steps.unbox).toFixed(0)} ms, repacking ${P.stepsMs(steps.repack).toFixed(0)} ms`);

    // At rest: everything on the felt by its drawn bottom, nothing overlapping
    // (15 mm apart; two dice's drawn boxes 2 mm: their reach, above, keeps
    // 6.5 mm), on the felt, the boxes where
    // the director sets them down (BS_BOX_REST).
    const S = P.solids;
    const restSet = [
        ["Battleship base", S.navalBase()], ["Battleship lid", S.navalLid()], ["dice box base", S.diceBase()], ["dice box lid", S.diceLid()],
        ["red unit", S.unitOpen(0)], ["blue unit", S.unitOpen(1)], ["cup", S.cupBox(P.SEATS.cup)],
        ...P.DICE.map(([kind, k]) => [`${kind}#${k}`, S.die(P.dieSpot(kind, k, rest), kind, kind), true]),
    ];
    for (const [name, parts, isDie] of restSet) {
        // (A die's drawn box reaches below its drawn bottom, checked above on its vertices.)
        const bottom = Math.min(...parts.map(geom.obbMinY));
        if (!isDie) assert.ok(Math.abs(bottom - P.FELT_Y) < 2.5e-4, `${name} rests on the felt (${((bottom - P.FELT_Y) * 1000).toFixed(2)} mm)`);
        for (const p of parts) for (const c of geom.obbCorners(p)) assert.ok(Math.hypot(c[0] - DEN.x, c[2] - DEN.z) < TABLE_R - 0.08 - 0.05, `${name} on the felt`);
    }
    for (let i = 0; i < restSet.length; i++) for (let j = i + 1; j < restSet.length; j++) {
        const [an, ap] = restSet[i];
        const [bn, bp] = restSet[j];
        const dice2 = i >= 7 && j >= 7;
        let d = -Infinity;
        for (const a of ap) for (const b of bp) d = Math.max(d, geom.obbDepth(a, b));
        assert.ok(d <= -(dice2 ? 0.002 : 0.015) + 1e-9, `${an} and ${bn} ${(-d * 1000).toFixed(1)} mm apart`);
    }
    for (const [key, r] of Object.entries(BS_BOX_REST)) {
        assert.ok(Math.abs(P.REST[key].p[0] - (DEN.x + r.x)) < 1e-12 && Math.abs(P.REST[key].p[2] - (DEN.z + r.z)) < 1e-12, `${key} rests at BS_BOX_REST`);
    }

    // In view at rest: every piece inside the BS seat's frame (1440 × 900,
    // left of the 352 px dock; phones 390 × 844, across), and each empty box
    // and lid seen from the seat: no other piece in front of its top corners
    // or the middle of its front edge.
    const camera = (pose) => {
        const f0 = pose.target.map((v, k) => v - pose.position[k]);
        const f = f0.map((v) => v / Math.hypot(...f0));
        const r0 = [-f[2], 0, f[0]];
        const r = r0.map((v) => v / Math.hypot(...r0));
        const u = geom.cross(r, f);
        const t = Math.tan((pose.fov * Math.PI) / 360);
        return (p, W, H) => {
            const d = p.map((v, k) => v - pose.position[k]);
            const z = geom.dot(d, f);
            return [((geom.dot(d, r) / (z * t * W / H)) + 1) / 2 * W, (1 - geom.dot(d, u) / (z * t)) / 2 * H];
        };
    };
    const corners = restSet.flatMap(([, parts]) => parts.flatMap(geom.obbCorners));
    const land = camera(POSES.bs);
    for (const c of corners) {
        const [x, y] = land(c, 1440, 900);
        assert.ok(x > 16 && x < 1440 - 352 - 16 && y > 16 && y < 900 - 16, `in the BS frame left of the dock (${x.toFixed(0)}, ${y.toFixed(0)})`);
    }
    const phone = camera({ ...POSES.bs, ...POSES.bs.portrait });
    for (const c of corners) {
        const [x, y] = phone(c, 390, 844);
        assert.ok(x > 4 && x < 386 && y > 16 && y < 844 * 0.6, `in the phone frame above the dock (${x.toFixed(0)}, ${y.toFixed(0)})`);
    }
    // A ray from the eye to a point is blocked by an oriented box if it passes through it (slab test).
    const blocks = (o, from, to) => {
        let t0 = 0, t1 = 1;
        const d = to.map((v, k) => v - from[k]);
        const rel = from.map((v, k) => v - o.c[k]);
        for (let a = 0; a < 3; a++) {
            const e = geom.dot(o.axes[a], rel), g = geom.dot(o.axes[a], d);
            const lo = -o.he[a], hi = o.he[a];
            if (Math.abs(g) < 1e-12) {
                if (e < lo || e > hi) return false;
                continue;
            }
            let ta = (lo - e) / g, tb = (hi - e) / g;
            if (ta > tb) [ta, tb] = [tb, ta];
            t0 = Math.max(t0, ta);
            t1 = Math.min(t1, tb);
            if (t0 > t1) return false;
        }
        return t1 > 1e-6 && t0 < 1 - 1e-6;
    };
    const eye = POSES.bs.position;
    for (const [name, shape, pose] of [["Battleship base", { min: [-0.1982, 0, -0.1307], max: [0.1982, 0.0507, 0.1307] }, P.REST.navalBox], ["Battleship lid", { min: [-0.2, 0, -0.1325], max: [0.2, 0.0525, 0.1325] }, P.REST.navalLid], ["dice box base", { min: [-0.1225, 0, -0.08], max: [0.1225, 0.1025, 0.08] }, P.REST.diceBox], ["dice box lid", { min: [-0.124, 0.058, -0.0815], max: [0.124, 0.108, 0.0815] }, P.REST.diceLid]]) {
        const o = geom.obbOf(pose, shape);
        const top = geom.obbCorners(o).filter((c) => c[1] > o.c[1]);
        // The middle of its edge nearest the seat, at the felt.
        const front = top.slice().sort((a, b) => b[2] - a[2]).slice(0, 2);
        const mid = [(front[0][0] + front[1][0]) / 2, P.FELT_Y + 0.002, (front[0][2] + front[1][2]) / 2];
        const shrink = (p) => p.map((v, k) => v + (o.c[k] - v) * 0.01);
        const others = restSet.filter(([n]) => n !== name).flatMap(([, parts]) => parts);
        for (const p of [...top, mid].map(shrink)) for (const b of others) assert.ok(!blocks(b, eye, p), `${name} seen from the seat (${b.name} in the way)`);
    }
}
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
    // Dice: the last row cup's five faces, the last d12 and d6.
    const lastBuild = 199;
    const faces = diceFacesAt(show, lastBuild);
    assert.equal(faces.d10.length, 5);
    assert.ok(faces.d10.every((f) => f >= 1 && f <= 9));
    const cups = show.reads[1].filter((r) => r.cup.length);
    assert.deepEqual(faces.d10, cupFaces(cups.at(-1)), "the last cup's dice, each at its last generated Throw");
    assert.deepEqual(diceFacesAt(show, -1), { d10: [1, 2, 3, 4, 5], d12: 12, d6: 6 }, "at rest before BUILD");
}

console.log("bs layout tests ok");
