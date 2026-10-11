// BS unboxing at run time (bs-unbox.js) on stand-in scene objects
// (three-mini.mjs): packed at once, a snapped unboxing ends exactly where
// the plan's moves end, the repacking (the moves reversed) ends exactly
// packed, and leaving mid-unbox repacks only the moves done (or packs at
// once when snapped).
import assert from "node:assert/strict";
import { Group, Quaternion, Scene, Vector3, glbMesh } from "./three-mini.mjs";
import { createBsUnbox } from "./bs-unbox.js";
import * as P from "./bs-unbox-plan.js";
import * as battleship from "../anim/battleship/index.js";
import * as yahtzee from "../anim/yahtzee/index.js";
import { setWorldPose } from "../anim/shared/run.js";
import { stubThree } from "./three-stub.mjs";

stubThree();
const { BS_MODELS } = await import("./bs-stage.js");

const meshes = Object.fromEntries(["d10", "d12", "d6"].map((kind) => [kind, glbMesh(new URL(`../bs/assets/models/${BS_MODELS[kind]}`, import.meta.url))]));
const rest = P.makeDieRest((kind) => meshes[kind], Quaternion, Vector3);

function named(name, parent) {
    const g = new Group();
    g.name = name;
    parent?.add(g);
    return g;
}

/** A scene with both boxes at their rest on the felt and every rig BS has. */
function makeRigs() {
    const scene = new Scene();
    scene.name = "scene";
    const box = (name, pose) => {
        const group = named(name, scene);
        setWorldPose(group, pose);
        return { group, lid: named(`${name}-lid`, group) };
    };
    const units = [0, 1].map((k) => {
        const group = named(`unit-${k}`, scene);
        return { group, lid: named(`unit-${k}-lid`, group) };
    });
    const rigs = {
        naval: box("naval", P.REST.navalBox),
        diceBox: box("diceBox", P.REST.diceBox),
        units,
        cup: named("cup", scene),
        diceRow: named("diceRow"),
        dice: { d10: [0, 1, 2, 3, 4].map((k) => named(`d10#${k}`)), d12: named("d12#0"), d6: named("d6#0") },
    };
    return { scene, rigs };
}

const all = (rigs) => [
    rigs.naval.lid, rigs.diceBox.lid, ...rigs.units.flatMap((u) => [u.group, u.lid]), rigs.cup, rigs.diceRow,
    ...rigs.dice.d10, rigs.dice.d12, rigs.dice.d6,
];
/** Every rig's parent and world pose (the dice row's pose only while it is in the scene). */
const state = (rigs) => all(rigs).map((o) => ({ name: o.name, parent: o.parent?.name ?? null, ...(o.parent ? o.world() : { p: [], q: [] }) }));
const near = (a, b, eps = 1e-9) => a.every((v, i) => Math.abs(v - b[i]) < eps);
const sameQ = (a, b, eps = 1e-9) => near(a, b, eps) || near(a, b.map((v) => -v), eps);
function assertState(got, want, what) {
    got.forEach((g, i) => {
        const w = want[i];
        assert.equal(g.parent, w.parent, `${what}: ${g.name} in ${w.parent}`);
        assert.ok(near(g.p, w.p) && sameQ(g.q, w.q), `${what}: ${g.name} where it was packed`);
    });
}
const dieOf = (rigs, kind, k) => (kind === "d10" ? rigs.dice.d10[k] : rigs.dice[kind]);
/** A snapped clock that counts the moves it plays. */
function snapRun() {
    const run = (ms, step) => {
        run.calls += 1;
        step(ms);
        run.onCall?.(run.calls);
        return Promise.resolve(true);
    };
    run.calls = 0;
    return run;
}

// ---- packNow: everything in its box ----
const { scene, rigs } = makeRigs();
const box = createBsUnbox({ scene, rigs, rest });
box.packNow();
assert.equal(box.packed, true);
for (const r of [rigs.naval, rigs.diceBox]) {
    assert.equal(r.lid.parent, r.group, "the lid on its box");
    assert.ok(near(r.lid.position.toArray(), [0, 0, 0]) && near([r.lid.quaternion.x, r.lid.quaternion.y, r.lid.quaternion.z, r.lid.quaternion.w], [0, 0, 0, 1]), "at its origin");
}
rigs.units.forEach((u, k) => {
    assert.equal(u.group.parent, rigs.naval.group, `unit ${k} in the Battleship box`);
    const want = battleship.box.pocketPose(P.REST.navalBox, k);
    assert.ok(near(u.group.world().p, want.p) && sameQ(u.group.world().q, want.q), `unit ${k} in its pocket`);
    assert.equal(u.lid.quaternion.w, 1, `unit ${k} shut`);
});
assert.ok(rigs.cup.parent === rigs.diceBox.group, "the cup in the dice box");
{
    const want = yahtzee.box.pocketPose(P.REST.diceBox);
    assert.ok(near(rigs.cup.world().p, want.p) && sameQ(rigs.cup.world().q, want.q), "lying in its well");
}
for (const [kind, k] of P.DICE) {
    const d = dieOf(rigs, kind, k);
    assert.ok(d.parent === rigs.diceBox.group, `${kind}#${k} in the dice box`);
    assert.ok(near(d.position.toArray(), P.packOf(kind, k)), `${kind}#${k} in its place there`);
}
assert.equal(rigs.diceRow.parent, null, "the empty dice row out of the scene");
const packed = state(rigs);
box.packNow();
assertState(state(rigs), packed, "packNow twice");
assert.equal(scene.children.filter((c) => c.name === "diceRow").length, 0, "no dice row left in the scene");

// ---- a snapped unboxing ends where the plan's moves end ----
const steps = P.unboxSteps(rest);
const end = (name) => steps.find((s) => s.name === name).plan.to;
{
    const run = snapRun();
    await box.unbox(run);
    assert.equal(box.packed, false);
    assert.equal(run.calls, steps.length, "every move played once");
    const at = (o, pose, what) => assert.ok(near(o.world().p, pose.p) && sameQ(o.world().q, pose.q), what);
    at(rigs.naval.lid, end("naval-lid-off"), "the Battleship lid at its rest");
    at(rigs.naval.lid, P.REST.navalLid, "(BS_BOX_REST)");
    at(rigs.diceBox.lid, end("dice-lid-off"), "the dice box's lid at its rest");
    at(rigs.diceBox.lid, P.REST.diceLid, "(BS_BOX_REST)");
    rigs.units.forEach((u, k) => {
        at(u.group, end(`unit-${k}-out`), `unit ${k} at its seat`);
        at(u.group, P.SEATS.units[k], "(its T1 seat)");
        const open = steps.find((s) => s.name === `unit-${k}-open`).plan;
        assert.ok(Math.abs(2 * Math.acos(u.lid.quaternion.w) - open.to) < 1e-9 && open.to > 1.5, `unit ${k}'s lid open (${open.to.toFixed(3)} rad)`);
    });
    at(rigs.cup, end("cup-out"), "the cup at its spot");
    assert.equal(rigs.diceRow.parent, scene, "the dice row on the felt");
    at(rigs.diceRow, P.SEATS.dice, "at its seat");
    for (const [kind, k] of P.DICE) {
        const d = dieOf(rigs, kind, k);
        assert.equal(d.parent, rigs.diceRow, `${kind}#${k} on the row`);
        at(d, end(`${kind}-${k}-out`), `${kind}#${k} on its spot`);
        at(d, P.dieSpot(kind, k, rest), "(dieSpot)");
        assert.ok(Math.abs(d.position.x - P.rowX(kind, k)) < 1e-12 && Math.abs(d.position.z) < 1e-12, "exactly on its row x");
    }
    assert.ok(Math.abs(box.repackMs() - P.stepsMs(P.repackSteps(rest))) < 1e-9, "repacking all: every move backwards");
    // The steps reversed bring everything back exactly as packNow lays it.
    const back = snapRun();
    for (const s of P.reverseSteps(steps)) await s.play(rigs, { run: back });
    assert.equal(back.calls, steps.length);
    assert.equal(rigs.diceRow.children.length, 0, "the row empty");
    rigs.diceRow.removeFromParent(); // (packNow's own tidying)
    assertState(state(rigs), packed, "the moves reversed");
}

// ---- repack: equal to packNow ----
{
    box.packNow();
    await box.unbox(snapRun());
    const run = snapRun();
    await box.repack(run);
    assert.equal(run.calls, steps.length, "repack plays every move backwards");
    assert.equal(box.packed, true);
    assertState(state(rigs), packed, "repack");
    assert.equal(rigs.diceRow.parent, null, "the dice row gone again");
}

// ---- leaving mid-unbox: only the moves done, backwards ----
{
    const run = snapRun();
    run.onCall = (n) => n === 3 && box.cancel(); // during the third move (unit 1 out)
    await box.unbox(run);
    assert.equal(run.calls, 3, "it stops after the move in progress");
    assert.equal(rigs.units[0].group.parent, scene, "unit 0 out");
    assert.equal(rigs.units[1].group.parent, scene, "unit 1 out (its move finished)");
    assert.equal(rigs.units[0].lid.quaternion.w, 1, "but not opened");
    assert.ok(rigs.cup.parent === rigs.diceBox.group, "the cup still in its box");
    const done = steps.slice(0, 3);
    assert.ok(Math.abs(box.repackMs() - P.stepsMs(P.reverseSteps(done))) < 1e-9, "repacking only what was done");
    const back = snapRun();
    await box.repack(back);
    assert.equal(back.calls, 3, "three moves back");
    assertState(state(rigs), packed, "repacked after a cancel");
}
{
    // Cancelled during a die's move, snapped: packed at once.
    const run = snapRun();
    run.onCall = (n) => n === 9 && box.cancel();
    await box.unbox(run);
    assert.equal(run.calls, 9);
    assert.ok(rigs.dice.d12.parent === rigs.diceRow, "the d12 on its row");
    assert.ok(rigs.dice.d10[4].parent === rigs.diceBox.group, "the fifth d10 still in the box");
    const back = snapRun();
    await box.repack(back, { snap: true });
    assert.equal(back.calls, 0, "snapped: no moves");
    assertState(state(rigs), packed, "snapped repack");
}
{
    // A cancel while a move plays on a slow clock: repack waits for it, then reverses it.
    let release;
    const slow = (ms, step) => new Promise((resolve) => {
        release = () => { step(ms); resolve(true); };
    });
    const unboxing = box.unbox(slow);
    await Promise.resolve();
    box.cancel();
    const back = snapRun();
    const repacking = box.repack(back);
    release();
    await unboxing;
    await repacking;
    assert.equal(back.calls, 1, "the one move in progress, backwards");
    assertState(state(rigs), packed, "repacked after a slow cancel");
}
console.log("bs unbox tests ok");
