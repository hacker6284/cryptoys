/**
 * BS unboxing, as plans (no three.js): where the boxes rest on the felt,
 * where everything they hold goes, and every move of the unboxing and the
 * repacking with what stands around it at that moment. The runtime
 * (bs-unbox.js) plays exactly these moves through the library's entries
 * (anim/battleship, anim/yahtzee, anim/dice); bs-layout.test.mjs checks
 * every one of them for overlap and real size, and the rest layout.
 *
 * Unboxing, one move after another (the composition is the hub demo's):
 *   1. the Battleship box's lid off, to its rest;
 *   2. Alice's red unit, then Bob's blue unit, lifted out to their seats;
 *   3. each unit's lid opened (T1: the lid's grid is the workspace);
 *   4. the dice box's lid off, to its rest;
 *   5. the cup (with the dice) lifted out to its spot;
 *   6. the dice, top layer first, out of the cup onto the dice row.
 * Repacking is the same moves backwards.
 */
import { BS_BOX_REST, BS_DICE, BS_DICE_PACK, BS_SEAT_XZ, DEN, TOP_Y } from "./constants.js";
import * as battleship from "../anim/battleship/index.js";
import * as yahtzee from "../anim/yahtzee/index.js";
import * as dice from "../anim/dice/index.js";
import { obbOf, quatRotate } from "../anim/shared/geom.js";

/** The felt a toy is seated on (world.getTablePose: the felt top + 1 mm). */
export const FELT_Y = TOP_Y + 0.032 + 0.001;

const yawQ = (a) => [0, Math.sin(a / 2), 0, Math.cos(a / 2)];
const onFelt = (x, z, yaw = 0) => ({ p: [DEN.x + x, FELT_Y, DEN.z + z], q: yawQ(yaw) });
const add = (a, b) => [a[0] + b[0], a[1] + b[1], a[2] + b[2]];

/**
 * Rest poses on the felt (world): each box's base and its lid, set down by
 * their drawn bottoms (the dice box's lid is drawn 58 mm up its frame: it
 * fits over the top of the base).
 */
export const REST = Object.fromEntries(Object.entries(BS_BOX_REST).map(([k, r]) => [k, onFelt(r.x, r.z, r.yaw)]));
REST.diceLid.p[1] -= yahtzee.box.LID.y0;
/** The seats the contents go to (world.getTablePose's BS layout): the units, the cup, the dice row's origin. */
export const SEATS = {
    units: [onFelt(...BS_SEAT_XZ.bs), onFelt(...BS_SEAT_XZ.bsB)],
    cup: onFelt(...BS_SEAT_XZ.bsCup),
    dice: onFelt(...BS_SEAT_XZ.bsDice),
};
/** The dice, out of the cup in this order (the top layer first); back in, the reverse. */
export const DICE = [["d6", 0], ["d12", 0], ["d10", 4], ["d10", 3], ["d10", 2], ["d10", 1], ["d10", 0]];
const packOf = (kind, k) => (kind === "d10" ? BS_DICE_PACK.d10[k] : BS_DICE_PACK[kind]);
/** The die's x on the dice row (bsDice frame). */
export const rowX = (kind, k) => (kind === "d10" ? BS_DICE.d10[k] : BS_DICE[kind]);

/** A die packed in the cup at `cup` (world; the die in its model's own orientation, turned with the cup). */
export function packedDie(cup, kind, k) {
    return { p: add(cup.p, quatRotate(cup.q, packOf(kind, k))), q: cup.q.slice() };
}

/** A die on its spot in the row: rest(kind, k) → { y: centre above the felt, q: its rotation }. */
export function dieSpot(kind, k, rest) {
    const { y, q } = rest(kind, k);
    return { p: [SEATS.dice.p[0] + rowX(kind, k), FELT_Y + y, SEATS.dice.p[2]], q };
}

// ---- solids: what stands where (anim/shared/geom.js oriented boxes, named) ----

const named = (o, name) => ({ ...o, name });
const CLOSED_DICE_BOX = { min: [-yahtzee.box.LID.hx, 0, -yahtzee.box.LID.hz], max: [yahtzee.box.LID.hx, yahtzee.box.LID.y1, yahtzee.box.LID.hz] };
const CLOSED_NAVAL_BOX = { min: [-battleship.box.LID.hx, 0, -battleship.box.LID.hz], max: [battleship.box.LID.hx, battleship.box.LID.h, battleship.box.LID.hz] };
const CUP_FLOOR_Y = 0.0041;
const CUP_IN_R = 0.0342;

export const solids = {
    navalClosed: (pose = REST.navalBox) => [named(obbOf(pose, CLOSED_NAVAL_BOX), "the Battleship box")],
    navalBase: (pose = REST.navalBox) => battleship.box.baseSolids(pose).map((s) => named(s, `Battleship ${s.name}`)),
    navalLid: (pose = REST.navalLid) => battleship.box.lidSolids(pose).map((s) => named(s, `Battleship ${s.name}`)),
    diceClosed: (pose = REST.diceBox) => [named(obbOf(pose, CLOSED_DICE_BOX), "the dice box")],
    diceBase: (pose = REST.diceBox) => yahtzee.box.baseSolids(pose).map((s) => named(s, `dice ${s.name}`)),
    diceLid: (pose = REST.diceLid) => yahtzee.box.lidSolids(pose).map((s) => named(s, `dice ${s.name}`)),
    unitPacked: (k) => [named(obbOf(battleship.box.pocketPose(REST.navalBox, k), battleship.box.UNIT), `unit ${k} in its box`)],
    unitClosed: (k, pose = SEATS.units[k]) => [named(obbOf(pose, battleship.unit.SHUT), `unit ${k} shut`)],
    unitOpen: (k, pose = SEATS.units[k]) => battleship.unit.OPEN_PARTS.map((s, i) => named(obbOf(pose, s), `unit ${k} ${i ? "lid" : "tray"}`)),
    cupBox: (pose) => [named(obbOf(pose, yahtzee.box.CUP), "the cup")],
    /** The cup as its wall (a ring) and its floor, for what goes in and out of it. */
    cupRing: (pose) => [
        { kind: "cyl", x: pose.p[0], z: pose.p[2], r: 0.0413, rIn: CUP_IN_R, y0: pose.p[1], y1: pose.p[1] + 0.1016, name: "the cup's wall" },
        named(obbOf(pose, { min: [-0.0413, 0, -0.0413], max: [0.0413, CUP_FLOOR_Y, 0.0413] }), "the cup's floor"),
    ],
    die: (pose, kind, name) => [named(obbOf(pose, dice.SHAPES[kind]), name)],
};

/** Each entry's tempo for the unboxing ("unbox") and the repacking ("repack"): its settings' tempos. */
export function tempoOf(entry, phase) {
    const settings = { "battleship/box": battleship.box.settings, "battleship/unit": battleship.unit.settings, "yahtzee/box": yahtzee.box.settings, dice: dice.settings }[entry];
    return settings.tempos?.[phase] ?? 1;
}

/** The cup's rim height at `pose`. */
export const cupRimY = (pose) => pose.p[1] + 0.1016;

/**
 * Every move of the unboxing, in order: { name, entry, plan, solids, check }
 * (solids: what stands still around the mover then; check(): the entry's
 * own checks over that plan). rest: the dice's rest on their row (above).
 */
export function unboxSteps(rest, phase = "unbox") {
    const steps = [];
    const T = (entry) => tempoOf(entry, phase);
    const S = solids;
    const naval = () => [...S.navalBase()];
    // 1. The Battleship lid off (the dice box, still shut, beside it).
    {
        const around = [...naval(), ...S.unitPacked(0), ...S.unitPacked(1), ...S.diceClosed()];
        const plan = battleship.box.planLidOff({ box: REST.navalBox, to: REST.navalLid, solids: around, tempo: T("battleship/box") });
        steps.push({ name: "naval-lid-off", entry: "battleship/box", plan, solids: around });
    }
    // 2. The units out, red then blue.
    {
        const around = [...S.navalLid(), ...S.unitPacked(1), ...S.diceClosed()];
        const plan = battleship.box.planOut({ box: REST.navalBox, k: 0, to: SEATS.units[0], solids: around, tempo: T("battleship/box") });
        steps.push({ name: "unit-0-out", entry: "battleship/box", plan, solids: [...naval(), ...around] });
    }
    {
        const around = [...S.navalLid(), ...S.unitClosed(0), ...S.diceClosed()];
        const plan = battleship.box.planOut({ box: REST.navalBox, k: 1, to: SEATS.units[1], solids: around, tempo: T("battleship/box") });
        steps.push({ name: "unit-1-out", entry: "battleship/box", plan, solids: [...naval(), ...around] });
    }
    // 3. Their lids open.
    {
        const around = [...naval(), ...S.navalLid(), ...S.unitClosed(1), ...S.diceClosed()];
        const plan = battleship.unit.planLid({ pose: SEATS.units[0], from: 0, to: 1, solids: around, tempo: T("battleship/unit") });
        steps.push({ name: "unit-0-open", entry: "battleship/unit", plan, solids: around });
    }
    {
        const around = [...naval(), ...S.navalLid(), ...S.unitOpen(0), ...S.diceClosed()];
        const plan = battleship.unit.planLid({ pose: SEATS.units[1], from: 0, to: 1, solids: around, tempo: T("battleship/unit") });
        steps.push({ name: "unit-1-open", entry: "battleship/unit", plan, solids: around });
    }
    const set = () => [...naval(), ...S.navalLid(), ...S.unitOpen(0), ...S.unitOpen(1)];
    // 4. The dice box's lid off.
    const packedCup = yahtzee.box.pocketPose(REST.diceBox);
    {
        const around = [...set(), ...S.diceBase(), ...S.cupBox(packedCup)];
        const plan = yahtzee.box.planLidOff({ box: REST.diceBox, to: REST.diceLid, solids: around, tempo: T("yahtzee/box") });
        steps.push({ name: "dice-lid-off", entry: "yahtzee/box", plan, solids: around });
    }
    // 5. The cup out.
    {
        const around = [...set(), ...S.diceLid()];
        const plan = yahtzee.box.planOut({ box: REST.diceBox, to: SEATS.cup, solids: around, tempo: T("yahtzee/box") });
        steps.push({ name: "cup-out", entry: "yahtzee/box", plan, solids: [...S.diceBase(), ...around] });
    }
    // 6. The dice onto the row, the top layer first.
    const placed = [];
    DICE.forEach(([kind, k], i) => {
        const still = DICE.slice(i + 1).flatMap(([kd, kk]) => S.die(packedDie(SEATS.cup, kd, kk), kd, `${kd}#${kk} in the cup`));
        const around = [...set(), ...S.diceBase(), ...S.diceLid(), ...S.cupRing(SEATS.cup), ...still, ...placed];
        const plan = dice.planPlace({ kind, from: packedDie(SEATS.cup, kind, k), to: dieSpot(kind, k, rest), clearY: cupRimY(SEATS.cup), solids: around, tempo: T("dice") });
        steps.push({ name: `${kind}-${k}-out`, entry: "dice", plan, solids: around, die: [kind, k], clearY: cupRimY(SEATS.cup) });
        placed.push(...S.die(dieSpot(kind, k, rest), kind, `${kind}#${k} on the row`));
    });
    return steps;
}

/** Every move of the repacking: the unboxing backwards, each move reversed (same path, same law). */
export function repackSteps(rest, phase = "repack") {
    const T = (entry) => tempoOf(entry, phase);
    const steps = [];
    for (const step of unboxSteps(rest, phase).reverse()) {
        const k = Number(step.name[5]);
        const tempo = T(step.entry);
        let plan;
        if (step.entry === "battleship/unit") plan = battleship.unit.planLid({ pose: SEATS.units[k], from: step.plan.fraction, to: 0, solids: step.solids, tempo });
        else if (step.name === "naval-lid-off") plan = battleship.box.planLidOn({ box: REST.navalBox, from: REST.navalLid, solids: step.solids, tempo });
        else if (step.name.startsWith("unit-")) plan = battleship.box.planIn({ box: REST.navalBox, k, from: SEATS.units[k], solids: step.solids.filter((s) => !s.name.startsWith("Battleship box")), tempo });
        else if (step.name === "dice-lid-off") plan = yahtzee.box.planLidOn({ box: REST.diceBox, from: REST.diceLid, solids: step.solids, tempo });
        else if (step.name === "cup-out") plan = yahtzee.box.planIn({ box: REST.diceBox, from: SEATS.cup, solids: step.solids.filter((s) => !s.name.startsWith("dice box")), tempo });
        else {
            const [kind, kk] = step.die;
            plan = dice.planPlace({ kind, from: dieSpot(kind, kk, rest), to: packedDie(SEATS.cup, kind, kk), clearY: step.clearY, solids: step.solids, tempo });
        }
        steps.push({ ...step, name: step.name.replace(/-out$/, "-in").replace(/-off$/, "-on").replace(/-open$/, "-close"), plan });
    }
    return steps;
}

/** Total ms of a step list played one after another (at the tempos it was planned at). */
export const stepsMs = (steps) => steps.reduce((t, s) => t + s.plan.ms, 0);
