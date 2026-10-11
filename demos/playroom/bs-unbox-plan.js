/**
 * BS unboxing, as steps (no three.js): where the boxes rest on the felt,
 * where everything they hold goes, and every move of the unboxing with
 * what stands around it at that moment. Each step carries its own
 * behaviour: { name, entry, plan, solids, play(rigs, opts), reverse(tempo) }
 * — play runs the move through its library entry (anim/battleship,
 * anim/yahtzee, anim/dice) on the rigs, reverse(tempo) is the same move
 * backwards as a step of its own. The runtime (bs-unbox.js) only plays
 * steps; bs-layout.test.mjs checks every plan for overlap and real size,
 * and the rest layout.
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
import { BS_BOX_REST, BS_DICE, BS_DICE_PACK, BS_DICE_FACES, BS_DICE_YAW, BS_DIE_LIFT, BS_SEAT_XZ, DEN, TABLE_SEAT_Y } from "./constants.js";
import * as battleship from "../anim/battleship/index.js";
import * as yahtzee from "../anim/yahtzee/index.js";
import * as dice from "../anim/dice/index.js";
import { add, obbOf, quatRotate } from "../anim/shared/geom.js";
import { cupRimY, cupSolids } from "../anim/shared/cup.js";

/** The felt a toy is seated on: world.getTablePose's seat height (constants.js TABLE_SEAT_Y, the felt top + 1 mm). */
export const FELT_Y = TABLE_SEAT_Y;

const yawQ = (a) => [0, Math.sin(a / 2), 0, Math.cos(a / 2)];
const onFelt = (x, z, yaw = 0) => ({ p: [DEN.x + x, FELT_Y, DEN.z + z], q: yawQ(yaw) });

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
/** A die's place in the cup (cup frame, the die unturned): constants.js BS_DICE_PACK. */
export const packOf = (kind, k) => (kind === "d10" ? BS_DICE_PACK.d10[k] : BS_DICE_PACK[kind]);
/** The die's x on the dice row (bsDice frame). */
export const rowX = (kind, k) => (kind === "d10" ? BS_DICE.d10[k] : BS_DICE[kind]);

/** A die packed in the cup at `cup` (world; the die in its model's own orientation, turned with the cup). */
export function packedDie(cup, kind, k) {
    return { p: add(cup.p, quatRotate(cup.q, packOf(kind, k))), q: cup.q.slice() };
}

/** The face a die shows on its row spot and its yaw there (constants.js). */
export const dieFace = (kind, k) => (kind === "d10" ? BS_DICE_FACES.d10[k] : BS_DICE_FACES[kind]);
export const dieYaw = (kind, k) => (kind === "d10" ? BS_DICE_YAW.d10[k] : BS_DICE_YAW[kind]);

/**
 * The dice's rest on their row, one pure rest(kind, k) → { y: the centre
 * above the felt, q: the rotation } for the stage and the tests alike:
 * dice.restHeight of the die's drawn mesh showing its face (lifted
 * BS_DIE_LIFT), turned by dice.restQuaternion. meshOf(kind, k): the die's
 * mesh (geometry, scale, quaternion); Q, V: three's Quaternion, Vector3.
 */
export function makeDieRest(meshOf, Q, V) {
    const cache = new Map();
    return (kind, k) => {
        const key = `${kind}#${k}`;
        if (!cache.has(key)) {
            const face = dieFace(kind, k);
            const q = dice.restQuaternion(kind, face, dieYaw(kind, k), Q, V);
            cache.set(key, { y: dice.restHeight(meshOf(kind, k), kind, face, Q, V) + BS_DIE_LIFT, q: [q.x, q.y, q.z, q.w] });
        }
        return cache.get(key);
    };
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
    /** The cup as its wall (a ring) and its floor, for what goes in and out of it (anim/shared/cup.js). */
    cupRing: (pose) => cupSolids(pose),
    die: (pose, kind, name) => [named(obbOf(pose, dice.SHAPES[kind]), name)],
};

/** Each entry's tempo for the unboxing ("unbox") and the repacking ("repack"): its settings' tempos. */
export function tempoOf(entry, phase) {
    const settings = { "battleship/box": battleship.box.settings, "battleship/unit": battleship.unit.settings, "yahtzee/box": yahtzee.box.settings, dice: dice.settings }[entry];
    return settings.tempos?.[phase] ?? 1;
}

/**
 * One move as a step, either way round (way 0: as unboxed, way 1: back):
 * names [out, back]; plan(way, tempo) → the entry's plan; play(way, rigs,
 * opts) → the entry's live move (opts: { run, tempo }). Its reverse is the
 * other way at the given tempo; reversed again, the first way.
 */
function moveStep(move, tempo, way = 0) {
    const { names, entry, solids, plan, play, ...more } = move;
    return {
        name: names[way],
        entry,
        solids,
        ...more,
        plan: plan(way, tempo),
        play: (rigs, opts = {}) => play(way, rigs, { ...opts, tempo }),
        reverse: (t) => moveStep(move, t, 1 - way),
    };
}

const dieOf = (rigs, kind, k) => (kind === "d10" ? rigs.dice.d10[k] : rigs.dice[kind]);

/**
 * Every move of the unboxing, in order, as steps: { name, entry, plan,
 * solids, play(rigs, opts), reverse(tempo) } (solids: what stands still
 * around the mover then, the base it leaves included). rest: the dice's
 * rest on their row (makeDieRest). rigs (for play): { naval, diceBox:
 * { group, lid }, units: [{ group, lid }], cup, diceRow, dice: { d10: [× 5],
 * d12, d6 } }; opts: { run } (the caller's clock).
 */
export function unboxSteps(rest, phase = "unbox") {
    const steps = [];
    const T = (entry) => tempoOf(entry, phase);
    const push = (move) => steps.push(moveStep(move, T(move.entry)));
    const S = solids;
    const naval = () => [...S.navalBase()];
    // 1. The Battleship lid off (the dice box, still shut, beside it).
    {
        const around = [...naval(), ...S.unitPacked(0), ...S.unitPacked(1), ...S.diceClosed()];
        push({
            names: ["naval-lid-off", "naval-lid-on"],
            entry: "battleship/box",
            solids: around,
            plan: (way, tempo) => (way
                ? battleship.box.planLidOn({ box: REST.navalBox, from: REST.navalLid, solids: around, tempo })
                : battleship.box.planLidOff({ box: REST.navalBox, to: REST.navalLid, solids: around, tempo })),
            play: (way, rigs, o) => (way
                ? battleship.box.putLid(rigs.naval, { ...o, solids: around })
                : battleship.box.liftLid(rigs.naval, REST.navalLid, { ...o, solids: around })),
        });
    }
    // 2. The units out, red then blue (the entry adds the base's own card).
    for (const k of [0, 1]) {
        const around = k === 0
            ? [...S.navalLid(), ...S.unitPacked(1), ...S.diceClosed()]
            : [...S.navalLid(), ...S.unitClosed(0), ...S.diceClosed()];
        const seat = SEATS.units[k];
        push({
            names: [`unit-${k}-out`, `unit-${k}-in`],
            entry: "battleship/box",
            solids: [...naval(), ...around],
            plan: (way, tempo) => (way
                ? battleship.box.planIn({ box: REST.navalBox, k, from: seat, solids: around, tempo })
                : battleship.box.planOut({ box: REST.navalBox, k, to: seat, solids: around, tempo })),
            play: (way, rigs, o) => (way
                ? battleship.box.putIn(rigs.naval, k, rigs.units[k].group, { ...o, solids: around })
                : battleship.box.liftOut(rigs.naval, k, rigs.units[k].group, seat, { ...o, solids: around })),
        });
    }
    // 3. Their lids open (shut again: from wherever the open stopped).
    for (const k of [0, 1]) {
        const around = k === 0
            ? [...naval(), ...S.navalLid(), ...S.unitClosed(1), ...S.diceClosed()]
            : [...naval(), ...S.navalLid(), ...S.unitOpen(0), ...S.diceClosed()];
        const pose = SEATS.units[k];
        const open = (tempo) => battleship.unit.planLid({ pose, from: 0, to: 1, solids: around, tempo });
        push({
            names: [`unit-${k}-open`, `unit-${k}-close`],
            entry: "battleship/unit",
            solids: around,
            plan: (way, tempo) => (way ? battleship.unit.planLid({ pose, from: open(tempo).fraction, to: 0, solids: around, tempo }) : open(tempo)),
            play: (way, rigs, o) => (way
                ? battleship.unit.closeLid(rigs.units[k], { ...o, solids: around })
                : battleship.unit.openLid(rigs.units[k], { ...o, solids: around })),
        });
    }
    const set = () => [...naval(), ...S.navalLid(), ...S.unitOpen(0), ...S.unitOpen(1)];
    // 4. The dice box's lid off.
    const packedCup = yahtzee.box.pocketPose(REST.diceBox);
    {
        const around = [...set(), ...S.diceBase(), ...S.cupBox(packedCup)];
        push({
            names: ["dice-lid-off", "dice-lid-on"],
            entry: "yahtzee/box",
            solids: around,
            plan: (way, tempo) => (way
                ? yahtzee.box.planLidOn({ box: REST.diceBox, from: REST.diceLid, solids: around, tempo })
                : yahtzee.box.planLidOff({ box: REST.diceBox, to: REST.diceLid, solids: around, tempo })),
            play: (way, rigs, o) => (way
                ? yahtzee.box.putLid(rigs.diceBox, { ...o, solids: around })
                : yahtzee.box.liftLid(rigs.diceBox, REST.diceLid, { ...o, solids: around })),
        });
    }
    // 5. The cup out (the entry adds the base's own card).
    {
        const around = [...set(), ...S.diceLid()];
        push({
            names: ["cup-out", "cup-in"],
            entry: "yahtzee/box",
            solids: [...S.diceBase(), ...around],
            plan: (way, tempo) => (way
                ? yahtzee.box.planIn({ box: REST.diceBox, from: SEATS.cup, solids: around, tempo })
                : yahtzee.box.planOut({ box: REST.diceBox, to: SEATS.cup, solids: around, tempo })),
            play: (way, rigs, o) => (way
                ? yahtzee.box.putIn(rigs.diceBox, rigs.cup, { ...o, solids: around })
                : yahtzee.box.liftOut(rigs.diceBox, rigs.cup, SEATS.cup, { ...o, solids: around })),
        });
    }
    // 6. The dice onto the row, the top layer first. Out, a die joins the
    // row (exactly on its spot there, its home); back, the cup (exactly in
    // its place there).
    const placed = [];
    const clearY = cupRimY(SEATS.cup);
    DICE.forEach(([kind, k], i) => {
        const still = DICE.slice(i + 1).flatMap(([kd, kk]) => S.die(packedDie(SEATS.cup, kd, kk), kd, `${kd}#${kk} in the cup`));
        const around = [...set(), ...S.diceBase(), ...S.diceLid(), ...S.cupRing(SEATS.cup), ...still, ...placed];
        const inCup = packedDie(SEATS.cup, kind, k);
        const spot = dieSpot(kind, k, rest);
        push({
            names: [`${kind}-${k}-out`, `${kind}-${k}-in`],
            entry: "dice",
            solids: around,
            die: [kind, k],
            clearY,
            plan: (way, tempo) => dice.planPlace({ kind, from: way ? spot : inCup, to: way ? inCup : spot, clearY, solids: around, tempo }),
            async play(way, rigs, o) {
                const holder = dieOf(rigs, kind, k);
                (way ? rigs.cup : rigs.diceRow).attach(holder);
                const done = await dice.place(holder, kind, way ? inCup : spot, { ...o, clearY, solids: around });
                if (way) {
                    holder.position.fromArray(packOf(kind, k));
                    holder.quaternion.set(0, 0, 0, 1);
                } else holder.position.set(rowX(kind, k), holder.position.y, 0);
                return done;
            },
        });
        placed.push(...S.die(spot, kind, `${kind}#${k} on the row`));
    });
    return steps;
}

/** The steps backwards, each reversed at its entry's repacking tempo (same path, same law). */
export const reverseSteps = (steps, phase = "repack") => steps.toReversed().map((s) => s.reverse(tempoOf(s.entry, phase)));

/** Every move of the repacking: the whole unboxing backwards. */
export const repackSteps = (rest) => reverseSteps(unboxSteps(rest));

/** Total ms of a step list played one after another (at the tempos it was planned at). */
export const stepsMs = (steps) => steps.reduce((t, s) => t + s.plan.ms, 0);
