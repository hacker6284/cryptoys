/**
 * BS unboxing on the table: the boxes' contents packed, unpacked and
 * repacked, by playing bs-unbox-plan.js's moves through the library's own
 * entries (anim/battleship box and unit, anim/yahtzee box, anim/dice
 * place), one after another on the caller's clock (`run(ms, step)`; a
 * snapped clock finishes each move at once).
 *
 *   const box = createBsUnbox({ scene, rigs, rest })
 *   box.packNow()          everything in its box, at once (the boxes wait packed)
 *   await box.unbox(run)   lids off, units out and open, cup out, dice out
 *   await box.repack(run)  the same backwards
 *
 * rigs: { naval: { group, lid }, diceBox: { group, lid }, units: [{ group, lid }],
 * cup, diceRow, dice: { d10: [holder × 5], d12, d6 } }. rest(kind, k) →
 * { y, q }: the die's resting centre height and rotation on its row spot.
 */
import * as battleship from "../anim/battleship/index.js";
import * as yahtzee from "../anim/yahtzee/index.js";
import * as dice from "../anim/dice/index.js";
import { setWorldPose } from "../anim/shared/run.js";
import { BS_DICE_PACK } from "./constants.js";
import { DICE, SEATS, repackSteps, rowX, stepsMs, tempoOf, unboxSteps } from "./bs-unbox-plan.js";

export function createBsUnbox({ scene, rigs, rest }) {
    let packed = false;
    let busy = null;
    const dieOf = (kind, k) => (kind === "d10" ? rigs.dice.d10[k] : rigs.dice[kind]);

    function packNow() {
        const { naval, diceBox, units, cup } = rigs;
        for (const rig of [naval, diceBox]) {
            rig.group.attach(rig.lid);
            rig.lid.position.set(0, 0, 0);
            rig.lid.quaternion.identity();
        }
        units.forEach((u, k) => {
            battleship.unit.setLid(u, 0);
            battleship.box.pack(naval, k, u.group);
        });
        yahtzee.box.pack(diceBox, cup);
        for (const [kind, k] of DICE) {
            const holder = dieOf(kind, k);
            cup.add(holder);
            holder.position.fromArray(kind === "d10" ? BS_DICE_PACK.d10[k] : BS_DICE_PACK[kind]);
            holder.quaternion.identity();
        }
        packed = true;
    }

    // The row the dice land on stands at its seat on the felt.
    function seatRow() {
        if (rigs.diceRow.parent !== scene) scene.add(rigs.diceRow);
        setWorldPose(rigs.diceRow, SEATS.dice);
    }

    async function play(steps, phase, run) {
        const { naval, diceBox, units, cup } = rigs;
        for (const step of steps) {
            const opts = { solids: step.solids, tempo: tempoOf(step.entry, phase), run };
            const n = step.name;
            if (n === "naval-lid-off") await battleship.box.liftLid(naval, step.plan.to, opts);
            else if (n === "naval-lid-on") await battleship.box.putLid(naval, opts);
            else if (/^unit-\d-out$/.test(n)) await battleship.box.liftOut(naval, +n[5], units[+n[5]].group, step.plan.to, opts);
            else if (/^unit-\d-in$/.test(n)) await battleship.box.putIn(naval, +n[5], units[+n[5]].group, opts);
            else if (/^unit-\d-open$/.test(n)) await battleship.unit.openLid(units[+n[5]], opts);
            else if (/^unit-\d-close$/.test(n)) await battleship.unit.closeLid(units[+n[5]], opts);
            else if (n === "dice-lid-off") await yahtzee.box.liftLid(diceBox, step.plan.to, opts);
            else if (n === "dice-lid-on") await yahtzee.box.putLid(diceBox, opts);
            else if (n === "cup-out") await yahtzee.box.liftOut(diceBox, cup, step.plan.to, opts);
            else if (n === "cup-in") await yahtzee.box.putIn(diceBox, cup, opts);
            else if (step.die) {
                const [kind, k] = step.die;
                const holder = dieOf(kind, k);
                // Out: onto the row (its spot there is its home); in: into the cup.
                (n.endsWith("-out") ? rigs.diceRow : cup).attach(holder);
                await dice.place(holder, kind, step.plan.to, { ...opts, clearY: step.clearY });
                // Exactly on its spot in the row (its home there), or in its place in the cup.
                if (n.endsWith("-out")) holder.position.set(rowX(kind, k), holder.position.y, 0);
            }
        }
    }

    return {
        get packed() {
            return packed;
        },
        packNow,
        /** Lids off, units out and open, the cup out, the dice onto their row. */
        async unbox(run) {
            if (!packed) return;
            packed = false;
            seatRow();
            busy = play(unboxSteps(rest), "unbox", run);
            await busy;
            busy = null;
        },
        /** Everything back into its box (the unboxing backwards). */
        async repack(run) {
            if (packed) return;
            await busy;
            await play(repackSteps(rest), "repack", run);
            packNow();
        },
        unboxMs: () => stepsMs(unboxSteps(rest)),
        repackMs: () => stepsMs(repackSteps(rest)),
    };
}
