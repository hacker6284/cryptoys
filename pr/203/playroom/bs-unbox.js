/**
 * BS unboxing on the table: the boxes' contents packed, unpacked and
 * repacked, by playing bs-unbox-plan.js's steps (each carries its own move
 * through the library's entries) one after another on the caller's clock
 * (`run(ms, step)`; a snapped clock finishes each move at once).
 *
 *   const box = createBsUnbox({ scene, rigs, rest })
 *   box.packNow()                everything in its box, at once (the boxes wait packed)
 *   await box.unbox(run)         lids off, units out and open, cup out, dice out
 *   box.cancel()                 stop after the move in progress (leaving mid-unbox)
 *   await box.repack(run)        the moves done, backwards, then packed exactly
 *   await box.repack(run, { snap: true })   packed at once
 *
 * rigs: { naval: { group, lid }, diceBox: { group, lid }, units: [{ group, lid }],
 * cup, diceRow, dice: { d10: [holder × 5], d12, d6 } }. rest(kind, k) →
 * { y, q }: the die's resting centre height and rotation on its row spot
 * (bs-unbox-plan.js makeDieRest).
 */
import * as battleship from "../anim/battleship/index.js";
import * as yahtzee from "../anim/yahtzee/index.js";
import { setWorldPose } from "../anim/shared/run.js";
import { DICE, SEATS, packOf, reverseSteps, stepsMs, unboxSteps } from "./bs-unbox-plan.js";

export function createBsUnbox({ scene, rigs, rest }) {
    let packed = false;
    let busy = null;
    let cancelled = false;
    let done = [];
    let steps = null;
    const unboxing = () => (steps ??= unboxSteps(rest));
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
            diceBox.group.add(holder);
            holder.position.fromArray(packOf(kind, k));
            holder.quaternion.identity();
        }
        // The row is empty now: it leaves the scene until the next unboxing.
        rigs.diceRow.removeFromParent();
        done = [];
        packed = true;
    }

    // The row the dice land on stands at its seat on the felt (one row, added once).
    function seatRow() {
        if (rigs.diceRow.parent !== scene) scene.add(rigs.diceRow);
        setWorldPose(rigs.diceRow, SEATS.dice);
    }

    const repacking = () => reverseSteps(packed ? [] : done);

    return {
        get packed() {
            return packed;
        },
        packNow,
        /** Lids off, units out and open, the cup out, the dice onto their row (until cancel()). */
        async unbox(run) {
            if (!packed || busy) return;
            packed = false;
            cancelled = false;
            done = [];
            seatRow();
            busy = (async () => {
                for (const s of unboxing()) {
                    if (cancelled) break;
                    await s.play(rigs, { run });
                    done.push(s);
                }
            })();
            try {
                await busy;
            } finally {
                busy = null;
            }
        },
        /** Stop the unboxing after the move in progress. */
        cancel() {
            cancelled = true;
        },
        /** Back into the boxes: the moves done, backwards (snap: everything at once), then exactly packed. */
        async repack(run, { snap = false } = {}) {
            if (packed) return;
            cancelled = true;
            await busy;
            if (!snap) for (const s of repacking()) await s.play(rigs, { run });
            packNow();
        },
        unboxMs: () => stepsMs(unboxing()),
        /** How long repack() plays: the moves done so far, backwards. */
        repackMs: () => stepsMs(repacking()),
    };
}
