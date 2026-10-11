import { ORDER, mountTablePage } from "../shared/doubledeal-table.js";
import settings from "./settings.js";

// Inverse GridCycle take: a card lifts off its seat onto the hand pile.
void mountTablePage({
    id: "doubledeal-take",
    title: "Take a card",
    slots: [
        { name: "take", gapMs: 60, voices: 3 },
    ],
    prepareEach: true,
    prepare(table, ctx, loop) {
        if (loop % 13 === 0) table.applyInstant({ kind: "dealrm", message: ORDER });
    },
    step(ctx, loop, pace) {
        const col = loop % 13;
        const card = ORDER[26 + col];
        return { step: { kind: "take", card, row: 2, col, amount: col }, contacts: [["take", ctx.timing("takeMs") / pace]] };
    },
}, settings);
