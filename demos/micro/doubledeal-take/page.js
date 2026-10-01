import { ORDER, mountTablePage } from "../shared/doubledeal-table.js";

// Inverse GridCycle take: a card lifts off its seat onto the hand pile.
void mountTablePage({
    id: "doubledeal-take",
    title: "DoubleDeal: take a card",
    summary: "Inverse GridCycle take (table.js takeCard): a seated card makes a lifted hop onto the hand pile.",
    timingKeys: ["takeMs", "liftHop"],
    slots: [
        { name: "take", label: "Take", contact: "the card lands on the pile", from: ["doubledeal-take"], gapMs: 60, voices: 3 },
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
});
