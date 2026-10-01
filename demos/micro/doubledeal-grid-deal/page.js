import { ORDER, mountTablePage } from "../shared/doubledeal-table.js";

void mountTablePage({
    id: "doubledeal-grid-deal",
    title: "DoubleDeal: deal into the grid",
    summary: "The hand packet is dealt into the 4×13 message grid (table.js seatPacket: one card every dealStaggerMs, each a lifted hop of dealMs).",
    choices: [{ key: "major", label: "Order", value: "deal", options: [["deal", "column-major (deal)"], ["dealrm", "row-major (dealrm)"]] }],
    timingKeys: ["dealMs", "dealStaggerMs", "liftHop"],
    slots: [
        { name: "stream", label: "Grid stream (one per step)", contact: "first card lands", from: ["doubledeal-grid-deal"], gapMs: 300, voices: 2 },
        { name: "card", label: "Card lands (per card, ≤15/s)", contact: "each card lands", from: ["doubledeal-table-settle", ["card-deal", "setdown"], "doubledeal-packet-lay", ["doubledeal-place", "place"]], gapMs: 66, voices: 4, off: true },
    ],
    prepareEach: true,
    prepare(table, ctx) {
        const kind = ctx.choice("major");
        table.applyInstant({ kind, message: ORDER });
        table.applyInstant({ kind: kind === "deal" ? "scoopcm" : "scooprm" });
    },
    step(ctx, loop, pace) {
        const deal = ctx.timing("dealMs") / pace;
        const stagger = ctx.timing("dealStaggerMs") / pace;
        const contacts = [["stream", deal]];
        for (let i = 0; i < 52; i++) contacts.push(["card", i * stagger + deal]);
        return { step: { kind: ctx.choice("major"), message: ORDER }, contacts };
    },
});
