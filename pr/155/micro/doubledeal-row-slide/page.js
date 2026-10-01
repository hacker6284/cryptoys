import { ORDER, mountTablePage } from "../shared/doubledeal-table.js";

void mountTablePage({
    id: "doubledeal-row-slide",
    title: "DoubleDeal: row slide and column belt",
    summary: "ShiftRows / SumRanks slide a row along the felt (low hop); the SumRanks column belt lifts a column round. Each loop slides back.",
    choices: [
        { key: "kind", label: "Step", value: "shift", options: [["shift", "ShiftRows row (shift)"], ["sumrow", "SumRanks row (sumrow)"], ["sumcol", "SumRanks column belt (sumcol)"]] },
        { key: "amount", label: "Amount", value: 3, options: [[1, "1"], [2, "2"], [3, "3"], [5, "5"], [6, "6"], [13, "13 (hop in place)"]] },
    ],
    timingKeys: ["shiftMs", "sumrowMs", "sumcolMs", "hop", "liftHop", "zeroShiftHop"],
    slots: [
        { name: "slide", label: "Row slide", contact: "the row starts moving", from: ["doubledeal-row-slide"], gapMs: 120, voices: 2 },
        { name: "belt", label: "Column belt", contact: "the column starts moving", from: ["doubledeal-column-belt"], gapMs: 120, voices: 2 },
        { name: "hop", label: "Hop in place (amount 13)", contact: "the card lands", from: ["doubledeal-table-settle"], gapMs: 120, voices: 2 },
    ],
    prepare(table) {
        table.applyInstant({ kind: "dealrm", message: ORDER });
    },
    step(ctx, loop, pace) {
        const kind = ctx.choice("kind");
        const amount = Number(ctx.choice("amount")) * (loop % 2 === 0 ? 1 : -1);
        if (kind === "sumcol") {
            const a = amount % 4 === 0 ? 1 : amount;
            return { step: { kind, col: 6, amount: a }, contacts: [["belt", 0]] };
        }
        const ms = ctx.timing(kind === "shift" ? "shiftMs" : "sumrowMs") / pace;
        const contacts = Math.abs(amount) % 13 === 0 ? [["hop", ms]] : [["slide", 0]];
        return { step: { kind, row: 1, amount }, contacts };
    },
});
