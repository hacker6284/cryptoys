import { ORDER, mountTablePage } from "../shared/doubledeal-table.js";
import settings from "./settings.js";

void mountTablePage({
    id: "doubledeal-row-slide",
    title: "Row slide",
    slots: [
        { name: "slide", gapMs: 120, voices: 2 },
        { name: "belt", gapMs: 120, voices: 2 },
        { name: "hop", gapMs: 120, voices: 2 },
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
}, settings);
