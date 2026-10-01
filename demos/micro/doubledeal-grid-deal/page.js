import { ORDER, mountTablePage } from "../shared/doubledeal-table.js";
import settings from "./settings.js";

void mountTablePage({
    id: "doubledeal-grid-deal",
    title: "Deal into the grid",
    slots: [
        { name: "stream", gapMs: 300, voices: 2 },
        { name: "card", gapMs: 66, voices: 4 },
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
}, settings);
