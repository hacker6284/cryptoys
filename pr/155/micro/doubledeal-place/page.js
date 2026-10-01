import { ORDER, mountTablePage } from "../shared/doubledeal-table.js";
import settings from "./settings.js";

// GridCycle place: a card from the hand pile hops to its seat (flag 0),
// or drops from above onto it (flag 1).
let taken = [];

void mountTablePage({
    id: "doubledeal-place",
    title: "Place a card",
    slots: [
        { name: "place", gapMs: 60, voices: 3 },
        { name: "drop", gapMs: 60, voices: 3 },
    ],
    prepareEach: true,
    prepare(table, ctx, loop) {
        if (loop % 13 !== 0) return;
        table.applyInstant({ kind: "dealrm", message: ORDER });
        table.applyInstant({ kind: "scooprm" });
        taken = ORDER.slice().reverse();
    },
    step(ctx, loop, pace) {
        const flag = Number(ctx.choice("flag"));
        const card = taken[loop % 13];
        const ms = ctx.timing(flag === 1 ? "dropMs" : "placeMs") / pace;
        return { step: { kind: "place", card, row: 2, col: loop % 13, flag }, contacts: [[flag === 1 ? "drop" : "place", ms]] };
    },
}, settings);
