import { ORDER, mountTablePage } from "../shared/doubledeal-table.js";

// GridCycle place: a card from the hand pile hops to its seat (flag 0),
// or drops from above onto it (flag 1).
let taken = [];

void mountTablePage({
    id: "doubledeal-place",
    title: "DoubleDeal: place a card",
    summary: "GridCycle place (table.js placeCard): a card hops from the hand pile to its seat, or (flag 1) drops onto it from above.",
    choices: [{ key: "flag", label: "Place", value: 0, options: [[0, "hop from the pile (flag 0)"], [1, "drop from above (flag 1)"]] }],
    timingKeys: ["placeMs", "dropMs", "liftHop", "hop", "dropY"],
    slots: [
        { name: "place", label: "Set down (hop)", contact: "the card lands", from: [["doubledeal-place", "place"]], gapMs: 60, voices: 3 },
        { name: "drop", label: "Set down (drop)", contact: "the card lands", from: [["doubledeal-place", "drop"]], gapMs: 60, voices: 3 },
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
});
