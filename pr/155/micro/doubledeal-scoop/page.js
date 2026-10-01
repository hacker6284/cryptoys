import { ORDER, mountTablePage } from "../shared/doubledeal-table.js";

void mountTablePage({
    id: "doubledeal-scoop",
    title: "DoubleDeal: scoop into the hand pile",
    summary: "scoopcm / scooprm sweep the whole grid into the hand pile in front (all 52 cards at once), then the pile is squared.",
    choices: [{ key: "kind", label: "Step", value: "scoopcm", options: [["scoopcm", "column-major (scoopcm, low)"], ["scooprm", "row-major (scooprm, lifted)"]] }],
    timingKeys: ["scoopColMs", "scoopRowMs", "hop", "liftHop"],
    slots: [
        { name: "sweep", label: "Sweep", contact: "the cards start moving", from: ["doubledeal-scoop"], gapMs: 200, voices: 2 },
        { name: "knock", label: "Pile squared (knock)", contact: "the cards land on the pile", from: ["doubledeal-square"], gapMs: 200, voices: 2 },
    ],
    prepareEach: true,
    prepare(table) {
        table.applyInstant({ kind: "dealrm", message: ORDER });
    },
    step(ctx, loop, pace) {
        const kind = ctx.choice("kind");
        const ms = ctx.timing(kind === "scoopcm" ? "scoopColMs" : "scoopRowMs") / pace;
        return { step: { kind }, contacts: [["sweep", 0], ["knock", ms]] };
    },
});
