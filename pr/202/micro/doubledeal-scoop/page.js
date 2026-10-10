import { ORDER, mountTablePage } from "../shared/doubledeal-table.js";
import settings from "./settings.js";

void mountTablePage({
    id: "doubledeal-scoop",
    title: "Scoop",
    slots: [
        { name: "sweep", gapMs: 200, voices: 2 },
        { name: "knock", gapMs: 200, voices: 2 },
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
}, settings);
