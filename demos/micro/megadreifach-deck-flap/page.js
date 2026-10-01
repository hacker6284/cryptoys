import { mountMicro } from "../shared/micro.js";
import { addGlow, buildBox, restowBox } from "../shared/boxes.js";
import { DEN } from "../../playroom/constants.js";

// MegaDreifach's DEAL deck flap. Its code (playroom/drei-stage.js
// dealCards: flap ms(260) open, the deal, ms(260) closed; quadratic
// easeInOut; ms(x) = max(40, x / tempo), demo speed 2) lives on
// keynote/megadreifach-demo, which is not on main yet, so this page
// mirrors those lines around the same unbox-rig flap (setFlap) instead
// of importing them. The deal in between is a hold here.
function easeInOut(t) {
    return t < 0.5 ? 2 * t * t : 1 - ((-2 * t + 2) ** 2) / 2;
}

let rig = null;
let raf = 0;

function tween(duration, step) {
    cancelAnimationFrame(raf);
    if (!duration) {
        step(1);
        return Promise.resolve();
    }
    return new Promise((resolve) => {
        const start = performance.now();
        const tick = (now) => {
            const t = Math.min(1, (now - start) / duration);
            step(easeInOut(t));
            if (t < 1) raf = requestAnimationFrame(tick);
            else resolve();
        };
        raf = requestAnimationFrame(tick);
    });
}

function ms(ctx, base) {
    return Math.max(40, base / Math.max(0.25, ctx.timing("tempo")));
}

void mountMicro({
    id: "megadreifach-deck-flap",
    title: "MegaDreifach: deck-box flap",
    summary: "The DEAL deck's flap opens for a block's deal and closes after it (ms(260) each way at the demo speed). Timing mirrors drei-stage.js on keynote/megadreifach-demo.",
    source: "unbox-rig.js setFlap · timing from drei-stage.js dealCards (keynote/megadreifach-demo, not on main)",
    camera: { position: [DEN.x + 0.22, 1.02, DEN.z + 0.42], target: [DEN.x, 0.82, DEN.z], fov: 30 },
    loopGapMs: 700,
    timing: [
        { key: "tempo", label: "Speed (tempo)", min: 0.5, max: 12, step: 0.1, value: 2, unit: "×", note: "MegaDreifach dock speed (default 2)" },
        { key: "flapMs", label: "flap (ms at 1×)", min: 40, max: 1500, step: 10, value: 260, unit: " ms" },
        { key: "holdMs", label: "deal in between (ms at 1×)", min: 0, max: 4000, step: 10, value: 51 * 38 + 320, unit: " ms", note: "52 cards: stagger 38 ms × 51 + flight 320 ms" },
    ],
    slots: [
        { name: "open", label: "Flap opens", contact: "the flap starts to lift", from: [["unbox", "tuck-flap-open"], "doubledeal-tuck-flap"], gapMs: 100, voices: 2 },
        { name: "close", label: "Flap closes", contact: "the flap shuts", from: [["doubledeal-restow", "flap"]], gapMs: 100, voices: 2 },
    ],
    async setup(ctx) {
        addGlow(ctx.world, "deck");
        ctx.status("Loading the deck…");
        rig = await buildBox(ctx.world, "deck", "DEAL");
    },
    stop() {
        cancelAnimationFrame(raf);
    },
    async reset(ctx) {
        restowBox(rig);
        ctx.world.applyPose(rig.group, ctx.world.getTablePose("deck"));
        rig.packet.visible = true;
    },
    async cycle(ctx) {
        const gen = ctx.alive;
        const flap = ms(ctx, ctx.timing("flapMs"));
        const hold = ms(ctx, ctx.timing("holdMs"));
        const contacts = [["open", 0], ["close", flap + hold + flap]];
        const lead = ctx.leadIn(contacts);
        if (lead && !(await ctx.wait(lead))) return;
        if (gen !== ctx.alive) return;
        const t0 = performance.now();
        for (const [slot, at] of contacts) ctx.contact(slot, t0 + at);
        await tween(flap, (t) => rig.setFlap(t));
        if (!(await ctx.wait(hold))) return;
        await tween(flap, (t) => rig.setFlap(1 - t));
    },
    config(ctx) {
        return {
            demo: "megadreifach",
            paste: "flap → drei-stage.js dealCards ms(260); speed → createMegaDreifachAdapter speed; sounds → demos/megadreifach/sound.js SOUNDS shape",
            dealCards: { flapMs: ctx.timing("flapMs") },
            speed: { min: 0.5, max: 12, value: ctx.timing("tempo") },
        };
    },
});
