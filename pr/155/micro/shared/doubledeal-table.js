/**
 * DoubleDeal table microdemos: the real 52+52 card table
 * (doubledeal/table.js via playroom/card-stage.js, scaled onto the felt)
 * playing one step kind in a loop at the dock pace.
 */
import { mountMicro } from "./micro.js";
import { TABLE_TIMING, loadCardTextures } from "../../doubledeal/table.js";
import { stageCardTable } from "../../playroom/card-stage.js";
import { DEN, DEAL_SCALE } from "../../playroom/constants.js";
import { MESSAGE_X } from "../../doubledeal/layout.js";

const LABEL = {
    stepMs: "stepMs (reset/pass/compose)",
    dealMs: "dealMs (per card)",
    dealStaggerMs: "dealStaggerMs",
    shiftMs: "shiftMs (ShiftRows)",
    sumrowMs: "sumrowMs (SumRanks row)",
    sumcolMs: "sumcolMs (column belt)",
    scoopColMs: "scoopColMs",
    scoopRowMs: "scoopRowMs",
    placeMs: "placeMs (hop)",
    dropMs: "dropMs (drop)",
    takeMs: "takeMs",
    hop: "hop (low, units)",
    liftHop: "liftHop (lifted, units)",
    zeroShiftHop: "zeroShiftHop",
    dropY: "dropY (units)",
};

const RANGE = {
    hop: [0, 1.5, 0.01],
    liftHop: [0, 2.5, 0.01],
    zeroShiftHop: [0, 1, 0.01],
    dropY: [0.2, 3, 0.05],
};

// A fixed shuffled deck order (so the grid reads as a real deal).
export const ORDER = (() => {
    const order = Array.from({ length: 52 }, (_, i) => i);
    let seed = 7;
    for (let i = 51; i > 0; i--) {
        seed = (seed * 1103515245 + 12345) % 2147483648;
        const j = seed % (i + 1);
        [order[i], order[j]] = [order[j], order[i]];
    }
    return order;
})();

/**
 * page: { id, title, summary, timingKeys, slots, choices, loopGapMs,
 *         prepare(table, ctx)  instant state before each loop
 *         step(ctx, loop) → { step, contacts: [[slot, msFromStart]] } }
 */
export function mountTablePage(page) {
    let table = null;
    let loop = 0;
    const scale = DEAL_SCALE;
    const mx = DEN.x + MESSAGE_X * scale;
    return mountMicro({
        id: page.id,
        title: page.title,
        summary: page.summary,
        source: page.source || "doubledeal/table.js play(step, pace) · playroom/card-stage.js",
        camera: page.camera || { position: [mx + 0.16, 1.18, DEN.z + 0.62], target: [mx, 0.78, DEN.z + 0.04], fov: 34 },
        loopGapMs: page.loopGapMs ?? 700,
        choices: page.choices || [],
        timing: [
            { key: "pace", label: "Speed (pace)", min: 0.6, max: 8, step: 0.1, value: 1.8, unit: "×", note: "Dock speed slider → table.play(step, pace): every ms is divided by it" },
            ...page.timingKeys.map((key) => {
                const [min, max, step] = RANGE[key] || [0, Math.max(40, TABLE_TIMING[key] * 3), key === "scanMs" ? 1 : 5];
                return { key, label: LABEL[key] || key, min, max, step, value: TABLE_TIMING[key], unit: RANGE[key] ? "" : " ms" };
            }),
        ],
        slots: page.slots,
        async setup(ctx) {
            ctx.status("Loading cards…");
            const textures = await loadCardTextures(4);
            table = stageCardTable(ctx.world, textures, { poses: null, visible: true });
            table.showDecks(ORDER, ORDER.slice().reverse());
            table.setCardsVisible(true);
            for (const key of page.timingKeys) TABLE_TIMING[key] = ctx.timing(key);
            ctx.table = table;
        },
        onTiming(ctx, key, v) {
            if (key in TABLE_TIMING) TABLE_TIMING[key] = v;
        },
        async reset(ctx) {
            loop = 0;
            table.showDecks(ORDER, ORDER.slice().reverse());
            await page.prepare?.(table, ctx, loop);
        },
        async cycle(ctx) {
            const gen = ctx.alive;
            if (page.prepareEach) await page.prepare?.(table, ctx, loop);
            const pace = ctx.timing("pace");
            const { step, contacts } = page.step(ctx, loop, pace);
            const lead = ctx.leadIn(contacts);
            if (lead && !(await ctx.wait(lead))) return;
            if (gen !== ctx.alive) return;
            const t0 = performance.now();
            for (const [slot, at] of contacts) ctx.contact(slot, t0 + at);
            await table.play(step, pace);
            loop += 1;
        },
        config(ctx) {
            const timing = {};
            for (const key of page.timingKeys) timing[key] = ctx.timing(key);
            return {
                demo: "doubledeal",
                paste: "TABLE_TIMING → demos/doubledeal/table.js; speed → createDoubleDealAdapter speed; sounds → a demos/shared/sound.js table (offsetMs is relative to each contact)",
                TABLE_TIMING: timing,
                speed: { min: 0.6, max: 8, value: ctx.timing("pace") },
                ...(page.config ? page.config(ctx) : {}),
            };
        },
    });
}
