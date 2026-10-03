/**
 * DoubleDeal table microdemos: the real 52+52 card table
 * (doubledeal/table.js via playroom/card-stage.js, scaled onto the felt)
 * playing one step kind in a loop at the dock pace.
 */
import { mountMicro } from "./micro.js";
import { TABLE_TIMING, loadCardTextures } from "../../doubledeal/table.js";
import { stageCardTable } from "../../playroom/card-stage.js";
import { DEN } from "../../playroom/constants.js";

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
 * page: { id, title, slots: [{ name, gapMs, voices }],
 *         prepare(table, ctx, loop)  instant state before a loop
 *         prepareEach                call prepare before every loop
 *         step(ctx, loop, pace) → { step, contacts: [[slot, msFromStart]] } }
 * settings.timing: pace plus any TABLE_TIMING keys (written into it).
 *
 * A library entry's viewer (demos/anim/doubledeal-*) passes instead
 *   voice   the entry's voice (its settings are the page's), no slots
 *   layout  doubledeal/real-layout.js REAL_LAYOUT: real-size cards
 *   camera  { position, target, fov, margin } override
 *   frameAll  frame both grids and the hand pile (else the message grid
 *             and the pile)
 *   frameLift m of room above the cards (their hop)
 */
export function mountTablePage(page, settings) {
    let table = null;
    let loop = 0;
    for (const [key, v] of Object.entries(settings.timing || {})) if (key in TABLE_TIMING) TABLE_TIMING[key] = v;
    return mountMicro({
        id: page.id,
        title: page.title,
        camera: page.camera ?? { position: [DEN.x + 0.1, 1.3, DEN.z + 0.62], target: [DEN.x, 0.78, DEN.z], fov: 34, margin: page.margin ?? 0.96 },
        ...(page.voice ? { voice: page.voice } : { slots: page.slots }),
        async setup(ctx) {
            ctx.status("Loading cards…");
            const textures = await loadCardTextures(4, { aspect: page.layout?.artAspect ?? null });
            table = stageCardTable(ctx.world, textures, { poses: null, visible: true, layout: page.layout ?? null });
            table.setCardsVisible(true);
        },
        frame(ctx) {
            // Every card in place first (the key grid too: frameAll).
            table.showDecks(ORDER, ORDER.slice().reverse());
            // The message grid and the hand pile in front of it (frameAll: and the key grid).
            const box = new ctx.THREE.Box3();
            for (const state of [{ kind: "dealrm", message: ORDER }, { kind: "scoopcm" }]) {
                table.applyInstant(state);
                table.group.updateMatrixWorld(true);
                for (const mesh of table.cardsOf("message")) box.expandByObject(mesh);
                if (page.frameAll) for (const mesh of table.cardsOf("key")) box.expandByObject(mesh);
            }
            // frameLift (m): room above the cards for their hop.
            if (page.frameLift) box.max.y += page.frameLift;
            return box;
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
    }, settings);
}
