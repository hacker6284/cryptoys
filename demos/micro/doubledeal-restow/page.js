import { mountMicro } from "../shared/micro.js";
import { ORDER } from "../shared/doubledeal-table.js";
import { addGlow, buildBox, restowBox } from "../shared/boxes.js";
import { loadCardTextures } from "../../doubledeal/table.js";
import { createBeatClock } from "../../playroom/beat-clock.js";
import { stageCardTable } from "../../playroom/card-stage.js";
import { DEN, GATHER_MS, RESTOW_MS } from "../../playroom/constants.js";
import { gatherSessionTable } from "../../playroom/table-form.js";
import { createDealerKey, playRestow } from "../../playroom/unbox-physical.js";

// DoubleDeal leave (adapters.js): the 4×13 grids hop back onto the two
// boxes (gatherSessionTable, GATHER_MS), the piles vanish into the boxes
// and both flaps ease shut (playRestow, RESTOW_MS). There is no separate
// deck-in motion in the real code: the packet is restowed under the
// closing flap.
let key = null;
let msg = null;
let table = null;
let clock = null;

function seatBoxes(ctx) {
    for (const [name, rig] of [["deck", key], ["deck2", msg]]) {
        restowBox(rig);
        ctx.world.applyPose(rig.group, ctx.world.getBoxRestPose(name));
        rig.setFlap(1);
    }
}

void mountMicro({
    id: "doubledeal-restow",
    title: "Put back: cards in, flap closed",
    summary: "DoubleDeal's leave: the two card grids hop back onto their boxes, vanish inside, and both tuck flaps close.",
    source: "playroom/adapters.js leave · table-form.js gatherSessionTable · unbox-physical.js playRestow",
    camera: { position: [DEN.x, 1.55, 1.05], target: [DEN.x, 0.8, -0.18], fov: 55 },
    loopGapMs: 900,
    choices: [{ key: "phase", label: "Loop", value: "leave", options: [["leave", "gather → restow (leave)"], ["restow", "flaps close only (playRestow)"]] }],
    timing: [
        { key: "GATHER_MS", label: "GATHER_MS", min: 100, max: 2000, step: 10, value: GATHER_MS, unit: " ms" },
        { key: "RESTOW_MS", label: "RESTOW_MS", min: 60, max: 1500, step: 10, value: RESTOW_MS, unit: " ms" },
    ],
    slots: [
        { name: "gather", label: "Cards gathered", contact: "the piles land on the boxes", from: ["doubledeal-gather"], gapMs: 200, voices: 2 },
        { name: "deckIn", label: "Deck slides in", contact: "restow starts (piles go in)", from: [["unbox", "deck-slide-in"], ["doubledeal-restow", "extract"]], gapMs: 200, voices: 2 },
        { name: "flap", label: "Flap closes", contact: "the flap shuts", from: [["doubledeal-restow", "flap"], ["unbox", "tuck-flap-open"]], gapMs: 100, voices: 3 },
    ],
    async setup(ctx) {
        const keyLight = createDealerKey(ctx.world);
        keyLight.intensity = 0.45;
        addGlow(ctx.world, "deck");
        addGlow(ctx.world, "deck2");
        ctx.status("Loading the decks…");
        key = await buildBox(ctx.world, "deck", "KEY");
        msg = await buildBox(ctx.world, "deck2", "MSG");
        table = stageCardTable(ctx.world, await loadCardTextures(4), { poses: null, visible: true });
    },
    stop() {
        clock?.skip();
    },
    async reset(ctx) {
        seatBoxes(ctx);
        table.showDecks(ORDER, ORDER.slice().reverse());
        table.setCardsVisible(ctx.choice("phase") === "leave");
    },
    async cycle(ctx) {
        const gen0 = ctx.alive;
        await this.reset(ctx);
        const leave = ctx.choice("phase") === "leave";
        const gather = leave ? ctx.timing("GATHER_MS") : 0;
        const restow = ctx.timing("RESTOW_MS");
        const contacts = [["deckIn", gather], ["flap", gather + restow]];
        if (leave) contacts.push(["gather", gather]);
        const lead = ctx.leadIn(contacts);
        if (lead && !(await ctx.wait(lead))) return;
        if (gen0 !== ctx.alive) return;
        const t0 = performance.now();
        for (const [slot, at] of contacts) ctx.contact(slot, t0 + at);
        clock = createBeatClock({ reduced: false });
        const gen = clock.begin();
        if (leave) {
            await gatherSessionTable({ table, clock, gen, keyBox: key.group.position, messageBox: msg.group.position, ms: gather });
            table.setCardsVisible(false);
        }
        await Promise.all([
            playRestow({ rig: key, clock, gen, ms: restow }),
            playRestow({ rig: msg, clock, gen, ms: restow }),
        ]);
    },
    config(ctx) {
        return {
            demo: "doubledeal (playroom leave)",
            paste: "constants → demos/playroom/constants.js; sounds → a demos/shared/sound.js table (offsetMs is relative to each contact)",
            constants: { GATHER_MS: ctx.timing("GATHER_MS"), RESTOW_MS: ctx.timing("RESTOW_MS") },
        };
    },
});
