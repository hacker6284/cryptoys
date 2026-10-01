import { mountMicro } from "../shared/micro.js";
import { EASE_OPTIONS, addGlow, buildBox, restowBox } from "../shared/boxes.js";
import { createBeatClock } from "../../playroom/beat-clock.js";
import { DEN } from "../../playroom/constants.js";
import {
    UNBOX_TIMING, createDealerKey, packetOrigin, playUnbox,
    unboxAside, unboxDeal, unboxExtract, unboxFlap, unboxLay,
} from "../../playroom/unbox-physical.js";

const NUM = [
    ["flapMs", "flapMs", 60, 2000, 10],
    ["flapPauseMs", "flapPauseMs", 0, 800, 10],
    ["extractMs", "extractMs", 60, 2000, 10],
    ["extractRise", "extractRise (m)", 0.02, 0.2, 0.002],
    ["layMs", "layMs", 60, 2000, 10],
    ["layLift", "layLift (m)", 0, 0.15, 0.002],
    ["asideMs", "asideMs", 60, 2000, 10],
    ["asideLift", "asideLift (m)", 0, 0.15, 0.002],
    ["dealStaggerMs", "dealStaggerMs", 0, 300, 2],
    ["dealMs", "dealMs", 60, 1500, 10],
    ["dealLift", "dealLift (m)", 0, 0.2, 0.002],
];
const EASES = ["flapEase", "extractEase", "layEase", "asideEase", "dealEase"];
const ZERO = { ...UNBOX_TIMING, flapMs: 0, flapPauseMs: 0, extractMs: 0, layMs: 0, asideMs: 0, dealMs: 0, dealStaggerMs: 0 };

let rig = null;
let keyLight = null;
let clock = null;

function apply(ctx) {
    for (const [key] of NUM) UNBOX_TIMING[key] = ctx.timing(key);
    for (const key of EASES) UNBOX_TIMING[key] = ctx.choice(key);
}

void mountMicro({
    id: "doubledeal-unbox",
    title: "Unbox: flap, deck out, set down",
    summary: "The DoubleDeal KEY tuck box on the felt: the flap lifts, the short packet slides out, is laid on the felt, the sleeve hops aside and the cards are dealt (playroom/unbox-physical.js, the same beats as the enter).",
    source: "playroom/unbox-physical.js (UNBOX_TIMING, unboxFlap/Extract/Lay/Aside/Deal, playUnbox) · unbox-rig.js",
    camera: { position: [DEN.x + 0.42, 1.2, DEN.z + 0.86], target: [DEN.x + 0.2, 0.8, DEN.z + 0.04], fov: 38 },
    loopGapMs: 900,
    choices: [
        { key: "phase", label: "Loop", value: "out", options: [["flap", "flap only"], ["extract", "deck slides out (flap already open)"], ["out", "flap → deck out → set down"], ["lay", "set down only"], ["deal", "sleeve aside + deal"], ["full", "whole unbox (playUnbox)"]] },
        ...EASES.map((key) => ({ key, label: key, value: UNBOX_TIMING[key], options: EASE_OPTIONS })),
    ],
    timing: NUM.map(([key, label, min, max, step]) => ({ key, label, min, max, step, value: UNBOX_TIMING[key], unit: key.endsWith("Ms") ? " ms" : "" })),
    slots: [
        { name: "flap", label: "Flap opens", contact: "the flap starts to lift (flap beat)", from: [["unbox", "tuck-flap-open"], "doubledeal-tuck-flap"], gapMs: 200, voices: 2 },
        { name: "extract", label: "Deck slides out", contact: "the packet starts to rise (extract beat)", from: [["unbox", "deck-slide-out"], "doubledeal-tuck-extract"], gapMs: 200, voices: 2 },
        { name: "lay", label: "Packet set down", contact: "the packet lands on the felt", from: ["doubledeal-packet-lay", ["unbox", "box-setdown-felt"]], gapMs: 200, voices: 2 },
        { name: "aside", label: "Sleeve set aside", contact: "the empty box lands", from: ["doubledeal-sleeve-aside", ["unbox", "box-setdown-felt"]], gapMs: 200, voices: 2 },
        { name: "deal", label: "Card dealt (per card)", contact: "each card lands", from: ["doubledeal-deal"], gapMs: 50, voices: 4 },
    ],
    async setup(ctx) {
        keyLight = createDealerKey(ctx.world);
        addGlow(ctx.world, "deck");
        ctx.status("Loading the deck…");
        rig = await buildBox(ctx.world, "deck", "KEY");
        apply(ctx);
    },
    onTiming(ctx) {
        apply(ctx);
    },
    stop() {
        clock?.skip();
    },
    async reset(ctx) {
        apply(ctx);
        restowBox(rig);
        ctx.world.applyPose(rig.group, ctx.world.getTablePose("deck"));
        keyLight.intensity = 2.15;
    },
    async cycle(ctx) {
        apply(ctx);
        const gen0 = ctx.alive;
        const phase = ctx.choice("phase");
        const T = UNBOX_TIMING;
        await this.reset(ctx);
        clock = createBeatClock({ reduced: false });
        let gen = clock.begin();
        const world = ctx.world;
        const pile = packetOrigin(world, "deck");
        const fast = { world, rig, clock, gen, keyLight, name: "deck", pile, timing: ZERO };
        // Instant set-up to the start of the looped beat.
        if (["extract", "lay", "deal"].includes(phase)) await unboxFlap(fast);
        if (["lay", "deal"].includes(phase)) await unboxExtract(fast);
        if (phase === "deal") await unboxLay(fast);
        const beat = { world, rig, clock, gen, keyLight, name: "deck", pile, timing: T };
        // Contacts from the real timings (ms after the loop starts).
        const contacts = [];
        let t = 0;
        if (phase === "full") t += T.settleMs + T.holdMs;
        if (["flap", "out", "full"].includes(phase)) {
            contacts.push(["flap", t]);
            t += T.flapMs + (phase === "flap" ? 0 : T.flapPauseMs);
        }
        if (["extract", "out", "full"].includes(phase)) {
            contacts.push(["extract", t]);
            t += T.extractMs;
        }
        if (["lay", "out", "full"].includes(phase)) {
            t += T.layMs;
            contacts.push(["lay", t]);
        }
        if (["deal", "full"].includes(phase)) {
            contacts.push(["aside", t + T.asideMs]);
            for (let i = 0; i < rig.cards.length; i++) contacts.push(["deal", t + i * T.dealStaggerMs + T.dealMs]);
        }
        const lead = ctx.leadIn(contacts);
        if (lead && !(await ctx.wait(lead))) return;
        if (gen0 !== ctx.alive) return;
        const t0 = performance.now();
        for (const [slot, at] of contacts) ctx.contact(slot, t0 + at);
        if (phase === "full") {
            await playUnbox({ world, rig, clock, gen, keyLight, name: "deck" });
            return;
        }
        if (["flap", "out"].includes(phase)) {
            await unboxFlap(beat);
            if (phase === "out") await clock.wait(T.flapPauseMs, gen);
        }
        if (["extract", "out"].includes(phase)) await unboxExtract(beat);
        if (["lay", "out"].includes(phase)) await unboxLay(beat);
        if (phase === "deal") await Promise.all([unboxAside(beat), unboxDeal(beat)]);
        gen = 0;
    },
    config(ctx) {
        apply(ctx);
        return {
            demo: "doubledeal (playroom unbox)",
            paste: "UNBOX_TIMING → demos/playroom/unbox-physical.js; sounds → a demos/shared/sound.js table (offsetMs is relative to each contact)",
            UNBOX_TIMING: { ...UNBOX_TIMING },
        };
    },
});
