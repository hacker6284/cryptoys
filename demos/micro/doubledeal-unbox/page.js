import { mountMicro } from "../shared/micro.js";
import settings from "./settings.js";
import { addGlow, buildBox, restowBox } from "../shared/boxes.js";
import { createBeatClock } from "../../playroom/beat-clock.js";
import { DEN } from "../../playroom/constants.js";
import {
    UNBOX_TIMING, createDealerKey, packetOrigin, playUnbox,
    unboxAside, unboxDeal, unboxExtract, unboxFlap, unboxLay,
} from "../../playroom/unbox-physical.js";

const NUM = ["flapMs", "flapPauseMs", "extractMs", "extractRise", "layMs", "layLift", "asideMs", "asideLift", "dealStaggerMs", "dealMs", "dealLift"];
const EASES = ["flapEase", "extractEase", "layEase", "asideEase", "dealEase"];
const ZERO = { ...UNBOX_TIMING, flapMs: 0, flapPauseMs: 0, extractMs: 0, layMs: 0, asideMs: 0, dealMs: 0, dealStaggerMs: 0 };

let rig = null;
let keyLight = null;
let clock = null;

function apply(ctx) {
    for (const key of NUM) UNBOX_TIMING[key] = ctx.timing(key);
    for (const key of EASES) UNBOX_TIMING[key] = ctx.choice(key);
}

void mountMicro({
    id: "doubledeal-unbox",
    title: "Unbox",
    camera: { position: [DEN.x + 0.42, 1.2, DEN.z + 0.86], target: [DEN.x + 0.2, 0.8, DEN.z + 0.04], fov: 34, margin: 0.95 },
    slots: [
        { name: "flap", gapMs: 200, voices: 2 },
        { name: "extract", gapMs: 200, voices: 2 },
        { name: "lay", gapMs: 200, voices: 2 },
        { name: "aside", gapMs: 200, voices: 2 },
        { name: "deal", gapMs: 50, voices: 4 },
    ],
    frame(ctx) {
        // The box with its flap open, the packet's rise above it and the
        // spot on the felt where the packet is laid.
        restowBox(rig);
        ctx.world.applyPose(rig.group, ctx.world.getTablePose("deck"));
        rig.setFlap(1);
        const box = new ctx.THREE.Box3().setFromObject(rig.group);
        box.max.y += ctx.timing("extractRise");
        const pile = packetOrigin(ctx.world, "deck");
        box.expandByPoint(new ctx.THREE.Vector3(pile.x - 0.05, pile.y, pile.z - 0.05));
        box.expandByPoint(new ctx.THREE.Vector3(pile.x + 0.05, pile.y, pile.z + 0.05));
        return box;
    },
    async setup(ctx) {
        keyLight = createDealerKey(ctx.world);
        addGlow(ctx.world, "deck");
        ctx.status("Loading the deck…");
        rig = await buildBox(ctx.world, "deck", "KEY");
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
}, settings);
