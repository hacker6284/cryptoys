import { mountMicro } from "../../shared/micro.js";
import { settings } from "../../../anim/deck/carry/index.js";
import { carrySchedule, DECK_BOX, DEFAULT_SEED, CYCLES } from "../../../anim/deck/carry/placements.js";
import { obbCorners, obbOf } from "../../../anim/shared/geom.js";
import {
    options, placeChest, applyPose, createRunner, createInfo, createFrameCheck, seatedFail, sizeFail, roomCheck, framePoints, surfacePoints,
} from "../../shared/primitive.js";

// deck/carry (anim/deck/carry): the two deck boxes carried around the playroom,
// a different start and end every cycle (anim/deck/carry/placements.js, seeded),
// each cycle starting where the last one ended. Only the carried box moves:
// the chest is shut scenery. One primitive, nothing composed.
const opt = options(DEFAULT_SEED);
let schedule = null;
let runner = null;
let info = null;
let k = 0;
let loops = 0;
const NAMES = { deck: "KEY", deck2: "MSG" };
const results = [];

void mountMicro({
    id: "carry",
    title: "Carry",
    camera: { position: [0.9, 2.3, 3.1], target: [-1.15, 0.8, -0.25], fov: 40, fill: 0.92 },
    slots: [],
    silent: true,
    frame() {
        // The union of the loop: every pose and every path (the table and shelf).
        const pts = [...surfacePoints()];
        for (const c of schedule.cycles) {
            pts.push(...obbCorners(obbOf(c.from, DECK_BOX)), ...obbCorners(obbOf(c.to, DECK_BOX)));
            pts.push(...c.plan.path.pts.filter((_, i) => i % 8 === 0));
        }
        return framePoints(pts);
    },
    async setup(ctx) {
        ctx.status("Planning the loop…");
        placeChest(ctx.world);
        schedule = carrySchedule(opt.seed);
        runner = createRunner(ctx);
        info = createInfo();
        const bad = roomCheck(ctx.world);
        for (const name of ["deck", "deck2"]) bad.push(...sizeFail(ctx.world.toys[name], DECK_BOX, `${NAMES[name]} box`));
        if (bad.length) console.error(`carry: the room differs from anim/shared/room.js: ${bad.join("; ")}`);
        window.__primitive = { name: "carry", seed: opt.seed, schedule, results, roomBad: bad, settings };
    },
    stop() {
        runner?.stop();
    },
    async reset(ctx) {
        // Start of the loop (or of ?cycle / ?only): each box where the cycle before left it.
        const startAt = (opt.only || opt.cycle) - 1;
        k = Math.max(0, Math.min(CYCLES - 1, startAt));
        const at = { deck: schedule.poseOf(schedule.start.deck), deck2: schedule.poseOf(schedule.start.deck2) };
        for (const c of schedule.cycles.slice(0, k)) at[c.mover] = c.to;
        applyPose(ctx.world.toys.deck, at.deck);
        applyPose(ctx.world.toys.deck2, at.deck2);
    },
    async cycle(ctx) {
        const c = schedule.cycles[k];
        const toy = ctx.world.toys[c.mover];
        const plan = c.plan;
        const head = `seed ${schedule.seed} · cycle ${c.n} of ${CYCLES} · ${c.kind}: ${c.label}`;
        const stats = `${NAMES[c.mover]} ${plan.L.toFixed(2)} m in ${plan.ms.toFixed(0)} ms, top +${(plan.top - Math.max(c.from.p[1], c.to.p[1])).toFixed(2)} m`;
        info.set(`${head}\n${stats} · checking…`);
        if (opt.only) await this.reset(ctx);
        if (opt.view === "cycle") {
            const pts = [...obbCorners(obbOf(c.from, DECK_BOX)), ...obbCorners(obbOf(c.to, DECK_BOX)), ...plan.path.pts.filter((_, i) => i % 4 === 0)];
            ctx.frame(framePoints(pts));
        }
        applyPose(toy, c.from);
        const check = createFrameCheck({ name: NAMES[c.mover], solids: c.solids, shape: DECK_BOX, maxSpeed: plan.peakSpeed, ms: plan.ms, peakMs: plan.peakMs });
        const ok = await runner.run(plan.ms, (t) => {
            applyPose(toy, plan.at(t));
            check.frame(toy, t);
        }, `carry ${c.n}`);
        if (!ok) return;
        const fail = [...check.finish(), ...seatedFail(toy, c.surfaceTo, NAMES[c.mover]), ...sizeFail(toy, DECK_BOX, NAMES[c.mover]), ...c.check.fail];
        results.push({ loop: loops, n: c.n, ok: fail.length === 0, fail, ms: plan.ms, L: plan.L, peakAt: check.peakAt, lawPeak: plan.peakMs });
        if (fail.length) console.error(`carry cycle ${c.n}: ${fail.join("; ")}`);
        info.set(`${head}\n${stats} · ${fail.length ? `✗ ${fail.join("; ")}` : "checks ✓ (no overlap, seated, real size, duration and peak speed on the law)"}`, fail.length === 0);
        if (!opt.only) {
            k = (k + 1) % CYCLES;
            if (k === 0) loops += 1;
        }
    },
}, settings);
