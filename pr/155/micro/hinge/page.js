import { mountMicro } from "../shared/micro.js";
import { settings, parts, planHinge } from "../../anim/hinge/index.js";
import { hingeSchedule, flapObb, FLAP_FOLD, TUCK_BOX, DEFAULT_SEED, CYCLES } from "../../anim/hinge/placements.js";
import { DECK_BOX } from "../../anim/carry/placements.js";
import { CHEST, chestLidObb, roomSolids } from "../../anim/room.js";
import { obbCorners, obbOf, worstDepth } from "../../anim/geom.js";
import { addGlow, buildBox, restowBox } from "../shared/boxes.js";
import {
    options, placeChest, applyPose, poseOf, createRunner, createInfo, createFrameCheck, seatedFail, sizeFail, roomCheck, drawnBox, framePoints, chestPoints, surfacePoints,
} from "../shared/primitive.js";

// P2 hinge (anim/hinge): the KEY tuck box's flap (playroom/unbox-rig.js)
// opened and shut at a different pose every cycle, the box carried there
// with P1 carry; every fourth cycle the toy chest's lid. Seeded loop:
// anim/hinge/placements.js.
const opt = options(DEFAULT_SEED);
let schedule = null;
let runner = null;
let info = null;
let rig = null;
let k = 0;
const results = [];
const HOLD_MS = 380;
const FLAP_RAD = parts["tuck-flap"].openRad;

/** One swing, checked per frame: the part's box against the solids, the measured time and peak angular speed. */
async function swing(ctx, sw, { set, sweep, solids, name, label }) {
    const plan = sw.plan;
    const fail = [];
    let worst = -Infinity, where = "", last = null, peak = 0, peakAt = 0, end = 0, maxDt = 0;
    const ok = await runner.run(plan.ms, (t) => {
        const a = plan.at(t);
        set(a);
        if (sweep) {
            const w = worstDepth(sweep(a), solids, 0);
            if (w.depth > worst) { worst = w.depth; where = `${w.solid?.name} at ${t.toFixed(0)} ms`; }
        }
        if (last && t > last.t) {
            const r = Math.abs(a - last.a) / ((t - last.t) / 1000);
            if (r > peak) { peak = r; peakAt = (t + last.t) / 2; }
            maxDt = Math.max(maxDt, t - last.t);
        }
        last = { t, a };
        end = t;
    }, label);
    if (!ok) return null;
    if (worst > 0.0005) fail.push(`${name} overlaps ${(worst * 1000).toFixed(1)} mm (${where})`);
    if (Math.abs(end - plan.ms) > 1) fail.push(`${name} took ${end.toFixed(0)} ms, law ${plan.ms.toFixed(0)}`);
    if (plan.ms > 120 && Math.abs(peakAt - plan.peakMs) > Math.max(40, maxDt) + plan.ms * 0.04) fail.push(`${name} fastest at ${peakAt.toFixed(0)} ms, law ${plan.peakMs.toFixed(0)}`);
    return [...fail, ...sw.check.fail];
}

void mountMicro({
    id: "hinge",
    title: "Hinge",
    camera: { position: [0.9, 2.3, 3.1], target: [-1.15, 0.8, -0.25], fov: 40, fill: 0.92 },
    slots: [],
    silent: true,
    frame() {
        // The union of the loop: every pose and path of the box, the MSG box, the open chest.
        const pts = [...chestPoints(CHEST.lidOpenAngle * 1.03), ...surfacePoints(), ...obbCorners(obbOf(schedule.msgPose, DECK_BOX))];
        for (const c of schedule.cycles) {
            if (!c.carry) continue;
            pts.push(...obbCorners(obbOf(c.carry.to, TUCK_BOX)));
            pts.push(...c.carry.plan.path.pts.filter((_, i) => i % 8 === 0));
        }
        return framePoints(pts);
    },
    async setup(ctx) {
        ctx.status("Loading the tuck box…");
        placeChest(ctx.world);
        addGlow(ctx.world, "deck");
        rig = await buildBox(ctx.world, "deck", "KEY");
        restowBox(rig);
        schedule = hingeSchedule(opt.seed);
        runner = createRunner(ctx);
        info = createInfo();
        const bad = roomCheck(ctx.world);
        bad.push(...sizeFail(rig.group, TUCK_BOX, "KEY tuck box"), ...sizeFail(ctx.world.toys.deck2, DECK_BOX, "MSG box"));
        // The flap's planned box against its drawn mesh at a few angles.
        applyPose(rig.group, schedule.cycles[0].pose);
        for (const a of [0, 1, FLAP_RAD]) {
            rig.setFlap(a / FLAP_RAD);
            const drawn = drawnBox(rig.flapPivot);
            const corners = obbCorners(flapObb(poseOf(rig.group), a));
            ["x", "y", "z"].forEach((ax, i) => {
                const lo = Math.min(...corners.map((c) => c[i])), hi = Math.max(...corners.map((c) => c[i]));
                if (Math.abs(drawn.min[ax] - lo) > 0.0004 || Math.abs(drawn.max[ax] - hi) > 0.0004) bad.push(`flap at ${a.toFixed(2)} rad: drawn ${ax} ${drawn.min[ax].toFixed(4)}..${drawn.max[ax].toFixed(4)}, planned ${lo.toFixed(4)}..${hi.toFixed(4)}`);
            });
        }
        rig.setFlap(0);
        if (bad.length) console.error(`hinge: the room differs from anim/room.js: ${bad.join("; ")}`);
        window.__primitive = { name: "hinge", seed: opt.seed, schedule, results, roomBad: bad, settings };
    },
    stop() {
        runner?.stop();
    },
    async reset(ctx) {
        const startAt = (opt.only || opt.cycle) - 1;
        k = Math.max(0, Math.min(CYCLES - 1, startAt));
        let at = null;
        for (const c of schedule.cycles.slice(0, k)) if (c.pose) at = c.pose;
        applyPose(ctx.world.toys.deck2, schedule.msgPose);
        applyPose(rig.group, at || schedule.cycles[0].carry.from);
        rig.setFlap(0);
        ctx.world.setChestLid(0);
    },
    async cycle(ctx) {
        const c = schedule.cycles[k];
        const head = `seed ${schedule.seed} · cycle ${c.n} of ${CYCLES} · ${c.kind}: ${c.label}`;
        const swings = c.swings.map((w) => `${Math.round((w.plan.from * 180) / Math.PI)}°→${Math.round((w.plan.to * 180) / Math.PI)}° ${w.plan.ms.toFixed(0)} ms${w.plan.stopped ? ` (stopped by ${w.plan.stopped})` : ""}`).join(", ");
        const stats = `${c.what === "lid" ? "chest lid" : "flap"} ${swings}`;
        info.set(`${head}\n${stats} · checking…`);
        if (opt.only) await this.reset(ctx);
        if (opt.view === "cycle") {
            // The box where it is set down, its flap open, and the room just around it; or the chest.
            const pts = c.what === "lid" ? chestPoints(CHEST.lidOpenAngle * 1.03) : [...obbCorners(obbOf(c.pose, TUCK_BOX)), ...obbCorners(flapObb(c.pose, FLAP_RAD * 1.06))];
            if (c.what !== "lid") for (const p of [...pts]) pts.push([p[0] + 0.07, p[1] + 0.04, p[2] + 0.07], [p[0] - 0.07, p[1] - 0.01, p[2] - 0.07]);
            ctx.frame(framePoints(pts));
        }
        const fail = [];
        if (c.what === "flap") {
            const plan = c.carry.plan;
            applyPose(rig.group, c.carry.from);
            const check = createFrameCheck({ name: "KEY box", solids: c.carry.solids, shape: TUCK_BOX, maxSpeed: plan.peakSpeed, ms: plan.ms, peakMs: plan.peakMs });
            const ok = await runner.run(plan.ms, (t) => {
                applyPose(rig.group, plan.at(t));
                check.frame(rig.group, t);
            }, `carry ${c.n}`);
            if (!ok) return;
            fail.push(...check.finish(), ...seatedFail(rig.group, c.carry.surfaceTo, "KEY box"), ...sizeFail(rig.group, TUCK_BOX, "KEY box"), ...c.carry.check.fail);
            if (!(await ctx.wait(160))) return;
            for (const [i, sw] of c.swings.entries()) {
                const f = await swing(ctx, sw, {
                    set: (a) => rig.setFlap(a / FLAP_RAD),
                    sweep: (a) => flapObb(c.pose, a, FLAP_FOLD),
                    solids: c.flapSolids,
                    name: "flap",
                    label: `flap ${c.n}.${i + 1}`,
                });
                if (!f) return;
                fail.push(...f);
                if (i < c.swings.length - 1 && !(await ctx.wait(HOLD_MS))) return;
            }
        } else {
            const body = roomSolids().filter((s) => s.name !== "chest-lid");
            for (const [i, sw] of c.swings.entries()) {
                const f = await swing(ctx, sw, {
                    set: (a) => ctx.world.setChestLid(a / CHEST.lidOpenAngle),
                    sweep: (a) => chestLidObb(a),
                    solids: body,
                    name: "chest lid",
                    label: `lid ${c.n}.${i + 1}`,
                });
                if (!f) return;
                fail.push(...f);
                if (i < c.swings.length - 1 && !(await ctx.wait(HOLD_MS + 120))) return;
            }
        }
        const uniq = [...new Set(fail)];
        results.push({ n: c.n, ok: uniq.length === 0, fail: uniq, ms: c.swings.reduce((s, w) => s + w.plan.ms, 0), peakAt: 0, lawPeak: 0 });
        if (uniq.length) console.error(`hinge cycle ${c.n}: ${uniq.join("; ")}`);
        info.set(`${head}\n${stats} · ${uniq.length ? `✗ ${uniq.join("; ")}` : "checks ✓ (no overlap, seated, real size, duration and peak speed on the law)"}`, uniq.length === 0);
        if (!opt.only) k = (k + 1) % CYCLES;
    },
}, settings);
