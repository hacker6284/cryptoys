import { mountMicro } from "../../shared/micro.js";
import * as chest from "../../../anim/chest/index.js";
import { lidPlacement, DEFAULT_SEED, CAMERA } from "../../../anim/chest/placements.js";
import {
    options, placeChest, lidCheck, onlyToy, createRunner, createInfo, createSwingCheck, roomCheck, framePoints, chestPoints,
} from "../../shared/primitive.js";

// chest: open the lid, close the lid (anim/chest). The chest standing at
// one fixed spot (?seed=N picks it: anim/chest/placements.js), its lid
// opened and closed there on a loop, played through the library's own
// chest.openLid / closeLid. Nothing else moves; no toy is shown.
const opt = options(DEFAULT_SEED);
const P = lidPlacement(opt.seed);
const OPEN = chest.lid.openRad;
const HOLD_MS = 500;
let runner = null;
let info = null;
let lidRig = null;
let n = 0;
const results = [];

void mountMicro({
    id: "chest-open-close-lid",
    title: "Chest: open and close the lid",
    camera: CAMERA,
    slots: [],
    silent: true,
    frame() {
        // The chest with its lid as far open as it goes here.
        return framePoints(chestPoints(Math.max(P.open.to, 0.2) * 1.03, P.at));
    },
    async setup(ctx) {
        ctx.status("Loading the chest…");
        onlyToy(ctx.world, null);
        placeChest(ctx.world);
        const bad = roomCheck(ctx.world);
        placeChest(ctx.world, P.at);
        bad.push(...lidCheck(ctx.world, P.at));
        lidRig = ctx.world.chest; // { group, setLid(fraction), getLid() }
        runner = createRunner(ctx);
        info = createInfo();
        if (bad.length) console.error(`chest: the room differs from anim/shared/room.js: ${bad.join("; ")}`);
        window.__primitive = { name: "chest open-close-lid", seed: opt.seed, placement: P, results, roomBad: bad, settings: chest.settings };
    },
    stop() {
        runner?.stop();
    },
    async reset(ctx) {
        ctx.world.setChestLid(0);
    },
    async cycle(ctx) {
        n += 1;
        const deg = (a) => Math.round((a * 180) / Math.PI);
        const head = `seed ${P.seed} · ${P.kind}: ${P.label} · loop ${n}`;
        const stats = `lid 0°→${deg(P.open.to)}° ${P.open.ms.toFixed(0)} ms${P.open.stopped ? ` (stopped by ${P.open.stopped})` : ""}, drops shut ${P.close.ms.toFixed(0)} ms`;
        info.set(`${head}\n${stats} · checking…`);
        const fail = [];
        for (const [move, want, from, label] of [[chest.openLid, P.open, 0, "open lid"], [chest.closeLid, P.close, P.open.to / OPEN, "close lid"]]) {
            const check = createSwingCheck({ name: label, angle: () => lidRig.getLid() * OPEN, sweep: want.sweep, solids: want.solids });
            const plan = await move(lidRig, { at: P.at, from, solids: P.solids, run: (ms, step) => runner.run(ms, (t) => { step(t); check.frame(t); }, label) });
            if (!plan) return;
            if (Math.abs(plan.to - want.to) > 1e-9 || Math.abs(plan.ms - want.ms) > 1e-9) fail.push(`${label}: played ${plan.to.toFixed(3)} rad in ${plan.ms.toFixed(0)} ms, planned ${want.to.toFixed(3)} in ${want.ms.toFixed(0)}`);
            fail.push(...check.finish(plan), ...P.checks[want === P.open ? 0 : 1].fail);
            if (!(await ctx.wait(HOLD_MS))) return;
        }
        const uniq = [...new Set(fail)];
        results.push({ n, ok: uniq.length === 0, fail: uniq, ms: P.open.ms + P.close.ms });
        if (uniq.length) console.error(`chest loop ${n}: ${uniq.join("; ")}`);
        info.set(`${head}\n${stats} · ${uniq.length ? `✗ ${uniq.join("; ")}` : "checks ✓ (no overlap, drawn lid in its box, duration and peak speed on the law)"}`, uniq.length === 0);
    },
}, chest.settings);
