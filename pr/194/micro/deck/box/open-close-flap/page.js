import { mountMicro } from "../../../shared/micro.js";
import * as box from "../../../../anim/deck/box/index.js";
import { flapPlacement, DEFAULT_SEED } from "../../../../anim/deck/box/placements.js";
import { obbCorners, obbOf } from "../../../../anim/shared/geom.js";
import { addGlow, buildBox, restowBox } from "../../../shared/boxes.js";
import {
    options, placeChest, onlyToy, applyPose, poseOf, createRunner, createInfo, createSwingCheck, seatedFail, sizeFail, roomCheck, drawnBox, framePoints,
} from "../../../shared/primitive.js";

// deck/box: open the flap, close the flap (anim/deck/box). One tuck box at
// one fixed pose (?seed=N picks it: anim/deck/box/placements.js), its flap
// opened and closed there on a loop, played through the library's own
// deck.box.openFlap / closeFlap. Nothing else moves; no other toy is shown.
const opt = options(DEFAULT_SEED);
const P = flapPlacement(opt.seed);
const OPEN = box.flap.openRad;
const HOLD_MS = 450;
let runner = null;
let info = null;
let rig = null;
let n = 0;
const results = [];

void mountMicro({
    id: "deck-box-open-close-flap",
    title: "Deck box: open and close the flap",
    camera: { position: [0.9, 2.3, 3.1], target: [-1.15, 0.8, -0.25], fov: 40, fill: 0.92 },
    slots: [],
    silent: true,
    frame() {
        // The box and its flap fully open, with a little of the room around it.
        const pts = [...obbCorners(obbOf(P.pose, box.TUCK_BOX)), ...obbCorners(box.flapObb(P.pose, OPEN * 1.06))];
        for (const p of [...pts]) pts.push([p[0] + 0.07, p[1] + 0.04, p[2] + 0.07], [p[0] - 0.07, p[1] - 0.01, p[2] - 0.07]);
        return framePoints(pts);
    },
    async setup(ctx) {
        ctx.status("Loading the tuck box…");
        placeChest(ctx.world);
        addGlow(ctx.world, "deck");
        rig = await buildBox(ctx.world, "deck", "KEY");
        restowBox(rig);
        onlyToy(ctx.world, "deck");
        runner = createRunner(ctx);
        info = createInfo();
        const bad = roomCheck(ctx.world);
        bad.push(...sizeFail(rig.group, box.TUCK_BOX, "KEY tuck box"));
        // The flap's planned box against its drawn mesh at a few angles.
        applyPose(rig.group, P.pose);
        for (const a of [0, 1, OPEN]) {
            rig.setFlap(a / OPEN);
            const drawn = drawnBox(rig.flapPivot);
            const corners = obbCorners(box.flapObb(poseOf(rig.group), a));
            ["x", "y", "z"].forEach((ax, i) => {
                const lo = Math.min(...corners.map((c) => c[i])), hi = Math.max(...corners.map((c) => c[i]));
                if (Math.abs(drawn.min[ax] - lo) > 0.0004 || Math.abs(drawn.max[ax] - hi) > 0.0004) bad.push(`flap at ${a.toFixed(2)} rad: drawn ${ax} ${drawn.min[ax].toFixed(4)}..${drawn.max[ax].toFixed(4)}, planned ${lo.toFixed(4)}..${hi.toFixed(4)}`);
            });
        }
        rig.setFlap(0);
        if (bad.length) console.error(`deck box: the room differs from anim/shared/room.js: ${bad.join("; ")}`);
        window.__primitive = { name: "deck/box open-close-flap", seed: opt.seed, placement: P, results, roomBad: bad, settings: box.settings };
    },
    stop() {
        runner?.stop();
    },
    async reset() {
        applyPose(rig.group, P.pose);
        rig.setFlap(0);
    },
    async cycle(ctx) {
        n += 1;
        const deg = (a) => Math.round((a * 180) / Math.PI);
        const head = `seed ${P.seed} · ${P.kind}: ${P.label} · loop ${n}`;
        const stats = `flap 0°→${deg(P.open.to)}° ${P.open.ms.toFixed(0)} ms${P.open.stopped ? ` (stopped by ${P.open.stopped})` : ""}, back to 0° ${P.close.ms.toFixed(0)} ms`;
        info.set(`${head}\n${stats} · checking…`);
        const fail = [...seatedFail(rig.group, P.surfaceY, "KEY box"), ...sizeFail(rig.group, box.TUCK_BOX, "KEY box")];
        const at0 = poseOf(rig.group);
        for (const [move, want, from, label] of [[box.openFlap, P.open, 0, "open flap"], [box.closeFlap, P.close, P.open.to / OPEN, "close flap"]]) {
            const check = createSwingCheck({ name: label, angle: () => -rig.flapPivot.rotation.x, sweep: want.sweep, solids: want.solids });
            const plan = await move(rig, { from, solids: P.solids, run: (ms, step) => runner.run(ms, (t) => { step(t); check.frame(t); }, label) });
            if (!plan) return;
            if (Math.abs(plan.to - want.to) > 1e-9 || Math.abs(plan.ms - want.ms) > 1e-9) fail.push(`${label}: played ${plan.to.toFixed(3)} rad in ${plan.ms.toFixed(0)} ms, planned ${want.to.toFixed(3)} in ${want.ms.toFixed(0)}`);
            fail.push(...check.finish(plan), ...P.checks[want === P.open ? 0 : 1].fail);
            if (!(await ctx.wait(HOLD_MS))) return;
        }
        const at1 = poseOf(rig.group);
        if (Math.hypot(...at1.p.map((v, i) => v - at0.p[i])) > 1e-6) fail.push("the box moved while its flap swung");
        fail.push(...sizeFail(rig.group, box.TUCK_BOX, "KEY box"));
        const uniq = [...new Set(fail)];
        results.push({ n, ok: uniq.length === 0, fail: uniq, ms: P.open.ms + P.close.ms });
        if (uniq.length) console.error(`deck box loop ${n}: ${uniq.join("; ")}`);
        info.set(`${head}\n${stats} · ${uniq.length ? `✗ ${uniq.join("; ")}` : "checks ✓ (no overlap, seated, real size, duration and peak speed on the law)"}`, uniq.length === 0);
    },
}, box.settings);
