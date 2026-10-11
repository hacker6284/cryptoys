import * as THREE from "three";
import { mountMicro } from "../../../shared/micro.js";
import * as box from "../../../../anim/yahtzee/box/index.js";
import { CAMERA, feltPose, placeBox, report } from "../../../shared/bs-scene.js";

// yahtzee/box: lid off, lid on (anim/yahtzee/box). The dice game's retail
// box (248 × 163 × 108 mm, the cup standing in it) on the felt: its 50 mm
// lid lifted straight up off the base, carried across and set down beside
// it, then put back on. Each hop is checked: no overlap, ends exact, on
// the law.
let rig = null;
let aside = null;
let shut = null;

void mountMicro({
    id: "yahtzee-box-lid-off-on",
    title: "Dice box: lid off, lid on",
    badge: "not yet approved",
    camera: { ...CAMERA, fill: 0.7 },
    slots: [],
    silent: true,
    async setup(ctx) {
        ctx.status("Loading the box…");
        shut = feltPose(ctx.world, -0.14, 0);
        aside = feltPose(ctx.world, 0.14, 0);
        aside.p[1] -= box.LID.y0; // the lid set down by its drawn bottom
        rig = await placeBox(ctx.world, "proc_dice_game_box_245x160x108.glb", "dicebox_lid", shut);
        window.__primitive = { name: "yahtzee/box lid-off-on", settings: box.settings };
    },
    frame() {
        const b = new THREE.Box3().setFromObject(rig.group);
        return b.union(b.clone().translate(new THREE.Vector3(0.28, 0, 0))).expandByScalar(0.02);
    },
    async reset() {
        rig.group.add(rig.lid);
        rig.lid.position.set(0, 0, 0);
        rig.lid.quaternion.identity();
    },
    async cycle(ctx) {
        const off = await box.liftLid(rig, aside, { solids: box.baseSolids(shut) });
        if (off) report(ctx, box.checkHop(off, { solids: box.baseSolids(shut) }), "lid off");
        await ctx.wait(500);
        const on = await box.putLid(rig, { solids: box.baseSolids(shut) });
        if (on) report(ctx, box.checkHop(on, { solids: box.baseSolids(shut) }), "lid on");
    },
}, box.settings);
