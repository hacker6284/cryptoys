import * as THREE from "three";
import { mountMicro } from "../../../shared/micro.js";
import * as box from "../../../../anim/yahtzee/box/index.js";
import { CAMERA, feltPose, loadGlb, placeBox, report } from "../../../shared/bs-scene.js";
import { BS_DICE_PACK } from "../../../../playroom/constants.js";

// yahtzee/box: lift the cup out, put it in (anim/yahtzee/box). The dice
// box open on the felt (its lid set aside, out of view), the cup standing
// in it with the BS key dice packed inside (playroom/constants.js
// BS_DICE_PACK): the cup lifted straight up out of the box, set down in
// front of it, and put back. Each hop is checked against the box: no
// overlap, ends exact, on the law.
let rig = null;
let cup = null;
let at = null;
let spot = null;

void mountMicro({
    id: "yahtzee-box-lift-cup-out-in",
    title: "Dice box: lift the cup out, put it in",
    badge: "not yet approved",
    camera: { ...CAMERA, fill: 0.6 },
    slots: [],
    silent: true,
    async setup(ctx) {
        ctx.status("Loading the box, the cup and the dice…");
        at = feltPose(ctx.world, -0.08, -0.04);
        spot = feltPose(ctx.world, 0.11, 0.06);
        rig = await placeBox(ctx.world, "proc_dice_game_box_245x160x108.glb", "dicebox_lid", at);
        rig.lid.visible = false;
        cup = new THREE.Group();
        cup.add((await loadGlb("proc_dice_cup_83x102mm.glb")).scene);
        const files = { d10: "facehunter_d10_22mm.glb", d12: "facehunter_d12_19mm_box.glb", d6: "facehunter_d6_16mm.glb" };
        const dieOf = async (kind, p) => {
            const m = (await loadGlb(files[kind])).scene.children[0].clone();
            m.position.fromArray(p);
            cup.add(m);
        };
        for (const p of BS_DICE_PACK.d10) await dieOf("d10", p);
        await dieOf("d12", BS_DICE_PACK.d12);
        await dieOf("d6", BS_DICE_PACK.d6);
        window.__primitive = { name: "yahtzee/box lift-cup-out-in", settings: box.settings };
    },
    frame() {
        const b = new THREE.Box3().setFromObject(rig.group);
        b.expandByPoint(new THREE.Vector3(spot.p[0] + 0.05, spot.p[1] + 0.1, spot.p[2] + 0.05));
        return b.expandByScalar(0.02);
    },
    async reset() {
        box.pack(rig, cup);
    },
    async cycle(ctx) {
        const out = await box.liftOut(rig, cup, spot);
        if (out) report(ctx, box.checkHop(out, { solids: box.baseSolids(at) }), "cup out");
        await ctx.wait(500);
        const back = await box.putIn(rig, cup);
        if (back) report(ctx, box.checkHop(back, { solids: box.baseSolids(at) }), "cup in");
    },
}, box.settings);
