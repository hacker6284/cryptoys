import * as THREE from "three";
import { mountMicro } from "../../../shared/micro.js";
import * as box from "../../../../anim/battleship/box/index.js";
import { CAMERA, feltPose, placeBox, report } from "../../../shared/bs-scene.js";

// battleship/box: lid off, lid on (anim/battleship/box). The Battleship
// retail box (400 × 265 × 52.5 mm, empty here: the units are
// lift-units-out-in's) on the felt: its lid lifted straight up off the
// base, carried across and set down beside it, then put back on. Each hop is checked: no overlap, ends exact,
// on the law.
let rig = null;
let aside = null;
let shut = null;

void mountMicro({
    id: "battleship-box-lid-off-on",
    title: "Battleship box: lid off, lid on",
    badge: "not yet approved",
    camera: { ...CAMERA, fill: 0.7 },
    slots: [],
    silent: true,
    async setup(ctx) {
        ctx.status("Loading the box…");
        shut = feltPose(ctx.world, -0.215, 0);
        aside = feltPose(ctx.world, 0.215, 0);
        rig = await placeBox(ctx.world, "proc_naval_game_box_400x265x52.glb", "navalbox_lid", shut);
        window.__primitive = { name: "battleship/box lid-off-on", settings: box.settings };
    },
    frame() {
        const b = new THREE.Box3().setFromObject(rig.group);
        return b.union(b.clone().translate(new THREE.Vector3(0.43, 0, 0))).expandByScalar(0.02);
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
