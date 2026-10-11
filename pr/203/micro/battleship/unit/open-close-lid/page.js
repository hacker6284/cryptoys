import * as THREE from "three";
import { mountMicro } from "../../../shared/micro.js";
import * as unit from "../../../../anim/battleship/unit/index.js";
import { CAMERA, closedUnit, feltPose, setPose } from "../../../shared/bs-scene.js";

// battleship/unit: open and close the lid (anim/battleship/unit). Alice's
// red unit, shut, on the felt: its lid swings up on its hinge to upright
// (T1: the lid's grid is the workspace) and back down onto the tray. The
// swing is checked: no overlap, ends exact, duration and peak on the law.
let rig = null;

void mountMicro({
    id: "battleship-unit-open-close-lid",
    title: "Battleship unit: open and close the lid",
    badge: "not yet approved",
    camera: { ...CAMERA, fill: 0.7 },
    slots: [],
    silent: true,
    async setup(ctx) {
        ctx.status("Loading the unit…");
        rig = await closedUnit("bs_unit_red.glb");
        setPose(rig.group, feltPose(ctx.world));
        ctx.world.scene.add(rig.group);
        window.__primitive = { name: "battleship/unit open-close-lid", settings: unit.settings };
    },
    frame() {
        const b = new THREE.Box3().setFromObject(rig.group);
        return b.expandByPoint(b.min.clone().setY(b.min.y + unit.OPEN.max[1])).expandByScalar(0.02);
    },
    async reset() {
        unit.setLid(rig, 0);
    },
    async cycle(ctx) {
        const open = await unit.openLid(rig);
        if (open) report(ctx, unit.checkLid(open), "open");
        await ctx.wait(500);
        const shut = await unit.closeLid(rig);
        if (shut) report(ctx, unit.checkLid(shut), "close");
    },
}, unit.settings);

function report(ctx, r, what) {
    if (!r.ok) {
        console.warn(`${what}: ${r.fail.join("; ")}`);
        ctx.status(`${what}: ${r.fail.join("; ")}`);
    }
}
