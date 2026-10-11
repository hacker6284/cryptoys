import * as THREE from "three";
import { mountMicro } from "../../../shared/micro.js";
import * as box from "../../../../anim/battleship/box/index.js";
import { obbOf } from "../../../../anim/shared/geom.js";
import { CAMERA, closedUnit, feltPose, placeBox } from "../../../shared/bs-scene.js";

// battleship/box: lift the units out, put them in (anim/battleship/box).
// The Battleship box open on the felt (its lid set aside, out of view) with
// both units packed in it, shut, either side of the card divider: Alice's
// red unit lifted out and set down in front, square to the seat, then Bob's
// blue unit; then each put back in its pocket. Each hop is checked against
// the box and the other unit: no overlap, ends exact, on the law.
let rig = null;
let units = [];
let at = null;
let seats = [];

void mountMicro({
    id: "battleship-box-lift-units-out-in",
    title: "Battleship box: lift the units out, put them in",
    badge: "not yet approved",
    camera: { ...CAMERA, fill: 0.7 },
    slots: [],
    silent: true,
    async setup(ctx) {
        ctx.status("Loading the box and the units…");
        at = feltPose(ctx.world, 0, -0.2);
        seats = [feltPose(ctx.world, -0.135, 0.12), feltPose(ctx.world, 0.135, 0.12)];
        rig = await placeBox(ctx.world, "proc_naval_game_box_400x265x52.glb", "navalbox_lid", at);
        rig.lid.visible = false;
        units = [await closedUnit("bs_unit_red.glb"), await closedUnit("bs_unit_blue.glb")];
        window.__primitive = { name: "battleship/box lift-units-out-in", settings: box.settings };
    },
    frame() {
        const b = new THREE.Box3().setFromObject(rig.group);
        for (const s of seats) b.expandByPoint(new THREE.Vector3(s.p[0], s.p[1], s.p[2] + 0.09));
        return b.expandByScalar(0.03);
    },
    async reset() {
        units.forEach((u, k) => box.pack(rig, k, u.group));
    },
    async cycle(ctx) {
        const unitSolid = (k, pose) => [{ ...obbOf(pose, box.UNIT), name: `unit ${k}` }];
        for (const k of [0, 1]) {
            const other = k ? unitSolid(0, seats[0]) : unitSolid(1, box.pocketPose(at, 1));
            const plan = await box.liftOut(rig, k, units[k].group, seats[k], { solids: other });
            if (plan) report(ctx, box.checkHop(plan, { solids: [...box.baseSolids(at), ...other] }), `unit ${k} out`);
            await ctx.wait(250);
        }
        await ctx.wait(400);
        for (const k of [1, 0]) {
            const other = k ? unitSolid(0, seats[0]) : [];
            const plan = await box.putIn(rig, k, units[k].group, { solids: other });
            if (plan) report(ctx, box.checkHop(plan, { solids: [...box.baseSolids(at), ...other] }), `unit ${k} in`);
            await ctx.wait(250);
        }
    },
}, box.settings);

function report(ctx, r, what) {
    if (!r.ok) {
        console.warn(`${what}: ${r.fail.join("; ")}`);
        ctx.status(`${what}: ${r.fail.join("; ")}`);
    }
}
