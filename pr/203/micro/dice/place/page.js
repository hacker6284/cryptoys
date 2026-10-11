import * as THREE from "three";
import { mountMicro } from "../../shared/micro.js";
import * as dice from "../../../anim/dice/index.js";
import { CAMERA, feltPose, loadGlb, placeBox, report } from "../../shared/bs-scene.js";
import { setWorldPose, worldPose } from "../../../anim/shared/run.js";
import { obbOf } from "../../../anim/shared/geom.js";
import { BS_DICE_PACK, BS_DIE_LIFT } from "../../../playroom/constants.js";

// dice: place (anim/dice). The dice box open on the felt (scenery, its
// lid off) with a d10, the d12 and the d6 lying in its strip on the other
// four d10s, where they are packed (playroom/constants.js BS_DICE_PACK):
// each lifted straight up out of the box until it clears the rim, carried
// across turning onto the face it shows, set down on its spot, then put
// back. Each hop is checked: clear of the other dice, ends exact, on the
// law.
const KINDS = [["d6", "facehunter_d6_16mm.glb", BS_DICE_PACK.d6, 6], ["d12", "facehunter_d12_19mm_box.glb", BS_DICE_PACK.d12, 12], ["d10", "facehunter_d10_22mm.glb", BS_DICE_PACK.d10[4], 5]];
let box = null;
let at = null;
let rim = 0;
const dies = [];

const under = []; // the four d10s they lie on (scenery: the strip's bottom layer)

// What a die must not touch on its way: the other two dice, wherever they are, and the layer under them.
const others = (d) => [
    ...dies.filter((e) => e !== d).map((e) => ({ ...obbOf(worldPose(e.holder), dice.SHAPES[e.kind]), name: e.kind })),
    ...under.map((m, k) => ({ ...obbOf(worldPose(m), dice.SHAPES.d10), name: `d10#${k}` })),
];

void mountMicro({
    id: "dice-place",
    title: "Dice: place",
    badge: "not yet approved",
    camera: { ...CAMERA, fill: 0.55 },
    slots: [],
    silent: true,
    async setup(ctx) {
        ctx.status("Loading the box and the dice…");
        at = feltPose(ctx.world, -0.07, 0);
        box = await placeBox(ctx.world, "proc_dice_game_box_120x114x89.glb", "dicebox_lid", at);
        box.lid.removeFromParent();
        rim = new THREE.Box3().setFromObject(box.group).max.y; // the base's rim, as drawn
        for (const p of BS_DICE_PACK.d10.slice(0, 4)) {
            const m = (await loadGlb("facehunter_d10_22mm.glb")).scene.children[0].clone();
            m.position.fromArray(p);
            box.group.add(m);
            under.push(m);
        }
        for (const [i, [kind, file, packed, face]] of KINDS.entries()) {
            const mesh = (await loadGlb(file)).scene.children[0].clone();
            const holder = new THREE.Group();
            holder.add(mesh);
            holder.userData.mesh = mesh;
            ctx.world.scene.add(holder);
            const q = dice.restQuaternion(kind, face, 0.3 * i, THREE.Quaternion, THREE.Vector3);
            const f = feltPose(ctx.world, 0.03 + i * 0.035, 0.05);
            const spot = { p: [f.p[0], f.p[1] + dice.restHeight(mesh, kind, face, THREE.Quaternion, THREE.Vector3) + BS_DIE_LIFT, f.p[2]], q: [q.x, q.y, q.z, q.w] };
            const inBox = { p: [at.p[0] + packed[0], at.p[1] + packed[1], at.p[2] + packed[2]], q: [0, 0, 0, 1] };
            dies.push({ holder, kind, spot, inBox });
        }
        window.__primitive = { name: "dice place", settings: dice.settings };
    },
    frame() {
        const b = new THREE.Box3().setFromObject(box.group);
        for (const d of dies) b.expandByPoint(new THREE.Vector3(...d.spot.p));
        return b.expandByScalar(0.03);
    },
    async reset() {
        for (const d of dies) setWorldPose(d.holder, d.inBox);
    },
    async cycle(ctx) {
        for (const d of dies) {
            const solids = others(d);
            const plan = await dice.place(d.holder, d.kind, d.spot, { clearY: rim, solids });
            if (plan) report(ctx, dice.checkHop(plan, { solids }), `${d.kind} out`);
            await ctx.wait(150);
        }
        await ctx.wait(500);
        for (const d of dies.slice().reverse()) {
            const solids = others(d);
            const plan = await dice.place(d.holder, d.kind, d.inBox, { clearY: rim, solids });
            if (plan) report(ctx, dice.checkHop(plan, { solids }), `${d.kind} in`);
            await ctx.wait(150);
        }
    },
}, dice.settings);
