import * as THREE from "three";
import { mountMicro } from "../../shared/micro.js";
import * as dice from "../../../anim/dice/index.js";
import { CAMERA, feltPose, loadGlb, setPose } from "../../shared/bs-scene.js";
import { BS_DICE_PACK } from "../../../playroom/constants.js";

// dice: place (anim/dice). The cup on the felt (scenery) with a d10, the
// d12 and the d6 in it where they are packed (playroom/constants.js
// BS_DICE_PACK): each lifted straight up out of the cup, carried across
// turning onto the face it shows, set down on its spot, then put back.
// Each hop is checked against the cup's wall: no overlap, ends exact, on
// the law.
const KINDS = [["d6", "facehunter_d6_16mm.glb", BS_DICE_PACK.d6, 6], ["d12", "facehunter_d12_19mm_box.glb", BS_DICE_PACK.d12, 12], ["d10", "facehunter_d10_22mm.glb", BS_DICE_PACK.d10[4], 5]];
let cup = null;
let at = null;
const dies = [];

function restY(holder, kind, q) {
    const mesh = holder.userData.mesh;
    const pos = mesh.geometry.attributes.position;
    const v = new THREE.Vector3();
    let min = Infinity;
    for (let i = 0; i < pos.count; i++) min = Math.min(min, v.fromBufferAttribute(pos, i).multiply(mesh.scale).applyQuaternion(q).y);
    return -min + 0.0002;
}

const cupRing = () => [
    { kind: "cyl", x: at.p[0], z: at.p[2], r: 0.0413, rIn: 0.0342, y0: at.p[1], y1: at.p[1] + 0.1016, name: "the cup's wall" },
];

void mountMicro({
    id: "dice-place",
    title: "Dice: place",
    badge: "not yet approved",
    camera: { ...CAMERA, fill: 0.55 },
    slots: [],
    silent: true,
    async setup(ctx) {
        ctx.status("Loading the cup and the dice…");
        at = feltPose(ctx.world, -0.07, 0);
        cup = (await loadGlb("proc_dice_cup_83x102mm.glb")).scene;
        setPose(cup, at);
        ctx.world.scene.add(cup);
        for (const [i, [kind, file, packed, face]] of KINDS.entries()) {
            const mesh = (await loadGlb(file)).scene.children[0].clone();
            const holder = new THREE.Group();
            holder.add(mesh);
            holder.userData.mesh = mesh;
            ctx.world.scene.add(holder);
            const q = dice.restQuaternion(kind, face, 0.3 * i, THREE.Quaternion, THREE.Vector3);
            const f = feltPose(ctx.world, 0.03 + i * 0.035, 0.03);
            const spot = { p: [f.p[0], f.p[1] + restY(holder, kind, q), f.p[2]], q: [q.x, q.y, q.z, q.w] };
            const inCup = { p: [at.p[0] + packed[0], at.p[1] + packed[1], at.p[2] + packed[2]], q: [0, 0, 0, 1] };
            dies.push({ holder, kind, spot, inCup });
        }
        window.__primitive = { name: "dice place", settings: dice.settings };
    },
    frame() {
        const b = new THREE.Box3().setFromObject(cup);
        for (const d of dies) b.expandByPoint(new THREE.Vector3(...d.spot.p));
        return b.expandByScalar(0.03);
    },
    async reset() {
        for (const d of dies) setPose(d.holder, d.inCup);
    },
    async cycle(ctx) {
        const rim = at.p[1] + 0.1016;
        for (const d of dies) {
            const plan = await dice.place(d.holder, d.kind, d.spot, { clearY: rim, solids: cupRing() });
            if (plan) report(ctx, dice.checkHop(plan, { solids: cupRing() }), `${d.kind} out`);
            await ctx.wait(150);
        }
        await ctx.wait(500);
        for (const d of dies.slice().reverse()) {
            const plan = await dice.place(d.holder, d.kind, d.inCup, { clearY: rim, solids: cupRing() });
            if (plan) report(ctx, dice.checkHop(plan, { solids: cupRing() }), `${d.kind} in`);
            await ctx.wait(150);
        }
    },
}, dice.settings);

function report(ctx, r, what) {
    if (!r.ok) {
        console.warn(`${what}: ${r.fail.join("; ")}`);
        ctx.status(`${what}: ${r.fail.join("; ")}`);
    }
}
