import * as THREE from "three";
import { mountMicro } from "../../shared/micro.js";
import * as dice from "../../../anim/dice/index.js";
import { CAMERA, feltAt, loadGlb } from "../../shared/bs-scene.js";

// dice: roll (anim/dice). The BS key dice at real size on the felt: a d10
// (0–9), the d12 and the d6, each thrown in turn and landing on the next
// face, so every face shows once per few loops.
const KINDS = [["d10", "facehunter_d10_22mm.glb", 10, 0], ["d12", "facehunter_d12_19mm.glb", 12, 1], ["d6", "facehunter_d6_16mm.glb", 6, 1]];
let group = null;
const dies = [];
let n = 0;

function restY(holder, kind, face) {
    const mesh = holder.userData.mesh;
    const q = dice.restQuaternion(kind, face, 0, THREE.Quaternion, THREE.Vector3);
    const pos = mesh.geometry.attributes.position;
    const v = new THREE.Vector3();
    let min = Infinity;
    for (let i = 0; i < pos.count; i++) min = Math.min(min, v.fromBufferAttribute(pos, i).multiply(mesh.scale).applyQuaternion(q).y);
    return -min + 0.0002;
}

void mountMicro({
    id: "dice-roll",
    title: "Dice: roll",
    badge: "not yet approved",
    camera: { ...CAMERA, fill: 0.5 },
    slots: [],
    silent: true,
    async setup(ctx) {
        ctx.status("Loading the dice…");
        group = new THREE.Group();
        group.position.copy(feltAt(ctx.world));
        ctx.world.scene.add(group);
        for (const [i, [kind, file, sides, from]] of KINDS.entries()) {
            const mesh = (await loadGlb(file)).scene.children[0].clone();
            const holder = new THREE.Group();
            holder.add(mesh);
            holder.userData.mesh = mesh;
            holder.position.set((i - 1) * 0.04, 0, 0);
            group.add(holder);
            dies.push({ holder, kind, sides, from });
        }
        window.__primitive = { name: "dice roll", settings: dice.settings };
    },
    frame() {
        const box = new THREE.Box3().setFromObject(group);
        return box.expandByScalar(0.03);
    },
    async reset() {
        for (const d of dies) {
            d.holder.quaternion.copy(dice.restQuaternion(d.kind, d.from, 0, THREE.Quaternion, THREE.Vector3));
            d.holder.position.y = restY(d.holder, d.kind, d.from);
        }
    },
    async cycle(ctx) {
        n += 1;
        for (const d of dies) {
            const face = d.from + (n % d.sides);
            await dice.roll(d.holder, d.kind, face, { landY: restY(d.holder, d.kind, face) });
            await ctx.wait(200);
        }
    },
}, dice.settings);
