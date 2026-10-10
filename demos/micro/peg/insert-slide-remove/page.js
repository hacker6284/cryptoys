import * as THREE from "three";
import { mountMicro } from "../../shared/micro.js";
import * as peg from "../../../anim/peg/index.js";
import { CAMERA, hideToys, loadGlb, placeUnit } from "../../shared/bs-scene.js";

// peg: insert, slide, remove (anim/peg). A white peg goes into a hole of
// the key (ocean) grid and comes out; a red peg goes into the workspace
// (the lid's target grid, pointing out of it), slides two rows down and
// comes out: the moves the BS demo plays, at the entry's own tempo.
let unit = null;
let white = null;
let red = null;
const UP = new THREE.Vector3(0, 1, 0);
const OUT = new THREE.Vector3(0, -1, 0); // out of the lid's holes, lid frame

void mountMicro({
    id: "peg-insert-slide-remove",
    title: "Peg: insert, slide, remove",
    badge: "not yet approved",
    camera: CAMERA,
    slots: [],
    silent: true,
    async setup(ctx) {
        ctx.status("Loading the unit…");
        hideToys(ctx.world);
        unit = await placeUnit(ctx.world);
        const pegs = (await loadGlb("bs_pegs.glb")).scene;
        white = pegs.getObjectByName("peg_white").clone();
        red = pegs.getObjectByName("peg_red").clone();
        red.rotation.x = Math.PI;
        unit.root.add(white);
        unit.lid.add(red);
        window.__primitive = { name: "peg insert-slide-remove", settings: peg.settings };
    },
    frame() {
        return new THREE.Box3().setFromObject(unit.root);
    },
    async reset() {
        white.visible = false;
        red.visible = false;
    },
    async cycle(ctx) {
        const go = (p) => p.then((ok) => ok && ctx.alive);
        await go(peg.insert(white, unit.ocean(44), UP));
        await ctx.wait(300);
        await go(peg.insert(red, unit.lidSeat(44), OUT));
        await ctx.wait(300);
        await go(peg.slide(red, unit.lidSeat(44), unit.lidSeat(64), OUT));
        await ctx.wait(300);
        await go(peg.remove(red, OUT));
        await go(peg.remove(white, UP));
    },
}, peg.settings);
