import * as THREE from "three";
import { mountMicro } from "../../shared/micro.js";
import * as ship from "../../../anim/ship/index.js";
import { CAMERA, loadGlb, placeUnit } from "../../shared/bs-scene.js";
import { BS_GRID as G } from "../../../playroom/constants.js";

// ship: place, move, lift (anim/ship). A Destroyer is laid across C3–C4
// of the key grid, swapped for the Sub as the ship grows (BUILD, SPEC
// §4.2); the walk cursor's Destroyer slides along the grid's number strip
// (§4.3); then each piece lifts off.
let unit = null;
let pieces = {};
let cursor = null;

void mountMicro({
    id: "ship-place-move-lift",
    title: "Ship: place, move, lift",
    badge: "not yet approved",
    camera: CAMERA,
    slots: [],
    silent: true,
    async setup(ctx) {
        ctx.status("Loading the unit…");
        unit = await placeUnit(ctx.world);
        const ships = (await loadGlb("bs_ships.glb")).scene;
        pieces = { d: ships.getObjectByName("ship_destroyer_2").clone(), s: ships.getObjectByName("ship_submarine_3").clone() };
        cursor = ships.getObjectByName("ship_destroyer_2").clone();
        for (const m of [pieces.d, pieces.s, cursor]) {
            m.position.set(0, 0, 0);
            m.visible = false;
            unit.root.add(m);
        }
        window.__primitive = { name: "ship place-move-lift", settings: ship.settings };
    },
    frame() {
        return new THREE.Box3().setFromObject(unit.root);
    },
    async reset() {
        for (const m of [pieces.d, pieces.s, cursor]) m.visible = false;
    },
    async cycle(ctx) {
        const mid = (a, b) => unit.ocean(a).add(unit.ocean(b)).multiplyScalar(0.5);
        const strip = (col) => new THREE.Vector3(G.x0 + col * G.pitch, G.plateY, G.frameTopZ);
        await ship.place(pieces.d, mid(22, 23));
        await ctx.wait(300);
        await ship.lift(pieces.d);
        await ship.place(pieces.s, mid(22, 24));
        await ctx.wait(300);
        cursor.position.copy(strip(0));
        cursor.visible = true;
        for (let c = 1; c < 6; c++) await ship.move(cursor, strip(c));
        await ctx.wait(300);
        await ship.lift(cursor);
        await ship.lift(pieces.s);
    },
}, ship.settings);
