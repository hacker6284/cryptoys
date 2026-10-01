import { mountMicro } from "../shared/micro.js";
import { GLTFLoader } from "three/addons/loaders/GLTFLoader.js";
import { DEN } from "../../playroom/constants.js";
import { easeInOutCubic, easeOutCubic } from "../../playroom/beat-clock.js";

// New primitive (no demo code yet): a peg pushed into a hole of the
// procedural ocean grid (Scrounger's bs-ecbs blockouts, real scale) on
// the playroom felt. Approach, push (accelerating into the seat), hold,
// pull out. Contact = the peg bottoms out in the hole.
const PITCH = 0.013;
const MODELS = new URL("../models/", import.meta.url);
const EASE = {
    easeInOutCubic,
    easeOutCubic,
    easeInCubic: (t) => t * t * t,
    easeInQuad: (t) => t * t,
    linear: (t) => t,
};
const EASES = Object.keys(EASE).map((k) => [k, k]);

const pegs = [];
let template = {};
let grid = null;
let raf = 0;
let hole = 0;

function animate(duration, step) {
    cancelAnimationFrame(raf);
    if (!(duration > 0)) {
        step(1);
        return Promise.resolve();
    }
    return new Promise((resolve) => {
        const start = performance.now();
        const tick = (now) => {
            const t = Math.min(1, (now - start) / duration);
            step(t);
            if (t < 1) raf = requestAnimationFrame(tick);
            else resolve();
        };
        raf = requestAnimationFrame(tick);
    });
}

function holeLocal(i) {
    // Holes at (col × pitch, −k × pitch) in the plate's frame; the
    // labels run A (k = 9, far side) to J (k = 0). Row C: k = 7.
    return { x: (i % 10) * PITCH, z: -7 * PITCH };
}

void mountMicro({
    id: "peg",
    title: "Peg into a grid hole",
    summary: "A peg is pushed into a hole of the procedural ocean grid on the felt, held, and pulled out; each loop takes the next hole along the row.",
    source: "new (no demo code yet) · models: Scrounger bs-ecbs procedural peg + ocean grid",
    camera: { position: [DEN.x + 0.05, 0.98, DEN.z + 0.26], target: [DEN.x, 0.775, DEN.z - 0.005], fov: 34 },
    timingTitle: "Timing (starting values: no demo code yet)",
    loopGapMs: 500,
    choices: [
        { key: "color", label: "Peg", value: "white", options: [["white", "white"], ["red", "red"]] },
        { key: "fill", label: "Holes", value: "row", options: [["row", "next hole each loop (fills the row)"], ["same", "same hole, pulled out"]] },
        { key: "approachEase", label: "approach ease", value: "easeInOutCubic", options: EASES },
        { key: "pushEase", label: "push ease", value: "easeInCubic", options: EASES },
        { key: "pullEase", label: "pull ease", value: "easeOutCubic", options: EASES },
    ],
    timing: [
        { key: "approachMs", label: "approachMs", min: 60, max: 1500, step: 10, value: 420, unit: " ms" },
        { key: "pushMs", label: "pushMs (into the seat)", min: 20, max: 800, step: 5, value: 140, unit: " ms" },
        { key: "holdMs", label: "holdMs", min: 0, max: 2000, step: 10, value: 450, unit: " ms" },
        { key: "pullMs", label: "pullMs", min: 60, max: 1500, step: 10, value: 320, unit: " ms" },
        { key: "hover", label: "start height (mm)", min: 5, max: 80, step: 1, value: 28, unit: " mm" },
        { key: "seat", label: "seat depth (mm)", min: 1, max: 9, step: 0.5, value: 5, unit: " mm" },
    ],
    slots: [
        { name: "push", label: "Peg seats", contact: "the peg bottoms out", from: [["peg", "in"]], gapMs: 60, voices: 3 },
        { name: "pull", label: "Peg pulled out", contact: "the peg starts to lift", from: [["peg", "out"]], gapMs: 60, voices: 3 },
    ],
    async setup(ctx) {
        ctx.status("Loading the grid and pegs…");
        const loader = new GLTFLoader();
        const load = (file) => loader.loadAsync(new URL(file, MODELS).href).then((g) => g.scene);
        const [plate, white, red] = await Promise.all([load("ocean_grid_10x10_holes.glb"), load("peg_white.glb"), load("peg_red.glb")]);
        template = { white, red };
        for (const obj of [plate, white, red]) {
            obj.traverse((n) => {
                if (n.isMesh) {
                    n.castShadow = true;
                    n.receiveShadow = true;
                }
            });
        }
        grid = new ctx.THREE.Group();
        grid.name = "micro-peg-grid";
        // Plate top at y = 0 in its frame; centre the hole field on the den.
        plate.position.set(-4.5 * PITCH, 0.003, 4.5 * PITCH);
        grid.add(plate);
        grid.position.set(DEN.x, ctx.world.table.feltTopY + 0.0005, DEN.z);
        grid.rotation.y = 0;
        ctx.world.scene.add(grid);
        ctx.plate = plate;
    },
    stop() {
        cancelAnimationFrame(raf);
    },
    async reset(ctx) {
        for (const peg of pegs.splice(0)) peg.parent?.remove(peg);
        hole = 0;
    },
    async cycle(ctx) {
        const gen = ctx.alive;
        const T = (k) => ctx.timing(k);
        const fill = ctx.choice("fill") === "row";
        if (fill && hole >= 10) await this.reset(ctx);
        const i = fill ? hole : 4;
        const peg = template[ctx.choice("color")].clone();
        const at = holeLocal(i);
        const plate = ctx.plate;
        peg.position.set(plate.position.x + at.x, 0, plate.position.z + at.z);
        const topY = plate.position.y; // plate top
        const hover = topY + T("hover") / 1000;
        const entry = topY + 0.0004;
        const seat = topY - T("seat") / 1000;
        peg.position.y = hover;
        grid.add(peg);
        pegs.push(peg);
        const approach = T("approachMs");
        const push = T("pushMs");
        const contacts = [["push", approach + push]];
        const pullAt = approach + push + T("holdMs");
        if (!fill) contacts.push(["pull", pullAt]);
        const lead = ctx.leadIn(contacts);
        if (lead && !(await ctx.wait(lead))) return;
        if (gen !== ctx.alive) return;
        const t0 = performance.now();
        for (const [slot, ms] of contacts) ctx.contact(slot, t0 + ms);
        const ea = EASE[ctx.choice("approachEase")];
        const ep = EASE[ctx.choice("pushEase")];
        await animate(approach, (t) => { peg.position.y = hover + (entry - hover) * ea(t); });
        if (gen !== ctx.alive) return;
        await animate(push, (t) => { peg.position.y = entry + (seat - entry) * ep(t); });
        if (gen !== ctx.alive) return;
        hole += 1;
        if (fill) return;
        if (!(await ctx.wait(T("holdMs")))) return;
        const eo = EASE[ctx.choice("pullEase")];
        await animate(T("pullMs"), (t) => { peg.position.y = seat + (hover - seat) * eo(t); });
        peg.parent?.remove(peg);
        pegs.pop();
    },
    config(ctx) {
        const t = {};
        for (const k of ["approachMs", "pushMs", "holdMs", "pullMs", "hover", "seat"]) t[k] = ctx.timing(k);
        return {
            demo: "peg (new primitive)",
            paste: "PEG_TIMING → the future peg demo; sounds → a demos/shared/sound.js table (offsetMs is relative to each contact)",
            PEG_TIMING: { ...t, approachEase: ctx.choice("approachEase"), pushEase: ctx.choice("pushEase"), pullEase: ctx.choice("pullEase") },
        };
    },
});
