/**
 * Shared bits of the primitive microdemos (carry, hinge): the proposed
 * chest placement, a frame-driven tween, the small seed / cycle / checks
 * line, the per-frame checks, and the room check (the numbers in
 * anim/room.js against the drawn meshes).
 */
import * as THREE from "three";
import { CHEST, chestBodyObb, chestFrame, chestLidObb, ROOM, FELT_Y, DEN } from "../../anim/room.js";
import { obbCorners, obbOf, worstDepth } from "../../anim/geom.js";

/**
 * URL options: ?seed=N, ?cycle=N (start there), ?only=N (loop that
 * cycle), ?view=cycle (inspection: the view framed on each cycle's own
 * placements, fixed for the cycle, instead of the loop's union).
 */
export function options(defaultSeed) {
    const q = new URLSearchParams(location.search);
    const num = (k, d) => (q.has(k) && Number.isFinite(+q.get(k)) ? +q.get(k) : d);
    return { seed: num("seed", defaultSeed), cycle: num("cycle", 1), only: num("only", 0), view: q.get("view") || "loop" };
}

/** Turn the chest to anim/room.js CHEST (yaw about its own centre). */
export function placeChest(world, chest = CHEST) {
    const g = world.chest.group;
    world.setChestLid(0);
    g.rotation.y = chest.yaw;
    g.updateMatrixWorld(true);
    const c = drawnBox(g).getCenter(new THREE.Vector3());
    g.position.x += chest.centre[0] - c.x;
    g.position.z += chest.centre[1] - c.z;
    g.updateMatrixWorld(true);
}

/**
 * The drawn chest against room.js at `chest` (anim/room.js chestAt): its
 * hinge height, and its lid's oriented box holding the drawn dome shut,
 * half and fully open (the rounded top leaves the box's corner up to
 * ~19 cm proud part-way open). Returns mismatches.
 */
export function lidCheck(world, chest = CHEST) {
    const bad = [];
    const g = world.chest.group;
    let lidPivot = null;
    g.traverse((o) => { if (o.name === "chest-lid-pivot") lidPivot = o; });
    if (!lidPivot) return ["chest: no lid pivot"];
    const lidAt = world.getChestLid?.() ?? 0;
    const p = lidPivot.getWorldPosition(new THREE.Vector3());
    const want = chestFrame(chest).pivot;
    if (Math.abs(p.y - want[1]) > 0.003) bad.push(`chest hinge height: drawn ${p.y.toFixed(4)}, room.js ${want[1].toFixed(4)}`);
    for (const k of [0, 0.5, 1]) {
        world.setChestLid(k);
        const drawn = drawnBox(lidPivot);
        const corners = obbCorners(chestLidObb(k * CHEST.lidOpenAngle, chest));
        const lo = [0, 1, 2].map((i) => Math.min(...corners.map((c) => c[i])));
        const hi = [0, 1, 2].map((i) => Math.max(...corners.map((c) => c[i])));
        ["x", "y", "z"].forEach((ax, i) => {
            if (drawn.min[ax] < lo[i] - 0.003 || drawn.max[ax] > hi[i] + 0.003) bad.push(`chest lid at ${k}: drawn ${ax} outside its box`);
            if (lo[i] < drawn.min[ax] - 0.2 || hi[i] > drawn.max[ax] + 0.2) bad.push(`chest lid at ${k}: box ${ax} too loose`);
        });
    }
    world.setChestLid(lidAt);
    return bad;
}

/** World box of an object's meshes (vertex-precise, the contact shadow plane left out). */
export function drawnBox(object) {
    const box = new THREE.Box3();
    object.updateMatrixWorld(true);
    object.traverse((o) => {
        if (!o.isMesh || !o.geometry || o.userData.noBounds) return;
        if (o.geometry.type === "PlaneGeometry" && o.material?.transparent && o.material?.depthWrite === false) return;
        const pos = o.geometry.attributes.position;
        const v = new THREE.Vector3();
        for (let i = 0; i < pos.count; i++) box.expandByPoint(v.fromBufferAttribute(pos, i).applyMatrix4(o.matrixWorld));
    });
    return box;
}

/** The object's drawn bounds in its own frame (min, max arrays). */
export function localBounds(object) {
    const box = new THREE.Box3();
    object.updateMatrixWorld(true);
    const inv = object.matrixWorld.clone().invert();
    object.traverse((o) => {
        if (!o.isMesh || !o.geometry) return;
        const pos = o.geometry.attributes.position;
        const v = new THREE.Vector3();
        const m = inv.clone().multiply(o.matrixWorld);
        for (let i = 0; i < pos.count; i++) box.expandByPoint(v.fromBufferAttribute(pos, i).applyMatrix4(m));
    });
    return { min: box.min.toArray(), max: box.max.toArray() };
}

/**
 * The fixed view's frame: a THREE.Box3 over `points` ([x, y, z]) that
 * carries them, so micro.js fits the view to the points themselves (the
 * union of the loop's placements and paths), not the box's empty corners.
 */
export function framePoints(points) {
    const vs = points.map((p) => new THREE.Vector3(...p));
    const box = new THREE.Box3().setFromPoints(vs);
    box.points = vs;
    return box;
}

/** The chest's points for the frame: its body's top corners and its lid open. */
export function chestPoints(lidAngle = CHEST.lidOpenAngle, chest = CHEST) {
    return [...obbCorners(chestBodyObb(chest)), ...obbCorners(chestLidObb(lidAngle, chest))];
}

/** The surfaces the loops use, for the frame: the felt's rim and the stretch of shelf. */
export function surfacePoints() {
    const pts = [];
    for (let i = 0; i < 24; i++) {
        const a = (i / 24) * Math.PI * 2;
        pts.push([DEN.x + Math.cos(a) * 1.03, 0.79, DEN.z + Math.sin(a) * 1.03]);
    }
    for (const x of [-2.15, 0.25]) pts.push([x, 1.24, -2.3], [x, 1.24, -2.0], [x, 1.475, -2.3]);
    return pts;
}

export function applyPose(object, pose) {
    object.position.set(...pose.p);
    object.quaternion.set(...pose.q);
    object.updateMatrixWorld(true);
}

export function poseOf(object) {
    return { p: object.position.toArray(), q: object.quaternion.toArray() };
}

/**
 * Frame-driven tween: step(elapsedMs) every frame until `ms`, then
 * step(ms). Resolves false if the loop was restarted (ctx.alive changed).
 */
export function createRunner(ctx) {
    let job = null;
    ctx.onFrame = (now) => {
        if (!job) return;
        const t = Math.min(job.ms, now - job.t0);
        job.step(t, now);
        if (t >= job.ms) {
            const done = job.done;
            job = null;
            done(true);
        }
    };
    return {
        /** name: what moves (published as window.__primitiveJob for captures). */
        run(ms, step, name = "") {
            const gen = ctx.alive;
            window.__primitiveJob = { name, ms, t0: performance.now(), seq: (window.__primitiveJob?.seq || 0) + 1 };
            return new Promise((resolve) => {
                const t0 = performance.now();
                step(0, t0);
                if (!(ms > 0)) return resolve(gen === ctx.alive);
                job = { ms, t0, step, done: (ok) => resolve(ok && gen === ctx.alive) };
            });
        },
        stop() {
            if (job) { const d = job.done; job = null; d(false); }
        },
    };
}

/** The small line under the scene: seed, cycle, what it shows, the checks. */
export function createInfo() {
    const el = document.createElement("p");
    el.className = "micro-seed";
    el.setAttribute("aria-live", "polite");
    document.querySelector(".micro")?.append(el);
    return {
        set(text, ok) {
            el.textContent = text;
            el.classList.toggle("is-bad", ok === false);
        },
    };
}

/**
 * Per-frame checks of a moving object as drawn: no overlap with the
 * solids, unit scale, no jump beyond the law's speed, and the measured
 * duration and peak-speed time. finish() returns the failures.
 */
export function createFrameCheck({ name, solids, shape, maxSpeed, ms, peakMs, tolMs = 40 }) {
    const fail = [];
    let last = null, peak = 0, peakAt = 0, first = null, end = null, worst = -Infinity, where = "", maxDt = 0;
    return {
        frame(object, t) {
            const pose = poseOf(object);
            if (Math.abs(object.scale.x - 1) > 1e-6 || Math.abs(object.scale.y - 1) > 1e-6 || Math.abs(object.scale.z - 1) > 1e-6) fail.push(`${name} scaled`);
            if (!object.visible) fail.push(`${name} hidden`);
            if (solids && shape) {
                const w = worstDepth(obbOf(pose, shape), solids, 0);
                if (w.depth > worst) { worst = w.depth; where = `${w.solid?.name} at ${t.toFixed(0)} ms`; }
            }
            if (last && t > last.t) {
                const d = Math.hypot(pose.p[0] - last.p[0], pose.p[1] - last.p[1], pose.p[2] - last.p[2]);
                const v = d / ((t - last.t) / 1000);
                if (maxSpeed != null && d > maxSpeed * ((t - last.t) / 1000) * 1.05 + 0.001) fail.push(`${name} jumped ${(d * 1000).toFixed(0)} mm in one frame`);
                if (v > peak) { peak = v; peakAt = (t + last.t) / 2; }
                maxDt = Math.max(maxDt, t - last.t);
            }
            if (first == null) first = t;
            end = t;
            last = { t, p: pose.p };
        },
        finish() {
            if (worst > 0.0005) fail.push(`${name} overlaps ${(worst * 1000).toFixed(1)} mm (${where})`);
            if (end != null && Math.abs(end - ms) > 1) fail.push(`${name} took ${end.toFixed(0)} ms, law ${ms.toFixed(0)}`);
            // Frames sample the speed: the peak is known to within the longest frame.
            if (peakMs != null && peak > 0 && Math.abs(peakAt - peakMs) > Math.max(tolMs, maxDt) + ms * 0.04) fail.push(`${name} fastest at ${peakAt.toFixed(0)} ms, law ${peakMs.toFixed(0)}`);
            return [...new Set(fail)];
        },
        get peakAt() { return peakAt; },
    };
}

/** Seated by drawn geometry: the object's lowest drawn point on surfaceY + 1 mm (± 0.5 mm). */
export function seatedFail(object, surfaceY, name) {
    const minY = drawnBox(object).min.y;
    const off = minY - (surfaceY + 0.001);
    return Math.abs(off) > 0.0005 ? [`${name} not seated: drawn bottom ${(off * 1000).toFixed(1)} mm off its surface`] : [];
}

/** Real size: the drawn local bounds match the shape the primitive plans with (± 0.3 mm). */
export function sizeFail(object, shape, name) {
    const b = localBounds(object);
    const off = Math.max(...[0, 1, 2].flatMap((k) => [Math.abs(b.min[k] - shape.min[k]), Math.abs(b.max[k] - shape.max[k])]));
    return off > 0.0003 ? [`${name}: drawn size off its real size by ${(off * 1000).toFixed(1)} mm`] : [];
}

/**
 * The room as drawn against anim/room.js: the chest (turned), its lid's
 * hinge and sweep, the shelf boards, the felt. Returns the mismatches.
 */
export function roomCheck(world) {
    const bad = [];
    const near = (a, b, tol, what) => {
        if (Math.abs(a - b) > tol) bad.push(`${what}: drawn ${a.toFixed(4)}, room.js ${b.toFixed(4)}`);
    };
    const g = world.chest.group;
    const lidAt = world.getChestLid?.() ?? 0;
    world.setChestLid(0);
    let lidPivot = null;
    g.traverse((o) => { if (o.name === "chest-lid-pivot") lidPivot = o; });
    const body = new THREE.Box3();
    g.traverse((o) => { if (o.isMesh && o.name && !lidPivot?.getObjectById(o.id)) body.union(drawnBox(o)); });
    ["x", "y", "z"].forEach((k, i) => {
        near(body.min[k], CHEST.outer.min[i], 0.003, `chest body min ${k}`);
        near(body.max[k], CHEST.outer.max[i], 0.003, `chest body max ${k}`);
    });
    bad.push(...lidCheck(world, CHEST));
    world.setChestLid(lidAt);
    // Shelf boards, backboard and brackets: every BoxGeometry mesh in the scene
    // that is one of room.js's named boxes.
    const named = new Map(ROOM.filter((s) => s.kind === "box").map((s) => [s.name, s]));
    const boxes = [];
    world.scene.children.forEach((c) => { if (c.isMesh && c.geometry?.type === "BoxGeometry") boxes.push(drawnBox(c)); });
    for (const n of ["shelf-top", "shelf-low", "shelf-back", "bracket-1", "bracket-2", "bracket-3", "bracket-4"]) {
        const s = named.get(n);
        const lo = s.c.map((v, i) => v - s.he[i]), hi = s.c.map((v, i) => v + s.he[i]);
        const hit = boxes.some((b) => ["x", "y", "z"].every((ax, i) => Math.abs(b.min[ax] - lo[i]) < 0.002 && Math.abs(b.max[ax] - hi[i]) < 0.002));
        if (!hit) bad.push(`${n}: no drawn box matches room.js`);
    }
    near(world.table.feltTopY, FELT_Y, 0.0005, "felt height");
    return bad;
}
