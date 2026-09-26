/**
 * Small playroom motion helpers. Continuous hops, holds, and camera
 * tracks — no opacity fades, no hide/show cuts. Shared by Scramble
 * and DoubleDeal enter (follow-cam + hops), not one-off per-algo
 * spaghetti.
 *
 * Not a second animation engine. Tweens stay on `beat-clock`.
 * Shelf / toybox fly-in stays on `toy-director`. Camera follow lives
 * on the pose controller (`followTo`).
 */

import { easeInOutCubic, easeOutCubic, lerp } from "./beat-clock.js";

export function markBeat(beat) {
    const root = typeof document !== "undefined" ? document.documentElement : null;
    if (root?.dataset?.playroomDebug === "1") root.dataset.beat = beat;
}

export function pose3(raw) {
    if (!raw) return null;
    if (raw.position) {
        return {
            x: raw.position.x,
            y: raw.position.y,
            z: raw.position.z,
            rx: raw.rotation?.x ?? 0,
            ry: raw.rotation?.y ?? 0,
            rz: raw.rotation?.z ?? 0,
        };
    }
    const hasRot = raw.rx != null || raw.ry != null || raw.rz != null;
    return {
        x: raw.x,
        y: raw.y,
        z: raw.z,
        rx: hasRot ? (raw.rx ?? 0) : null,
        ry: hasRot ? (raw.ry ?? 0) : null,
        rz: hasRot ? (raw.rz ?? 0) : null,
    };
}

/**
 * Hop or slide an object to a pose. Lift is a sine arc so the move
 * reads as a pick-up, not a slide through the felt.
 */
export function hopTo(object, dest, clock, gen, {
    ms = 520,
    lift = 0.06,
    delay = 0,
    ease = easeOutCubic,
} = {}) {
    const to = pose3(dest);
    if (!object || !to) return Promise.resolve();
    return (async () => {
        if (delay) await clock.wait(delay, gen);
        const from = pose3(object);
        const rotate = to.rx != null && object.rotation;
        await clock.tween(ms, (t) => {
            object.position.x = lerp(from.x, to.x, t);
            object.position.y = lerp(from.y, to.y, t) + Math.sin(Math.PI * t) * lift;
            object.position.z = lerp(from.z, to.z, t);
            if (rotate) {
                object.rotation.set(
                    lerp(from.rx, to.rx, t),
                    lerp(from.ry, to.ry, t),
                    lerp(from.rz, to.rz, t),
                );
                object.quaternion?.setFromEuler?.(object.rotation);
            }
        }, { ease, generation: gen });
    })();
}

export async function waitToyIdle(toy, clock, gen, { tries = 40, ms = 40 } = {}) {
    if (!toy) return;
    for (let i = 0; i < tries && toy.userData?.flightBusy; i++) {
        await clock.wait(ms, gen);
    }
}

export function trackToy(world, name) {
    return () => world.toys[name]?.position;
}

function worldXYZ(node) {
    if (!node) return null;
    if (typeof node.updateMatrixWorld === "function") {
        node.updateMatrixWorld(true);
        const e = node.matrixWorld?.elements;
        if (e && e.length >= 15 && Number.isFinite(e[12])) {
            return { x: e[12], y: e[13], z: e[14] };
        }
    }
    const p = node.position || node;
    if (p && Number.isFinite(p.x) && Number.isFinite(p.y) && Number.isFinite(p.z)) {
        return { x: p.x, y: p.y, z: p.z };
    }
    return null;
}

function pushPoint(points, value) {
    if (!value) return;
    const node = typeof value === "function" ? value() : value;
    const p = worldXYZ(node) || (node && Number.isFinite(node.x) ? node : null);
    if (p && Number.isFinite(p.x) && Number.isFinite(p.y) && Number.isFinite(p.z)) {
        points.push(p);
    }
}

function focusOf(points) {
    const c = centroidOf(points);
    if (!c) return null;
    let r = 0.05;
    for (const p of points) {
        const dx = p.x - c.x;
        const dy = p.y - c.y;
        const dz = p.z - c.z;
        r = Math.max(r, Math.hypot(dx, dy, dz));
    }
    return { x: c.x, y: c.y, z: c.z, r };
}

/** Average of live world-space points. Empty set → null. */
export function centroidOf(points) {
    if (!points?.length) return null;
    let x = 0;
    let y = 0;
    let z = 0;
    for (const p of points) {
        x += p.x;
        y += p.y;
        z += p.z;
    }
    const n = points.length;
    return { x: x / n, y: y / n, z: z / n };
}

/**
 * Frame the named toys (and optional extra meshes / getters).
 * Always the full set — use `trackActive` when only in-flight
 * props should pull the lens.
 */
export function trackToys(world, names, extras = []) {
    const list = Array.isArray(names) ? names : [names];
    return () => {
        const points = [];
        for (const name of list) pushPoint(points, world.toys?.[name]);
        for (const extra of extras) pushPoint(points, extra);
        return focusOf(points);
    };
}

/**
 * Dynamic enter framing: centroid of toys that are flying or
 * unboxing, falling back to the whole set so the lens never
 * snaps to a named empty shot.
 */
export function trackActive(world, names, extras = []) {
    const list = Array.isArray(names) ? names : [names];
    return () => {
        const busy = [];
        const all = [];
        for (const name of list) {
            const toy = world.toys?.[name];
            if (!toy) continue;
            pushPoint(all, toy);
            if (toy.userData?.flightBusy || toy.userData?.unboxBusy) pushPoint(busy, toy);
        }
        const extracting = [];
        for (const extra of extras) {
            const node = typeof extra === "function" ? extra() : extra;
            if (!node) continue;
            pushPoint(all, node);
            if (node.userData?.flightBusy || node.userData?.unboxBusy) pushPoint(busy, node);
            if (node.userData?.unboxBusy && node.name === "packet") pushPoint(extracting, node);
        }
        if (extracting.length) return focusOf(extracting);
        return focusOf(busy.length ? busy : all);
    };
}

/**
 * Hold the current shot so a toy leaving home stays in frame, then
 * ease to `to` while tracking. Kept for callers that still want a
 * named-shot ease; happy-path hub→play uses `followEnter`.
 */
export function trackEnter(poses, {
    to,
    track,
    holdMs = 0,
    duration,
    reduced = false,
} = {}) {
    if (!poses) return;
    if (reduced) {
        poses.snap?.(to);
        return;
    }
    poses.goTo(to, {
        duration,
        delay: holdMs || 0,
        track,
    });
}

/**
 * Continuous follow-cam hop. Shared by hub→play and play→hub so
 * neither path falls back to via:shelf / look.copy snaps.
 */
function followShot(poses, {
    to,
    track,
    holdMs = 0,
    duration,
    reduced = false,
    settleAt,
} = {}) {
    if (!poses) return;
    if (reduced) {
        poses.snap?.(to);
        return;
    }
    if (poses.followTo) {
        return poses.followTo(to, {
            duration,
            delay: holdMs || 0,
            track,
            settleAt,
        });
    }
    poses.goTo(to, {
        duration,
        delay: holdMs || 0,
        track,
    });
}

/**
 * Shared hub→play enter for Scramble and DoubleDeal. Starts from the
 * live hub framing, follows the actual flying toys (no via:shelf /
 * unbox_travel chain), and lands at `to` without a cut.
 */
export function followEnter(poses, opts = {}) {
    return followShot(poses, opts);
}

/**
 * Shared play→hub return. Same follow primitive as enter: live track,
 * eased look, late settle into the room pose. No via:shelf, no cut.
 */
export function followLeave(poses, opts = {}) {
    return followShot(poses, {
        ...opts,
        to: opts.to || "landing",
        settleAt: opts.settleAt ?? 0.86,
    });
}

/** Ease from the live camera to a named pose. Skip uses this too. */
export function continueTo(poses, name, { duration = 720, reduced = false } = {}) {
    if (!poses) return Promise.resolve();
    if (reduced) {
        poses.snap?.(name);
        return Promise.resolve(name);
    }
    if (poses.playTo) return poses.playTo(name, { duration });
    poses.goTo?.(name, { duration });
    return Promise.resolve(name);
}

/**
 * Set toys on a sensible felt rest (or table seat). Standing, not a
 * tipped discard. World supplies `getBoxRestPose` / `getTablePose`.
 */
export async function seatToys(world, clock, gen, names, { ms = 520, lift = 0.03 } = {}) {
    const jobs = names.map((name) => {
        const toy = world.toys?.[name];
        const dest = world.getBoxRestPose?.(name) || world.getTablePose?.(name);
        if (!toy || !dest) return Promise.resolve();
        return hopTo(toy, dest, clock, gen, { ms, lift, ease: easeInOutCubic });
    });
    await Promise.all(jobs);
}
