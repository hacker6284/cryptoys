/**
 * Small playroom motion helpers. Continuous hops, holds, and camera
 * tracks — no opacity fades, no hide/show cuts. Used by DoubleDeal
 * enter today; named for Scramble and future toys.
 *
 * Not a second animation engine. Tweens stay on `beat-clock`.
 * Shelf / toybox fly-in stays on `toy-director`.
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

/**
 * Hold the current shot so a toy leaving home stays in frame, then
 * ease to `to` while tracking. No named-shot snap on the happy path.
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
