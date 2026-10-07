/**
 * Shared runtime glue for the objects' moves: play a planned move on the
 * real clock (requestAnimationFrame), and read an object's world pose.
 * A caller with its own clock (a microdemo's runner, a stage's beat
 * clock) passes `run(ms, step)` instead; it resolves false if stopped.
 */

/** Calls step(t) each frame for t in [0, ms] (the last call exactly ms); resolves true. */
export function rafRun(ms, step) {
    return new Promise((resolve) => {
        const t0 = performance.now();
        const tick = () => {
            const t = Math.min(ms, performance.now() - t0);
            step(t);
            if (t >= ms) resolve(true);
            else requestAnimationFrame(tick);
        };
        requestAnimationFrame(tick);
    });
}

/** A three.js object's world pose as { p: [x, y, z], q: [x, y, z, w] }. */
export function worldPose(object) {
    object.updateMatrixWorld(true);
    const p = object.getWorldPosition(new object.position.constructor());
    const q = object.getWorldQuaternion(new object.quaternion.constructor());
    return { p: [p.x, p.y, p.z], q: [q.x, q.y, q.z, q.w] };
}
