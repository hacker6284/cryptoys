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

/** Put a three.js object at a world pose { p, q } (its parent unscaled), whatever its parent. */
export function setWorldPose(object, { p, q }) {
    const V = object.position.constructor;
    const Q = object.quaternion.constructor;
    const wp = new V(p[0], p[1], p[2]);
    const wq = new Q(q[0], q[1], q[2], q[3]);
    const parent = object.parent;
    if (parent) {
        parent.updateMatrixWorld(true);
        parent.worldToLocal(wp);
        wq.premultiply(parent.getWorldQuaternion(new Q()).invert());
    }
    object.position.copy(wp);
    object.quaternion.copy(wq);
    object.updateMatrixWorld(true);
}

/** Play a plan whose at(ms) is a world pose on `object`; resolves with the plan (null if stopped). */
export async function playPose(object, plan, run = rafRun) {
    const ok = await run(plan.ms, (t) => setWorldPose(object, plan.at(t)));
    setWorldPose(object, plan.at(plan.ms));
    return ok === false ? null : plan;
}
