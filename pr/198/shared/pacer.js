/**
 * Frame skipping for fast playback.
 *
 * At high speed a motion can be shorter than a frame. Then it does not
 * tween: it jumps to its end (every step is still applied, in order) and
 * its time passes on a virtual clock instead. Waits shorter than a frame
 * do the same. The clock lets virtual time run only as fast as the wall
 * clock: whatever falls due within a frame is released in time order,
 * then the page paints, so a chain of tiny motions plays at its true
 * speed (a 100× run takes a hundredth of the 1× time) instead of costing
 * a frame each, and motions that run side by side share their time.
 *
 * Only above 1×: at 1× and slower every motion runs exactly as before.
 */
export const FRAME_MS = 1000 / 60;

const now = () => performance.now();

/**
 * The time a motion takes at `speed` (its multiplier over 1×) when it is
 * too short for a frame, else null (tween it as usual).
 * ms1x: its length at 1×. A motion never took less than a frame at 1×
 * (a tween's first tick is a frame away), so `floor` keeps that frame,
 * scaled; pass floor: false for a plain wait.
 */
export function skipMs(ms1x, speed = 1, { floor = true } = {}) {
    if (!(speed > 1)) return null;
    const ms = Math.max(0, Number(ms1x) || 0);
    if (ms / speed >= FRAME_MS) return null;
    return (floor ? Math.max(ms, FRAME_MS) : ms) / speed;
}

// ---- the virtual clock ---------------------------------------------------

const queue = []; // { due, resolve }, by due then arrival
let driving = false;
let current = null; // virtual now while releasing an event

function nextFrame() {
    return new Promise((resolve) => {
        if (typeof requestAnimationFrame === "function") requestAnimationFrame(() => resolve());
        else setTimeout(resolve, FRAME_MS);
    });
}

// A macrotask hop: every continuation of the released promises runs (and
// queues its next wait) before the next event is released.
let hopWaiting = [];
let channel = null;
function hop() {
    return new Promise((resolve) => {
        if (typeof MessageChannel !== "function") {
            setTimeout(resolve, 0);
            return;
        }
        if (!channel) {
            channel = new MessageChannel();
            channel.port1.onmessage = () => {
                const ready = hopWaiting;
                hopWaiting = [];
                for (const fn of ready) fn();
            };
        }
        channel.port1.ref?.();
        hopWaiting.push(resolve);
        if (hopWaiting.length === 1) channel.port2.postMessage(0);
    });
}

/** Virtual now: the due time of the event being released, else the wall clock. */
function virtualNow() {
    return current ?? now();
}

async function drive() {
    driving = true;
    let paintedAt = now();
    try {
        while (queue.length) {
            const t = now();
            // Nothing due yet, or a frame's worth of work done: paint first.
            if (queue[0].due > t || t - paintedAt > FRAME_MS * 0.75) {
                current = null;
                await nextFrame();
                paintedAt = now();
                continue;
            }
            const due = queue[0].due;
            // After a stall (a long task, a background tab) the debt is
            // capped at one frame: what follows takes real time again
            // instead of being paid back in one burst.
            current = Math.max(due, t - FRAME_MS);
            while (queue.length && queue[0].due === due) queue.shift().resolve();
            await hop();
        }
    } finally {
        current = null;
        driving = false;
        // Node (tests): an idle channel must not keep the process alive.
        channel?.port1.unref?.();
    }
}

/** Resolves after `ms` of virtual time (at once for 0). */
export function pacedWait(ms) {
    const d = Math.max(0, Number(ms) || 0);
    if (d === 0) return Promise.resolve();
    return new Promise((resolve) => {
        const due = virtualNow() + d;
        let i = queue.length;
        while (i > 0 && queue[i - 1].due > due) i -= 1;
        queue.splice(i, 0, { due, resolve });
        if (!driving) void drive();
    });
}

/**
 * A cancellable timer: on the virtual clock when `skip` (a skipMs result)
 * is set, else setTimeout(fn, ms). Returns cancel().
 */
export function pacedTimer(fn, ms, skip = null) {
    if (skip === null || skip === undefined) {
        const id = setTimeout(fn, ms);
        return () => clearTimeout(id);
    }
    let live = true;
    void pacedWait(skip).then(() => {
        if (live) fn();
    });
    return () => {
        live = false;
    };
}
