/**
 * A stage's clock for its motions: a tween on requestAnimationFrame that
 * stops when the stage moves on (its generation changes), with the pacer's
 * frame skipping above 1× (shared/pacer.js) and no motion under reduced
 * motion. Shared by the MegaDreifach and BS stages.
 *
 *   const time = createStageTime({ current: (mine) => mine === gen, speed: () => k, reduced });
 *   await time.tween(ms, (t) => …, mine);   // ms: wall time at this speed; t: 0 → 1
 *   await time.wait(ms, mine);              // paced only above 1×
 */
import { pacedWait, skipMs } from "../shared/pacer.js";

export function createStageTime({ current, speed, reduced = () => false }) {
    function tween(duration, step, mine, { floor = true } = {}) {
        if (!duration || reduced()) {
            step(1);
            return Promise.resolve(current(mine));
        }
        const k = speed();
        const skip = skipMs(duration * k, k, { floor });
        if (skip !== null) {
            step(1);
            return pacedWait(skip).then(() => current(mine));
        }
        return new Promise((resolve) => {
            const start = performance.now();
            function tick(now) {
                if (!current(mine)) return resolve(false);
                const t = Math.min(1, (now - start) / duration);
                step(t);
                if (t < 1) requestAnimationFrame(tick);
                else resolve(true);
            }
            requestAnimationFrame(tick);
        });
    }

    function wait(duration, mine) {
        return tween(reduced() ? 0 : duration, () => {}, mine, { floor: false });
    }

    return { tween, wait };
}
