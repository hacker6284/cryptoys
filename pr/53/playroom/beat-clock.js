import { CLOCK_STEP_MS } from "./constants.js";

/**
 * Labeled waits/tweens on the same rAF + generation pattern as
 * `table.js` and `toy-director.js`. Skip / reduced-motion snap to the
 * end of the current beat. Not a second animation engine.
 */

export function lerp(a, b, t) {
    return a + (b - a) * t;
}

export function easeOutCubic(t) {
    return 1 - (1 - t) ** 3;
}

export function easeInOutCubic(t) {
    return t < 0.5 ? 4 * t * t * t : 1 - (-2 * t + 2) ** 3 / 2;
}

export function easeOutQuart(t) {
    return 1 - (1 - t) ** 4;
}

export function easeInOut(t) {
    return t < 0.5 ? 2 * t * t : 1 - ((-2 * t + 2) ** 2) / 2;
}

export function prefersReducedMotion() {
    return Boolean(window.matchMedia?.("(prefers-reduced-motion: reduce)")?.matches);
}

/** One paint so mesh/CSS work cannot starve the 3D rAF loop. */
export function yieldFrame() {
    return new Promise((resolve) => {
        if (typeof requestAnimationFrame === "function") requestAnimationFrame(() => resolve());
        else setTimeout(resolve, 0);
    });
}

export function createBeatClock({ reduced } = {}) {
    let gen = 0;
    const snap = Boolean(reduced || prefersReducedMotion());

    function skip() {
        gen += 1;
    }

    function begin() {
        gen += 1;
        return gen;
    }

    function dead(g) {
        return g !== gen;
    }

    function tween(ms, step, { ease = easeInOutCubic, generation: g } = {}) {
        const apply = (t) => step(ease(Math.min(1, Math.max(0, t))));
        if (snap || !(ms > 0) || dead(g)) {
            apply(1);
            return Promise.resolve();
        }
        return new Promise((resolve) => {
            const start = performance.now();
            let last = start;
            let elapsed = 0;
            const mine = g;
            function tick(now) {
                if (mine !== gen) {
                    apply(1);
                    resolve();
                    return;
                }
                elapsed += Math.min(CLOCK_STEP_MS, Math.max(0, now - last));
                last = now;
                const t = Math.min(1, elapsed / ms);
                apply(t);
                if (t < 1) requestAnimationFrame(tick);
                else resolve();
            }
            requestAnimationFrame(tick);
        });
    }

    function wait(ms, g) {
        return tween(ms, () => {}, { ease: (t) => t, generation: g });
    }

    return {
        begin,
        skip,
        dead,
        tween,
        wait,
        get generation() {
            return gen;
        },
        get reduced() {
            return snap;
        },
    };
}
