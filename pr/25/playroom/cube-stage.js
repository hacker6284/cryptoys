import { SETTLE_HOLD_MS, TURN_LIFT, TURN_LIFT_MS } from "./constants.js";

function easeInOut(t) {
    return t < 0.5 ? 2 * t * t : 1 - ((-2 * t + 2) ** 2) / 2;
}

function tween(ms, step, snap) {
    if (snap) {
        step(1);
        return Promise.resolve();
    }
    return new Promise((resolve) => {
        const start = performance.now();
        function tick(now) {
            const t = Math.min(1, (now - start) / Math.max(1, ms));
            step(easeInOut(t));
            if (t < 1) requestAnimationFrame(tick);
            else resolve();
        }
        requestAnimationFrame(tick);
    });
}

/**
 * Playroom-only cube motion around the live Scramble rig: remember the
 * seated table pose, lift for turn sequences, and ask the pose
 * controller to keep the cube in frame while it is in the air.
 */
export function stageCubeView(rig, { poses, prefersReducedMotion } = {}) {
    let seatedY = null;
    let lifted = false;
    let motion = null;
    let token = 0;
    let settleTimer = 0;

    function reduced() {
        return Boolean(prefersReducedMotion?.());
    }

    function cubeTarget() {
        return rig.group.position;
    }

    function rememberSeated() {
        const marked = rig.group.userData.seatedY;
        seatedY = Number.isFinite(marked) ? marked : rig.group.position.y;
        rig.group.userData.seatedY = seatedY;
    }

    function engageFrame() {
        poses?.frame?.(cubeTarget);
    }

    function releaseFrame() {
        poses?.releaseFrame?.();
    }

    async function moveY(toY, { snap = false } = {}) {
        const toy = rig.group;
        const fromY = toy.position.y;
        const my = ++token;
        motion = tween(TURN_LIFT_MS, (t) => {
            if (my !== token) return;
            toy.position.y = fromY + (toY - fromY) * t;
        }, snap || reduced());
        await motion;
        if (my === token) toy.position.y = toY;
        if (my === token) motion = null;
    }

    async function lift() {
        window.clearTimeout(settleTimer);
        engageFrame();
        if (lifted) return;
        if (seatedY == null) rememberSeated();
        if (motion) await motion;
        if (lifted) return;
        await moveY(seatedY + TURN_LIFT);
        lifted = true;
    }

    async function setDown({ snap = false } = {}) {
        window.clearTimeout(settleTimer);
        token += 1;
        motion = null;
        if (!lifted && seatedY != null) {
            if (Math.abs(rig.group.position.y - seatedY) < 1e-4) {
                releaseFrame();
                return;
            }
        }
        const dest = seatedY == null ? rig.group.position.y : seatedY;
        await moveY(dest, { snap });
        lifted = false;
        releaseFrame();
    }

    function settle({ snap = false } = {}) {
        window.clearTimeout(settleTimer);
        return setDown({ snap });
    }

    function scheduleSetDown() {
        window.clearTimeout(settleTimer);
        settleTimer = window.setTimeout(() => {
            void setDown();
        }, SETTLE_HOLD_MS);
    }

    async function withLift(run) {
        await lift();
        try {
            return await run();
        } finally {
            scheduleSetDown();
        }
    }

    return {
        group: rig.group,
        inner: rig.inner,
        paint: (facelets) => rig.paint(facelets),
        animateMove: (move, ms) => withLift(() => rig.animateMove(move, ms)),
        animateReorient: (from, up, front, ms) => withLift(() => rig.animateReorient(from, up, front, ms)),
        highlightLayer: (...args) => rig.highlightLayer(...args),
        highlightCubie: (...args) => rig.highlightCubie(...args),
        highlightRuleB: (...args) => rig.highlightRuleB(...args),
        clearHighlights: () => rig.clearHighlights(),
        dispose: () => {
            window.clearTimeout(settleTimer);
            token += 1;
            releaseFrame();
            rig.dispose();
        },
        rememberSeated,
        settle,
    };
}
