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

    function destY() {
        return seatedY == null ? rig.group.position.y : seatedY;
    }

    function cancelEase() {
        token += 1;
        window.clearTimeout(settleTimer);
        rig.group.userData.easeBusy = false;
    }

    rig.group.userData.cancelEase = cancelEase;

    function engageFrame() {
        poses?.frame?.(cubeTarget);
    }

    function releaseFrame() {
        poses?.releaseFrame?.();
    }

    async function moveY(toY, { snap = false } = {}) {
        const toy = rig.group;
        const fromY = toy.position.y;
        if (Math.abs(fromY - toY) < 1e-4) {
            toy.position.y = toY;
            return true;
        }
        const my = ++token;
        rig.group.userData.easeBusy = true;
        await tween(TURN_LIFT_MS, (t) => {
            if (my !== token) return;
            toy.position.y = fromY + (toY - fromY) * t;
        }, snap || reduced());
        if (my !== token) return false;
        toy.position.y = toY;
        rig.group.userData.easeBusy = false;
        return true;
    }

    async function lift() {
        window.clearTimeout(settleTimer);
        engageFrame();
        if (seatedY == null) rememberSeated();
        const up = destY() + TURN_LIFT;
        if (Math.abs(rig.group.position.y - up) < 1e-3) {
            lifted = true;
            return;
        }
        const ok = await moveY(up);
        if (ok) lifted = true;
    }

    async function setDown({ snap = false } = {}) {
        window.clearTimeout(settleTimer);
        const dest = destY();
        const ok = await moveY(dest, { snap });
        if (!ok) return;
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

    // Per-move lift; the settle-hold timer is cleared by the next lift so a
    // Play/Solve sequence stays up until the last turn's hold expires.
    async function withLift(run) {
        await lift();
        try {
            return await run();
        } finally {
            scheduleSetDown();
        }
    }

    function call(name, fallback) {
        return typeof rig[name] === "function" ? (...args) => rig[name](...args) : fallback;
    }

    return {
        group: rig.group,
        inner: rig.inner ?? rig.lift,
        lift: rig.lift,
        fit: rig.fit,
        puzzleId: rig.puzzleId,
        paint: (facelets) => rig.paint?.(facelets),
        animateMove: (move, ms) => withLift(() => rig.animateMove(move, ms)),
        animateReorient: (from, up, front, ms) => withLift(() => rig.animateReorient(from, up, front, ms)),
        playLeaves: rig.playLeaves
            ? (from, to, opts = {}) => withLift(() => rig.playLeaves(from, to, {
                ...opts,
                snap: Boolean(opts.snap) || reduced(),
            }))
            : undefined,
        playMoves: rig.playMoves
            ? (moves, opts = {}) => withLift(() => rig.playMoves(moves, {
                ...opts,
                snap: Boolean(opts.snap) || reduced(),
            }))
            : undefined,
        jumpToLeaf: call("jumpToLeaf"),
        setAlg: call("setAlg"),
        setSetup: call("setSetup"),
        setTempo: call("setTempo"),
        resetTimeline: call("reset"),
        pauseTimeline: call("pause"),
        highlightLayer: call("highlightLayer", () => {}),
        highlightCubie: call("highlightCubie", () => {}),
        highlightRuleB: call("highlightRuleB", () => {}),
        clearHighlights: call("clearHighlights", () => {}),
        dispose: () => {
            cancelEase();
            rig.group.position.y = destY();
            lifted = false;
            releaseFrame();
            rig.dispose?.();
        },
        rememberSeated,
        settle,
        swapPuzzle: call("swapPuzzle"),
    };
}
