import { scrambleTurnVoice, timing as scrambleTurnTiming } from "../anim/scramble-turn/index.js";

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
 * Lift/settle timings (TURN_LIFT, TURN_LIFT_MS, SETTLE_HOLD_MS), read at
 * call time: the scramble-turn entry in the animation library
 * (demos/anim/scramble-turn/settings.js).
 */
export const CUBE_STAGE_TIMING = scrambleTurnTiming;

/**
 * Playroom-only cube motion around the live Scramble rig: remember the
 * seated table pose, lift for turn sequences, and ask the pose
 * controller to keep the cube in frame while it is in the air.
 *
 * voice: the sounds for it, by default the scramble-turn library entry's
 * (a click per turn, a pat when the cube lands on the felt), on the
 * page's shared AudioContext; null for none.
 */
export function stageCubeView(rig, { poses, prefersReducedMotion, timing = CUBE_STAGE_TIMING, voice: voiceOpt } = {}) {
    let seatedY = null;
    let lifted = false;
    let token = 0;
    let settleTimer = 0;
    let epoch = 0;
    // Bumped whenever playback stops or ends, so clicks still waiting
    // for a later turn stay quiet.
    let turnGen = 0;
    const voice = voiceOpt === undefined ? scrambleTurnVoice() : voiceOpt;

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

    // onMove(endsAt, stillMoving): the tween really runs and ends at endsAt.
    async function moveY(toY, { snap = false, onMove = null } = {}) {
        const toy = rig.group;
        const fromY = toy.position.y;
        const my = ++token;
        if (Math.abs(fromY - toY) < 1e-4) {
            toy.position.y = toY;
            rig.group.userData.easeBusy = false;
            return true;
        }
        rig.group.userData.easeBusy = true;
        if (onMove && !(snap || reduced())) onMove(performance.now() + timing.TURN_LIFT_MS, () => my === token);
        await tween(timing.TURN_LIFT_MS, (t) => {
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
        const up = destY() + timing.TURN_LIFT;
        if (Math.abs(rig.group.position.y - up) < 1e-3) {
            lifted = true;
            return;
        }
        const ok = await moveY(up, {
            onMove: (endsAt, stillMoving) => voice?.lift(performance.now(), stillMoving),
        });
        if (ok) lifted = true;
    }

    async function setDown({ snap = false } = {}) {
        window.clearTimeout(settleTimer);
        const dest = destY();
        // The pat sounds where the cube touches the felt: the end of the set-down.
        const ok = await moveY(dest, {
            snap,
            onMove: (endsAt, stillMoving) => voice?.landing(endsAt, stillMoving),
        });
        if (!ok) return;
        lifted = false;
        releaseFrame();
    }

    function settle({ snap = false } = {}) {
        epoch += 1;
        window.clearTimeout(settleTimer);
        return setDown({ snap });
    }

    function scheduleSetDown() {
        window.clearTimeout(settleTimer);
        settleTimer = window.setTimeout(() => {
            void setDown();
        }, timing.SETTLE_HOLD_MS);
    }

    // Per-move lift; the settle-hold timer is cleared by the next lift so a
    // Play/Solve sequence stays up until the last turn's hold expires.
    async function withLift(run) {
        const mine = epoch;
        await lift();
        if (mine !== epoch) return undefined;
        try {
            return await run();
        } finally {
            scheduleSetDown();
        }
    }

    function call(name, fallback) {
        return typeof rig[name] === "function" ? (...args) => rig[name](...args) : fallback;
    }

    // A timeline call that stops playback also drops its pending clicks.
    function stopping(name) {
        const run = call(name);
        return run && ((...args) => {
            turnGen += 1;
            return run(...args);
        });
    }

    // A turn step: lift, then the leaves, with the voice's sounds. The
    // rig readies the leaves while the cube lifts and asks before they
    // play; when a click's file has to begin before the turn (a lead-in),
    // the voice gets the turn then, timed to the planned start. The turn
    // starts when the lift ends, or after the lead-in when the cube is
    // already up. A step needing no lead-in (the single click) never waits.
    async function liftAndTurn(play, opts) {
        const mine = epoch;
        const gen = ++turnGen;
        const live = () => mine === epoch && gen === turnGen;
        const up = destY() + timing.TURN_LIFT;
        const tweening = Math.abs(rig.group.position.y - up) >= 1e-3 && !reduced();
        const liftEndsAt = performance.now() + (tweening ? timing.TURN_LIFT_MS : 0);
        const lifting = lift();
        // Without a lead-in the voice hears the turn as it really starts
        // (onStart), as before; with one, at the planned start.
        let planned = false;
        const beforeStart = async (info) => {
            const lead = voice?.lead?.(info) ?? 0;
            const at = Math.max(liftEndsAt, performance.now() + lead);
            if (lead > 0) {
                planned = true;
                voice?.turns({ ...info, at }, live);
            }
            const wait = at - performance.now();
            if (wait > 0) await new Promise((resolve) => window.setTimeout(resolve, wait));
            if (!live()) return false;
            await opts.beforeStart?.(info);
            return true;
        };
        try {
            const onStart = (info) => {
                if (!planned) voice?.turns(info, live);
                opts.onStart?.(info);
            };
            const result = await play({ ...opts, beforeStart, onStart, snap: Boolean(opts.snap) || reduced() });
            await lifting;
            return mine === epoch ? result : undefined;
        } finally {
            if (gen === turnGen) turnGen += 1;
            if (mine === epoch) scheduleSetDown();
        }
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
            ? (from, to, opts = {}) => liftAndTurn((o) => rig.playLeaves(from, to, o), opts)
            : undefined,
        playMoves: rig.playMoves
            ? (moves, opts = {}) => liftAndTurn((o) => rig.playMoves(moves, o), opts)
            : undefined,
        jumpToLeaf: stopping("jumpToLeaf"),
        setAlg: call("setAlg"),
        setSetup: call("setSetup"),
        setTempo: call("setTempo"),
        status: call("status"),
        resetTimeline: stopping("reset"),
        pauseTimeline: stopping("pause"),
        highlightLayer: call("highlightLayer", () => {}),
        highlightCubie: call("highlightCubie", () => {}),
        highlightRuleB: call("highlightRuleB", () => {}),
        clearHighlights: call("clearHighlights", () => {}),
        dispose: () => {
            turnGen += 1;
            cancelEase();
            rig.group.position.y = destY();
            lifted = false;
            releaseFrame();
            rig.dispose?.();
        },
        rememberSeated,
        settle,
        keepFitted: call("keepFitted"),
        swapPuzzle: call("swapPuzzle"),
    };
}
