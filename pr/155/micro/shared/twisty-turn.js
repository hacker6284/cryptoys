import { mountMicro } from "./micro.js";
import { createScrambleAdapter } from "../../playroom/adapters.js";
import { CUBE_STAGE_TIMING } from "../../playroom/cube-stage.js";
import { DEN } from "../../playroom/constants.js";

/**
 * Twisty face-turn page (Scramble 3×3 or the megaminx), on the real
 * playroom adapter: one lift per step, cubing.js leaves at the dock
 * speed (tempo), settle on the felt. Each loop undoes the last.
 */

export function amountOf(move) {
    const m = /^([A-Za-z]+)(\d*)('?)$/.exec(move);
    return m ? Number(m[2] || 1) : 1;
}

function slotOf(move) {
    if (/^[xyz]/.test(move)) return "rotation";
    const n = amountOf(move);
    return n === 1 ? "single" : n === 2 ? "double" : "triple";
}

function invert(moves) {
    return moves.slice().reverse().map((m) => (m.endsWith("'") ? m.slice(0, -1) : `${m}'`));
}

/** cubing.js default move durations (ms at tempo 1): 1 → 1000, 2 → 1500, more → 2000. */
export function cubingMs(amount) {
    return amount === 1 ? 1000 : amount === 2 ? 1500 : 2000;
}

/** cubing.js eases every move with smootherStep (Cube3D and PG3D `ease`). */
export function smootherStep(x) {
    return x * x * x * (10 - x * (15 - 6 * x));
}

function inverseSmootherStep(y) {
    let lo = 0;
    let hi = 1;
    for (let i = 0; i < 40; i++) {
        const mid = (lo + hi) / 2;
        if (smootherStep(mid) < y) lo = mid;
        else hi = mid;
    }
    return (lo + hi) / 2;
}

/**
 * Detent click times for an `amount`-click turn, in ms relative to the
 * end of the leaf (the face seats on the last click): click k lands
 * when the eased angle crosses k/amount.
 */
export function clickTimes(amount, tempo) {
    const total = cubingMs(amount) / tempo;
    const out = [];
    for (let k = 1; k <= amount; k++) out.push((inverseSmootherStep(k / amount) - 1) * total);
    return out;
}

export function mountTwistyTurn(page, settings) {
    const timing = { ...CUBE_STAGE_TIMING };
    let adapter = null;
    let rig = null;
    let leg = 0;
    let loaded = "";

    function syncTiming(ctx) {
        timing.TURN_LIFT = ctx.timing("TURN_LIFT");
        timing.TURN_LIFT_MS = ctx.timing("TURN_LIFT_MS");
        timing.SETTLE_HOLD_MS = ctx.timing("SETTLE_HOLD_MS");
    }

    const perClick = (amount) => ({ slot: "single", clicks: (ctx) => clickTimes(amount, ctx.timing("speed")) });

    return mountMicro({
        id: page.id,
        title: page.title,
        camera: { position: [DEN.x + 0.32, 1.17, DEN.z + 0.74], target: [DEN.x, 0.9, DEN.z], fov: 30, margin: page.margin ?? 1.08 },
        slots: [
            { name: "single", gapMs: 55, voices: 3, jitter: 0.06 },
            { name: "double", gapMs: 55, voices: 3, jitter: 0.06, perClick: perClick(2) },
            { name: "triple", gapMs: 55, voices: 3, jitter: 0.06, perClick: perClick(3) },
            { name: "rotation", gapMs: 140, voices: 2 },
            { name: "lift", gapMs: 140, voices: 2 },
            { name: "settle", gapMs: 140, voices: 2 },
        ],
        async setup(ctx) {
            syncTiming(ctx);
            adapter = createScrambleAdapter();
            // The adapter reads the puzzle from ?puzzle= (alt puzzles need
            // ?debug=1) when it installs; set it just for the install.
            const href = location.href;
            if (page.puzzle) {
                const url = new URL(href);
                url.searchParams.set("debug", "1");
                url.searchParams.set("puzzle", page.puzzle);
                history.replaceState(history.state, "", url);
            }
            try {
                adapter.install(ctx.world, { poses: null, prefersReducedMotion: () => false, timing });
            } finally {
                if (page.puzzle) history.replaceState(history.state, "", href);
            }
            const cube = ctx.world.toys.cube;
            cube.userData.seatSurface = "table";
            ctx.world.applyPose(cube, ctx.world.getTablePose("cube"));
            cube.userData.seatedY = cube.position.y;
        },
        async ready(ctx) {
            ctx.status("Loading the puzzle…");
            rig = await adapter.ready();
            rig.rememberSeated?.();
            ctx.status("");
        },
        frame(ctx) {
            // The puzzle seated on the felt (it may be lifted right now)
            // and the height it lifts to.
            const { THREE, world } = ctx;
            const size = new THREE.Box3().setFromObject(world.toys.cube).getSize(new THREE.Vector3());
            const seat = world.getTablePose("cube").position;
            const box = new THREE.Box3().setFromCenterAndSize(new THREE.Vector3(seat.x, seat.y, seat.z), size);
            box.max.y += ctx.timing("TURN_LIFT");
            return box;
        },
        async reset(ctx) {
            if (!rig?.setAlg) return;
            await rig.settle?.({ snap: true });
            const moves = page.moves[ctx.choice("move")] || page.moves[page.defaultMove];
            const alg = [...moves, ...invert(moves)].join(" ");
            if (alg !== loaded) {
                rig.setAlg(alg);
                loaded = alg;
            }
            leg = 0;
            await rig.jumpToLeaf(-1);
            rig.setTempo(ctx.timing("speed"));
        },
        stop() {
            rig?.pauseTimeline?.();
        },
        async cycle(ctx) {
            if (!rig?.playLeaves) {
                await ctx.wait(500);
                return;
            }
            const gen = ctx.alive;
            syncTiming(ctx);
            const moves = page.moves[ctx.choice("move")] || page.moves[page.defaultMove];
            const leaves = leg % 2 === 0 ? moves : invert(moves);
            const from = leg % 2 === 0 ? 0 : moves.length;
            const tempo = ctx.timing("speed");
            rig.setTempo(tempo);
            // The lift starts the step; the lead-in lets an early file start first.
            const lead = ctx.leadIn([["lift", 0]]);
            if (lead && !(await ctx.wait(lead))) return;
            ctx.contact("lift", performance.now());
            // Each leaf's contact is the moment its face seats: playback
            // start plus the leaf durations so far, at the tempo.
            await rig.playLeaves(from, from + moves.length, {
                onStart: ({ at, durations }) => {
                    let t = at;
                    leaves.forEach((move, k) => {
                        t += (durations[k] ?? cubingMs(amountOf(move))) / tempo;
                        ctx.contact(slotOf(move), t);
                    });
                },
            });
            if (gen !== ctx.alive) return;
            // stageCubeView sets the puzzle down SETTLE_HOLD_MS after the last leaf.
            const down = timing.SETTLE_HOLD_MS + timing.TURN_LIFT_MS;
            ctx.contact("settle", performance.now() + down);
            await ctx.wait(down + 40);
            leg += 1;
        },
    }, settings);
}
