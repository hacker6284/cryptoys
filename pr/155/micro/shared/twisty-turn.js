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

export function mountTwistyTurn(page) {
    const timing = { ...CUBE_STAGE_TIMING };
    let adapter = null;
    let rig = null;
    let leg = 0;
    let loaded = "";
    const turnSlots = page.turnSlots;

    function syncTiming(ctx) {
        timing.TURN_LIFT = ctx.timing("TURN_LIFT");
        timing.TURN_LIFT_MS = ctx.timing("TURN_LIFT_MS");
        timing.SETTLE_HOLD_MS = ctx.timing("SETTLE_HOLD_MS");
    }

    const perClick = (amount) => ({
        slot: "single",
        label: `single turn file × ${amount}, at the real click times`,
        clicks: (ctx) => clickTimes(amount, ctx.timing("speed")),
    });

    return mountMicro({
        id: page.id,
        title: page.title,
        summary: page.summary,
        source: page.source,
        camera: page.camera || { position: [DEN.x + 0.32, 1.17, DEN.z + 0.74], target: [DEN.x, 0.9, DEN.z], fov: 28 },
        loopGapMs: 700,
        choices: [{ key: "move", label: "Move", value: page.defaultMove, options: page.moveOptions }],
        timing: [
            { key: "speed", label: "Speed (tempo)", min: 0.5, max: 4, step: 0.1, value: 1.4, unit: "×", note: "Dock speed slider → rig.setTempo (cubing.js tempoScale)" },
            { key: "TURN_LIFT_MS", label: "TURN_LIFT_MS", min: 60, max: 900, step: 10, value: CUBE_STAGE_TIMING.TURN_LIFT_MS, unit: " ms" },
            { key: "TURN_LIFT", label: "TURN_LIFT", min: 0, max: 0.3, step: 0.005, value: CUBE_STAGE_TIMING.TURN_LIFT, unit: " m" },
            { key: "SETTLE_HOLD_MS", label: "SETTLE_HOLD_MS", min: 0, max: 800, step: 10, value: CUBE_STAGE_TIMING.SETTLE_HOLD_MS, unit: " ms" },
        ],
        slots: [
            { name: "single", label: "Single turn (one click)", contact: "the face seats (end of leaf)", from: [[turnSlots, "single"]], gapMs: 55, voices: 3, jitter: 0.06 },
            { name: "double", label: "Double turn (two clicks)", contact: "the face seats (end of leaf)", from: [[turnSlots, "double"]], gapMs: 55, voices: 3, jitter: 0.06, perClick: perClick(2) },
            { name: "triple", label: "Triple turn (three clicks)", contact: "the face seats (end of leaf)", from: [[turnSlots, "triple"]], gapMs: 55, voices: 3, jitter: 0.06, perClick: perClick(3) },
            ...(page.rotation ? [{ name: "rotation", label: "Whole-puzzle rotation", contact: "rotation ends", from: [[turnSlots, "rotation"]], gapMs: 140, voices: 2 }] : []),
            { name: "lift", label: "Lift off felt", contact: "the puzzle leaves the felt", from: ["scramble-lift"], gapMs: 140, voices: 2, off: true, gainTrimDb: -6 },
            { name: "settle", label: "Settle on felt", contact: "the puzzle touches the felt", from: [["scramble-turn", "settle"]], pick: "scramble-turn/settle/settle_emapuree-848748", gapMs: 140, voices: 2 },
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
            ctx.status(`Loading cubing.js${page.puzzle ? ` (${page.puzzle})` : ""}…`);
            rig = await adapter.ready();
            rig.rememberSeated?.();
            ctx.status("");
        },
        onTiming(ctx, key, v) {
            syncTiming(ctx);
            if (key === "speed") rig?.setTempo?.(v);
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
            await rig.playLeaves(from, from + moves.length, {
                onLeaf: (i) => {
                    const move = leaves[i - from];
                    if (move) ctx.contact(slotOf(move), performance.now() + cubingMs(amountOf(move)) / tempo);
                },
            });
            if (gen !== ctx.alive) return;
            // stageCubeView sets the puzzle down SETTLE_HOLD_MS after the last leaf.
            const down = timing.SETTLE_HOLD_MS + timing.TURN_LIFT_MS;
            ctx.contact("settle", performance.now() + down);
            await ctx.wait(down + 40);
            leg += 1;
        },
        config(ctx) {
            return {
                demo: page.demo,
                paste: "constants → demos/playroom/constants.js; speed → createScrambleAdapter speed; sounds → a demos/shared/sound.js table (offsetMs is relative to each contact; perClick = play that slot once per click at clicksMs)",
                ...(page.puzzle ? { puzzle: page.puzzle } : {}),
                constants: {
                    TURN_LIFT: ctx.timing("TURN_LIFT"),
                    TURN_LIFT_MS: ctx.timing("TURN_LIFT_MS"),
                    SETTLE_HOLD_MS: ctx.timing("SETTLE_HOLD_MS"),
                },
                speed: { min: 0.5, max: 4, value: ctx.timing("speed") },
            };
        },
    });
}
