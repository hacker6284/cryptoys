import { mountMicro } from "./micro.js";
import { createScrambleAdapter } from "../../playroom/adapters.js";
import { CUBE_STAGE_TIMING } from "../../playroom/cube-stage.js";
import { DEN } from "../../playroom/constants.js";
import { amountOf, cubingMs, slotOf, twistySlots } from "../../anim/twisty.js";

/**
 * Twisty face-turn page (Scramble 3×3 or the megaminx), on the real
 * playroom adapter: one lift per step, cubing.js leaves at the dock
 * speed (tempo), settle on the felt. Each loop undoes the last.
 *
 * With page.voice (a library entry, e.g. demos/anim/scramble-turn) the
 * page only watches: cube-stage.js plays the entry's timings and
 * sounds, exactly as in the playroom. Without it (megaminx-turn, not
 * yet in the library) the page passes its own timing and sounds.
 *
 * page.choice: which settings.choices key picks the move (default "move").
 * page.moves[key]: an array of moves is one step (lift, the moves,
 * settle), turned back on the next loop. { steps: [...] } plays each
 * move as its own step (lift, turn, settle) in order, and repeats the
 * list until the cube is back where it started.
 */

function invert(moves) {
    return moves.slice().reverse().map((m) => (m.endsWith("'") ? m.slice(0, -1) : `${m}'`));
}

/** Quarter turns of a face move (R2 → 2, R' → −1, R3' → −3). */
function quarters(move) {
    const m = /^([A-Za-z]+?)(\d*)('?)$/.exec(move);
    return m ? Number(m[2] || 1) * (m[3] ? -1 : 1) : 0;
}

/**
 * The leaves one round of the loop plays: [...moves, ...undo] for a
 * single step; for { steps } on one face, the steps repeated until the
 * face is back home (R R2 R3 is six quarters: two rounds).
 */
export function loopLeaves(entry) {
    if (Array.isArray(entry)) return [...entry, ...invert(entry)];
    const steps = entry.steps;
    const faces = new Set(steps.map((m) => m.replace(/[\d']+$/, "")));
    if (faces.size !== 1 || /^[xyz]/.test(steps[0])) return [...steps, ...invert(steps)];
    const net = ((steps.reduce((a, m) => a + quarters(m), 0) % 4) + 4) % 4;
    const rounds = net === 0 ? 1 : net === 2 ? 2 : 4;
    return Array.from({ length: rounds }, () => steps).flat();
}

/** [from, to) leaf ranges, one per loop. */
function loopSteps(entry) {
    const leaves = loopLeaves(entry);
    if (Array.isArray(entry)) return [[0, entry.length], [entry.length, leaves.length]];
    return leaves.map((_, k) => [k, k + 1]);
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

    const viewer = Boolean(page.voice);
    const pick = (ctx) => page.moves[ctx.choice(page.choice ?? "move")] || page.moves[page.defaultMove];

    return mountMicro({
        id: page.id,
        title: page.title,
        camera: { position: [DEN.x + 0.32, 1.17, DEN.z + 0.74], target: [DEN.x, 0.9, DEN.z], fov: 30, margin: page.margin ?? 1.08 },
        voice: page.voice,
        slots: twistySlots(),
        async setup(ctx) {
            if (!viewer) syncTiming(ctx);
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
                const stage = viewer ? { voice: page.voice } : { voice: null, timing };
                adapter.install(ctx.world, { poses: null, prefersReducedMotion: () => false, ...stage });
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
            const alg = loopLeaves(pick(ctx)).join(" ");
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
            const entry = pick(ctx);
            const all = loopLeaves(entry);
            const ranges = loopSteps(entry);
            if (leg >= ranges.length) {
                // A full round: the cube is home again. A single step and
                // its undo just play again; a step list rewinds its alg.
                leg = 0;
                if (!Array.isArray(entry)) await rig.jumpToLeaf(-1);
            }
            const [from, to] = ranges[leg];
            const leaves = all.slice(from, to);
            const tempo = ctx.timing("speed");
            rig.setTempo(tempo);
            if (viewer) {
                // cube-stage.js lifts, turns, sets down and plays the sounds.
                await rig.playLeaves(from, to);
                if (gen !== ctx.alive) return;
                await ctx.wait(timing.SETTLE_HOLD_MS + timing.TURN_LIFT_MS + 40);
                leg += 1;
                return;
            }
            syncTiming(ctx);
            // The lift starts the step; the lead-in lets an early file start first.
            const lead = ctx.leadIn([["lift", 0]]);
            if (lead && !(await ctx.wait(lead))) return;
            ctx.contact("lift", performance.now());
            // Each leaf's contact is the moment its face seats: playback
            // start plus the leaf durations so far, at the tempo.
            await rig.playLeaves(from, to, {
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
