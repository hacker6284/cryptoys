// Megaminx face turn: what you hear and how it moves, everywhere it plays
// (demos/micro/megaminx-turn; MegaDreifach's stage once it lands, see
// ../README.md). Edit a value and reload the microdemo.
//
// sounds: file = path under demos/anim/sounds/ (no extension; run
//   tools/sync-micro-sounds.py after changing it). gainDb = loudness
//   (+ louder). Placement, from the slot's contact:
//   align: "peak-velocity" = the centre of the file's audible part (its
//   energy centroid above −30 dB, measured from the decoded file) lands
//   where the face turns fastest; nudgeMs moves it (+ later, ms at
//   timing.speed). Or offsetMs = when the file starts relative to the
//   contact (−peak puts the loudest sample on it). null = silent.
//   The default rules for a turn entry (Zachary, 2026-10-02): "the audible
//   part of the sound should be centered over the part of the animation
//   where the face is at maximum velocity". cubing.js eases megaminx
//   turns (72°, 144°, 216°) with smootherStep, like the cube (sampled from
//   the real face angle), fastest exactly half way: 357 / 536 / 714 ms into
//   a single / double / triple at 1.4×; it scales with the tempo.
// timing: read by playroom/cube-stage.js (lift height and time, hold before
//   setting down); speed = the starting tempo (cubing.js tempoScale).
// loopGapMs, choices: the microdemo loop only.
export default {
    loopGapMs: 700,
    choices: {
        move: "U-U2-U3", // micro/megaminx-turn: "U-U2-U3" (a single, double and triple turn, one step each), "U", "Ui", "U2", "U3", "R", "R2", "seq"
    },
    timing: {
        speed: 1.4, // ×
        TURN_LIFT_MS: 320,
        TURN_LIFT: 0.14, // m
        SETTLE_HOLD_MS: 90,
    },
    sounds: {
        // APPROVED and LOCKED (Zachary at d952e6a: "Sounds are ok for that
        // one."): single, double and triple: file, gainDb, align
        // "peak-velocity", nudgeMs 0. Do not change them, or anything they
        // depend on, without his sign-off; ../library.test.mjs pins them.
        // Single turn (one 72° click): SpaceJoe "Rubik Cube Turn – 20", one clean
        // click, audible centre 128.5 ms in.
        single: { file: "megaminx-turn/single/single_spacejoe-486573", gainDb: 10, align: "peak-velocity", nudgeMs: 0 },
        // Double turn (two clicks): SpaceJoe "Rubik Cube Turn – 13", a weaker then a
        // stronger click 50 ms apart, cluster centre 171.9 ms in. Or { perClick: true }.
        double: { file: "megaminx-turn/double/double_spacejoe-486565", gainDb: 6.5, align: "peak-velocity", nudgeMs: 0 },
        // Triple turn (three clicks): SpaceJoe "Rubik Cube Turn – 14", three strong
        // clicks 45–50 ms apart, cluster centre 108.4 ms in. Or { perClick: true }.
        triple: { file: "megaminx-turn/triple/triple_spacejoe-486566", gainDb: 5, align: "peak-velocity", nudgeMs: 0 },
        // Whole-puzzle rotation: the megaminx alg has none (cubing.js rejects them).
        rotation: null,
        // Lift off felt; contact: the puzzle leaves the felt. Off.
        lift: null,
        // Settle on felt; contact: the puzzle touches the felt. The same muffled
        // pat as scramble-turn (Zachary's pick there; no megaminx pat yet).
        settle: { file: "scramble-turn/settle/settle_kenney-carpet-000-soft-cut", gainDb: -14.6, offsetMs: -22 },
    },
};
