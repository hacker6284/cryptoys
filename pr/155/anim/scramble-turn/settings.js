// Scramble face turn: what you hear and how it moves, everywhere it plays
// (the playroom's Scramble seat and demos/micro/scramble-turn). Edit a
// value and reload the microdemo; see ../README.md before changing an
// approved entry.
//
// sounds: file = path under demos/anim/sounds/ (no extension; run
//   tools/sync-micro-sounds.py after changing it). gainDb = loudness
//   (+ louder). Placement, from the slot's contact:
//   align: "peak-velocity" = the centre of the file (centre: "audible",
//   the default: its energy centroid above −30 dB; "swell": its loudest
//   10 ms; measured from the decoded file) lands where the face or the
//   puzzle turns fastest; nudgeMs moves it (+ later, ms at timing.speed). Or offsetMs = when the file starts (more negative =
//   earlier; −peak puts the loudest sample on it); peakAtMs = when its
//   loudest sample lands.
//   startMs skips the file's head; fadeMs / maxMs shorten the tail
//   (0 = play it out). null = silent.
//   The turn sounds (single, double, triple, rotation) keep their place
//   in the turn at any speed: an aligned sound's contact is a point of
//   the turn and its nudgeMs scales (× speed / tempo); an offsetMs
//   sound's loudest-sample-to-contact time scales the same way. The
//   settle pat does not scale.
//   A file that has to start before its turn does gets the turn handed
//   over during the lift; with the cube already up the turn never waits
//   (the file's head is skipped instead).
// timing: read by playroom/cube-stage.js (lift height and time, hold before
//   setting down); speed = the dock's starting tempo (cubing.js tempoScale).
// loopGapMs, choices: the microdemo loop only.
export default {
    loopGapMs: 700,
    choices: {
        move: "R-R2-R3", // micro/scramble-turn: "R-R2-R3" (a single, double and triple turn, one step each), "R", "Ri", "R2", "seq", "x", "R3"
        rotation: "y", // micro/scramble-rotate: "y", "yi", "x", "xi", "z", "zy"
    },
    timing: {
        speed: 1.4, // ×
        TURN_LIFT_MS: 320,
        TURN_LIFT: 0.14, // m
        SETTLE_HOLD_MS: 90,
    },
    sounds: {
        // Face turns. Rule (Zachary, 2026-10-02; supersedes the single's lock at
        // af9a8fb/2b5f6d4): "the audible part of the sound should be centered
        // over the part of the animation where the face is at maximum
        // velocity." cubing.js eases every turn with smootherStep, fastest at
        // exactly half way: 357 ms into a single (714 ms), 536 ms into a double
        // (1071 ms), 714 ms into a triple (1429 ms) at 1.4×; it scales with the
        // tempo.
        // APPROVED and LOCKED (Zachary at 6014bfc: "All look pretty good."):
        // single, double and triple: file, gainDb, align "peak-velocity",
        // nudgeMs 0. Do not change them, or anything they depend on, without
        // his sign-off; ../library.test.mjs pins them.
        // Single turn (one click), audible centre 141 ms into the file.
        single: { file: "scramble-turn/single/single_spacejoe-486564", gainDb: 11, align: "peak-velocity", nudgeMs: 0 },
        // Double turn (two clicks), audible centre of the cluster 107 ms in.
        // Or { perClick: true }: the single file once per click.
        double: { file: "scramble-turn/double/double_spacejoe-486567", gainDb: 8.5, align: "peak-velocity", nudgeMs: 0 },
        // Triple turn (three clicks), audible centre of the cluster 203 ms in. Or { perClick: true }.
        triple: { file: "scramble-turn/triple/triple_spacejoe-486581", gainDb: 6.5, align: "peak-velocity", nudgeMs: 0 },
        // Whole-puzzle rotation, Zachary's pick (approved 2026-10-02): a real
        // recording of a plastic broomstick swung softly past the mic
        // (Sadiquecat), a low, rounded swish at about the pat's level. Same rule
        // as the turns: its swell (loudest 10 ms, 124 ms in) at mid-rotation
        // (cubing.js eases rotations with smootherStep too), for any rotation
        // (y, y2) at any tempo. Where Zachary approved it for a quarter turn.
        rotation: { file: "scramble-rotate/7_sadiquecat-816261-broomstick-soft", gainDb: -14.9, align: "peak-velocity", centre: "swell", nudgeMs: 0 },
        // Lift off felt; contact: the puzzle leaves the felt. Off (try "scramble-lift/lift/regrip-1_01kamii05-428594").
        lift: null,
        // Settle on felt; contact: the puzzle touches the felt.
        // Zachary's pick (option 3): a soft muffled pat (Kenney carpet
        // footstep past its first scuff, low-passed 1.8 kHz, 20 ms soft
        // attack, ~115 ms). Output peak about 17 dB under the click's.
        settle: { file: "scramble-turn/settle/settle_kenney-carpet-000-soft-cut", gainDb: -14.6, offsetMs: -22 },
    },
};
