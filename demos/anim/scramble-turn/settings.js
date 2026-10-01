// Scramble face turn: what you hear and how it moves, everywhere it plays
// (the playroom's Scramble seat and demos/micro/scramble-turn). Edit a
// value and reload the microdemo; see ../README.md before changing an
// approved entry.
//
// sounds: file = path under demos/anim/sounds/ (no extension; run
//   tools/sync-micro-sounds.py after changing it). gainDb = loudness
//   (+ louder). offsetMs = when the file starts relative to the contact
//   (more negative = earlier; −peak puts the loudest sample on it).
//   startMs skips the file's head; fadeMs / maxMs shorten the tail
//   (0 = play it out). null = silent.
//   The turn sounds (single, double, triple, rotation) are tuned at
//   timing.speed. At another speed the time from the file's loudest
//   sample to the contact scales with the turn (× speed / tempo), so a
//   click keeps its place in the turn. The settle pat does not scale.
// timing: read by playroom/cube-stage.js (lift height and time, hold before
//   setting down); speed = the dock's starting tempo (cubing.js tempoScale).
// loopGapMs, choices: the microdemo loop only.
export default {
    loopGapMs: 700,
    choices: {
        move: "R", // "R", "Ri", "R2", "seq", "x", "R3"
    },
    timing: {
        speed: 1.4, // ×
        TURN_LIFT_MS: 320,
        TURN_LIFT: 0.14, // m
        SETTLE_HOLD_MS: 90,
    },
    sounds: {
        // Single turn (one click); contact: the face seats (end of leaf).
        single: { file: "scramble-turn/single/single_spacejoe-486564", gainDb: 11, offsetMs: -393 }, // at 1.4×: peak 250 ms before the face seats, ~65% into the 714 ms turn (Zachary: "still late ... maybe 200 ms earlier")
        // Double turn (two clicks); contact: the face seats (end of leaf). Or { perClick: true }: the single file once per click.
        double: { file: "scramble-turn/double/double_spacejoe-486567", gainDb: 8.5, offsetMs: -119 },
        // Triple turn (three clicks); contact: the face seats (end of leaf). Or { perClick: true }: the single file once per click.
        triple: { file: "scramble-turn/triple/triple_spacejoe-486581", gainDb: 6.5, offsetMs: -194 },
        // Whole-puzzle rotation; contact: rotation ends.
        rotation: { file: "scramble-turn/rotation/rotation_01kamii05-428594", gainDb: 3.5, offsetMs: -30 },
        // Lift off felt; contact: the puzzle leaves the felt. Off (try "scramble-lift/lift/regrip-1_01kamii05-428594").
        lift: null,
        // Settle on felt; contact: the puzzle touches the felt.
        // Zachary's pick (option 3): a soft muffled pat (Kenney carpet
        // footstep past its first scuff, low-passed 1.8 kHz, 20 ms soft
        // attack, ~115 ms). Output peak about 17 dB under the click's.
        settle: { file: "scramble-turn/settle/settle_kenney-carpet-000-soft-cut", gainDb: -14.6, offsetMs: -22 },
    },
};
