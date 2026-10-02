// Scramble face turn: what you hear and how it moves, everywhere it plays
// (the playroom's Scramble seat and demos/micro/scramble-turn). Edit a
// value and reload the microdemo; see ../README.md before changing an
// approved entry.
//
// sounds: file = path under demos/anim/sounds/ (no extension; run
//   tools/sync-micro-sounds.py after changing it). gainDb = loudness
//   (+ louder). Placement, from the slot's contact:
//   peakAtMs = when the file's loudest click lands (0 = on the contact,
//   + later), or offsetMs = when the file starts (more negative =
//   earlier; −peak puts the loudest sample on it).
//   startMs skips the file's head; fadeMs / maxMs shorten the tail
//   (0 = play it out). null = silent.
//   The turn sounds (single, double, triple, rotation) are tuned at
//   timing.speed. At another speed the time from the contact to the
//   file's loudest sample scales with the turn (× speed / tempo), so a
//   click keeps its place in the turn. The settle pat does not scale.
//   A face turn whose file starts before the turn does gets it in time:
//   the stage hands the voice the turn ahead (during the lift).
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
        // Single turn (one click); contact: the face starts moving (start of leaf).
        // LOCKED, approved by Zachary (af9a8fb, tempo-scaled at 2b5f6d4): do not
        // change. The file starts 393 ms before the face seats at 1.4×, i.e.
        // 1000/1.4 − 393 = 321.3 ms into the 714 ms turn; its loudest click
        // (143 ms in) lands ~464 ms after the start, 250 ms before seating,
        // ~65% of the way through. Pinned by ../library.test.mjs.
        single: { file: "scramble-turn/single/single_spacejoe-486564", gainDb: 11, offsetMs: 1000 / 1.4 - 393 },
        // Double turn (two clicks); contact: the face starts moving (start of leaf).
        // Zachary: "The sounds are too late! They should be playing right at the
        // beginning and then if they seem too early we adjust." peakAtMs 0: the
        // loudest click on the turn's start; later = + ms (of a 1071 ms turn at 1.4×).
        // Or { perClick: true }: the single file once per click.
        double: { file: "scramble-turn/double/double_spacejoe-486567", gainDb: 8.5, peakAtMs: 0 },
        // Triple turn (three clicks); contact: the face starts moving (start of leaf).
        // peakAtMs 0, as the double (of a 1429 ms turn at 1.4×). Or { perClick: true }.
        triple: { file: "scramble-turn/triple/triple_spacejoe-486581", gainDb: 6.5, peakAtMs: 0 },
        // Whole-puzzle rotation; contact: rotation ends. Zachary's pick: a real
        // recording of a plastic broomstick swung softly past the mic (Sadiquecat),
        // a low, rounded swish; its swell (125 ms in) peaks at mid-rotation
        // (357 ms before the end at 1.4×), at about the pat's level.
        rotation: { file: "scramble-rotate/7_sadiquecat-816261-broomstick-soft", gainDb: -14.9, offsetMs: -482 },
        // Lift off felt; contact: the puzzle leaves the felt. Off (try "scramble-lift/lift/regrip-1_01kamii05-428594").
        lift: null,
        // Settle on felt; contact: the puzzle touches the felt.
        // Zachary's pick (option 3): a soft muffled pat (Kenney carpet
        // footstep past its first scuff, low-passed 1.8 kHz, 20 ms soft
        // attack, ~115 ms). Output peak about 17 dB under the click's.
        settle: { file: "scramble-turn/settle/settle_kenney-carpet-000-soft-cut", gainDb: -14.6, offsetMs: -22 },
    },
};
