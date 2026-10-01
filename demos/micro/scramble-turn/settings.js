// Scramble face turn: what you hear and how it moves. Edit a value and reload.
//
// sounds: file = path under demos/micro/sounds/ (no extension; run
//   tools/sync-micro-sounds.py after changing it). gainDb = loudness
//   (+ louder). offsetMs = when the file starts relative to the contact
//   (more negative = earlier; −peak puts the loudest sample on it).
//   fadeMs / maxMs shorten long files (0 = play it out). null = silent.
// timing: real code values (playroom/cube-stage.js CUBE_STAGE_TIMING; speed = the dock tempo (cubing.js tempoScale)).
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
        single: { file: "scramble-turn/single/single_spacejoe-486564", gainDb: 11, offsetMs: -143 },
        // Double turn (two clicks); contact: the face seats (end of leaf). Or { perClick: true }: the single file once per click.
        double: { file: "scramble-turn/double/double_spacejoe-486567", gainDb: 8.5, offsetMs: -119 },
        // Triple turn (three clicks); contact: the face seats (end of leaf). Or { perClick: true }: the single file once per click.
        triple: { file: "scramble-turn/triple/triple_spacejoe-486581", gainDb: 6.5, offsetMs: -194 },
        // Whole-puzzle rotation; contact: rotation ends.
        rotation: { file: "scramble-turn/rotation/rotation_01kamii05-428594", gainDb: 3.5, offsetMs: -30 },
        // Lift off felt; contact: the puzzle leaves the felt. Off (try "scramble-lift/lift/regrip-1_01kamii05-428594").
        lift: null,
        // Settle on felt; contact: the puzzle touches the felt.
        settle: { file: "scramble-turn/settle/settle_emapuree-848748", gainDb: 6, offsetMs: -33 },
    },
};
