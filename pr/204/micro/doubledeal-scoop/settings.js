// DoubleDeal scoop: what you hear and how it moves. Edit a value and reload.
//
// sounds: file = path under demos/micro/sounds/ (no extension; run
//   tools/sync-micro-sounds.py after changing it). gainDb = loudness
//   (+ louder). offsetMs = when the file starts relative to the contact
//   (more negative = earlier; −peak puts the loudest sample on it).
//   fadeMs / maxMs shorten long files (0 = play it out). null = silent.
// timing: real code values (doubledeal/table.js TABLE_TIMING; pace = the dock speed (every ms is divided by it)).
export default {
    loopGapMs: 700,
    choices: {
        kind: "scoopcm", // "scoopcm", "scooprm"
    },
    timing: {
        pace: 1.8, // ×
        scoopColMs: 240,
        scoopRowMs: 300,
        hop: 0.25,
        liftHop: 0.9,
    },
    sounds: {
        // Sweep; contact: the cards start moving.
        sweep: { file: "doubledeal-scoop/sweep-1_kenney-card-shove-2", gainDb: 12.5, offsetMs: -210 },
        // Pile squared (knock); contact: the cards land on the pile.
        knock: { file: "doubledeal-square/knock-a_hoganthelogan-466789-slice", gainDb: 9, offsetMs: -13 },
    },
};
