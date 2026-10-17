// DoubleDeal row slide: what you hear and how it moves. Edit a value and reload.
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
        kind: "shift", // "shift", "sumrow", "sumcol"
        amount: 3, // 1, 2, 3, 5, 6, 13
    },
    timing: {
        pace: 1.8, // ×
        shiftMs: 320,
        sumrowMs: 380,
        sumcolMs: 300,
        hop: 0.25,
        liftHop: 0.9,
        zeroShiftHop: 0.18,
    },
    sounds: {
        // Row slide; contact: the row starts moving.
        slide: { file: "doubledeal-row-slide/slide-1_kenney-card-slide-5", gainDb: 13.5, offsetMs: -124 },
        // Column belt; contact: the column starts moving.
        belt: { file: "doubledeal-column-belt/slide-2_kenney-card-shove-4", gainDb: 8.5, offsetMs: -224 },
        // Hop in place (amount 13); contact: the card lands.
        hop: { file: "doubledeal-table-settle/setdown_eggdeng-502658", gainDb: 8, offsetMs: -28 },
    },
};
