// DoubleDeal deal into the grid: what you hear and how it moves. Edit a value and reload.
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
        major: "deal", // "deal", "dealrm"
    },
    timing: {
        pace: 1.8, // ×
        dealMs: 260,
        dealStaggerMs: 36,
        liftHop: 0.9,
    },
    sounds: {
        // Grid stream (one per step); contact: first card lands.
        stream: { file: "doubledeal-grid-deal/fan-1_kenney-card-fan-1", gainDb: 5.5, offsetMs: -467 },
        // Card lands (per card, ≤15/s); contact: each card lands. Off (try "doubledeal-table-settle/setdown_eggdeng-502658").
        card: null,
    },
};
