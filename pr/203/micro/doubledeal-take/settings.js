// DoubleDeal take a card: what you hear and how it moves. Edit a value and reload.
//
// sounds: file = path under demos/micro/sounds/ (no extension; run
//   tools/sync-micro-sounds.py after changing it). gainDb = loudness
//   (+ louder). offsetMs = when the file starts relative to the contact
//   (more negative = earlier; −peak puts the loudest sample on it).
//   fadeMs / maxMs shorten long files (0 = play it out). null = silent.
// timing: real code values (doubledeal/table.js TABLE_TIMING; pace = the dock speed (every ms is divided by it)).
export default {
    loopGapMs: 700,
    timing: {
        pace: 1.8, // ×
        takeMs: 200,
        liftHop: 0.9,
    },
    sounds: {
        // Take; contact: the card lands on the pile.
        take: { file: "doubledeal-take/deal_kenney-card-slide-1", gainDb: 9.5, offsetMs: -77 },
    },
};
