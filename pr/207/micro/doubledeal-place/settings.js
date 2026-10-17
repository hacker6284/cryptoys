// DoubleDeal place a card: what you hear and how it moves. Edit a value and reload.
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
        flag: 0, // 0, 1
    },
    timing: {
        pace: 1.8, // ×
        placeMs: 240,
        dropMs: 160,
        liftHop: 0.9,
        hop: 0.25,
        dropY: 1.4,
    },
    sounds: {
        // Set down (hop); contact: the card lands.
        place: { file: "doubledeal-place/place/setdown_kenney-card-place-1", gainDb: 9, offsetMs: -102 },
        // Set down (drop); contact: the card lands.
        drop: { file: "doubledeal-place/drop/setdown_deathpie-19244", gainDb: 12.5, offsetMs: -191 },
    },
};
