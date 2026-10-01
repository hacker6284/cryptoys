// Put the decks back: what you hear and how it moves. Edit a value and reload.
//
// sounds: file = path under demos/micro/sounds/ (no extension; run
//   tools/sync-micro-sounds.py after changing it). gainDb = loudness
//   (+ louder). offsetMs = when the file starts relative to the contact
//   (more negative = earlier; −peak puts the loudest sample on it).
//   fadeMs / maxMs shorten long files (0 = play it out). null = silent.
// timing: real code values (playroom/table-form.js GATHER_MS, unbox-physical.js RESTOW_MS).
export default {
    loopGapMs: 900,
    choices: {
        phase: "leave", // "leave", "restow"
    },
    timing: {
        GATHER_MS: 680,
        RESTOW_MS: 380,
    },
    sounds: {
        // Cards gathered; contact: the piles land on the boxes.
        gather: { file: "doubledeal-gather/fan-2_kenney-card-fan-2", gainDb: 14, offsetMs: -1054 },
        // Deck slides in; contact: restow starts (piles go in).
        deckIn: { file: "unbox/deck-slide-in/1_stirfydotwad-789738", gainDb: 12.5, offsetMs: -540 },
        // Flap closes; contact: the flap shuts.
        flap: { file: "doubledeal-restow/flap/flap-2_kenney-cards-pack-open-2", gainDb: 6, offsetMs: -220 },
    },
};
