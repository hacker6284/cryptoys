// Unbox: what you hear and how it moves. Edit a value and reload.
//
// sounds: file = path under demos/micro/sounds/ (no extension; run
//   tools/sync-micro-sounds.py after changing it). gainDb = loudness
//   (+ louder). offsetMs = when the file starts relative to the contact
//   (more negative = earlier; −peak puts the loudest sample on it).
//   fadeMs / maxMs shorten long files (0 = play it out). null = silent.
// timing: real code values (playroom/unbox-physical.js UNBOX_TIMING).
export default {
    loopGapMs: 900,
    choices: {
        phase: "out", // "flap", "extract", "out", "lay", "deal", "full"
        flapEase: "easeOutCubic", // "easeOutCubic", "easeInOutCubic", "easeOutQuart", "linear"
        extractEase: "easeOutQuart", // "easeOutCubic", "easeInOutCubic", "easeOutQuart", "linear"
        layEase: "easeInOutCubic", // "easeOutCubic", "easeInOutCubic", "easeOutQuart", "linear"
        asideEase: "easeInOutCubic", // "easeOutCubic", "easeInOutCubic", "easeOutQuart", "linear"
        dealEase: "easeOutCubic", // "easeOutCubic", "easeInOutCubic", "easeOutQuart", "linear"
    },
    timing: {
        flapMs: 680,
        flapPauseMs: 120,
        extractMs: 760,
        extractRise: 0.086,
        layMs: 600,
        layLift: 0.04,
        asideMs: 780,
        asideLift: 0.055,
        dealStaggerMs: 64,
        dealMs: 560,
        dealLift: 0.07,
    },
    sounds: {
        // Flap opens; contact: the flap starts to lift (flap beat).
        flap: { file: "unbox/tuck-flap-open/1_kenney-cards-pack-open-1", gainDb: 8, offsetMs: -312 },
        // Deck slides out; contact: the packet starts to rise (extract beat).
        extract: { file: "unbox/deck-slide-out/1_kenney-cards-pack-take-out-1", gainDb: 0.5, offsetMs: -183 },
        // Packet set down; contact: the packet lands on the felt.
        lay: { file: "doubledeal-packet-lay/setdown_kenney-card-place-1", gainDb: 9, offsetMs: -102 },
        // Sleeve set aside; contact: the empty box lands.
        aside: { file: "doubledeal-sleeve-aside/aside_emapuree-848748", gainDb: 6, offsetMs: -33 },
        // Card dealt (per card); contact: each card lands.
        deal: { file: "doubledeal-deal/deal_realsquink-787405", gainDb: 9.5, offsetMs: -250 },
    },
};
