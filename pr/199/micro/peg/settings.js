// Peg: what you hear and how it moves. Edit a value and reload.
//
// sounds: file = path under demos/micro/sounds/ (no extension; run
//   tools/sync-micro-sounds.py after changing it). gainDb = loudness
//   (+ louder). offsetMs = when the file starts relative to the contact
//   (more negative = earlier; −peak puts the loudest sample on it).
//   fadeMs / maxMs shorten long files (0 = play it out). null = silent.
// timing: real code values (starting values (no demo code yet)).
export default {
    loopGapMs: 500,
    choices: {
        color: "white", // "white", "red"
        fill: "row", // "row", "same"
        approachEase: "easeInOutCubic", // "easeInOutCubic", "easeOutCubic", "easeInCubic", "easeInQuad", "linear"
        pushEase: "easeInCubic", // "easeInOutCubic", "easeOutCubic", "easeInCubic", "easeInQuad", "linear"
        pullEase: "easeOutCubic", // "easeInOutCubic", "easeOutCubic", "easeInCubic", "easeInQuad", "linear"
    },
    timing: {
        approachMs: 420,
        pushMs: 140,
        holdMs: 450,
        pullMs: 320,
        hover: 28, // mm
        seat: 5, // mm
    },
    sounds: {
        // Peg seats; contact: the peg bottoms out.
        push: { file: "peg/in/peg_in_lego_click_670000", gainDb: 15.5, offsetMs: -19 },
        // Peg pulled out; contact: the peg starts to lift.
        pull: { file: "peg/out/peg_out_punch_pulled_431447", gainDb: 11, offsetMs: -156 },
    },
};
