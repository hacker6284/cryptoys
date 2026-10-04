// MegaDreifach deck flap: what you hear and how it moves. Edit a value and reload.
//
// sounds: file = path under demos/micro/sounds/ (no extension; run
//   tools/sync-micro-sounds.py after changing it). gainDb = loudness
//   (+ louder). offsetMs = when the file starts relative to the contact
//   (more negative = earlier; −peak puts the loudest sample on it).
//   fadeMs / maxMs shorten long files (0 = play it out). null = silent.
// timing: real code values (drei-stage.js dealCards (keynote/megadreifach-demo): flap ms(260) at tempo 2).
export default {
    loopGapMs: 700,
    timing: {
        tempo: 2, // ×
        flapMs: 260,
        holdMs: 2258,
    },
    sounds: {
        // Flap opens; contact: the flap starts to lift.
        open: { file: "unbox/tuck-flap-open/1_kenney-cards-pack-open-1", gainDb: 8, offsetMs: -312 },
        // Flap closes; contact: the flap shuts.
        close: { file: "doubledeal-restow/flap/flap-2_kenney-cards-pack-open-2", gainDb: 6, offsetMs: -220 },
    },
};
