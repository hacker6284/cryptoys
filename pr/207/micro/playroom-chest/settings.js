// Toy chest: what you hear and how it moves. Edit a value and reload.
//
// sounds: file = path under demos/micro/sounds/ (no extension; run
//   tools/sync-micro-sounds.py after changing it). gainDb = loudness
//   (+ louder). offsetMs = when the file starts relative to the contact
//   (more negative = earlier; −peak puts the loudest sample on it).
//   fadeMs / maxMs shorten long files (0 = play it out). null = silent.
// timing: real code values (playroom/toy-director.js DIRECTOR_TIMING).
export default {
    loopGapMs: 1200,
    choices: {
        mode: "borrow", // "lid", "borrow", "home", "both"
    },
    timing: {
        LID_OPEN_MS: 520,
        LID_CLOSE_MS: 560,
        FLY_MS: 1800,
        LIFT_MS: 380,
    },
    sounds: {
        // Lid opens (creak); contact: the lid starts to open.
        lidOpen: { file: "unbox/chest-lid-open/1_sheyvan-475294-slice", gainDb: 6.5, offsetMs: -16 },
        // Lid closes; contact: the lid shuts.
        lidClose: { file: "unbox/chest-lid-close/1_sheyvan-475294-slice", gainDb: 6, offsetMs: -58 },
        // Toy lifts off; contact: a toy leaves its seat. Off (try "playroom-fly/lift/lift-1_kenney-card-slide-3").
        lift: null,
        // Toy lands; contact: a toy lands (felt, shelf or chest).
        land: { file: "unbox/box-setdown-felt/1_emapuree-848748", gainDb: 6, offsetMs: -33 },
    },
};
