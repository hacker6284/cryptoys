// Dice cup: what you hear and how it moves. Edit a value and reload.
//
// sounds: file = path under demos/micro/sounds/ (no extension; run
//   tools/sync-micro-sounds.py after changing it). gainDb = loudness
//   (+ louder). offsetMs = when the file starts relative to the contact
//   (more negative = earlier; −peak puts the loudest sample on it).
//   fadeMs / maxMs shorten long files (0 = play it out). null = silent.
// timing: real code values (starting values (no demo code yet)).
export default {
    loopGapMs: 700,
    choices: {
        set: "poly", // "poly", "d6", "d20"
    },
    timing: {
        shakeMs: 900,
        shakeHz: 6.5, // Hz
        shakeAmp: 14, // mm
        shakeTilt: 9, // °
        pourMs: 520,
        pourAngle: 118, // °
        releaseAt: 0.55,
        restitution: 0.32,
        friction: 4.5, // /s
        holdMs: 900,
    },
    sounds: {
        // Cup shake; contact: the shake starts.
        shake: { file: "dice-cup/shake/cup_shake_6dice_185985_a", gainDb: 11, offsetMs: -503 },
        // Dice land; contact: the first die hits the felt.
        land: { file: "dice-cup/pour-slam/cup_pour_6dice_felt_185982_a", gainDb: 14, offsetMs: -128 },
        // Dice settle; contact: the last die comes to rest.
        settle: { file: "dice-cup/settle/settle_soft_tray_815672", gainDb: 7, offsetMs: -1382 },
    },
};
