// hinge: a lid or flap swings on its hinge (the toy chest's lid, a tuck
// box's flap). The motion is the part's own, in its container's frame,
// so the container's placement is always an input (any pose, any yaw,
// standing or lying). Edit and reload demos/micro/hinge/.
//
// NOT YET APPROVED. Curves (see ./index.js), u = time / ms:
//   swing: easeInOutCubic to the end angle plus overshoot (a fraction of
//     the sweep) over the first 1 − settle of the time, then
//     easeInOutSine back onto the end angle: the part is lifted or pushed
//     by hand and comes to rest against its stop. Fastest at
//     (1 − settle) / 2 of the time.
//   fall: the part drops shut under its own weight: angle ∝ u² over the
//     first 1 − settle (fastest at the moment it shuts), then one small
//     rebound of `bounce` of the sweep, sin-shaped, back onto shut.
//   ms is for the full sweep (shut ↔ open); a part already part-way
//     takes ms × √(fraction of the sweep left), ÷ tempo.
//   openRad: how far the part opens (the rigs' own angles: world.js
//     chest lid 1.45 rad = 83°, unbox-rig.js tuck flap 2.15 rad = 123°).
//   Stop: if a solid is in the sweep (a wall, a shelf's backboard, the
//     other box), the part opens only until it is stopGapM from it
//     (10 mm for the chest lid, 1 mm for the paper flap), without the
//     overshoot, and the page says what stopped it.
export default {
    loopGapMs: 600,
    choices: {},
    timing: {
        tempo: 1,
    },
    parts: {
        "chest-lid": {
            openRad: 1.45,
            stopGapM: 0.01,
            open: { ms: 640, curve: "swing", overshoot: 0.03, settle: 0.25 },
            close: { ms: 520, curve: "fall", bounce: 0.035, settle: 0.24 },
        },
        "tuck-flap": {
            openRad: 2.15,
            stopGapM: 0.001,
            open: { ms: 380, curve: "swing", overshoot: 0.06, settle: 0.3 },
            close: { ms: 300, curve: "swing", overshoot: 0, settle: 0 },
        },
    },
    sounds: {},
};
