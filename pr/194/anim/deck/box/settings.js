// deck/box: the deck's tuck box (playroom/unbox-rig.js). Its own moves:
// open the flap, close the flap. The flap swings in the box's frame, so
// the box's placement is always an input (any pose, any yaw, standing or
// lying). Edit and reload demos/micro/deck/box/open-close-flap/.
//
// NOT YET APPROVED. Curves (../../shared/swing.js), u = time / ms:
//   swing: easeInOutCubic to the end angle plus overshoot (a fraction of
//     the sweep) over the first 1 − settle of the time, then
//     easeInOutSine back onto the end angle: the flap is pushed open by a
//     thumb and comes to rest against its fold. Fastest at
//     (1 − settle) / 2 of the time.
//   ms is for the full sweep (shut ↔ open); a flap already part-way
//     takes ms × √(fraction of the sweep left), ÷ tempo.
//   openRad: how far the flap opens (unbox-rig.js 2.15 rad = 123°).
//   Stop: if a solid is in the sweep (the felt, a shelf's backboard),
//     the flap opens only until it is stopGapM (1 mm) from it, without
//     the overshoot, and the page says what stopped it.
export default {
    loopGapMs: 600,
    choices: {},
    timing: {
        tempo: 1,
    },
    flap: {
        openRad: 2.15,
        stopGapM: 0.001,
        open: { ms: 380, curve: "swing", overshoot: 0.06, settle: 0.3 },
        close: { ms: 300, curve: "swing", overshoot: 0, settle: 0 },
    },
    sounds: {},
};
