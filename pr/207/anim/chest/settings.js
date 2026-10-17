// chest: the playroom's toy chest. Its own moves: open the lid, close the
// lid. The lid swings in the chest's frame, so where the chest stands
// (anim/shared/room.js chestAt: centre and yaw) is always an input. Edit
// and reload demos/micro/chest/open-close-lid/.
//
// NOT YET APPROVED. Curves (../shared/swing.js), u = time / ms:
//   swing (open): easeInOutCubic to the end angle plus overshoot over the
//     first 1 − settle of the time, then easeInOutSine back onto it: the
//     lid is lifted and comes to rest. Fastest at (1 − settle) / 2.
//   fall (close): the lid drops shut under its own weight: angle ∝ u²
//     over the first 1 − settle (fastest at the moment it shuts), then
//     one small rebound of `bounce` of the sweep, sin-shaped.
//   ms is for the full sweep; part-way takes ms × √(fraction), ÷ tempo.
//   openRad: world.js chest lid 1.45 rad = 83°.
//   Stop: if a solid is in the sweep (a wall, the shelf), the lid opens
//     only until it is stopGapM (10 mm) from it, without the overshoot.
export default {
    loopGapMs: 600,
    choices: {},
    timing: {
        tempo: 1,
    },
    lid: {
        openRad: 1.45,
        stopGapM: 0.01,
        open: { ms: 640, curve: "swing", overshoot: 0.03, settle: 0.25 },
        close: { ms: 520, curve: "fall", bounce: 0.035, settle: 0.24 },
    },
    sounds: {},
};
