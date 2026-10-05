// carry: a rigid toy (deck box, deck, puzzle, empty sleeve) goes from one
// pose to another. Placement is always an input (any start, any end, any
// yaw, flips, any surface); these are the locked laws. Edit and reload
// demos/micro/carry/.
//
// NOT YET APPROVED. Laws (see ./index.js):
//   path: a cubic Bézier whose end handles point straight up, so the toy
//     lifts straight off its seat and sets straight down onto the next
//     (vertical take-off and touchdown); its top is
//     max(start, end) + riseM + risePerM × horizontal distance (capped at
//     riseMaxM), raised further until the toy's drawn box clears every
//     solid under and around the path by clearM (the margin ramps in
//     from 0 over the first clearM of horizontal travel from either
//     seat, so a toy set 1 cm beside another still goes straight down).
//   pace: smootherstep along the path's length: still at both ends (no
//     jerk at take-off or touchdown), fastest exactly half way (1.875 ×
//     the mean speed).
//   duration: baseMs + perSqrtM × √(path length in m), clamped to
//     [minMs, maxMs], ÷ tempo: a long flight is quicker per metre than a
//     short hop, so peak speed grows as √length.
//   turn: quaternion slerp (shorter arc) from the start orientation to
//     the end one, smootherstep over the middle turnFrom..turnTo of the
//     path, so the toy is up off its seat before it turns and square
//     again before it lands.
export default {
    loopGapMs: 650,
    choices: {},
    timing: {
        tempo: 1,
        baseMs: 450,
        perSqrtM: 650,
        minMs: 500,
        maxMs: 2000,
        riseM: 0.03,
        risePerM: 0.18,
        riseMaxM: 0.5,
        clearM: 0.03,
        turnFrom: 0.12,
        turnTo: 0.88,
    },
    sounds: {},
};
