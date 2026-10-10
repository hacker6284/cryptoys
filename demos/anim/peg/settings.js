// peg: a Battleship peg (Hasbro 2015 set: 18 mm, head Ø 5 × 12 mm, shank
// Ø 3 × 6 mm) and its own moves in a grid hole. Played by the BS stage
// (playroom/bs-stage.js); audited by demos/micro/peg/insert-remove.
//
// NOT YET APPROVED. Starting values from the pre-library peg microdemo
// (demos/micro/peg/settings.js: approach 420 ms, push 140 ms easeInCubic,
// pull 320 ms easeOutCubic, hover 28 mm). Curves, u = time / ms (ms ÷ tempo):
//   insert: the peg comes down its hole's axis from hoverM above the seat
//     (easeInOutCubic over approach), then pushes the last seatM home
//     (easeInCubic over push, fastest as it seats).
//   remove: the peg pulls straight out along its axis by hoverM
//     (easeOutCubic), then it is gone (back to the well).
//   slide: a peg moves from one hole to another: it pulls out, travels in
//     an arc (easeInOutQuad, top hopM above the higher hole) and pushes into
//     the new hole (BS: sliding the product strip's answer into a register).
// The BS stage plays the same laws at two tempos: `play` (a Play beat,
// every peg of the step moving together) and `step` (stepping through a
// step, one peg move after another, fast).
export default {
    loopGapMs: 500,
    choices: {},
    timing: {
        tempo: 1,
    },
    insert: { approachMs: 420, pushMs: 140, hoverM: 0.028, seatM: 0.005 },
    remove: { ms: 320, hoverM: 0.028 },
    slide: { ms: 560, hopM: 0.02 },
    // Tempo multipliers the BS stage plays them at (1× dock speed).
    tempos: { play: 3.2, step: 12 },
    sounds: {},
};
