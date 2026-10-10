// ship: a Battleship piece (Hasbro 2015 set: 10 mm wide; carrier 65,
// battleship 52, cruiser and sub 41, destroyer 27 mm; 2 legs × 5 mm) and its
// own moves on a grid. Played by the BS stage (playroom/bs-stage.js): BUILD
// lays a Destroyer and swaps it for the next longer piece as it grows
// (SPEC §4.2), and the walk cursor's two Destroyers move along the frame.
// Audited by demos/micro/ship/place-lift.
//
// NOT YET APPROVED. Curves, u = time / ms (ms ÷ tempo):
//   place: the piece comes straight down from dropM above its holes
//     (easeInOutCubic), its legs into the holes.
//   lift: straight up by dropM (easeOutCubic); then it is gone.
//   move: the cursor piece slides along the frame to its next hole
//     (easeInOutQuad), no hop.
export default {
    loopGapMs: 600,
    choices: {},
    timing: {
        tempo: 1,
    },
    place: { ms: 420, dropM: 0.03 },
    lift: { ms: 340, dropM: 0.03 },
    move: { ms: 260 },
    tempos: { play: 2.2, step: 4 },
    sounds: {},
};
