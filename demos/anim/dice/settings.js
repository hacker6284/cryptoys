// dice: one die (d10, d12 or d6; the BS key dice, SPEC §4.2) and its own
// move: a roll. Played by the BS stage (playroom/bs-stage.js): the row cup's
// five d10s at the start of each row (a die on its zero face is thrown
// again), the hole die (d12) and the d6. Audited by demos/micro/dice/roll.
//
// NOT YET APPROVED. Curves, u = time / ms (ms ÷ tempo):
//   roll: the die leaves its spot on the felt, tumbles through `turns` whole
//     turns about a tilted axis while it hops sin(πu) × hopM, and lands on
//     the same spot showing the face it was thrown (its orientation slerps
//     from the tumble onto the landing face over the last quarter).
export default {
    loopGapMs: 700,
    choices: {},
    timing: {
        tempo: 1,
    },
    roll: { ms: 640, hopM: 0.05, turns: 2 },
    tempos: { play: 2.2, step: 1.6 },
    sounds: {},
};
