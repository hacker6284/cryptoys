// battleship/box: the Battleship retail box (Hasbro 2015 set, 400 × 265 ×
// 52.5 mm, MEASURED by Zachary; demos/bs/assets/models/
// proc_naval_game_box_400x265x52.glb) and its own moves: take the lid off
// and put it back on, lift a unit out and put it back in. The box's pose,
// where the lid and the unit go and what is around are always inputs.
// Edit and reload demos/micro/battleship/box/lid-off-on/ and
// demos/micro/battleship/box/lift-units-out-in/.
//
// NOT YET APPROVED. Each is a hop (../../shared/hop.js): straight up until
// the moving part's bottom is clearM above the base's walls (and above
// anything it passes over), straight across at that height (a unit turns
// from its pocket to its seat on the way: slerp), straight down. Each leg
// eases in and out (easeInOutSine); a leg of d metres takes
// baseMs + perSqrtM × √d ms, within minMs … maxMs, ÷ tempo.
export default {
    loopGapMs: 700,
    choices: {},
    timing: {
        tempo: 1,
    },
    lid: { clearM: 0.02, baseMs: 140, perSqrtM: 700, minMs: 220, maxMs: 900 },
    unit: { clearM: 0.02, baseMs: 140, perSqrtM: 760, minMs: 240, maxMs: 1000 },
    // The playroom BS demo plays the unboxing and the repacking at these tempos.
    tempos: { unbox: 1.6, repack: 2.4 },
    sounds: {},
};
