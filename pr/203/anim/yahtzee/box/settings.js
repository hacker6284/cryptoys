// yahtzee/box: the dice game's retail box (demos/bs/assets/models/
// proc_dice_game_box_120x114x89.glb: 120.3 × 113.6 × 88.6 mm, DESIGNED TO
// FIT what it holds, tools/bs_boxes.py: the Ø 82.6 × 101.6 mm cup lying on
// its side and the dice in a strip beside it) and its own moves: take the
// lid off and put it back on, lift the cup out (standing it up on the way)
// and put it back in. The box's pose, where the lid and the cup go and
// what is around are always inputs. Edit and reload
// demos/micro/yahtzee/box/lid-off-on/ and
// demos/micro/yahtzee/box/lift-cup-out-in/.
//
// NOT YET APPROVED. Each is a hop (../../shared/hop.js): straight up until
// the moving part's bottom is clearM above the base's rim (and above
// anything it passes over), straight across at that height (the cup
// turning from lying to standing: slerp), straight down. Each leg eases
// in and out (easeInOutSine); a leg of d metres takes baseMs + perSqrtM ×
// √d ms, within minMs … maxMs, ÷ tempo.
export default {
    loopGapMs: 700,
    choices: {},
    timing: {
        tempo: 1,
    },
    lid: { clearM: 0.02, baseMs: 140, perSqrtM: 700, minMs: 220, maxMs: 900 },
    cup: { clearM: 0.02, baseMs: 160, perSqrtM: 760, minMs: 260, maxMs: 1000 },
    // The playroom BS demo plays the unboxing and the repacking at these tempos.
    tempos: { unbox: 1.6, repack: 2.4 },
    sounds: {},
};
