// battleship/unit: one Battleship player unit (the retail Hasbro travel
// unit, demos/bs/assets/models/bs_unit_*.glb, 230 × 35.1 × 171.4 mm closed)
// and its own moves: open the lid and close it. The lid swings on the
// unit's hinge (the GLB's lid_pivot), so where the unit stands is always an
// input. Edit and reload demos/micro/battleship/unit/open-close-lid/.
//
// NOT YET APPROVED. Curves (../../shared/swing.js), u = time / ms:
//   swing (open): easeInOutCubic up to the lid's stop, no overshoot (the
//     hinge stops it upright, the way the GLB's lid_open clip ends).
//   swing (close): easeInOutCubic down onto the tray.
//   ms is for the full sweep; part-way takes ms × √(fraction), ÷ tempo.
//   openRad: the GLB's lid_open clip, closed → open: 90°.
//   Stop: if a solid is in the sweep, the lid opens only until it is
//     stopGapM (5 mm) from it.
export default {
    loopGapMs: 700,
    choices: {},
    timing: {
        tempo: 1,
    },
    lid: {
        openRad: Math.PI / 2,
        stopGapM: 0.005,
        open: { ms: 760, curve: "swing", overshoot: 0, settle: 0 },
        close: { ms: 640, curve: "swing", overshoot: 0, settle: 0 },
    },
    // The playroom BS demo plays the unboxing and the repacking at these tempos.
    tempos: { unbox: 1.4, repack: 2 },
    sounds: {},
};
