// DoubleDeal deal into the grid: what you hear and how it moves, everywhere
// it plays (demos/micro/deck/deal; the playroom DoubleDeal once
// its table moves to the real-size layout, see ../README.md). Edit a value
// and reload the microdemo.
//
// ANIMATION APPROVED and LOCKED at 7b5028f (Zachary: "at speed it looks
// fine"): the motion, timing, layout and camera of 0aef6e8 (timing below;
// the real-size layout in ../../doubledeal/real-layout.js; the card hop
// liftHop 0.9 below; the camera and framing in
// ../../../micro/deck/deal/page.js). Do not change them without
// his sign-off; ../../library.test.mjs pins them. Sound is ON HOLD
// project-wide (animations first): the stream keeps its file unapproved,
// and the per-card sound stays card: null until sound work resumes.
//
// sounds: file = path under demos/anim/sounds/ (no extension; run
//   tools/sync-micro-sounds.py after changing it). gainDb = loudness
//   (+ louder). Placement, from the slot's contact:
//   align: "peak-velocity" = the centre of the file's audible part (its
//   energy centroid above −30 dB, measured from the decoded file) lands
//   where the cards move fastest; "motion-start" = the file's audible
//   onset (its attack: the first moment within −30 dB of its peak) lands
//   as the card leaves the packet. nudgeMs moves it (+ later, ms at
//   timing.pace; push a motion-start sound later only if it feels early).
//   null = silent.
//   Each card slides from the hand packet to its seat in dealMs with
//   easeInOutQuad (fastest half way) while it hops sin(πt) × liftHop; the
//   real-size layout keeps every card's path long enough (≥ 171 mm) that
//   its peak speed is that half-way point, not the take-off. stream: one
//   sound per deal, contact = the mean of the 52 cards' peak-velocity
//   times (card i at (i × dealStaggerMs + dealMs / 2) / pace: 582 ms at
//   1.8×). card: per card, align "motion-start", contact = the moment
//   that card leaves the packet (card i at i × dealStaggerMs / pace);
//   every card's sound plays, overlapping freely (no gap, a voice per
//   card).
// timing: read by doubledeal/table.js (TABLE_TIMING; ms at pace 1, every
//   ms is divided by the pace); pace = the microdemo's dock speed.
// loopGapMs, choices: the microdemo loop only.
export default {
    loopGapMs: 700,
    choices: {
        major: "deal", // "deal" (column by column: card i to row i % 4, column ⌊i / 4⌋), "dealrm" (row by row)
    },
    timing: {
        pace: 1.8, // ×
        dealMs: 260,
        dealStaggerMs: 36,
        liftHop: 0.9, // card hop height in table units (0.9 × 0.1125 m ≈ 101 mm)
    },
    sounds: {
        // The grid stream (one per deal): Kenney card fan.
        stream: { file: "doubledeal-grid-deal/fan-1_kenney-card-fan-1", gainDb: 5.5, align: "peak-velocity", nudgeMs: 0 },
        // Per card, as it leaves the packet. PENDING (sound on hold): off
        // until Zachary picks one ({ file, gainDb, align: "motion-start",
        // nudgeMs: 0 }; 14 candidates rendered, none chosen).
        card: null,
    },
};
