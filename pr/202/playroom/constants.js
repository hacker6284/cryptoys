// 1:1 playroom measures (metres). Demo-layer presentation only.
//
// INVARIANT (Zachary, 2026-10-02): "All toys in real life scale in the
// room and that's an invariant." Every toy in the room is at real-life
// scale; never fit a toy to another toy's box. Each toy is sized to its
// own real measure, below. A puzzle may share the cube's size only if
// that is its own real size. motion.js fitToRealSize applies a puzzle's
// entry on its true measure (not its bounding box); seatOnSurface then
// plants the live post-scale shape, so a bigger toy still sits on the
// felt or shelf.
//
// REAL_SIZES is the one table of real sizes, with the source beside
// each, to check by eye.
//   measure "face-to-face": distance between opposite parallel faces (a
//     cube's edge; how a megaminx is quoted, and the same in any
//     orientation). "edge": the longest straight line across the toy (a
//     tetrahedron's edge, how a pyraminx is quoted). "box": w × h × d.
//     "longest": the longest side.
export const REAL_SIZES = {
    // Rubik's 3×3: "3×3: … 57mm version" (Rubik's, rubiksgift.com/faqs);
    // "the original cube size was 57mm" (funCUBING, hjreggel.net/fun/fc_size.html).
    "3x3x3": { m: 0.057, measure: "face-to-face" },
    // Megaminx: Tomy original "2.75 inches between opposite faces" = 69.9 mm
    // (J. A. Storer, cs.brandeis.edu/~storer/JimPuzzles/ZPAGES/zzzMegaminx.html);
    // ShengShou Megaminx 72 × 72 × 72 mm (cuberspace.shop). 70 mm face to
    // face is about 88 mm corner to corner.
    megaminx: { m: 0.070, measure: "face-to-face" },
    // Pyraminx: QiYi Pyraminx "Edge-Length: 97.0mm" (yoyosam.com); QiYi
    // QiMing A 97.5 mm (cuberspace.shop); MoYu WeiLong 96 mm.
    pyraminx: { m: 0.097, measure: "edge" },
    // Poker-size playing card, 2.5 × 3.5 in (63.5 × 88.9 mm), sold as
    // 63 × 88 mm (boxbaba.com/blog/standard-playing-card-dimensions).
    card: { w: 0.063, d: 0.088, measure: "box" },
    // Poker tuck box: 66 × 91 × 19 mm (onocustomboxes.com/blog/playing-card-box-dimensions);
    // Bicycle 807 Rider Back 70 × 95 × 20 mm (dateks.lv).
    deckBox: { w: 0.067, h: 0.092, d: 0.020, measure: "box" },
    // Wooden toy chest: IKEA SMÅSTAD 90 × 52 × 48 cm (ikea.com); KALIX
    // 93.5 × 53 × 34.5 cm (nateoconcept.com).
    chest: { m: 0.95, measure: "longest" },
    // BS (Battleship travel unit, Hasbro 2015 edition #B7447/E6445): measured
    // by Zachary, 2026-10-07, on his own set (Scrounger's asset pack README
    // §2, battleship-assets/README.md). Closed 230 × 170 × 35 mm; the GLB is
    // modelled from these numbers with the lid open 90° (230 × 177 × 173.6 mm).
    bsUnit: { w: 0.230, h: 0.035, d: 0.170, measure: "box" },
    // Grid holes Ø 4 mm at 13.333 mm pitch (hole 1 to hole 10 = 120 mm), same source.
    bsPitch: { m: 0.12 / 9, measure: "pitch" },
    // Peg 18 mm long: head 12 mm × Ø 5 mm, shank 6 mm × Ø 3 mm, same source.
    bsPeg: { m: 0.018, measure: "longest" },
    // Ships 10 mm wide; carrier 65, battleship 52, cruiser 41, submarine 41,
    // destroyer 27 mm long, same source.
    bsShip: { w: 0.010, carrier: 0.065, battleship: 0.052, cruiser: 0.041, sub: 0.041, destroyer: 0.027, measure: "longest" },
    // d6 16 mm face to face: Chessex's standard "16mm d6" (Chessex 2019
    // catalogue, chessex.com/images/2019%20CAT06.pdf); size measured face to
    // face (diceemporium.com/dice-sizes-explained/).
    d6: { m: 0.016, measure: "face-to-face" },
    // d10 22 mm pole to pole: measured d10s are 21–24 mm tip to tip (Chessex
    // 22–24, Koplow 21, Bescon 21–22; DiceDB mould table, db.drnod.de/dice_molds.php).
    d10: { m: 0.022, measure: "pole-to-pole" },
    // d12 20.3 mm vertex to vertex: measured d12s are 20–22 mm tip to tip
    // (Chessex 22, Koplow 21, Bescon 21; DiceDB, same page).
    d12: { m: 0.0203, measure: "vertex-to-vertex" },
    // Leather dice cup, 3 1/4" × 4" (82.6 × 101.6 mm), "perfect for 5 dice"
    // (dicegames.com/products/deluxe-leather-dice-cup-3-1-4-x-4); cf.
    // myleathergoods.com 3.1" × 3.6", Julia Moss 3" × 3.5".
    diceCup: { m: 0.1016, w: 0.0826, measure: "height" },
};

/** A puzzle's real size: { m, measure } (unknown ids get the 3×3's). */
export function realSizeOf(puzzleId) {
    const entry = REAL_SIZES[puzzleId];
    return entry && Number.isFinite(entry.m) && entry.measure !== "box" ? entry : REAL_SIZES["3x3x3"];
}

export const ASSET_BASE = new URL("./assets/", import.meta.url);

export const CARD_W = REAL_SIZES.card.w;
export const CARD_D = REAL_SIZES.card.d;
// The Scramble 3×3's real edge. Not a size for any other toy: each puzzle
// is fitted to its own REAL_SIZES entry (twisty-rig adoptTwistyPuzzle).
export const CUBE = REAL_SIZES["3x3x3"].m;
// Each MegaDreifach megaminx at its own real size (REAL_SIZES.megaminx:
// 70 mm face to face).
export const MINX = REAL_SIZES.megaminx.m;
// MegaDreifach v3 layout (metres; x from DEN.x, z from DEN.z, +z toward
// the seat). Every toy and card at its real size, nothing overlapping:
//   - the puzzle row, B | A | C, on DREI_ROW_Z, DREI_PITCH apart (a 70 mm
//     megaminx is at most 88 mm across, so neighbours stay >= 50 mm
//     apart, also while one lifts for a turn);
//   - the DEAL tuck box (67 x 20 mm standing) one gap left of B, and the
//     held card's seat (63 x 88 mm, face up) one gap right of C;
//   - the deal: 52 cards in 13 columns x 4 rows, 4 mm apart (as
//     doubledeal/real-layout.js), its far row DREI_GAP in front of the
//     puzzles. 867 x 364 mm: well inside the 0.945 m felt radius.
// No tray, no cups, no labels: only toys on the table.
export const DREI_PITCH = 0.14;
export const DREI_ROW_Z = -0.25; // row centre line, from DEN.z
export const DREI_SEAT_XZ = {
    A: [0, 0],
    B: [-DREI_PITCH, 0],
    C: [DREI_PITCH, 0],
};
export const DREI_GAP = 0.04;
// A megaminx's widest footprint (corner to corner, 70 mm face to face).
export const MINX_SPAN = 0.088;
export const DREI_DECK_X = -(DREI_PITCH + MINX_SPAN / 2 + DREI_GAP + REAL_SIZES.deckBox.w / 2);
export const DREI_HELD_X = DREI_PITCH + MINX_SPAN / 2 + DREI_GAP + REAL_SIZES.card.w / 2;
// The deal grid: card pitch (63 + 4, 88 + 4 mm) and the far row's centre.
export const DREI_DEAL = {
    cols: 13,
    rows: 4,
    gap: 0.004,
    colPitch: REAL_SIZES.card.w + 0.004,
    rowPitch: REAL_SIZES.card.d + 0.004,
    farZ: DREI_ROW_Z + MINX_SPAN / 2 + DREI_GAP + REAL_SIZES.card.d / 2,
};
export const DREI_EXTRA = { dreiB: "B", dreiC: "C" };
// Standing deck box in world.makeDeckBox (bw × bh × bd).
export const DECK_H = REAL_SIZES.deckBox.h;

// BS layout (metres; x from DEN.x, z from DEN.z, +z toward the seat). Real
// size, nothing overlapping (playroom/bs-layout.test.mjs checks it):
//   - the two units side by side, lids up (T1: each player's ocean grid is
//     the key grid, the lid's target grid the workspace, SPEC §6): Alice's
//     red unit left, Bob's blue right, BS_GAP apart; an open unit's
//     footprint is 230 × 173.5 mm (BS_UNIT_FOOT, from its origin);
//   - the dice cup (Ø 83.7 mm at 101.6 mm tall) one gap left of Alice's
//     unit, its front in line with the units' (in front of them it would
//     hide their trays from the seat);
//   - the key dice one gap in front of the units, in a row: the row cup's
//     five d10s (rainbow), the d12 and the d6.
// No tray, no box, no labels: only toys on the table.
export const BS_GAP = 0.04;
export const BS_UNIT_FOOT = { x0: -0.115, x1: 0.115, z0: -0.0901, z1: 0.0834 };
export const BS_UNIT_Z = -0.12;
// The dice row on the bsDice toy's origin (on the felt): x of each die.
// Footprints (radius on the felt): cup 41.9 mm (the model's 41 mm rim at
// the sourced 101.6 mm height), d10 ≤ 12.5, d12 ≤ 10.2, d6 ≤ 11.3.
export const BS_DICE = {
    d10: [-0.1, -0.068, -0.036, -0.004, 0.028],
    d12: 0.066,
    d6: 0.1,
    reach: { cup: 0.0419, d10: 0.0125, d12: 0.0102, d6: 0.0114 },
};
export const BS_SEAT_XZ = {
    bs: [-(BS_UNIT_FOOT.x1 + BS_GAP / 2), BS_UNIT_Z],
    bsB: [BS_UNIT_FOOT.x1 + BS_GAP / 2, BS_UNIT_Z],
    bsDice: [0, BS_UNIT_Z + BS_UNIT_FOOT.z1 + BS_GAP + BS_DICE.reach.d10],
    bsCup: [-(2 * BS_UNIT_FOOT.x1 + BS_GAP / 2 + BS_GAP + BS_DICE.reach.cup), BS_UNIT_Z + BS_UNIT_FOOT.z1 - BS_DICE.reach.cup],
};
export const BS_SHELF = { x: 0.55, z: -2.165 };

// Fallback only, when a toy cannot be measured: seatOnSurface seats from
// the live post-scale shape (a megaminx's own height, not the cube's).
export function toyHalfHeight(name) {
    if (name === "deck" || name === "deck2" || name === "deck3") return DECK_H / 2;
    if (name === "drei" || name === "dreiB" || name === "dreiC") return MINX / 2;
    return CUBE / 2;
}

export const DEN = { x: -0.35, z: 0.15 };
export const SHELF_Z = -2.15;
export const TOP_Y = 0.74;
export const TABLE_R = 1.025;
export const CEIL_Y = 2.68;
export const SHADE_Y = 2.22;

// Against the empty −X side wall; not parked by the table.
export const CHEST = { x: -2.30, z: 1.05 };

export const SHELF_Y1 = 1.22;
export const SHELF_Y0 = 0.78;
export const SHELF_THICK = 0.04;
export const SHELF_TOP = SHELF_Y1 + SHELF_THICK / 2;

export const SLOTS = {
    deck: { x: -1.35, y: SHELF_Y1 },
    cube: { x: -0.55, y: SHELF_Y1 },
    // MegaDreifach's megaminx A; B, C and its deck wait in the chest.
    drei: { x: -0.04, y: SHELF_Y1 },
};

// Shared rAF step cap. 60fps is unchanged (~16ms). Software-GL and
// capture hitch cannot skip a beat-clock tween while the director
// and camera stay capped — that is what made gather look like a snap.
export const CLOCK_STEP_MS = 50;

export const TWEEN_MS = 1100;
export const FLY_MS = 1800;
export const LIFT_MS = 380;
// Shared lid + leave-prep beats. Borrow and home use the same
// hinge timing so enter and return stay on one clock.
export const LID_OPEN_MS = 520;
export const LID_CLOSE_MS = 560;
export const GATHER_MS = 680;
export const RESTOW_MS = 380;
// The cube's lift for face turns (TURN_LIFT, TURN_LIFT_MS, SETTLE_HOLD_MS)
// is in the animation library: demos/anim/cube/settings.js.
// Brief hub hold so a lift reads in the landing frame before the
// shared follow-cam starts chasing. Click/Escape still skip after LIFT_MS.
export const HOLD_MS = 760;
export const FOLLOW_HOLD_MS = 360; // position hold; look already eases onto the toys

// Standalone DoubleDeal table is ~17.4 units wide. Scale the live 4×13
// session onto the playroom felt. KNOWN EXCEPTION to the real-scale
// invariant: its cards (0.56 units) land 38 × 55 mm, not 63 × 88 (real
// scale, 0.1125, makes the two grids ~1.96 m wide on the 2.05 m table).
// Waiting on a layout decision. Enter lays these seats from the two
// physical decks after the short unbox packet — do not teleport a
// hidden pre-seated grid in.
export const DEAL_SCALE = 0.068;
