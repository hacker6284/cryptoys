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
