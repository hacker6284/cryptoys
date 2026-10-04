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
// Standing deck box in world.makeDeckBox (bw × bh × bd).
export const DECK_H = REAL_SIZES.deckBox.h;

// Fallback only, when a toy cannot be measured: seatOnSurface seats from
// the live post-scale shape (a megaminx's own height, not the cube's).
export function toyHalfHeight(name) {
    return name === "deck" || name === "deck2" ? DECK_H / 2 : CUBE / 2;
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
// is in the animation library: demos/anim/scramble-turn/settings.js.
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
