// 1:1 playroom measures. Poker card 63×88 mm; classic 3×3 ~57 mm; table ~2 m Ø.
// Demo-layer presentation only.

export const ASSET_BASE = new URL("./assets/", import.meta.url);

export const CARD_W = 0.063;
export const CARD_D = 0.088;
// Presentation edge for the playroom Twisty cube. Locked for the
// whole scene: cubing.js may spawn at native size, then a later
// layout / world-AABB / 1/3 puzzle.scale must not crush it. 57 mm
// is real-life 3×3 scale (120 mm was ~2× life size); seatOnSurface
// plants the live post-scale AABB.
export const CUBE = 0.057;
// Standing deck box in world.makeDeckBox (bw × bh × bd).
export const DECK_H = 0.092;

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

// Shared rAF step cap (director / beat-clock / capture harness).
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
// Pick the cube up this far for face turns so layers clear the felt/rim.
export const TURN_LIFT = 0.14;
export const TURN_LIFT_MS = 320;
export const SETTLE_HOLD_MS = 90;
// Brief hub hold so a lift reads in the landing frame before the
// shared follow-cam starts chasing. Click/Escape still skip after LIFT_MS.
export const HOLD_MS = 760;
export const FOLLOW_HOLD_MS = 360;

// Standalone DoubleDeal table is ~17.4 units wide. Scale the live 4×13
// session onto the playroom felt. Enter lays these seats from the two
// physical decks after the short unbox packet — do not teleport a
// hidden pre-seated grid in.
export const DEAL_SCALE = 0.068;
