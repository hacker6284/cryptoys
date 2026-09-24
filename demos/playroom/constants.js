// 1:1 playroom measures. Poker card 63×88 mm; cube 57 mm; table ~2 m Ø.
// Demo-layer presentation only.

export const ASSET_BASE = new URL("./assets/", import.meta.url);

export const CARD_W = 0.063;
export const CARD_D = 0.088;
export const CUBE = 0.057;

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

export const SLOTS = {
    deck: { x: -1.35, y: SHELF_Y1 },
    cube: { x: -0.55, y: SHELF_Y1 },
};

export const TWEEN_MS = 1100;
export const FLY_MS = 1400;
