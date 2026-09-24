// Table geometry for the two resting decks. The gap is part of the
// construction: every card box is checked against every other card box
// by tools and again from the meshes after they are placed.

export const CARD_W = 0.56;
export const CARD_D = CARD_W * (489 / 338);
const CARD_GAP = 0.07;
export const COL_PITCH = CARD_W + CARD_GAP;
export const ROW_PITCH = CARD_D + CARD_GAP;
// Clear space between the facing edges of the two 4×13 grids.
export const GUTTER = 1.15;

const HALF_W = 6 * COL_PITCH + CARD_W / 2;
const HALF_D = 1.5 * ROW_PITCH + CARD_D / 2;

export const MESSAGE_X = -(HALF_W + GUTTER / 2);
export const KEY_X = HALF_W + GUTTER / 2;

export function cell(row, col, centerX) {
    return {
        x: centerX + (col - 6) * COL_PITCH,
        z: (row - 1.5) * ROW_PITCH,
    };
}

export function cardBox(row, col, centerX) {
    const at = cell(row, col, centerX);
    return {
        minX: at.x - CARD_W / 2,
        maxX: at.x + CARD_W / 2,
        minZ: at.z - CARD_D / 2,
        maxZ: at.z + CARD_D / 2,
    };
}

export function edgeGap(a, b) {
    const dx = Math.max(a.minX - b.maxX, b.minX - a.maxX);
    const dz = Math.max(a.minZ - b.maxZ, b.minZ - a.maxZ);
    if (dx < 0 && dz < 0) return Math.max(dx, dz);
    if (dx < 0) return dz;
    if (dz < 0) return dx;
    return Math.hypot(dx, dz);
}

function boxesFor(centerX) {
    const boxes = [];
    for (let row = 0; row < 4; row++) {
        for (let col = 0; col < 13; col++) boxes.push(cardBox(row, col, centerX));
    }
    return boxes;
}

export function restingClearance() {
    const message = boxesFor(MESSAGE_X);
    const key = boxesFor(KEY_X);
    let within = Infinity;
    for (const deck of [message, key]) {
        for (let i = 0; i < deck.length; i++) {
            for (let j = i + 1; j < deck.length; j++) within = Math.min(within, edgeGap(deck[i], deck[j]));
        }
    }
    let between = Infinity;
    for (const a of message) {
        for (const b of key) between = Math.min(between, edgeGap(a, b));
    }
    return { within, between };
}
