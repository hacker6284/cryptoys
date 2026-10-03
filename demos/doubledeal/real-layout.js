// Real-size DoubleDeal table layout (demos/README.md "Real sizes"): poker
// cards 63×88 mm, 0.3 mm thick, the two 52-card grids side by side as
// 8 columns × 13 rows (each deck 4 columns × 13 rows: the algorithm's 4
// rows run across, its 13 columns run away from the player) with even
// 4 mm gaps, a 40 mm gutter between the message and key grids, and the
// hand packet a neat stack in front of the message grid, 80 mm clear of
// it, top card first.
//
// Positions are in the standalone DoubleDeal units (createCardTable
// works in them: CARD_W 0.56 = 63 mm, so 1 unit = 112.5 mm); the stage
// scales the group by UNIT_M onto the felt. Only the microdemos that have
// moved into the library use it (demos/anim/doubledeal-*); the playroom
// DoubleDeal keeps doubledeal/layout.js until every move has moved.
//
// The card art is 338×489 px (1.447); a 63×88 mm card is 1.397. The stage
// loads it redrawn at artAspect (table.js loadCardTextures), so faces and
// backs map onto the card undistorted; the old layout used the art's
// aspect for the card instead.
import { CARD_W, edgeGap } from "./layout.js";

export const UNIT_M = 0.063 / CARD_W; // m per table unit
const mm = (v) => v / 1000 / UNIT_M;

const W = CARD_W; // 63 mm
const D = mm(88);
const T = mm(0.3);
const GAP = mm(4);
const GUTTER = mm(40);
const PILE_GAP = mm(80);
const COL = W + GAP;
const ROW = D + GAP;
const HALF_W = 1.5 * COL + W / 2;
const HALF_D = 6 * ROW + D / 2;
const SIDE_X = { message: -(HALF_W + GUTTER / 2), key: HALF_W + GUTTER / 2 };
const PILE_Z = HALF_D + PILE_GAP + D / 2;

/** Seat of algorithm (row 0–3, col 0–12) on `side` ("message" | "key"). */
function cell(row, col, side) {
    return { x: SIDE_X[side] + (row - 1.5) * COL, z: (col - 6) * ROW };
}

/**
 * Packet card `index` of `count` in the pile in front of `side`'s grid:
 * one neat stack, index 0 on top (dealt first).
 */
function pile(side, index, count) {
    const x = side === "hand" ? SIDE_X.message : SIDE_X.key;
    return { x, y: (count - 1 - index) * T + T / 2, z: PILE_Z };
}

function box(at) {
    return { minX: at.x - W / 2, maxX: at.x + W / 2, minZ: at.z - D / 2, maxZ: at.z + D / 2 };
}

/** Every seat box per side, and the hand pile's box. */
export function realBoxes() {
    const seats = { message: [], key: [] };
    for (const side of ["message", "key"]) {
        for (let row = 0; row < 4; row++) for (let col = 0; col < 13; col++) seats[side].push(box(cell(row, col, side)));
    }
    return { seats, pile: box(pile("hand", 0, 52)) };
}

/** Smallest edge gaps (units): within a grid, between the grids, pile to grid. */
function restingClearance() {
    const { seats, pile: p } = realBoxes();
    let within = Infinity;
    let between = Infinity;
    let pileGap = Infinity;
    for (const side of ["message", "key"]) {
        const deck = seats[side];
        for (let i = 0; i < deck.length; i++) {
            pileGap = Math.min(pileGap, edgeGap(p, deck[i]));
            for (let j = i + 1; j < deck.length; j++) within = Math.min(within, edgeGap(deck[i], deck[j]));
        }
    }
    for (const a of seats.message) for (const b of seats.key) between = Math.min(between, edgeGap(a, b));
    return { within, between, pile: pileGap };
}

/** createCardTable({ layout: REAL_LAYOUT }); stageCardTable scales by `scale`. */
export const REAL_LAYOUT = {
    name: "real",
    scale: UNIT_M,
    cardW: W,
    cardD: D,
    cardT: T,
    artAspect: 63 / 88, // loadCardTextures(…, { aspect }): the art undistorted on the card
    seatY: T / 2, // card centre: its bottom on the group's plane
    liftM: 0.0005, // m: the card bottoms above the felt top (the stage's group height)
    cell,
    pile,
    restingClearance,
    span: { minX: SIDE_X.message - HALF_W, maxX: SIDE_X.key + HALF_W, minZ: -HALF_D, maxZ: PILE_Z + D / 2 },
};

export const REAL_MM = { card: [63, 88, 0.3], gap: 4, gutter: 40, pileGap: 80, grid: [8, 13] };
