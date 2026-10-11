/**
 * Megaminx presentation data for the MegaDreifach demo: names, colours,
 * the cubing.js move letters and the face directions of the cubing.js
 * megaminx. No algorithm step lives here: the turns all come from the
 * generated `trace_hash`. minx.test.mjs checks every table below against
 * the generated face tables (neighbours, opposites).
 */

// Sudo face id (= centre colour id, SPEC §4) → cubing.js megaminx move
// letter. Checked against the generated turn tables (the face ids and
// cubing.js faces agree on every corner and edge).
export const FACE_MOVE = ["U", "F", "L", "BL", "BR", "R", "FR", "FL", "DL", "B", "DR", "D"];

// Colour names: the community-standard 12-colour megaminx scheme. White
// is opposite grey; around white, clockwise: red, green, purple, yellow,
// blue; each is opposite its light partner (red/orange, green/light
// green, purple/pink, yellow/pale yellow, blue/light blue). Source:
// Speedsolving.com Wiki, "Megaminx", Colour scheme
// (https://www.speedsolving.com/wiki/index.php/Megaminx), which matches
// Wikipedia, "Megaminx" (white bordered by yellow, dark blue, red, dark
// green and purple; opposite grey, beige, light blue, orange, light
// green, pink). cubing.js paints exactly this scheme (hex below, from
// its puzzle-geometry megaminx colours; FR/FL/DL/B/DR are its C/A/I/BF/E).
export const FACE_NAME = [
    "white",
    "green",
    "purple",
    "yellow",
    "blue",
    "red",
    "pale yellow",
    "light blue",
    "orange",
    "light green",
    "pink",
    "grey",
];

export const FACE_HEX = [
    "#ffffff",
    "#008800",
    "#8800dd",
    "#f4f400",
    "#0000ff",
    "#ff0000",
    "#e8d0a0",
    "#3399ff",
    "#ff8000",
    "#99ff00",
    "#ff66cc",
    "#888888",
];

const UP_Y = 1 / Math.sqrt(5);
const RING_R = 2 / Math.sqrt(5);

// Outward face directions of the cubing.js megaminx in its own frame
// (U up, F toward the viewer, x to the right). Upper ring at azimuth
// F 0°, L 72°, BL 144°, BR 216°, R 288° (from +z toward −x); lower ring
// FR −36°, FL 36°, DL 108°, B 180°, DR 252°.
const AZIMUTH = {
    F: [0, UP_Y], L: [72, UP_Y], BL: [144, UP_Y], BR: [216, UP_Y], R: [288, UP_Y],
    FR: [-36, -UP_Y], FL: [36, -UP_Y], DL: [108, -UP_Y], B: [180, -UP_Y], DR: [252, -UP_Y],
};

function direction(move) {
    if (move === "U") return [0, 1, 0];
    if (move === "D") return [0, -1, 0];
    const [deg, y] = AZIMUTH[move];
    const a = (deg * Math.PI) / 180;
    return [-Math.sin(a) * RING_R, y, Math.cos(a) * RING_R];
}

export const FACE_NORMAL = FACE_MOVE.map(direction);

const PIPS = ["A", "2", "3", "4", "5", "6", "7", "8", "9", "10", "J", "Q", "K"];

// v3 (SPEC v3 §4): colour r carries rank r, so face id f is also the rank
// A, 2, …, 10, J, Q (no centre is a King).
export const RANK_NAME = PIPS.slice(0, 12);
const SUITS = ["♣", "♥", "♠", "♦"];
const SUIT_NAMES = ["clubs", "hearts", "spades", "diamonds"];

/** Card id (SPEC §3: rank × 4 + suit, suits in CHaSeD order). */
export function cardRank(card) {
    return Math.floor(card / 4);
}

export function cardSuit(card) {
    return card % 4;
}

/** SPEC §3: the suit amount k = suit + 1 (clubs 1, hearts 2, spades 3, diamonds 4). */
export function suitAmount(card) {
    return cardSuit(card) + 1;
}

export function cardLabel(card) {
    return `${PIPS[cardRank(card)]}${SUITS[cardSuit(card)]}`;
}

export function suitName(card) {
    return SUIT_NAMES[cardSuit(card)];
}

/** Index into doubledeal/table.js loadCardTextures().faces (suit-major). */
export function cardFaceIndex(card) {
    return cardSuit(card) * 13 + cardRank(card);
}

/** cubing.js move for a literal turn: +3 → "L3", −2 → "U2'", +1 → "F". */
export function turnMove(face, clicks) {
    const letter = FACE_MOVE[face];
    const n = Math.abs(clicks);
    if (!letter || n < 1 || n > 4) throw new RangeError(`bad turn ${face} ${clicks}`);
    return `${letter}${n === 1 ? "" : n}${clicks < 0 ? "'" : ""}`;
}

export function turnText(face, clicks) {
    return `${FACE_NAME[face]} ${clicks > 0 ? "+" : "−"}${Math.abs(clicks)}`;
}

function norm(a) {
    const l = Math.hypot(a[0], a[1], a[2]) || 1;
    return [a[0] / l, a[1] / l, a[2] / l];
}

/** Direction of a piece: the sum of its faces' directions (puzzle frame). */
export function pieceDirection(faces) {
    const sum = [0, 0, 0];
    for (const face of faces) {
        const n = FACE_NORMAL[face];
        sum[0] += n[0];
        sum[1] += n[1];
        sum[2] += n[2];
    }
    return norm(sum);
}
