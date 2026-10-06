/**
 * Megaminx presentation data for the MegaDreifach demo: names, colours,
 * the cubing.js move letters and the face directions of the cubing.js
 * megaminx. No algorithm step lives here: the turns, reads and grips all
 * come from the generated `trace_hash`. minx.test.mjs checks every table
 * below against the generated face tables (neighbours, opposites, spin).
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
const SUITS = ["♣", "♥", "♠", "♦"];
const SUIT_NAMES = ["clubs", "hearts", "spades", "diamonds"];

/** Card id (SPEC §3: rank × 4 + suit, suits in CHaSeD order). */
export function cardRank(card) {
    return Math.floor(card / 4);
}

export function cardSuit(card) {
    return card % 4;
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

function dot(a, b) {
    return a[0] * b[0] + a[1] * b[1] + a[2] * b[2];
}

function cross(a, b) {
    return [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]];
}

function norm(a) {
    const l = Math.hypot(a[0], a[1], a[2]) || 1;
    return [a[0] / l, a[1] / l, a[2] / l];
}

/**
 * Rotation (row-major 3×3) that holds the puzzle with face `up` on top
 * and face `front` toward you: up's direction goes to +y, front's goes
 * into the y–z plane facing +z.
 */
export function gripMatrix(up, front) {
    const u = FACE_NORMAL[up];
    const f0 = FACE_NORMAL[front];
    const f = norm([f0[0] - dot(f0, u) * u[0], f0[1] - dot(f0, u) * u[1], f0[2] - dot(f0, u) * u[2]]);
    const s = cross(u, f);
    return [s, u, f];
}

/** Quaternion [x, y, z, w] of a row-major rotation matrix. */
export function matrixQuaternion(m) {
    const [[m00, m01, m02], [m10, m11, m12], [m20, m21, m22]] = m;
    const trace = m00 + m11 + m22;
    let x;
    let y;
    let z;
    let w;
    if (trace > 0) {
        const s = 0.5 / Math.sqrt(trace + 1);
        w = 0.25 / s;
        x = (m21 - m12) * s;
        y = (m02 - m20) * s;
        z = (m10 - m01) * s;
    } else if (m00 > m11 && m00 > m22) {
        const s = 2 * Math.sqrt(1 + m00 - m11 - m22);
        w = (m21 - m12) / s;
        x = 0.25 * s;
        y = (m01 + m10) / s;
        z = (m02 + m20) / s;
    } else if (m11 > m22) {
        const s = 2 * Math.sqrt(1 + m11 - m00 - m22);
        w = (m02 - m20) / s;
        x = (m01 + m10) / s;
        y = 0.25 * s;
        z = (m12 + m21) / s;
    } else {
        const s = 2 * Math.sqrt(1 + m22 - m00 - m11);
        w = (m10 - m01) / s;
        x = (m02 + m20) / s;
        y = (m12 + m21) / s;
        z = 0.25 * s;
    }
    return [x, y, z, w];
}

export function gripQuaternion(up, front) {
    return matrixQuaternion(gripMatrix(up, front));
}

/** A King's spin: k clicks about Up, each bringing the face on your left to the front. */
export function spinMatrix(clicks) {
    const a = (clicks * 2 * Math.PI) / 5;
    const c = Math.cos(a);
    const s = Math.sin(a);
    return [[c, 0, s], [0, 1, 0], [-s, 0, c]];
}

export function mulMatrix(a, b) {
    return a.map((row) => [0, 1, 2].map((j) => row[0] * b[0][j] + row[1] * b[1][j] + row[2] * b[2][j]));
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
