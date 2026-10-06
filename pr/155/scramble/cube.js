// Demo cube: sticker spots for drawing, move names, and the short solve.
// Face turns and the solved pose come from the generated scramble.mjs (scramble.sudo).
import { apply_move, solved_facelets } from "./generated/scramble.mjs";

const SOLVED_FACELETS = solved_facelets();

const SPOTS = [
    // U
    [-1, 1, -1, "yp"], [0, 1, -1, "yp"], [1, 1, -1, "yp"],
    [-1, 1, 0, "yp"], [0, 1, 0, "yp"], [1, 1, 0, "yp"],
    [-1, 1, 1, "yp"], [0, 1, 1, "yp"], [1, 1, 1, "yp"],
    // R
    [1, 1, 1, "xp"], [1, 1, 0, "xp"], [1, 1, -1, "xp"],
    [1, 0, 1, "xp"], [1, 0, 0, "xp"], [1, 0, -1, "xp"],
    [1, -1, 1, "xp"], [1, -1, 0, "xp"], [1, -1, -1, "xp"],
    // F
    [-1, 1, 1, "zp"], [0, 1, 1, "zp"], [1, 1, 1, "zp"],
    [-1, 0, 1, "zp"], [0, 0, 1, "zp"], [1, 0, 1, "zp"],
    [-1, -1, 1, "zp"], [0, -1, 1, "zp"], [1, -1, 1, "zp"],
    // D
    [-1, -1, 1, "yn"], [0, -1, 1, "yn"], [1, -1, 1, "yn"],
    [-1, -1, 0, "yn"], [0, -1, 0, "yn"], [1, -1, 0, "yn"],
    [-1, -1, -1, "yn"], [0, -1, -1, "yn"], [1, -1, -1, "yn"],
    // L
    [-1, 1, -1, "xn"], [-1, 1, 0, "xn"], [-1, 1, 1, "xn"],
    [-1, 0, -1, "xn"], [-1, 0, 0, "xn"], [-1, 0, 1, "xn"],
    [-1, -1, -1, "xn"], [-1, -1, 0, "xn"], [-1, -1, 1, "xn"],
    // B
    [1, 1, -1, "zn"], [0, 1, -1, "zn"], [-1, 1, -1, "zn"],
    [1, 0, -1, "zn"], [0, 0, -1, "zn"], [-1, 0, -1, "zn"],
    [1, -1, -1, "zn"], [0, -1, -1, "zn"], [-1, -1, -1, "zn"],
];

const MOVES = ["U", "U'", "U2", "D", "D'", "D2", "L", "L'", "L2", "R", "R'", "R2", "F", "F'", "F2", "B", "B'", "B2"];

const FACE_INDEX = { U: 0, D: 1, R: 2, L: 3, F: 4, B: 5 };

export function parseMove(move) {
    const face = FACE_INDEX[move[0]];
    const turns = move.endsWith("2") ? 2 : move.endsWith("'") ? 3 : 1;
    return { face, turns };
}

// One quarter of this face, in Three.js's right-handed rotation.
// +90° about +Y is the U/D map. +90° about +X is the L map, so R is the opposite sign.
// +90° about +Z is the B map, so F is the opposite sign.
export function quarterSpin(face) {
    if (face === 0 || face === 1) return { axis: "y", sign: 1 };
    if (face === 2) return { axis: "x", sign: -1 };
    if (face === 3) return { axis: "x", sign: 1 };
    if (face === 4) return { axis: "z", sign: -1 };
    return { axis: "z", sign: 1 };
}

// apply_move only moves letters between facelets, so each move's map is read once,
// from these 54 distinct letters, and reused: shortSolve makes about 65,000 moves.
export const LETTERS = "0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQR";
const FROM = new Map();

export function applyMove(facelets, move) {
    if (!FROM.has(move)) FROM.set(move, Array.from(apply_move(LETTERS, move), (ch) => LETTERS.indexOf(ch)));
    return FROM.get(move).map((i) => facelets[i]).join("");
}

export function isSolved(facelets) {
    return facelets === SOLVED_FACELETS;
}

export function shortSolve(facelets, depth = 4) {
    if (isSolved(facelets)) return [];
    const seen = new Set([facelets]);
    const queue = [{ facelets, path: [] }];
    for (let i = 0; i < queue.length; i++) {
        const item = queue[i];
        if (item.path.length >= depth) continue;
        const prev = item.path.length ? item.path[item.path.length - 1][0] : "";
        for (const move of MOVES) {
            if (move[0] === prev) continue;
            const next = applyMove(item.facelets, move);
            if (seen.has(next)) continue;
            const path = item.path.concat(move);
            if (isSolved(next)) return path;
            seen.add(next);
            queue.push({ facelets: next, path });
        }
    }
    return null;
}

export function toCubejs(facelets) {
    const map = { W: "U", R: "R", G: "F", Y: "D", O: "L", B: "B" };
    return facelets.replace(/[WRGYOB]/g, (ch) => map[ch]);
}

export function flipU(move) {
    if (move === "U") return "U'";
    if (move === "U'") return "U";
    return move;
}

export { SOLVED_FACELETS, SPOTS };
