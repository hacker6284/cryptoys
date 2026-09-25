import { SOLVED_FACELETS } from "../scramble/cube.js";

/**
 * Map Scramble session steps onto a cubing.js alg.
 *
 * Face turns stay WCA (U/R/F/…). Rule B / seat are whole-cube rotations
 * (`x`/`y`/`z`) so TwistyPlayer can own interpolation. Centers only —
 * face turns never move them.
 */

export const FACE_CENTERS = { U: 4, R: 13, F: 22, D: 31, L: 40, B: 49 };

/** Stickers on `oldFace` move to dest[move][oldFace]. */
export const ROTATION_DEST = {
    x: { U: "B", B: "D", D: "F", F: "U", R: "R", L: "L" },
    "x'": { U: "F", F: "D", D: "B", B: "U", R: "R", L: "L" },
    x2: { U: "D", D: "U", F: "B", B: "F", R: "R", L: "L" },
    y: { F: "R", R: "B", B: "L", L: "F", U: "U", D: "D" },
    "y'": { F: "L", L: "B", B: "R", R: "F", U: "U", D: "D" },
    y2: { F: "B", B: "F", R: "L", L: "R", U: "U", D: "D" },
    z: { U: "R", R: "D", D: "L", L: "U", F: "F", B: "B" },
    "z'": { U: "L", L: "D", D: "R", R: "U", F: "F", B: "B" },
    z2: { U: "D", D: "U", R: "L", L: "R", F: "F", B: "B" },
};

const TO_U = { U: "", D: "x2", F: "x", B: "x'", R: "z'", L: "z" };
const TO_F = { F: "", R: "y'", B: "y2", L: "y" };

export function colorOnFace(facelets, face) {
    return facelets[FACE_CENTERS[face]];
}

export function faceWithColor(facelets, color) {
    for (const face of Object.keys(FACE_CENTERS)) {
        if (colorOnFace(facelets, face) === color) return face;
    }
    return null;
}

export function applyRotationToCenters(facelets, move) {
    const dest = ROTATION_DEST[move];
    if (!dest) return facelets;
    const next = facelets.split("");
    const saved = {};
    for (const face of Object.keys(FACE_CENTERS)) saved[face] = colorOnFace(facelets, face);
    for (const face of Object.keys(FACE_CENTERS)) {
        next[FACE_CENTERS[dest[face]]] = saved[face];
    }
    return next.join("");
}

/**
 * Whole-cube rotations that seat `up` on U and `front` on F.
 * Identity when the centers are already there.
 */
export function reorientMoves(facelets, up, front) {
    const fromUp = faceWithColor(facelets, up);
    const first = TO_U[fromUp] || "";
    const after = first ? applyRotationToCenters(facelets, first) : facelets;
    const fromFront = faceWithColor(after, front);
    const second = TO_F[fromFront] || "";
    return [first, second].filter(Boolean);
}

/**
 * @param {Array<{ kind: string, move?: string, up?: string, front?: string, facelets: string }>} trace
 * @returns {{ alg: string, units: { text: string, stepIndex: number }[], ranges: { from: number, to: number }[] }}
 */
export function mapTraceToAlg(trace, startFacelets = SOLVED_FACELETS) {
    const units = [];
    const ranges = [];
    let facelets = startFacelets;
    for (let i = 0; i < trace.length; i++) {
        const step = trace[i];
        const from = units.length;
        if (step.kind === "move" || step.kind === "closer") {
            if (step.move) units.push({ text: step.move, stepIndex: i });
        } else if (step.kind === "ruleB") {
            for (const text of reorientMoves(facelets, step.up, step.front)) {
                units.push({ text, stepIndex: i });
            }
        } else if (step.kind === "canonicalize") {
            for (const text of reorientMoves(facelets, "W", "G")) {
                units.push({ text, stepIndex: i });
            }
        }
        ranges.push({ from, to: units.length });
        if (step.facelets) facelets = step.facelets;
    }
    return {
        alg: units.map((unit) => unit.text).join(" "),
        units,
        ranges,
    };
}

export function prefixAlg(mapped, cursor) {
    if (!mapped || cursor < 0) return "";
    const end = mapped.ranges[cursor]?.to ?? 0;
    return mapped.units.slice(0, end).map((unit) => unit.text).join(" ");
}
