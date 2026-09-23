// Physical cube for the demo: face turns, facelets, and the short solve.
// The hash rules live in scramble.sudo. This file only turns faces.

const SOLVED_FACELETS = "WWWWWWWWWRRRRRRRRRGGGGGGGGGYYYYYYYYYOOOOOOOOOBBBBBBBBB";

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

function rot(face, x, y, z) {
    if (face === 0 || face === 1) return [z, y, -x];
    if (face === 2) return [x, z, -y];
    if (face === 3) return [x, -z, y];
    if (face === 4) return [y, -x, z];
    return [-y, x, z];
}

function axisName(x, y, z) {
    if (x === 1) return "xp";
    if (x === -1) return "xn";
    if (y === 1) return "yp";
    if (y === -1) return "yn";
    if (z === 1) return "zp";
    return "zn";
}

function onFace(face, x, y, z) {
    if (face === 0) return y === 1;
    if (face === 1) return y === -1;
    if (face === 2) return x === 1;
    if (face === 3) return x === -1;
    if (face === 4) return z === 1;
    return z === -1;
}

function solvedCube() {
    const cube = [];
    for (let x = -1; x <= 1; x++) {
        for (let y = -1; y <= 1; y++) {
            for (let z = -1; z <= 1; z++) {
                if (x === 0 && y === 0 && z === 0) continue;
                cube.push({
                    x, y, z,
                    xp: x === 1 ? "R" : "",
                    xn: x === -1 ? "O" : "",
                    yp: y === 1 ? "W" : "",
                    yn: y === -1 ? "Y" : "",
                    zp: z === 1 ? "G" : "",
                    zn: z === -1 ? "B" : "",
                });
            }
        }
    }
    return cube;
}

function turnCubie(c, face) {
    const [nx, ny, nz] = rot(face, c.x, c.y, c.z);
    const next = { x: nx, y: ny, z: nz, xp: "", xn: "", yp: "", yn: "", zp: "", zn: "" };
    for (const [ax, ay, az, key] of [[1, 0, 0, "xp"], [-1, 0, 0, "xn"], [0, 1, 0, "yp"], [0, -1, 0, "yn"], [0, 0, 1, "zp"], [0, 0, -1, "zn"]]) {
        if (!c[key]) continue;
        const [rx, ry, rz] = rot(face, ax, ay, az);
        next[axisName(rx, ry, rz)] = c[key];
    }
    return next;
}

function quarter(cube, face) {
    return cube.map((c) => onFace(face, c.x, c.y, c.z) ? turnCubie(c, face) : { ...c });
}

function faceletsOf(cube) {
    let out = "";
    for (const [x, y, z, axis] of SPOTS) {
        const cubie = cube.find((c) => c.x === x && c.y === y && c.z === z);
        out += cubie[axis];
    }
    return out;
}

function cubeFromFacelets(text) {
    const cube = solvedCube().map((c) => ({ x: c.x, y: c.y, z: c.z, xp: "", xn: "", yp: "", yn: "", zp: "", zn: "" }));
    SPOTS.forEach(([x, y, z, axis], i) => {
        const cubie = cube.find((c) => c.x === x && c.y === y && c.z === z);
        cubie[axis] = text[i];
    });
    return cube;
}

export function parseMove(move) {
    const face = FACE_INDEX[move[0]];
    const turns = move.endsWith("2") ? 2 : move.endsWith("'") ? 3 : 1;
    return { face, turns };
}

// One quarter of this face, as a right-handed radians step about a world axis.
export function quarterSpin(face) {
    if (face === 0 || face === 1) return { axis: "y", sign: 1 };
    if (face === 2) return { axis: "x", sign: 1 };
    if (face === 3) return { axis: "x", sign: -1 };
    if (face === 4) return { axis: "z", sign: -1 };
    return { axis: "z", sign: 1 };
}

export function applyMove(facelets, move) {
    const { face, turns } = parseMove(move);
    let cube = cubeFromFacelets(facelets);
    for (let i = 0; i < turns; i++) cube = quarter(cube, face);
    return faceletsOf(cube);
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
