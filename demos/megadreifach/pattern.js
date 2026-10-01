/**
 * Show a generated MegaDreifach Position on a cubing.js megaminx without
 * a move list: the fast-forward settles A on the real final h (and B on
 * h⁻¹), whose shortest known word is far too long to play.
 *
 * Nothing here knows the puzzle's piece numbering by heart. The bridge is
 * worked out from two sources that already agree turn for turn in the
 * show: the generated face turns (one +1 click of each face, from the
 * worker) and cubing.js's own transformation for the same move
 * (`turnMove`). A piece is named by the faces whose turns move it (three
 * for a corner, two for an edge); orientation offsets are solved from the
 * twelve turns and every turn is then checked. The generated Position
 * and cubing.js compose the same way (state, then turn), so a Position
 * maps piece by piece.
 */
import { FACE_MOVE, turnMove } from "./minx.js";

const ORBITS = [
    { name: "CORNERS", perm: "cp", ori: "co", n: 20, mod: 3, faces: 3 },
    { name: "EDGES", perm: "ep", ori: "eo", n: 30, mod: 2, faces: 2 },
];

function mod(a, m) {
    return ((a % m) + m) % m;
}

function signature(moved, n) {
    // moved[f][i]: does face f's turn move piece i? → sorted face list per piece.
    const out = [];
    for (let i = 0; i < n; i++) {
        const faces = [];
        for (let f = 0; f < moved.length; f++) if (moved[f][i]) faces.push(f);
        out.push(faces.join(","));
    }
    return out;
}

function solveOrbit(orbit, faceTurns, moveData, k) {
    const { name, perm, ori, n, mod: m } = orbit;
    const sudoSig = signature(faceTurns.map((t) => t[perm].map((v, i) => v !== i)), n);
    const cubeSig = signature(moveData.map((t) => t[name].permutation.map((v, i) => v !== i)), n);
    const sigma = sudoSig.map((sig) => cubeSig.indexOf(sig));
    if (sigma.some((i) => i < 0) || new Set(sigma).size !== n) return null;
    if (sudoSig.some((sig) => sig.split(",").length !== orbit.faces)) return null;
    // u[s]: per-slot orientation offset, so that for every turn t and slot s
    // cube.ori[σ(s)] = k·t.ori[s] + u[s] − u[t.perm[s]] (mod m).
    const u = new Array(n).fill(null);
    u[0] = 0;
    const queue = [0];
    while (queue.length) {
        const s = queue.shift();
        for (let f = 0; f < faceTurns.length; f++) {
            const t = faceTurns[f];
            const c = moveData[f][name];
            const from = t[perm][s];
            // u[from] = k·t.ori[s] + u[s] − cube.ori[σ(s)]
            const want = mod(k * t[ori][s] + u[s] - c.orientationDelta[sigma[s]], m);
            if (u[from] === null) {
                u[from] = want;
                queue.push(from);
            }
            // and backwards: the slot whose piece comes from s
            const to = t[perm].indexOf(s);
            const back = mod(c.orientationDelta[sigma[to]] - k * t[ori][to] + u[s], m);
            if (u[to] === null) {
                u[to] = back;
                queue.push(to);
            }
        }
    }
    if (u.some((v) => v === null)) return null;
    return { name, perm, ori, n, mod: m, sigma, u, k };
}

function mapOrbit(o, pos) {
    const permutation = new Array(o.n);
    const orientationDelta = new Array(o.n);
    for (let s = 0; s < o.n; s++) {
        const from = pos[o.perm][s];
        permutation[o.sigma[s]] = o.sigma[from];
        orientationDelta[o.sigma[s]] = mod(o.k * pos[o.ori][s] + o.u[s] - o.u[from], o.mod);
    }
    return { permutation, orientationDelta };
}

function sameOrbit(a, b) {
    return a.permutation.every((v, i) => v === b.permutation[i])
        && a.orientationDelta.every((v, i) => v === b.orientationDelta[i]);
}

/**
 * @param faceTurns  12 generated Positions (plain numbers): face f turned +1 click from solved.
 * @param moveData   12 cubing.js transformationData objects for turnMove(f, 1).
 * @returns {(pos) => transformationData}  CORNERS and EDGES from the Position, CENTERS solved.
 */
export function positionBridge(faceTurns, moveData) {
    if (faceTurns.length !== FACE_MOVE.length || moveData.length !== FACE_MOVE.length) {
        throw new Error("need one turn per face");
    }
    const orbits = ORBITS.map((orbit) => {
        for (const k of orbit.mod === 3 ? [1, 2] : [1]) {
            const solved = solveOrbit(orbit, faceTurns, moveData, k);
            if (!solved) continue;
            if (faceTurns.every((t, f) => sameOrbit(mapOrbit(solved, t), moveData[f][orbit.name]))) return solved;
        }
        throw new Error(`no consistent ${orbit.name} bridge between the generated turns and cubing.js`);
    });
    const centers = moveData[0].CENTERS;
    const solvedCenters = centers
        ? { permutation: centers.permutation.map((_, i) => i), orientationDelta: centers.permutation.map(() => 0) }
        : null;
    return function toTransformationData(pos) {
        const out = {};
        for (const o of orbits) out[o.name] = mapOrbit(o, pos);
        if (solvedCenters) out.CENTERS = { permutation: solvedCenters.permutation.slice(), orientationDelta: solvedCenters.orientationDelta.slice() };
        return out;
    };
}

/** The cubing.js moves the bridge is built from: one +1 click per sudo face. */
export function bridgeMoves() {
    return FACE_MOVE.map((_, f) => turnMove(f, 1));
}

const bridges = new WeakMap();

/**
 * Bridge for one TwistyPlayer's megaminx: Position → KTransformation (or
 * null for solved). Built once per kpuzzle and checked on all 12 turns.
 */
export async function playerBridge(player, faceTurns) {
    const kpuzzle = await player.experimentalModel.kpuzzle.get();
    let toData = bridges.get(kpuzzle);
    if (!toData) {
        const moveData = bridgeMoves().map((move) => kpuzzle.algToTransformation(move).transformationData);
        toData = positionBridge(faceTurns, moveData);
        bridges.set(kpuzzle, toData);
    }
    const KTransformation = kpuzzle.identityTransformation().constructor;
    return (pos) => (pos ? new KTransformation(kpuzzle, toData(pos)) : null);
}

/**
 * Put a generated Position (null = solved) on the player as its setup
 * state. The caller empties the alg first, so the player shows exactly
 * that position; null goes back to the plain alg timeline.
 */
export async function setSetupPosition(player, pos, faceTurns) {
    const toTransformation = pos ? await playerBridge(player, faceTurns) : () => null;
    player.experimentalModel.setupTransformation.set(toTransformation(pos));
}
