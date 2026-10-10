/**
 * BS step expander (sanctioned by Zachary, 2026-10-10: "a separate routine
 * which can create a fast animation from one summary step").
 *
 * The generated trace (bs.sudo trace_exchange) gives one summary per board
 * step: each hole of BUILD with the dice it read, and each multiplication,
 * start, tidy, clear and shot of the exchange with the player's X, Y and C
 * after it. This module turns one summary into the peg moves a person makes
 * for it, by the board recipes of SPEC §3 (B1 drop, B2 lay, B3 multiply,
 * B4 pay the toll, B5 tidy, §3.1 call the shots) and §4.2 (BUILD), so the
 * view can play them one by one when stepping. It is a view helper: the
 * show's registers come from the trace, and expand.test.mjs replays every
 * expansion from summary i and checks it lands exactly on summary i + 1, on
 * every vector and every step.
 *
 * A workspace is { x, y, c, s }: registers of n trits (hole 0 first;
 * 0 empty, 1 white, 2 red) and the product strip s of 2n + 2 holes (§6).
 *
 * Moves:
 *   { t: "set", r, h, from, to, why }   one hole changes: a peg goes in from
 *       the well, is swapped for the other colour, or comes out. why: "drop"
 *       (B1), "carry" (B1's flick), "lift" (B4's lift or B3's "lift the
 *       register's pegs"), "copy" (B5 step 1), "spill" (B5), "clear",
 *       "shot" (§3.1), "start" (B7 step 3).
 *   { t: "slide", from: { r, h }, to: { r, h }, colour }   a peg moves from
 *       one hole to another (B3 step 3 / B5: slide the answer in).
 * BUILD moves (one key grid):
 *   { t: "d10", die, face }   a row-cup die thrown (die 0-4, rainbow order);
 *       zero faces are thrown again.
 *   { t: "d12", face }  { t: "d6", face, for: "grow" | "kind" }
 *   { t: "ship", kind, down, row, col, bow_last, len }   the piece lying at
 *       the cursor hole now (laid, or swapped for a longer one).
 *   { t: "read", die, face }   the pair's die read for this hole (keypad).
 *   { t: "peg", hole, colour, inShip }
 */

export const OP = Object.freeze({
    start: 1, square: 2, cube: 3, hit: 4, tidy: 5, clear: 6, shot: 7, check: 8, checkTidy: 9,
});

export const OP_NAME = Object.freeze(Object.fromEntries(Object.entries(OP).map(([k, v]) => [v, k])));

const LIFTS_PER_HOLE = 4;

/** An empty workspace for n-trit registers (strip of 2n + 2 holes). */
export function emptyWorkspace(n) {
    return { x: new Array(n).fill(0), y: new Array(n).fill(0), c: new Array(n).fill(0), s: new Array(2 * n + 2).fill(0) };
}

export function cloneWorkspace(w) {
    return { x: w.x.slice(), y: w.y.slice(), c: w.c.slice(), s: w.s.slice() };
}

// B1: drop a peg of `colour` (1 white, 2 red) into hole `hole` of strip `r`,
// within its first `limit` holes, odometer carry included.
function drop(w, out, r, hole, colour, limit) {
    let clicks = colour;
    let why = "drop";
    for (let h = hole; h < limit; h++) {
        const from = w[r][h];
        const sum = from + clicks;
        const to = sum % 3;
        w[r][h] = to;
        out.push({ t: "set", r, h, from, to, why });
        if (sum < 3) return;
        clicks = 1;
        why = "carry";
    }
    throw new Error(`B1: a carry ran past hole ${limit - 1} of ${r}`);
}

// B2: lay a copy of `a` starting at hole `start`.
function lay(w, out, r, a, start, limit) {
    for (let j = 0; j < a.length; j++) if (a[j]) drop(w, out, r, start + j, a[j], limit);
}

function set(w, out, r, h, to, why) {
    const from = w[r][h];
    if (from === to) return;
    w[r][h] = to;
    out.push({ t: "set", r, h, from, to, why });
}

// B3 step 3 / B5: lift the register's pegs, then slide the strip's holes
// 0 .. n-1 into it.
function slideInto(w, out, dest, n) {
    for (let i = 0; i < n; i++) if (w[dest][i]) set(w, out, dest, i, 0, "lift");
    for (let i = 0; i < n; i++) {
        const colour = w.s[i];
        if (!colour) continue;
        w.s[i] = 0;
        w[dest][i] = colour;
        out.push({ t: "slide", from: { r: "s", h: i }, to: { r: dest, h: i }, colour });
    }
}

// B3 + B4: multiply a × b (nudged) in the strip, pay the toll, slide the answer into `dest`.
function multiply(w, out, field, a, b, nudge, dest) {
    const { n, toll } = field;
    const limit = 2 * n + nudge;
    if (w.s.some((t) => t)) throw new Error("B3: the strip must start clear");
    for (let i = 0; i < n; i++) {
        for (let k = 0; k < b[i]; k++) lay(w, out, "s", a, i + nudge, limit);
    }
    // B4: lift the highest peg at or beyond hole n, lay the toll n holes lower (twice if red).
    for (let h = limit - 1; h >= n; h--) {
        for (let lift = 0; lift < LIFTS_PER_HOLE; lift++) {
            const colour = w.s[h];
            if (!colour) break;
            set(w, out, "s", h, 0, "lift");
            for (let k = 0; k < colour; k++) lay(w, out, "s", toll, h - n, limit);
        }
        if (w.s[h]) throw new Error(`B4: hole ${h} still pegged`);
    }
    slideInto(w, out, dest, n);
}

// B5: tidy register `r` in place, through the strip.
function tidy(w, out, field, r) {
    const { n, toll } = field;
    if (w.s.some((t) => t)) throw new Error("B5: the strip must start clear");
    for (let i = 0; i < n; i++) if (w[r][i]) set(w, out, "s", i, w[r][i], "copy");
    lay(w, out, "s", toll, 0, n + 1);
    if (!w.s[n]) {
        for (let i = 0; i < n; i++) if (w.s[i]) set(w, out, "s", i, 0, "clear");
        return;
    }
    if (w.s[n] !== 1) throw new Error("B5: the spill is a lone white");
    set(w, out, "s", n, 0, "spill");
    slideInto(w, out, r, n);
}

/**
 * The peg moves of exchange step `step` (a trace step, plain numbers) on
 * the workspaces `ws` ([Alice, Bob]); applies them to ws[step.player] (and
 * reads the sender's X for a shot). field: { n, toll }. cellValue: the key
 * cell the step walks (trace.cells_*[step.cell]); shared: the step is in
 * the player's shared walk (B9 step 3). Returns the moves.
 */
export function expandStep(ws, step, field, { cellValue = 0, shared = false } = {}) {
    const w = ws[step.player];
    const out = [];
    const { n } = field;
    switch (step.op) {
    case OP.start:
        if (step.a.length) {
            multiply(w, out, field, step.a, step.b, step.nudge, "x");
        } else {
            // Public: a lone white at hole 1 (white cell) or 2 (red cell).
            // Shared, white cell: a copy of C. Either way the old X comes off first.
            for (let i = 0; i < n; i++) if (w.x[i]) set(w, out, "x", i, 0, "lift");
            if (shared) {
                for (let i = 0; i < n; i++) if (w.c[i]) set(w, out, "x", i, w.c[i], "start");
            } else {
                set(w, out, "x", cellValue, 1, "start");
            }
        }
        break;
    case OP.square:
        multiply(w, out, field, step.a, step.b, step.nudge, "y");
        break;
    case OP.cube:
    case OP.hit:
        multiply(w, out, field, step.a, step.b, step.nudge, "x");
        break;
    case OP.check:
        multiply(w, out, field, step.a, step.b, step.nudge, "c");
        break;
    case OP.tidy:
        tidy(w, out, field, "x");
        break;
    case OP.checkTidy:
        tidy(w, out, field, "c");
        break;
    case OP.clear:
        for (let i = 0; i < n; i++) if (w.y[i]) set(w, out, "y", i, 0, "clear");
        break;
    case OP.shot: {
        // §3.1: the sender answers from the called hole of their value (in their X);
        // a hit is a red peg, a miss a white one, a misfire nothing.
        const sender = ws[1 - step.player];
        const answer = sender.x[step.hole];
        if (answer) set(w, out, "y", step.hole, answer, "shot");
        break;
    }
    default:
        throw new Error(`unknown op ${step.op}`);
    }
    return out;
}

/** Apply moves to a workspace (no checks beyond `from`): for replaying in the view. */
export function applyMoves(w, moves) {
    for (const m of moves) {
        if (m.t === "set") {
            if (w[m.r][m.h] !== m.from) throw new Error(`move expects ${m.r}[${m.h}] = ${m.from}, found ${w[m.r][m.h]}`);
            w[m.r][m.h] = m.to;
        } else if (m.t === "slide") {
            if (w[m.from.r][m.from.h] !== m.colour || w[m.to.r][m.to.h] !== 0) throw new Error("slide: holes do not match");
            w[m.from.r][m.from.h] = 0;
            w[m.to.r][m.to.h] = m.colour;
        }
    }
    return w;
}

// ---- BUILD (§4.2) ---------------------------------------------------------

export const SHIP_LEN = Object.freeze({ Destroyer: 2, Sub: 3, Cruiser: 3, Battleship: 4, Carrier: 5 });
const GROW = ["Destroyer", "Sub", "Battleship", "Carrier"]; // the piece lying there at 2, 3, 4, 5 holes

/** An empty key grid: no ships, no pegs. */
export function emptyGrid() {
    return { ships: [], pegs: new Array(100).fill(0), covered: new Array(100).fill(false) };
}

export function shipHoles(s) {
    const len = SHIP_LEN[s.kind] ?? s.len;
    const step = s.down ? 10 : 1;
    return Array.from({ length: len }, (_, t) => s.row * 10 + s.col + t * step);
}

/**
 * The moves of BUILD read `read` (a trace BuildRead): the row cup at a row's
 * first hole (each die thrown until it shows 1-9), the hole die and the d6
 * rolls with the piece swapped up as the ship grows, then the pair's die
 * read and the peg. Applies them to `grid` and returns them.
 */
export function expandBuild(grid, read) {
    const out = [];
    const h = read.hole;
    if (read.cup.length) {
        let die = 0;
        for (const face of read.cup) {
            out.push({ t: "d10", die, face });
            if (face !== 0) die += 1;
        }
        if (die !== 5) throw new Error(`row cup: ${die} dice settled`);
    }
    for (const face of read.d12) out.push({ t: "d12", face });
    const ship = read.ship[0];
    if (ship) {
        const L = SHIP_LEN[ship.kind];
        const d6 = read.d6.slice();
        let len = 2;
        const piece = (kind, l) => ({ t: "ship", kind, down: ship.down, row: ship.row, col: ship.col, bow_last: ship.bow_last, len: l });
        out.push(piece("Destroyer", 2));
        while (len < L) {
            const face = d6.shift();
            if (face === undefined || face < (len === 2 ? 4 : 6)) throw new Error("BUILD: growth rolls do not match the ship");
            out.push({ t: "d6", face, for: "grow" });
            len += 1;
            out.push(piece(len === 3 ? "Sub" : GROW[len - 2], len));
        }
        const kindRoll = L === 3 ? d6.pop() : undefined;
        for (const face of d6) {
            if (face >= (len === 2 ? 4 : 6)) throw new Error("BUILD: a growth roll that should have grown");
            out.push({ t: "d6", face, for: "grow" });
        }
        if (L === 3) {
            if (kindRoll === undefined || (kindRoll <= 3) !== (ship.kind === "Sub")) throw new Error("BUILD: Sub/Cruiser roll");
            out.push({ t: "d6", face: kindRoll, for: "kind" });
            if (ship.kind === "Cruiser") out.push(piece("Cruiser", 3));
        }
        grid.ships.push({ kind: ship.kind, down: ship.down, row: ship.row, col: ship.col, bow_last: ship.bow_last });
        for (const k of shipHoles(ship)) grid.covered[k] = true;
    } else if (read.d6.length) {
        throw new Error("BUILD: d6 rolls without a ship");
    }
    out.push({ t: "read", die: Math.floor((h % 10) / 2), face: read.face });
    grid.pegs[h] = read.peg;
    if (read.peg) out.push({ t: "peg", hole: h, colour: read.peg, inShip: grid.covered[h] });
    return out;
}

/** Keypad (§4.2): the face's row gives the pair's first hole, its column the second. */
export function keypadPeg(face, second) {
    return second ? (face - 1) % 3 : Math.floor((face - 1) / 3);
}
