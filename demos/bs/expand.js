/**
 * BS: one step's peg moves on the lid. The moves themselves come from
 * generated code (bs.sudo step_moves, through worker.js `moves`); this only
 * says where each lands on the workspace grid and pairs a slide's two moves
 * (out of the strip, into the register) into one peg sliding across.
 *
 * A move is { reg: "X" | "Y" | "C" | "Strip", hole, from, into, why }.
 * cellOf(reg, hole): its workspace cell (playroom/bs-stage.js workspaceCell).
 * Returns, in order:
 *   { t: "set", cell, from, into }        a peg in, out, or swapped
 *   { t: "slide", from, to, colour }      a peg from cell `from` to cell `to`
 */
export function lidMoves(moves, cellOf) {
    const out = [];
    for (let i = 0; i < moves.length; i++) {
        const m = moves[i];
        const next = moves[i + 1];
        if (m.why === "Slide" && m.reg === "Strip" && next?.why === "Slide" && next.reg !== "Strip") {
            out.push({ t: "slide", from: cellOf(m.reg, m.hole), to: cellOf(next.reg, next.hole), colour: m.from });
            i += 1;
        } else {
            out.push({ t: "set", cell: cellOf(m.reg, m.hole), from: m.from, into: m.into });
        }
    }
    return out;
}

/** Apply lid moves to 100 workspace cells, checking each move's `from`. */
export function applyLidMoves(cells, moves) {
    for (const m of moves) {
        const [at, want] = m.t === "slide" ? [m.from, m.colour] : [m.cell, m.from];
        if (cells[at] !== want) throw new Error(`cell ${at} holds ${cells[at]}, the move expects ${want}`);
        if (m.t === "slide") {
            cells[m.from] = 0;
            cells[m.to] = m.colour;
        } else {
            cells[m.cell] = m.into;
        }
    }
    return cells;
}
