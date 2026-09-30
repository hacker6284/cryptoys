/**
 * Turn a generated `trace_hash` into the demo's show: every face turn of
 * the three puzzles (as cubing.js moves, one list per puzzle) and the
 * beats that play them. The turns of the cook and of E_m are the trace's
 * own; the 3-solve applies SPEC §5.7's hand rule, "solve by undoing":
 * each puzzle keeps the turns it has had since it was last solved, and
 * its solve is that list backwards with every click reversed, copied by
 * colour onto the other puzzles. plan.test.mjs replays every list with
 * the generated face turns and checks A, B, C against the trace's h, h⁻¹
 * and the solved position after each block.
 */
import { FACE_NAME, cardLabel, cardRank, suitName, turnMove, turnText } from "./minx.js";

// Animate at most two blocks (messages of up to 47 bytes). Every block
// more than doubles the undo-solves: block 1 plays 648 leader turns,
// block 2 adds 1,656, and a third block alone would add 3,696 (a 2,304 +
// 1,440 undo word), about 11 minutes even at the top speed. Longer
// messages show the digest only, and the dock says so.
export const MAX_ANIM_BLOCKS = 2;
export const BLOCK_BYTES = 28;
export const SOLVE_CHUNK = 12;
export const PUZZLES = ["A", "B", "C"];
export const HOME = { up: 0, front: 1 };

const HOLD_WORDS = [
    "Up",
    "Front",
    "left of Front",
    "back-left",
    "back-right",
    "right of Front",
    "below-right of Front",
    "below-left of Front",
    "lower back-left",
    "lower back",
    "lower back-right",
    "Down",
];

export function maxAnimBytes() {
    // SPEC §3 pad: M ‖ 0x80 ‖ zeros ‖ 8-byte length, so n bytes take
    // ceil((n + 9) / 28) blocks and two blocks hold 47 bytes. The worker
    // counts blocks with the generated pad_message; this is the dock's copy.
    return MAX_ANIM_BLOCKS * BLOCK_BYTES - 9;
}

export function undo(turns) {
    const out = [];
    for (let i = turns.length - 1; i >= 0; i--) out.push([turns[i][0], -turns[i][1]]);
    return out;
}

function pairs(flat) {
    const out = [];
    for (let i = 0; i + 1 < flat.length; i += 2) out.push([flat[i], flat[i + 1]]);
    return out;
}

function hex(bytes) {
    return bytes.map((b) => b.toString(16).padStart(2, "0")).join("");
}

function heldRule(rank) {
    if (rank === 0) return "A holds Up.";
    if (rank === 1) return "2 holds Front.";
    if (rank <= 5) return "3–6 walk the upper ring clockwise, from the left of Front.";
    if (rank <= 10) return "7–J walk the lower ring clockwise, from below-right of Front.";
    if (rank === 11) return "Q holds Down.";
    return "K turns Up back k clicks, then spins the puzzle k clicks: left comes to the front.";
}

function noonRule(rank) {
    if (rank === 0 || rank === 12) return "Up points to Front.";
    if (rank <= 5) return "The upper ring points to Up.";
    if (rank <= 10) return "The lower ring points to its upper-left neighbour.";
    return "Down points to the 7 face.";
}

function pieceWords(step) {
    const faces = [step.held, step.noon];
    if (step.corner) faces.push(step.third);
    return faces.map((f) => FACE_NAME[f]).join(", ");
}

function cardCaption(block, step) {
    const rank = cardRank(step.card);
    const [held, heldClicks] = step.turns;
    const hold = rank === 12 ? "Up" : HOLD_WORDS[rank];
    const kind = step.pos % 2 ? "corner" : "edge";
    return {
        kicker: `Block ${block + 1} · card ${step.pos} of 52`,
        title: `${cardLabel(step.card)}: turn ${turnText(held, heldClicks)}`,
        math: `${hold} is ${FACE_NAME[held]}. ${suitName(step.card)} = ${Math.abs(heldClicks)}.`
            + (rank === 12 ? ` Spin ${step.spin}.` : "")
            + ` Read the noon ${kind} (${pieceWords(step)}): c1 ${FACE_NAME[step.c1]}, c2 ${FACE_NAME[step.c2]}.`
            + ` Turn ${turnText(step.turns[2], 1)}, ${turnText(step.turns[4], 1)}.`
            + ` Re-grip ${FACE_NAME[step.c1]} up, ${FACE_NAME[step.c2]} front.`,
        why: `${heldRule(rank)} CHaSeD: clubs 1, hearts 2, spades 3, diamonds 4. ${noonRule(rank)}`
            + ` Odd cards read the corner, even cards the edge.`,
        spec: "5.3 Card step (card number i = 1 … 52)",
        short: `${cardLabel(step.card)} · ${turnText(held, heldClicks)} · read ${FACE_NAME[step.c1]}/${FACE_NAME[step.c2]}`,
    };
}

function f3Caption(block, step) {
    const round = step.pos - 52;
    const kind = round % 2 ? "corner" : "edge";
    return {
        kicker: `Block ${block + 1} · F3 round ${round} of 36`,
        title: `Turn ${turnText(step.turns[0], 1)} (Up)`,
        math: `Read Up's noon ${kind} (${pieceWords(step)}): c1 ${FACE_NAME[step.c1]}, c2 ${FACE_NAME[step.c2]}.`
            + ` Re-grip ${FACE_NAME[step.c1]} up, ${FACE_NAME[step.c2]} front.`,
        why: "No card: turn Up +1, read, re-grip. 36 rounds; odd rounds read the corner.",
        spec: "5.4 F3 blank rounds (t = 36, round r = 1 … 36)",
        short: `F3 ${round}/36 · ${turnText(step.turns[0], 1)} · read ${FACE_NAME[step.c1]}/${FACE_NAME[step.c2]}`,
    };
}

const SOLVE_WORDS = {
    1: { leader: "B", copies: ["A"], title: "Solve B onto A", rule: "Undo B's turns, last first, and copy each onto A by colour." },
    2: { leader: "A", copies: ["B", "C"], title: "Solve A onto B and C", rule: "Undo A's turns and copy each onto B and C." },
    3: { leader: "C", copies: ["A"], title: "Solve C onto A", rule: "Undo C's turns and copy each onto A." },
};

/**
 * @param trace host `trace_hash` output (plain numbers)
 * @returns {{ moves, beats, digest, blocks }}
 */
export function buildShow(trace) {
    const blocks = trace.blocks.length;
    if (blocks > MAX_ANIM_BLOCKS) throw new RangeError(`${blocks} blocks is too long to animate`);
    const moves = { A: [], B: [], C: [] };
    const hist = { A: [], B: [], C: [] };
    const beats = [];

    function mark() {
        return { A: moves.A.length, B: moves.B.length, C: moves.C.length };
    }
    function ranges(from) {
        const to = mark();
        const out = {};
        for (const p of PUZZLES) if (to[p] > from[p]) out[p] = [from[p], to[p]];
        return out;
    }
    function turn(p, face, clicks) {
        moves[p].push(turnMove(face, clicks));
        hist[p].push([face, clicks]);
    }

    const iv = pairs(trace.iv_turns);
    iv.forEach(([face, clicks], i) => {
        const from = mark();
        turn("A", face, clicks);
        beats.push({
            kind: "cook", puzzle: "A", block: -1, stage: "cook-a", ranges: ranges(from),
            caption: {
                kicker: `Cook A · ${i + 1} of 12`,
                title: `Turn ${turnText(face, clicks)}`,
                math: "From solved, in the home grip (white up, green front): every face +1, in card order A to Q.",
                why: "A starts as IV-COOK12, the chaining value before the first block.",
                spec: "5.7 By hand: the cook and the 3-solve",
                short: `Cook A · ${turnText(face, clicks)}`,
            },
        });
    });
    const back = undo(iv);
    back.forEach(([face, clicks], i) => {
        const from = mark();
        turn("B", face, clicks);
        beats.push({
            kind: "cook", puzzle: "B", block: -1, stage: "cook-b", ranges: ranges(from),
            caption: {
                kicker: `Cook B backwards · ${i + 1} of 12`,
                title: `Turn ${turnText(face, clicks)}`,
                math: "The mirror of A's cook: every face −1, in reverse card order Q to A.",
                why: "B holds the inverse of A. C stays solved.",
                spec: "5.7 By hand: the cook and the 3-solve",
                short: `Cook B backwards · ${turnText(face, clicks)}`,
            },
        });
    });

    trace.blocks.forEach((blk, b) => {
        beats.push({
            kind: "deal", block: b, stage: `deal-${b}`, ranges: {},
            chunk: blk.chunk.slice(), deal: blk.deal.slice(),
            caption: {
                kicker: `Block ${b + 1} of ${blocks}`,
                title: "Deal the 28 bytes as 52 cards",
                math: `Bytes ${hex(blk.chunk)} → the deal, read left to right, top row first.`,
                why: "Each block's 28 bytes pick one ordering of the deck (φ). Hold A in the home grip.",
                spec: "5. Compression",
                short: `Block ${b + 1}: deal 52 cards`,
            },
        });
        let grip = { ...HOME };
        for (const step of blk.steps) {
            const from = mark();
            for (const [face, clicks] of pairs(step.turns)) turn("A", face, clicks);
            const isCard = step.card >= 0;
            const beat = {
                kind: isCard ? "card" : "f3",
                block: b,
                stage: `${isCard ? "cards" : "f3"}-${b}`,
                ranges: ranges(from),
                pos: step.pos,
                card: step.card,
                turns: pairs(step.turns),
                grip: { ...grip },
                spin: step.spin,
                spunGrip: step.spin ? { up: step.up, front: step.noon } : null,
                read: { held: step.held, noon: step.noon, third: step.third, corner: step.corner },
                next: { up: step.c1, front: step.c2 },
                caption: isCard ? cardCaption(b, step) : f3Caption(b, step),
            };
            // The held-face turn comes first, then the read, then the rest.
            beat.readAfter = 1;
            beats.push(beat);
            grip = { up: step.c1, front: step.c2 };
        }
        beats.push({
            kind: "home", block: b, stage: `home-${b}`, ranges: {}, grip: { ...grip }, next: { ...HOME },
            caption: {
                kicker: `Block ${b + 1} · E_m done`,
                title: "Put A back in the home grip",
                math: "White up, green front. A now holds e = E_m(h).",
                why: "The grip never changes the position: the centres are fixed.",
                spec: "5.7 By hand: the cook and the 3-solve",
                short: "A back to white up, green front",
            },
        });
        for (const stage of [1, 2, 3]) {
            const words = SOLVE_WORDS[stage];
            const word = undo(hist[words.leader]);
            const targets = [words.leader, ...words.copies];
            for (let i = 0; i < word.length; i += SOLVE_CHUNK) {
                const from = mark();
                const part = word.slice(i, i + SOLVE_CHUNK);
                for (const [face, clicks] of part) for (const p of targets) turn(p, face, clicks);
                beats.push({
                    kind: "solve", block: b, stage: `solve${stage}-${b}`, solve: stage,
                    leader: words.leader, copies: words.copies.slice(), ranges: ranges(from),
                    turns: part,
                    caption: {
                        kicker: `Block ${b + 1} · 3-solve ${stage} of 3 · turns ${i + 1}–${i + part.length} of ${word.length}`,
                        title: words.title,
                        math: part.map(([f, c]) => turnText(f, c)).join(", "),
                        why: `${words.rule} Any solve gives the same result; undoing never needs thinking.`,
                        spec: "5.7 By hand: the cook and the 3-solve",
                        short: `${words.title} · ${i + part.length}/${word.length}`,
                    },
                });
            }
            hist[words.leader] = [];
        }
        beats.push({
            kind: "gather", block: b, stage: `gather-${b}`, ranges: {},
            caption: {
                kicker: `Block ${b + 1} done`,
                title: b + 1 < blocks ? "A = h′, B = h′⁻¹, C solved" : "A holds the digest",
                math: b + 1 < blocks
                    ? "Gather the cards. The next block starts from A."
                    : `Digest ${hex(trace.digest)}`,
                why: "h′ = compose(h, e): the 3-solve feeds h forward without any arithmetic.",
                spec: "5.7 By hand: the cook and the 3-solve",
                short: b + 1 < blocks ? `Block ${b + 1} done` : "Done: A holds the digest",
            },
        });
    });

    return { moves, beats, digest: trace.digest.slice(), blocks };
}

/** Beats per stage key, for the transport's stage jumps. */
export function stageKey(beat) {
    return beat?.stage ?? "";
}

export function blockKey(beat) {
    return beat ? String(beat.block) : "";
}

export function leaderTurns(show) {
    return show.moves.A.length;
}
