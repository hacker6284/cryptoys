/**
 * Turn a generated v3 `trace_hash` into the demo's show: every face turn
 * of the three puzzles (as cubing.js moves, one list per puzzle) and the
 * beats that play them, one action per beat.
 *
 * Every turn of the cook and of E_m (the 52 card steps and the 26 echoes,
 * six turns each) is the trace's own. The 3-solve applies SPEC §5.7's hand
 * rule, "solve each megaminx by any method you know", with the method
 * "undo": each puzzle keeps the turns it has had since it was last solved,
 * and its solve is that list backwards with every click reversed, copied
 * by colour onto the other puzzles. plan.test.mjs replays every list with
 * the generated face turns and checks A, B, C against the trace's h, h⁻¹
 * and solved after each block. Nothing here computes a step of the hash:
 * the captions only name what the trace already did.
 */
import { FACE_NAME, RANK_NAME, cardLabel, cardRank, suitAmount, turnMove, turnText } from "./minx.js";

// A message is traced and played turn for turn, never cut short or sped
// through, up to TRACE_BLOCKS blocks (a one-block message is up to 19
// bytes). Longer messages are too long to trace: block 1 alone plays
// 1,488 face turns, and the undo-solves more than double every block
// after it. They get the digest only, with no animation.
export const TRACE_BLOCKS = 1;
export const BLOCK_BYTES = 28;
export const CARD_STEPS = 52;
export const ECHOES = 26;
export const SOLVE_CHUNK = 12;
export const PUZZLES = ["A", "B", "C"];

export function undo(turns) {
    const out = [];
    for (let i = turns.length - 1; i >= 0; i--) out.push([turns[i][0], -turns[i][1]]);
    return out;
}

export function pairs(flat) {
    const out = [];
    for (let i = 0; i + 1 < flat.length; i += 2) out.push([flat[i], flat[i + 1]]);
    return out;
}

function hex(bytes) {
    return bytes.map((b) => b.toString(16).padStart(2, "0")).join("");
}

/** A face named by its centre colour and the rank it carries: "green (2)". */
export function faceText(face) {
    return `${FACE_NAME[face]} (${RANK_NAME[face]})`;
}

const SPEC_CARD = "5.3 Card step";
const SPEC_PIECES = "5.2 A card's two pieces";
const SPEC_ECHO = "5.4 Deal once, then 26 echoes";
const SPEC_HAND = "5.7 Hand details: IV-COOK12 and the 3-solve (same turns as v2)";
const SPEC_COMP = "5. Compression";

function note(kicker, title, why, spec, short, math = "") {
    return { kicker, title, math, why, spec, short };
}

const SOLVE_WORDS = {
    1: {
        leader: "B", copies: ["A"], name: "Solve B onto A",
        title: "Solve B by undoing its turns, making each turn on A as well",
        why: "B ends solved; A becomes h′ = h·W·h.",
    },
    2: {
        leader: "A", copies: ["B", "C"], name: "Solve A onto B and C",
        title: "Solve A by undoing its turns, making each turn on B and C as well",
        why: "A ends solved; B and C become h′⁻¹.",
    },
    3: {
        leader: "C", copies: ["A"], name: "Solve C onto A",
        title: "Solve C by undoing its turns, making each turn on A as well",
        why: "C ends solved; A holds h′ again, B its inverse.",
    },
};

const PIECE_WORDS = ["edge", "edge", "corner", "corner", "edge again"];

/**
 * @param trace host `trace_hash` output (plain numbers)
 * @param marks per block, per step: { edge, corner, lookEdge?, lookCorner? } slot faces (worker.js)
 * @returns {{ moves, beats, digest, blocks, held }}
 */
export function buildShow(trace, marks = []) {
    const blocks = trace.blocks.length;
    if (blocks > TRACE_BLOCKS) throw new RangeError(`too long to trace: ${blocks} blocks`);
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
            kind: "cook", puzzle: "A", block: -1, stage: "cook-a", ranges: ranges(from), face, clicks,
            caption: note(`Cook A · turn ${i + 1} of 12`, `On A, turn ${turnText(face, clicks)}`,
                "IV-COOK12: every face +1 once, in the rank order of the centre colours (A, 2, …, Q).", SPEC_HAND,
                `Cook A · ${turnText(face, clicks)} (${i + 1} of 12)`),
        });
    });
    undo(iv).forEach(([face, clicks], i) => {
        const from = mark();
        turn("B", face, clicks);
        beats.push({
            kind: "cook", puzzle: "B", block: -1, stage: "cook-b", ranges: ranges(from), face, clicks,
            caption: note(`Cook B backwards · turn ${i + 1} of 12`, `On B, turn ${turnText(face, clicks)}`,
                "A's cook undone, last turn first: B holds A's inverse. C stays solved.", SPEC_HAND,
                `Cook B backwards · ${turnText(face, clicks)} (${i + 1} of 12)`),
        });
    });

    trace.blocks.forEach((blk, b) => {
        const blockMarks = marks[b] || [];
        const held = blk.deal[CARD_STEPS - 1];
        const B = `Block ${b + 1} of ${blocks}`;
        beats.push({
            kind: "deal", block: b, stage: `deal-${b}`, ranges: {}, deal: blk.deal.slice(), chunk: blk.chunk.slice(),
            caption: note(B, "Lay out the block's deal face down, 13 to a row",
                "φ turns the block's 28 bytes into the order of the 52 cards. Far row first, left to right.", SPEC_COMP,
                `${B} · lay out the deal`, `Bytes ${hex(blk.chunk)}`),
        });
        blk.steps.forEach((st, s) => {
            const echo = st.pos > CARD_STEPS;
            const j = st.pos - CARD_STEPS;
            const where = echo ? `${B} · echo ${j} of ${ECHOES}` : `${B} · card ${st.pos} of ${CARD_STEPS}`;
            const tag = cardLabel(st.card);
            const turns = pairs(st.turns);
            const m = blockMarks[s] || {};
            const base = { block: b, stage: `${echo ? "echo" : "cards"}-${b}`, pos: st.pos, card: st.card, step: `${b}:${st.pos}` };
            const push = (kind, extra, caption) => beats.push({ kind, ...base, ranges: {}, ...extra, caption });
            const turnBeat = (kind, [face, n], caption, extra = {}) => {
                const from = mark();
                turn("A", face, n);
                push(kind, { ranges: ranges(from), face, clicks: n, ...extra }, caption);
            };
            const spec = echo ? SPEC_ECHO : SPEC_CARD;
            const c = FACE_NAME[st.colour];
            const n = FACE_NAME[st.n];
            const n2 = FACE_NAME[st.n2];
            const rank = cardRank(st.card);
            const k = suitAmount(st.card);
            if (echo) {
                push("count", { counter: j }, note(where, `Count a card off the dealt pile (${j} of ${ECHOES})`,
                    "Unread: the counter pile only counts the echoes.", SPEC_ECHO, `Echo ${j} · count a card off`));
                push("look", { marks: { edge: m.lookEdge, corner: m.lookCorner } }, note(where,
                    `Look: X = ${faceText(st.x)}, Y = ${faceText(st.y)}, so P = ${faceText(st.base)}`,
                    `X carries the held edge's ${FACE_NAME[blk.steps[CARD_STEPS - 1].n]} sticker, Y the held corner's. `
                        + "Count up from X by Y's rank: that colour is P.", SPEC_ECHO,
                    `Echo ${j} · look: P = ${FACE_NAME[st.base]}`));
            }
            // Step 1: the turn the card's rank and suit pick.
            const [f1, k1] = turns[0];
            const from = echo ? `P, ${FACE_NAME[st.base]}` : `the last face, ${FACE_NAME[st.base]}`;
            const pick = rank === 12
                ? `the face opposite ${from} is ${faceText(f1)}`
                : `count up from ${from}, by ${RANK_NAME[rank]} → ${faceText(f1)}`;
            turnBeat(echo ? "echo" : "card", turns[0], note(where, `${tag}: ${pick}; turn it +${k1}`,
                rank === 12
                    ? "A King turns the face opposite; the suit says how many clicks (clubs 1 … diamonds 4)."
                    : "The rank counts up the colour order; the suit says how many clicks (clubs 1 … diamonds 4).",
                spec, `${tag} · ${turnText(f1, k1)}`), { k, turnUp: !echo });
            // Step 2: name the edge and the corner by their colours.
            push("name", { marks: { edge: m.edge, corner: m.corner } }, note(where,
                `Name the pieces: edge ${c}–${n}, corner ${c}–${n}–${n2}`,
                `${echo ? "P" : "The card's colour"} is ${c}; the suit picks ${n} among its neighbours `
                    + "(clubs: the lowest-ranked, then clockwise), and the corner adds the next one clockwise.",
                SPEC_PIECES, `${tag} · edge ${c}–${n}, corner ${c}–${n}–${n2}`));
            // Steps 3–5: five single clicks, each on the face a named sticker is on now.
            turns.slice(1).forEach(([face, clicks], i) => {
                const sticker = i === 0 || i === 2 ? c : n;
                const piece = PIECE_WORDS[i];
                const last = i === 4;
                turnBeat("turn", [face, clicks], note(where,
                    `${piece[0].toUpperCase()}${piece.slice(1)}: turn the face its ${sticker} sticker is on, ${faceText(face)}, +1`,
                    last ? `${FACE_NAME[face]} is the new last face.` : "Find the piece wherever it is now.",
                    spec, `${tag} · ${piece} · ${turnText(face, clicks)}`), { role: i });
            });
            if (!echo && st.pos === CARD_STEPS) {
                push("hold", { held }, note(where, `Keep the ${tag} in hand: the held card`,
                    "Card 52 is not put on the pile. Its echoes come next.", SPEC_ECHO, `${tag} · held`));
            }
        });
        beats.push({
            kind: "done-w", block: b, stage: `wdone-${b}`, ranges: {},
            caption: note(`${B} · W done`, "A now holds W·h",
                "Next the 3-solve feeds h forward: h′ = h·W·h.", SPEC_HAND, `${B} · W done: A holds W·h`),
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
                    leader: words.leader, copies: words.copies.slice(), ranges: ranges(from), turns: part,
                    caption: note(`${B} · 3-solve ${stage} of 3 · ${words.name}`, words.title, words.why, SPEC_HAND,
                        `${words.name} · turns ${i + 1}–${i + part.length} of ${word.length}`),
                });
            }
            hist[words.leader] = [];
        }
        beats.push({
            kind: "gather", block: b, stage: `gather-${b}`, ranges: {}, deal: blk.deal.slice(),
            caption: b + 1 < blocks
                ? note(`${B} done`, "Gather the cards", `A carries h′ into block ${b + 2}.`, SPEC_HAND, `${B} done`)
                : note("Done", "A holds the digest", "Gather the cards. Read the digest off A (§6).", SPEC_HAND,
                    "Done: A holds the digest", hex(trace.digest)),
        });
    });

    return {
        moves, beats, digest: trace.digest.slice(), blocks,
        deals: trace.blocks.map((blk) => blk.deal.slice()),
        final: { A: trace.blocks.at(-1)?.h_next, B: trace.blocks.at(-1)?.h_next_inv },
    };
}

export function stageKey(beat) {
    return beat?.stage ?? "";
}

export function blockKey(beat) {
    return beat ? String(beat.block) : "";
}
