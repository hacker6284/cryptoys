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
import { FACE_NAME, cardLabel, cardRank, turnMove, turnText } from "./minx.js";

// Block 1 plays turn for turn, for any message. Every later block more
// than doubles the undo-solves (block 2 alone adds 1,656 leader turns, a
// third 3,696), so blocks 2–N are a marked fast-forward instead: the
// puzzles land on the trace's real final h (A), h⁻¹ (B) and solved (C),
// with the digest. No turns or cards of those blocks are shown.
export const FULL_BLOCKS = 1;
export const BLOCK_BYTES = 28;
export const SOLVE_CHUNK = 12;
export const PUZZLES = ["A", "B", "C"];
export const HOME = { up: 0, front: 1 };

/**
 * Length of the fast-forward over blocks from..to: long enough to read the
 * counter, short at any length (1.8 s for one block, at most 5 s at
 * tempo 1). Speed shortens it only gently, never under 1.4 s.
 */
export function ffMillis(from, to, tempo = 1) {
    const n = Math.max(1, to - from + 1);
    const base = Math.min(5000, 1800 + 160 * (n - 1));
    const speedUp = Math.min(2, Math.max(1, Math.sqrt(Number(tempo) || 1)));
    return Math.max(1400, base / speedUp);
}

/** The block the fast-forward counter shows at progress t (0..1). */
export function ffBlockAt(t, from, to) {
    const n = to - from + 1;
    return Math.min(to, from + Math.floor(Math.max(0, t) * n));
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

// Teach captions: one action per step, the words a player would say to
// themselves. The view rings the face being turned and dots the piece
// being read, so captions never list moves; the status line carries the
// count ("turns 61–72 of 216").
const SPEC_CARD = "5.3 Card step (card number i = 1 … 52)";
const SPEC_F3 = "5.4 F3 blank rounds (t = 36, round r = 1 … 36)";
const SPEC_HAND = "5.7 By hand: the cook and the 3-solve";

function note(kicker, title, why, spec, short, math = "") {
    return { kicker, title, math, why, spec, short };
}

function clicks(n) {
    return `${n > 0 ? "+" : "−"}${Math.abs(n)}`;
}

function gripWords(grip) {
    return `Hold ${FACE_NAME[grip.up]} up, ${FACE_NAME[grip.front]} front`;
}

const SOLVE_WORDS = {
    1: {
        leader: "B", copies: ["A"], name: "Solve B onto A",
        title: "Undo B, copying each turn onto A",
        why: "B ends solved; A becomes h′.",
    },
    2: {
        leader: "A", copies: ["B", "C"], name: "Solve A onto B and C",
        title: "Undo A, copying each turn onto B and C",
        why: "A ends solved; B and C become h′⁻¹.",
    },
    3: {
        leader: "C", copies: ["A"], name: "Solve C onto A",
        title: "Undo C, copying each turn onto A",
        why: "C ends solved; A holds h′ again.",
    },
};

/**
 * @param trace host `trace_hash` output (plain numbers)
 * @returns {{ moves, beats, digest, blocks, final, ffAt }} `final` (A = h, B = h⁻¹ after
 *   the last block) and `ffAt` (the fast-forward beat) are set when blocks > 1.
 */
export function buildShow(trace) {
    const blocks = trace.blocks.length;
    const shown = trace.blocks.slice(0, FULL_BLOCKS);
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
            face,
            caption: note(`Cook A · turn ${i + 1} of 12`, `Turn ${turnText(face, clicks)}`,
                "Every face once, in card order: A becomes the starting value.", SPEC_HAND,
                `Cook A · turn ${i + 1} of 12`),
        });
    });
    const back = undo(iv);
    back.forEach(([face, clicks], i) => {
        const from = mark();
        turn("B", face, clicks);
        beats.push({
            kind: "cook", puzzle: "B", block: -1, stage: "cook-b", ranges: ranges(from),
            face,
            caption: note(`Cook B backwards · turn ${i + 1} of 12`, `Turn ${turnText(face, clicks)}`,
                "A's cook undone, last turn first: B holds A's inverse.", SPEC_HAND,
                `Cook B backwards · turn ${i + 1} of 12`),
        });
    });

    shown.forEach((blk, b) => {
        beats.push({
            kind: "deal", block: b, stage: `deal-${b}`, ranges: {},
            chunk: blk.chunk.slice(), deal: blk.deal.slice(),
            caption: note(`Block ${b + 1} of ${blocks}`, "Deal 52 cards face down, in four rows",
                "The block's 28 bytes pick the order. Work left to right, far row first.", "5. Compression",
                `Block ${b + 1} · deal`, `Bytes ${hex(blk.chunk)}`),
        });
        let grip = { ...HOME };
        for (const step of blk.steps) {
            const isCard = step.card >= 0;
            const turns = pairs(step.turns);
            const where = isCard
                ? `Block ${b + 1} · card ${step.pos} of 52`
                : `Block ${b + 1} · blank round ${step.pos - 52} of 36`;
            const spec = isCard ? SPEC_CARD : SPEC_F3;
            const tag = isCard ? cardLabel(step.card) : `Round ${step.pos - 52}/36`;
            const base = {
                block: b, stage: `${isCard ? "cards" : "f3"}-${b}`, pos: step.pos, card: step.card,
                step: `${b}:${step.pos}`,
            };
            const push = (kind, extra, caption) => {
                beats.push({ kind, ...base, ranges: {}, grip: { ...grip }, ...extra, caption });
            };
            const turnBeat = (kind, [face, n], caption) => {
                const from = mark();
                turn("A", face, n);
                push(kind, { ranges: ranges(from), face, clicks: n }, caption);
            };
            // 1. The held face (a card's face and suit clicks; F3: Up +1).
            const [held, heldClicks] = turns[0];
            if (isCard) {
                turnBeat("card", turns[0], note(where, `${tag}: turn ${turnText(held, heldClicks)}`,
                    cardRank(step.card) === 12
                        ? "A King turns Up back by its suit, then spins."
                        : "The number picks the face (ringed); the suit, how far.",
                    spec, `${tag} · turn ${turnText(held, heldClicks)}`));
            } else {
                turnBeat("turn", turns[0], note(where, `Turn Up (${FACE_NAME[held]}) +1`,
                    "No card: a blank round turns Up.", spec, `${tag} · turn Up +1`));
            }
            if (step.spin) {
                const spun = { up: step.up, front: step.noon };
                push("spin", { next: spun, spin: step.spin }, note(where,
                    `Spin ${step.spin} click${step.spin === 1 ? "" : "s"}: the left face comes to the front`,
                    "Kings then turn the whole puzzle about Up.", spec, `${tag} · spin ${step.spin}`));
                grip = spun;
            }
            // 2. Read the noon piece: its first two colours set the next grip.
            const piece = step.corner ? "corner" : "edge";
            push("read", {
                read: { held: step.held, noon: step.noon, third: step.third, corner: step.corner },
                c1: step.c1, c2: step.c2,
            }, note(where, `Read the noon ${piece}: ${FACE_NAME[step.c1]}, ${FACE_NAME[step.c2]}`,
                `${step.pos % 2 ? "Odd" : "Even"} steps read the ${piece}: first the colour on the face just turned, then its noon.`,
                spec, `${tag} · read ${FACE_NAME[step.c1]}, ${FACE_NAME[step.c2]}`));
            // 3–4. The rest of the step's turns, one at a time.
            const rest = turns.slice(1);
            rest.forEach(([face, n], i) => {
                const isFront = i === rest.length - 1;
                const twice = rest.length === 2 && rest[0][0] === rest[1][0];
                let title = `Turn the noon face (${FACE_NAME[face]}) ${clicks(n)}`;
                let why = "The noon face: the neighbour the held face points to.";
                if (isFront) {
                    title = `Turn Front (${FACE_NAME[face]}) ${clicks(n)}`;
                    why = twice ? "Front again: +2 in all." : "Front: the face looking at you.";
                } else if (twice) {
                    title = `Turn the noon face, Front (${FACE_NAME[face]}), ${clicks(n)}`;
                    why = "Here the noon is Front, so Front turns twice.";
                }
                turnBeat("turn", [face, n], note(where, title, why, spec, `${tag} · turn ${turnText(face, n)}`));
            });
            // 5. Re-grip.
            const next = { up: step.c1, front: step.c2 };
            push("grip", { next }, note(where, gripWords(next),
                "Pick A up and set it down that way.", spec, `${tag} · ${gripWords(next).toLowerCase()}`));
            grip = next;
        }
        beats.push({
            kind: "home", block: b, stage: `home-${b}`, ranges: {}, grip: { ...grip }, next: { ...HOME },
            caption: note(`Block ${b + 1} · cards done`, gripWords(HOME),
                "A now holds e. The home grip starts the 3-solve.", SPEC_HAND, `Block ${b + 1} · home grip`),
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
                    caption: note(`Block ${b + 1} · 3-solve ${stage} of 3 · ${words.name}`, words.title,
                        words.why, SPEC_HAND,
                        `${words.name} · turns ${i + 1}–${i + part.length} of ${word.length}`),
                });
            }
            hist[words.leader] = [];
        }
        beats.push({
            kind: "gather", block: b, stage: `gather-${b}`, ranges: {},
            caption: b + 1 < blocks
                ? note(`Block ${b + 1} done`, "Gather the cards", `A carries h′ into block ${b + 2}.`, SPEC_HAND,
                    `Block ${b + 1} done`)
                : note("Done", "A holds the digest", "Read it off A (§6).", SPEC_HAND, "Done: A holds the digest",
                    hex(trace.digest)),
        });
    });

    let final = null;
    let ffAt = -1;
    if (blocks > shown.length) {
        // Blocks 2–N: no turns, no cards. The puzzles settle on the trace's
        // own last chaining value, its inverse, and solved.
        const last = trace.blocks[blocks - 1];
        final = { A: last.h_next, B: last.h_next_inv };
        const from = shown.length + 1;
        const range = from === blocks ? `block ${blocks}` : `blocks ${from}–${blocks}`;
        ffAt = beats.length;
        beats.push({
            kind: "ff", block: shown.length, stage: "ff", ranges: {}, from, to: blocks,
            caption: note(`Fast-forward · ${range}`, `Fast-forward: ${range}`,
                `Each block deals 52 cards, plays 88 steps and the 3-solve, just as block 1 did. Those turns are not shown; the puzzles land on the real result.`,
                SPEC_HAND, `Fast-forward: ${range}`),
        });
        beats.push({
            kind: "done", block: blocks - 1, stage: "done", ranges: {},
            caption: note("Done", "A holds the digest",
                `After block ${blocks}: A is h, B its inverse, C solved. Read the digest off A (§6).`, SPEC_HAND,
                "Done: A holds the digest", hex(trace.digest)),
        });
    }

    return { moves, beats, digest: trace.digest.slice(), blocks, final, ffAt };
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
