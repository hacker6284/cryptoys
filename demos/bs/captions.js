/**
 * BS captions: what each beat of the show is, in the board's own words
 * (SPEC §3, §3.1, §4.2, §4.3, §5). Read off the beat and the trace; no
 * arithmetic here.
 */

export const SPEC = {
    build: "4.2 BUILD: \"one hole at a time: ship, then peg\"",
    read: "4.3 READ: \"ships, then pegs\"",
    recipes: "3. The recipes (colours only)",
    call: "3.1 Sending a public value: call the shots",
    check: "5. Received-value check (Wong §5.4)",
    layout: "6. Layouts",
};

export const PLAYERS = ["Alice", "Bob"];
const PEG = ["no peg", "white", "red"];
const CELL = ["plain", "white", "red"];

/** "C7" for hole 27 of a key grid. */
export function holeName(h) {
    return `${"ABCDEFGHIJ"[Math.floor(h / 10)]}${(h % 10) + 1}`;
}

/** The register hole's Battleship call within T1's 9-hole rows ("A1" … "B9"). */
export function callName(h) {
    return `${"ABCDEFGHIJ"[Math.floor(h / 9)]}${(h % 9) + 1}`;
}

function shipText(s) {
    const lies = s.down ? "down" : "across";
    const bow = s.bow_last ? "bow on" : "bow back";
    return `${s.kind} ${lies} from ${holeName(s.row * 10 + s.col)}, ${bow}`;
}

function cellText(show, beat) {
    const p = beat.player;
    const step = show.steps[beat.step];
    if (step.cell < 0) return "";
    const h = show.holes[p][step.cell];
    const total = show.cells[p].length;
    const where = h < 0 ? "start marker" : h >= 100 ? `peg pass ${holeName(h - 100)}` : `ship pass ${holeName(h)}`;
    return `cell ${step.cell + 1}/${total} · ${where} · ${CELL[step.value] ?? "plain"}`;
}

function buildCaption(show, beat) {
    const p = beat.player;
    const read = show.reads[p][beat.read];
    const parts = [];
    if (read.cup.length) parts.push(`row cup ${read.cup.join(" ")}`);
    if (read.d12.length) parts.push(`d12 ${read.d12.join(" ")}`);
    if (read.ship.length) parts.push(shipText(read.ship[0]));
    if (read.d6.length) parts.push(`d6 ${read.d6.join(" ")}`);
    parts.push(`die ${read.die + 1} shows ${read.face} → ${PEG[read.peg]}`);
    const title = `${PLAYERS[p]}'s key: hole ${holeName(read.hole)}`;
    return {
        short: `${title} · ${PEG[read.peg]}`,
        kicker: `BUILD · ${PLAYERS[p]}`,
        title,
        math: parts.join(" · "),
        why: "One hole at a time: ship, then peg. The dice choose; the grid is the secret key.",
        spec: SPEC.build,
    };
}

const STEP = {
    Start: (s, shared) => (s.a.length ? ["Start X", shared ? "X = C × C (red start)" : "X from the start cell"]
        : ["Start X", shared ? "X = C" : "a lone white at hole 1 or 2"]),
    Square: () => ["Square", "Y = X × X"],
    Cube: (s) => ["Cube", s.nudge ? `X = Y × X, nudged ${s.nudge} hole${s.nudge > 1 ? "s" : ""}` : "X = Y × X"],
    TimesBase: () => ["Multiply by C", "X = X × C"],
    Tidy: () => ["Tidy X", "pour the toll into a copy; keep it if a white spills"],
    Clear: () => ["Clear Y", "lift every peg of Y before the call"],
    Call: (s) => [`Call ${callName(s.hole)}`, ""],
    Check: () => ["Square the received number", "C = Y × Y"],
    CheckTidy: () => ["Tidy C", "reject an empty square or a lone white"],
};

function phaseOf(beat) {
    if (beat.stage.startsWith("call")) return "CALL";
    if (beat.stage.startsWith("check")) return "CHECK";
    return beat.shared ? "SHARED WALK" : "PUBLIC WALK";
}

function stepCaption(show, beat) {
    const p = beat.player;
    const s = show.steps[beat.step];
    let [title, math] = STEP[s.op](s, beat.shared);
    let why = "";
    let spec = SPEC.recipes;
    if (s.op === "Call") {
        const answer = s.y[s.hole];
        const said = answer === 2 ? "Hit!" : answer === 1 ? "Miss!" : "Misfire!";
        math = `${PLAYERS[1 - p]}: “${said}” → ${PEG[answer]} in ${PLAYERS[p]}'s Y`;
        why = "Red hits, white misses, empty misfires.";
        spec = SPEC.call;
    } else if (s.op === "Clear") {
        spec = SPEC.call;
        why = `${PLAYERS[p]} copies ${PLAYERS[1 - p]}'s public value hole by hole.`;
    } else if (s.op === "Check" || s.op === "CheckTidy") {
        spec = SPEC.check;
        why = "Square first; an empty square or a lone white is rejected.";
    } else {
        const cell = cellText(show, beat);
        if (cell) math = `${math} · ${cell}`;
        spec = SPEC.read;
        why = beat.shared ? "The same walk over the checked base C gives the shared secret K."
            : "The walk turns the key grid into the public value, one cell at a time.";
        if (s.op === "Tidy") spec = SPEC.recipes;
    }
    const kicker = `${phaseOf(beat)} · ${PLAYERS[p]}`;
    return { short: `${PLAYERS[p]} · ${title}`, kicker, title, math, why, spec };
}

/** The caption for beat `index` of `show`. */
export function captionFor(show, index) {
    const beat = show?.beats[index];
    if (!beat) return null;
    return beat.kind === "build" ? buildCaption(show, beat) : stepCaption(show, beat);
}
