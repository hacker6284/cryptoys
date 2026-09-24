import { scramble_v1, scramble_v2, update, evaluate, solved_facelets } from "./generated/scramble.mjs";
import { mountCube } from "./view.js";
import { SOLVED_FACELETS, applyMove, isSolved, shortSolve, toCubejs, flipU, parseMove } from "./cube.js";
import {
    bindTeachKeys,
    colorName,
    headingId,
    nextGroup,
    renderOutline,
    setDisabled,
    stampHeadingIds,
} from "../shared/teach.js";

const canvas = document.querySelector("canvas");
const input = document.querySelector("#message");
const status = document.querySelector("#status");
const digestEl = document.querySelector("#digest");
const errorEl = document.querySelector("#error");
const specDialog = document.querySelector("#spec");
const specBody = document.querySelector("#spec-body");
const speed = document.querySelector("#speed");
const teachEl = document.querySelector("#teach");
const tapeEl = document.querySelector("#tape");
const teachCard = document.querySelector("#teach-card");
const teachPos = document.querySelector("#teach-pos");
const outlineEl = document.querySelector("#outline");

const view = mountCube(canvas);
const solved = solved_facelets();
if (solved !== SOLVED_FACELETS) {
    throw new Error("The demo cube and the reference cube disagree on the solved pose.");
}

const V2_TURNS = {
    0: "U R", 1: "U F", 2: "U L", 3: "U B",
    4: "D R", 5: "D F", 6: "R U", 7: "R D",
    8: "F U", 9: "F D", A: "B U", B: "F R",
    C: "L U", D: "F L", E: "R F", F: "R B",
};

let version = 2;
let encoding = "text";
let trace = [];
let facelets = solved;
let cursor = -1;
let playing = false;
let solving = false;
let busy = false;
let teaching = false;
let job = 0;
let solverReady = false;
let messageBytes = [];

function bytesOf(text) {
    if (encoding === "hex") {
        let body = text.trim().replace(/^0x/i, "").replace(/[\s_]/g, "");
        if (!body) return [];
        if (!/^[0-9a-fA-F]+$/.test(body)) throw new Error("Hex contains non-hex characters.");
        if (body.length % 2 === 1) body = `0${body}`;
        const out = [];
        for (let i = 0; i < body.length; i += 2) out.push(Number.parseInt(body.slice(i, i + 2), 16));
        return out;
    }
    return Array.from(new TextEncoder().encode(text));
}

function digestHex(bytes) {
    return bytes.map((b) => b.toString(16).padStart(2, "0")).join("").toUpperCase().slice(1);
}

function symbolWord(step) {
    return trace
        .filter((item) => item.kind === "move" && item.block === step.block)
        .sort((a, b) => a.index - b.index)
        .map((item) => item.move)
        .join("");
}

function caption() {
    if (cursor < 0) return "Solved start · white up, green front, red right";
    const step = trace[cursor];
    if (step.kind === "ruleB") return `Rule B · ${step.up} up, ${step.front} front`;
    if (step.kind === "closer") return `Closer · ${step.move}`;
    if (step.kind === "canonicalize") return "Seat white up, green front";
    if (version === 2) return `Symbol ${step.block + 1} · ${step.nybble} → ${symbolWord(step)} · ${step.move}`;
    return `Block ${step.block + 1} · ${step.nybble} → ${step.move}`;
}

function showStatus(text) {
    status.textContent = text;
}

function showFace(next) {
    facelets = next;
    view.paint(next);
}

function messageNybbleCount() {
    return messageBytes.length * 2;
}

function tapeCells() {
    const seen = new Map();
    for (const step of trace) {
        if (step.kind === "move" && step.nybble) seen.set(step.block, step.nybble);
    }
    const msg = messageNybbleCount();
    return [...seen.entries()].sort((a, b) => a[0] - b[0]).map(([block, nybble]) => ({
        block,
        nybble,
        padding: block >= msg,
        marker: block === msg && nybble === "8",
    }));
}

function renderTape(activeBlock) {
    tapeEl.replaceChildren();
    for (const cell of tapeCells()) {
        const el = document.createElement("span");
        el.className = "tape-cell";
        if (cell.padding) el.classList.add("pad");
        if (cell.marker) el.classList.add("marker");
        if (cell.block === activeBlock) el.classList.add("on");
        el.textContent = cell.nybble;
        el.title = cell.marker ? "padding marker 8" : cell.padding ? "padding" : "message";
        tapeEl.append(el);
    }
}

function stageKey(step) {
    if (step.kind === "move") return `move:${step.block}:${step.index}`;
    if (step.kind === "ruleB") return `ruleB:${step.block}`;
    return step.kind + (step.move || "");
}

function roundKey(step) {
    if (step.kind === "move" || step.kind === "ruleB") return `sym:${step.block}`;
    return step.kind === "closer" ? "closer" : "seat";
}

function outlineSections() {
    const msg = messageNybbleCount();
    const sections = [];
    const byRound = new Map();
    trace.forEach((step, index) => {
        let title;
        if (step.kind === "move" || step.kind === "ruleB") {
            const pad = step.block >= msg;
            title = pad
                ? (step.block === msg && (step.nybble === "8" || !step.nybble) ? "Padding · marker 8" : `Padding · nybble ${step.block + 1}`)
                : version === 2 ? `Symbol ${step.block + 1}` : `Block ${step.block + 1}`;
        } else if (step.kind === "closer") title = "Closer";
        else title = "Seat";
        if (!byRound.has(title)) byRound.set(title, []);
        const label = step.kind === "move"
            ? `Turn ${step.index + 1} · ${step.move}`
            : step.kind === "ruleB" ? "Rule B"
            : step.kind === "closer" ? step.move
            : "Seat W up, G front";
        byRound.get(title).push({ key: String(index), label, index });
    });
    for (const [title, items] of byRound) {
        sections.push({ title, items, open: items.some((item) => item.index === cursor) });
    }
    return sections;
}

function annotate(step) {
    const n = trace.length;
    const pos = cursor < 0 ? `start · ${n} steps` : `step ${cursor + 1} of ${n}`;
    if (cursor < 0 || !step) {
        return {
            kicker: pos,
            title: "Solved start",
            math: "White up, green front, red right.",
            why: "Step through walks the padded tape one turn at a time.",
            spec: version === 2 ? "scramble_v2" : "scramble_v1",
        };
    }
    const pad = (step.kind === "move" || step.kind === "ruleB") && step.block >= messageNybbleCount();
    if (step.kind === "move") {
        const pair = version === 2 ? V2_TURNS[step.nybble] : step.move;
        return {
            kicker: pos + (pad ? " · padding" : ` · symbol ${step.block + 1}`),
            title: pad && step.nybble === "8" ? "Padding marker" : `Turn ${step.move}`,
            math: version === 2
                ? `Nybble ${step.nybble} → ${pair}. This is turn ${step.index + 1} of 2.`
                : `Nybble ${step.nybble} → ${step.move}.`,
            why: pad
                ? (step.nybble === "8"
                    ? "Evaluate appends marker nybble 8, then fills the tape."
                    : "Filler from the padding cycle. It is not part of the message.")
                : "The nybble chooses the face turns that walk the cube.",
            spec: version === 2 ? "scramble_v2" : "scramble_v1",
        };
    }
    if (step.kind === "ruleB") {
        return {
            kicker: pos,
            title: "Rule B",
            math: `Cubie (1,1,1) reads ${colorName(step.up)} up, ${colorName(step.front)} front.`,
            why: "Rotate the whole cube so that cubie's up and front become world up and front.",
            spec: "Rule B",
        };
    }
    if (step.kind === "closer") {
        return {
            kicker: pos,
            title: `Closer · ${step.move}`,
            math: step.move === "F2" ? "Half turn of the front face." : "Half turn of the back face.",
            why: "After the padded tape: F2, then B2, then the seat.",
            spec: "Closer and seat",
        };
    }
    return {
        kicker: pos,
        title: "Seat",
        math: "Same rotation as Rule B, with up = W and front = G.",
        why: "The seated pose is the digest.",
        spec: "Closer and seat",
    };
}

function renderCard(note) {
    teachCard.replaceChildren();
    const kicker = document.createElement("p");
    kicker.className = "kicker";
    kicker.textContent = note.kicker;
    const title = document.createElement("h2");
    title.textContent = note.title;
    const math = document.createElement("p");
    math.className = "math";
    math.textContent = note.math;
    const why = document.createElement("p");
    why.className = "why";
    why.textContent = note.why;
    const spec = document.createElement("button");
    spec.type = "button";
    spec.className = "inline-link";
    spec.textContent = `SPEC · ${note.spec}`;
    spec.addEventListener("click", () => {
        openSpec(note.spec).catch((err) => {
            errorEl.textContent = err.message;
        });
    });
    teachCard.append(kicker, title, math, why, spec);
}

function applyHighlight(step) {
    if (!step) {
        view.clearHighlights();
        return;
    }
    if (step.kind === "move" || step.kind === "closer") view.highlightLayer(parseMove(step.move).face);
    else if (step.kind === "ruleB" || step.kind === "canonicalize") view.highlightCubie(1, 1, 1);
    else view.clearHighlights();
}

function refreshTeach() {
    const step = cursor >= 0 ? trace[cursor] : null;
    const activeBlock = step && (step.kind === "move" || step.kind === "ruleB") ? step.block : -1;
    renderTape(activeBlock);
    renderCard(annotate(step));
    teachPos.textContent = cursor < 0 ? `0 / ${trace.length}` : `${cursor + 1} / ${trace.length}`;
    renderOutline(outlineEl, outlineSections(), cursor < 0 ? "" : String(cursor), (index) => {
        void jumpTo(index, false);
    });
    const atStart = cursor < 0;
    const atEnd = cursor >= trace.length - 1;
    document.querySelectorAll("[data-jump]").forEach((button) => {
        const jump = button.dataset.jump;
        setDisabled(button, (jump === "back" || jump === "stage-back" || jump === "round-back") ? atStart : atEnd);
    });
}

function setTeaching(on) {
    teaching = on;
    teachEl.hidden = !on;
    outlineEl.hidden = !on;
    if (!on) view.clearHighlights();
}

function showPaused() {
    if (cursor < 0) showFace(solved);
    else showFace(trace[cursor].facelets);
    if (teaching) applyHighlight(cursor >= 0 ? trace[cursor] : null);
    showStatus(caption());
    if (teaching) refreshTeach();
}

function recompute() {
    job += 1;
    playing = false;
    solving = false;
    busy = false;
    errorEl.textContent = "";
    try {
        messageBytes = bytesOf(input.value);
    } catch (err) {
        errorEl.textContent = err.message;
        return;
    }
    const state = version === 2 ? scramble_v2() : scramble_v1();
    update(state, messageBytes);
    const result = evaluate(state);
    trace = result.trace;
    digestEl.textContent = digestHex(result.digest);
    cursor = -1;
    showFace(solved);
    showStatus(caption());
    if (teaching) refreshTeach();
}

function duration(kind) {
    const pace = Number(speed.value);
    return (kind === "move" || kind === "closer" ? 700 : 900) / pace;
}

async function playStep(token) {
    if (cursor >= trace.length - 1) return false;
    const step = trace[cursor + 1];
    const from = facelets;
    if (step.kind === "move" || step.kind === "closer") await view.animateMove(step.move, duration(step.kind));
    else if (step.kind === "ruleB") await view.animateReorient(from, step.up, step.front, duration(step.kind));
    else await view.animateReorient(from, "W", "G", duration(step.kind));
    if (token !== job) return false;
    cursor += 1;
    showFace(step.facelets);
    if (teaching) applyHighlight(step);
    showStatus(caption());
    if (teaching) refreshTeach();
    return true;
}

async function play() {
    if (playing || solving || busy) return;
    playing = true;
    const token = job;
    while (playing && token === job && cursor < trace.length - 1) {
        const ok = await playStep(token);
        if (!ok) break;
    }
    playing = false;
}

async function jumpTo(index, animate) {
    if (trace.length === 0 || busy) return;
    const next = Math.max(-1, Math.min(trace.length - 1, index));
    if (animate && next === cursor + 1) {
        playing = false;
        busy = true;
        const token = job;
        await playStep(token);
        busy = false;
        return;
    }
    job += 1;
    playing = false;
    cursor = next;
    showPaused();
}

async function stepBy(dir) {
    if (!teaching) enterTeach();
    if (dir < 0) return jumpTo(cursor - 1, false);
    return jumpTo(cursor + 1, true);
}

function enterTeach() {
    if (trace.length === 0) recompute();
    setTeaching(true);
    if (cursor < 0 && trace.length) {
        cursor = 0;
        showPaused();
    } else {
        showPaused();
    }
}

async function ensureSolver() {
    if (solverReady) return;
    const Cube = globalThis.Cube;
    if (!Cube || typeof Cube.initSolver !== "function") throw new Error("Could not solve this cube.");
    showStatus("Preparing a short solve…");
    await new Promise((resolve) => setTimeout(resolve, 30));
    Cube.initSolver();
    solverReady = true;
}

async function solve() {
    if (solving) return;
    playing = false;
    solving = true;
    setTeaching(false);
    const token = ++job;
    errorEl.textContent = "";
    try {
        let moves = shortSolve(facelets, 4);
        if (!moves) {
            await ensureSolver();
            if (token !== job) return;
            const raw = globalThis.Cube.fromString(toCubejs(facelets));
            const text = raw.solve(22) ?? raw.solve(24);
            if (!text || text === "-") throw new Error("No solution found.");
            moves = text.trim().split(/\s+/).map(flipU);
            let check = facelets;
            for (const move of moves) check = applyMove(check, move);
            if (!isSolved(check)) throw new Error("Solver returned a sequence that does not solve this cube.");
        }
        if (moves.length === 0) {
            showFace(solved);
            showStatus("Solved start · white up, green front, red right");
            return;
        }
        showStatus(`Solve · ${moves.length} moves`);
        let current = facelets;
        for (let i = 0; i < moves.length; i++) {
            if (token !== job) return;
            showStatus(`Solve ${i + 1}/${moves.length} · ${moves[i]}`);
            await view.animateMove(moves[i], duration("move"));
            if (token !== job) return;
            current = applyMove(current, moves[i]);
            showFace(current);
        }
        if (!isSolved(current)) throw new Error("Solver returned a sequence that does not solve this cube.");
        showStatus(`Solve · ${moves.length} moves`);
    } catch (err) {
        if (token === job) errorEl.textContent = err.message || "Could not solve this cube.";
    } finally {
        if (token === job) solving = false;
    }
}

function renderMarkdown(markdown) {
    const lines = markdown.replace(/\r\n/g, "\n").split("\n");
    let html = "";
    let i = 0;
    const esc = (s) => s.replace(/[&<>]/g, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;" }[c]));
    const inline = (s) => esc(s).replace(/`([^`]+)`/g, "<code>$1</code>").replace(/\[([^\]]+)\]\(([^)]+)\)/g, '<a href="$2">$1</a>');
    const hid = (title) => ` id="${headingId(title)}"`;
    while (i < lines.length) {
        const line = lines[i];
        if (line.startsWith("```")) {
            const buf = [];
            i += 1;
            while (i < lines.length && !lines[i].startsWith("```")) {
                buf.push(lines[i]);
                i += 1;
            }
            i += 1;
            html += `<pre><code>${esc(buf.join("\n"))}</code></pre>`;
            continue;
        }
        if (line.startsWith("|")) {
            const rows = [];
            while (i < lines.length && lines[i].startsWith("|")) {
                rows.push(lines[i]);
                i += 1;
            }
            const cells = (row) => row.split("|").slice(1, -1).map((c) => c.trim());
            const head = cells(rows[0]);
            const body = rows.slice(2).map(cells);
            html += "<table><thead><tr>" + head.map((c) => `<th>${inline(c)}</th>`).join("") + "</tr></thead><tbody>";
            for (const row of body) html += "<tr>" + row.map((c) => `<td>${inline(c)}</td>`).join("") + "</tr>";
            html += "</tbody></table>";
            continue;
        }
        if (line.startsWith("### ")) {
            const title = line.slice(4);
            html += `<h3${hid(title)}>${inline(title)}</h3>`;
            i += 1;
            continue;
        }
        if (line.startsWith("## ")) {
            const title = line.slice(3);
            html += `<h2${hid(title)}>${inline(title)}</h2>`;
            i += 1;
            continue;
        }
        if (line.startsWith("# ")) {
            const title = line.slice(2);
            html += `<h1${hid(title)}>${inline(title)}</h1>`;
            i += 1;
            continue;
        }
        if (line.startsWith("- ")) {
            html += "<ul>";
            while (i < lines.length && lines[i].startsWith("- ")) {
                html += `<li>${inline(lines[i].slice(2))}</li>`;
                i += 1;
            }
            html += "</ul>";
            continue;
        }
        if (line.trim() === "") {
            i += 1;
            continue;
        }
        html += `<p>${inline(line)}</p>`;
        i += 1;
    }
    return html;
}

function versionSlice(markdown) {
    const start = markdown.indexOf("## scramble_v1");
    const mid = markdown.indexOf("## scramble_v2");
    const common = markdown.slice(0, start);
    const section = version === 1 ? markdown.slice(start, mid) : markdown.slice(mid);
    return common + section;
}

async function openSpec(heading) {
    const response = await fetch("./SPEC.md");
    if (!response.ok) throw new Error("The specification file is missing. Run tools/build.sh.");
    const markdown = await response.text();
    specBody.innerHTML = renderMarkdown(versionSlice(markdown));
    stampHeadingIds(specBody);
    specDialog.showModal();
    if (heading) {
        const target = specBody.querySelector("#" + CSS.escape(headingId(heading)));
        if (target) target.scrollIntoView();
    }
}

document.querySelectorAll("[data-version]").forEach((button) => {
    button.addEventListener("click", () => {
        version = Number(button.dataset.version);
        document.querySelectorAll("[data-version]").forEach((item) => item.classList.toggle("on", item === button));
        document.querySelector("#gen-label").textContent = `Gen ${version}`;
        recompute();
    });
});

document.querySelectorAll("[data-encoding]").forEach((button) => {
    button.addEventListener("click", () => {
        encoding = button.dataset.encoding;
        document.querySelectorAll("[data-encoding]").forEach((item) => item.classList.toggle("on", item === button));
        input.placeholder = encoding === "hex" ? "a7  or  0xA7" : "hello";
        recompute();
    });
});

document.querySelector("#play").addEventListener("click", () => void play());
document.querySelector("#step-through").addEventListener("click", () => enterTeach());
document.querySelector("#step").addEventListener("click", () => {
    if (!teaching) enterTeach();
    else void stepBy(1);
});
document.querySelector("#reset").addEventListener("click", () => {
    job += 1;
    playing = false;
    solving = false;
    busy = false;
    cursor = -1;
    setTeaching(false);
    showFace(solved);
    showStatus(caption());
});
document.querySelector("#digest-btn").addEventListener("click", async () => {
    try {
        await navigator.clipboard.writeText(digestEl.textContent);
        showStatus("Digest copied");
    } catch {
        errorEl.textContent = "Could not copy the digest.";
    }
});
document.querySelector("#solve").addEventListener("click", () => void solve());
document.querySelector("#spec-btn").addEventListener("click", () => void openSpec().catch((err) => {
    errorEl.textContent = err.message;
}));
document.querySelector("#spec-close").addEventListener("click", () => specDialog.close());
input.addEventListener("input", () => recompute());

document.querySelectorAll("[data-jump]").forEach((button) => {
    button.addEventListener("click", () => {
        const jump = button.dataset.jump;
        if (jump === "back") void stepBy(-1);
        else if (jump === "fwd") void stepBy(1);
        else if (jump === "stage-back") void jumpTo(cursor < 0 ? -1 : nextGroup(trace, Math.max(0, cursor), stageKey, -1), false);
        else if (jump === "stage-fwd") void jumpTo(cursor < 0 ? 0 : nextGroup(trace, cursor, stageKey, 1), false);
        else if (jump === "round-back") void jumpTo(cursor < 0 ? -1 : nextGroup(trace, Math.max(0, cursor), roundKey, -1), false);
        else if (jump === "round-fwd") void jumpTo(cursor < 0 ? 0 : nextGroup(trace, cursor, roundKey, 1), false);
    });
});

bindTeachKeys({
    step: (dir) => { if (teaching) void stepBy(dir); },
    stage: (dir) => { if (teaching && cursor >= 0) void jumpTo(nextGroup(trace, cursor, stageKey, dir), false); },
    home: () => { if (teaching) void jumpTo(0, false); },
    end: () => { if (teaching) void jumpTo(trace.length - 1, false); },
});

showFace(solved);
recompute();
