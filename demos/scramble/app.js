import { scramble_v1, scramble_v2, update, evaluate, solved_facelets } from "./generated/scramble.mjs";
import { mountCube } from "./view.js";
import { SOLVED_FACELETS, applyMove, isSolved, shortSolve, toCubejs, flipU } from "./cube.js";

const canvas = document.querySelector("canvas");
const input = document.querySelector("#message");
const status = document.querySelector("#status");
const digestEl = document.querySelector("#digest");
const errorEl = document.querySelector("#error");
const specDialog = document.querySelector("#spec");
const specBody = document.querySelector("#spec-body");
const speed = document.querySelector("#speed");

const view = mountCube(canvas);
const solved = solved_facelets();
if (solved !== SOLVED_FACELETS) {
    throw new Error("The demo cube and the reference cube disagree on the solved pose.");
}

let version = 2;
let encoding = "text";
let trace = [];
let facelets = solved;
let cursor = -1;
let playing = false;
let solving = false;
let job = 0;
let solverReady = false;

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

function recompute() {
    job += 1;
    playing = false;
    solving = false;
    errorEl.textContent = "";
    let bytes;
    try {
        bytes = bytesOf(input.value);
    } catch (err) {
        errorEl.textContent = err.message;
        return;
    }
    const state = version === 2 ? scramble_v2() : scramble_v1();
    update(state, bytes);
    const result = evaluate(state);
    trace = result.trace;
    digestEl.textContent = digestHex(result.digest);
    cursor = -1;
    showFace(solved);
    showStatus(caption());
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
    showStatus(caption());
    return true;
}

async function play() {
    if (playing || solving) return;
    playing = true;
    const token = job;
    while (playing && token === job && cursor < trace.length - 1) {
        const ok = await playStep(token);
        if (!ok) break;
    }
    playing = false;
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
            html += `<h3>${inline(line.slice(4))}</h3>`;
            i += 1;
            continue;
        }
        if (line.startsWith("## ")) {
            html += `<h2>${inline(line.slice(3))}</h2>`;
            i += 1;
            continue;
        }
        if (line.startsWith("# ")) {
            html += `<h1>${inline(line.slice(2))}</h1>`;
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

async function openSpec() {
    const response = await fetch("./SPEC.md");
    if (!response.ok) throw new Error("The specification file is missing. Run tools/build.sh.");
    const markdown = await response.text();
    specBody.innerHTML = renderMarkdown(versionSlice(markdown));
    specDialog.showModal();
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
document.querySelector("#step").addEventListener("click", () => {
    playing = false;
    const token = ++job;
    void playStep(token);
});
document.querySelector("#reset").addEventListener("click", () => {
    job += 1;
    playing = false;
    solving = false;
    cursor = -1;
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

showFace(solved);
recompute();
