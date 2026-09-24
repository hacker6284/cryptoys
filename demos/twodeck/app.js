import { ecb_encrypt, ecb_decrypt, ctr_encrypt, ctr_decrypt, trace_ecb, trace_ctr, trace_decrypt, trace_ctr_decrypt } from "./generated/twodeck.mjs";
import { mountTable } from "./view.js";
import { decksToHex, decksToText, hexToDecks, randomHex, textToDecks, textToKey, textToNonce } from "./cards.js";

const messageEl = document.querySelector("#message");
const keyEl = document.querySelector("#key");
const nonceEl = document.querySelector("#nonce");
const outputEl = document.querySelector("#output");
const errorEl = document.querySelector("#error");
const nonceField = document.querySelector("#nonce-field");
const captionEl = document.querySelector("#caption");
const speedEl = document.querySelector("#speed");
const inputLabel = document.querySelector("#input-label");
const outputLabel = document.querySelector("#output-label");
const copyButton = document.querySelector("#copy");

const view = await mountTable(
    document.querySelector("canvas"),
    textToDecks(messageEl.value)[0],
    textToKey(keyEl.value),
);

let mode = "ecb";
let direction = "encrypt";
let trace = [];
let cursor = -1;
let playing = false;
let job = 0;
let laidEnd = null;

function setError(text) {
    errorEl.textContent = text;
}

function stopPlay() {
    playing = false;
    job += 1;
}

function readNonce() {
    return textToNonce(nonceEl.value);
}

function caption(step) {
    if (step.kind === "sumrow" && step.amount < 0) return `${step.label} · inverse SumRanks row ${step.row + 1} · back ${-step.amount}`;
    if (step.kind === "sumcol" && step.amount < 0) return `${step.label} · inverse SumRanks column ${step.col + 1} · back ${-step.amount}`;
    if (step.kind === "sumrow") return `${step.label} · SumRanks row ${step.row + 1} · sum ${step.total} → ${step.amount}`;
    if (step.kind === "sumcol") return `${step.label} · SumRanks column ${step.col + 1} · sum ${step.total} → ${step.amount}`;
    if (step.kind === "shift" && step.amount === 0) return `${step.label} · ShiftRows · row 1 stays`;
    if (step.kind === "shift" && step.amount < 0) return `${step.label} · inverse ShiftRows · row ${step.row + 1} slides back ${-step.amount}`;
    if (step.kind === "shift") return `${step.label} · ShiftRows · row ${step.row + 1} slides ${step.amount}`;
    if (step.kind === "reset" && step.amount > 0) return `${step.label} · ${step.amount} passes from here`;
    if (step.kind === "reset") return step.label;
    if (step.kind === "take") return `${step.label} · inverse GridCycle lifts a card`;
    if (step.kind === "scan") return `${step.label} · GridCycle overflow · scanning row ${step.row + 1}`;
    if (step.kind === "place" && step.flag === 1) return `${step.label} · GridCycle overflow into (${step.row + 1}, ${step.col + 1})`;
    if (step.kind === "pass" && step.flag === 2) return `${step.label} · rank cut on the key pile`;
    if (step.kind === "pass" && step.flag === 1) return `${step.label} · suit cut, then rank cut on the hand`;
    return step.label;
}

function applyLabels() {
    const encrypting = direction === "encrypt";
    inputLabel.textContent = encrypting ? "Plaintext" : "Ciphertext";
    outputLabel.textContent = encrypting ? "Ciphertext" : "Plaintext";
    copyButton.textContent = encrypting ? "Copy ciphertext" : "Copy plaintext";
}

function preview() {
    setError("");
    stopPlay();
    laidEnd = null;
    trace = [];
    cursor = -1;
    let key;
    try {
        key = textToKey(keyEl.value);
    } catch (err) {
        setError(err instanceof Error ? err.message : "That key could not be read.");
        return;
    }
    try {
        if (direction === "encrypt") {
            const blocks = textToDecks(messageEl.value);
            view.showDecks(blocks[0], key);
            const extra = blocks.length > 1 ? ` First of ${blocks.length} blocks.` : "";
            captionEl.textContent = `Plaintext on the left. Key on the right.${extra}`;
            return;
        }
        if (!messageEl.value.trim()) {
            captionEl.textContent = "Key on the right. Ciphertext goes in the input.";
            return;
        }
        const blocks = hexToDecks(messageEl.value);
        view.showDecks(blocks[0], key);
        const extra = blocks.length > 1 ? ` First of ${blocks.length} blocks.` : "";
        captionEl.textContent = `Ciphertext on the left. Key on the right.${extra}`;
    } catch (err) {
        if (direction === "encrypt") {
            setError(err instanceof Error ? err.message : "That input could not be read.");
        }
    }
}

async function playFrom(start) {
    playing = true;
    const token = ++job;
    for (let i = start; i < trace.length; i++) {
        if (!playing || token !== job) return;
        cursor = i;
        captionEl.textContent = caption(trace[i]);
        await view.play(trace[i], Number(speedEl.value));
    }
    playing = false;
    if (token === job && laidEnd) {
        view.showDecks(laidEnd.blocks[0], laidEnd.key);
        captionEl.textContent = laidEnd.caption;
    }
}

async function start() {
    setError("");
    stopPlay();
    laidEnd = null;
    try {
        const key = textToKey(keyEl.value);
        const nonce = mode === "ctr" ? readNonce() : [];
        if (direction === "encrypt") {
            const blocks = textToDecks(messageEl.value);
            const result = mode === "ecb" ? ecb_encrypt(blocks, key) : ctr_encrypt(blocks, key, nonce);
            outputEl.value = decksToHex(result);
            trace = mode === "ecb" ? trace_ecb([blocks[0]], key) : trace_ctr([blocks[0]], key, nonce);
            cursor = -1;
            const extra = result.length > 1 ? ` First of ${result.length} blocks.` : "";
            laidEnd = { blocks: result, key, caption: `Ciphertext on the left. Key on the right.${extra}` };
            view.showDecks(blocks[0], key);
            captionEl.textContent = `Encrypting.${blocks.length > 1 ? ` Hex has ${blocks.length} blocks. The table plays the first.` : ""}`;
            playFrom(0);
        } else {
            const blocks = hexToDecks(messageEl.value);
            const result = mode === "ecb" ? ecb_decrypt(blocks, key) : ctr_decrypt(blocks, key, nonce);
            outputEl.value = decksToText(result);
            trace = mode === "ecb" ? trace_decrypt(blocks[0], key) : trace_ctr_decrypt([blocks[0]], key, nonce);
            cursor = -1;
            const extra = result.length > 1 ? ` First of ${result.length} blocks.` : "";
            laidEnd = { blocks: result, key, caption: `Plaintext on the left. Key on the right.${extra}` };
            view.showDecks(blocks[0], key);
            const walk = mode === "ecb"
                ? "The master key is dealt again and passed 6 times, then 5, then 4, then 3, then 2, then 1."
                : "The counter is encrypted, then the ciphertext is inverse-composed with that keystream.";
            const more = blocks.length > 1 ? ` The table plays the first of ${blocks.length} blocks.` : "";
            captionEl.textContent = `Decrypting. ${walk}${more}`;
            playFrom(0);
        }
    } catch (err) {
        setError(err instanceof Error ? err.message : "That input could not be read.");
    }
}

document.querySelectorAll("[data-mode]").forEach((button) => {
    button.addEventListener("click", () => {
        mode = button.dataset.mode;
        document.querySelectorAll("[data-mode]").forEach((item) => item.classList.toggle("on", item === button));
        nonceField.hidden = mode !== "ctr";
    });
});

document.querySelectorAll("[data-direction]").forEach((button) => {
    button.addEventListener("click", () => {
        const next = button.dataset.direction;
        if (next === direction) return;
        stopPlay();
        const typed = messageEl.value;
        messageEl.value = outputEl.value;
        outputEl.value = typed;
        direction = next;
        document.querySelectorAll("[data-direction]").forEach((item) => item.classList.toggle("on", item === button));
        applyLabels();
        preview();
    });
});

document.querySelector("#start").addEventListener("click", () => start());
document.querySelector("#stop").addEventListener("click", () => {
    stopPlay();
});
document.querySelector("#step").addEventListener("click", async () => {
    if (trace.length === 0) {
        setError("Press Start first.");
        return;
    }
    setError("");
    stopPlay();
    cursor = Math.min(trace.length - 1, cursor + 1);
    captionEl.textContent = caption(trace[cursor]);
    await view.play(trace[cursor], Number(speedEl.value));
});
document.querySelector("#random-key").addEventListener("click", () => {
    keyEl.value = "0x" + randomHex(14);
    preview();
});
document.querySelector("#random-nonce").addEventListener("click", () => {
    nonceEl.value = "0x" + randomHex(8);
    setError("");
});
document.querySelector("#copy").addEventListener("click", async () => {
    if (!outputEl.value) {
        setError(direction === "encrypt" ? "There is no ciphertext to copy." : "There is no plaintext to copy.");
        return;
    }
    try {
        await navigator.clipboard.writeText(outputEl.value);
        setError("");
    } catch {
        setError("Could not copy the ciphertext.");
    }
});
messageEl.addEventListener("input", preview);
keyEl.addEventListener("input", preview);

const specDialog = document.querySelector("#spec");
const specBody = document.querySelector("#spec-body");

function renderMarkdown(markdown) {
    const lines = markdown.replace(/\r\n/g, "\n").split("\n");
    let html = "";
    let i = 0;
    const esc = (s) => s.replace(/[&<>]/g, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;" }[c]));
    const inline = (s) => esc(s)
        .replace(/`([^`]+)`/g, "<code>$1</code>")
        .replace(/\*\*([^*]+)\*\*/g, "<strong>$1</strong>")
        .replace(/\[([^\]]+)\]\(([^)]+)\)/g, '<a href="$2">$1</a>');
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
            const cells = (row) => row.split("|").slice(1, -1).map((cell) => cell.trim());
            const head = cells(rows[0]);
            const body = rows.slice(2).map(cells);
            html += "<table><thead><tr>" + head.map((cell) => `<th>${inline(cell)}</th>`).join("") + "</tr></thead><tbody>";
            for (const row of body) html += "<tr>" + row.map((cell) => `<td>${inline(cell)}</td>`).join("") + "</tr>";
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

async function openSpec() {
    const response = await fetch("./SPEC.md");
    if (!response.ok) throw new Error("The specification file is missing. Run tools/build.sh.");
    specBody.innerHTML = renderMarkdown(await response.text());
    specDialog.showModal();
}

document.querySelector("#spec-btn").addEventListener("click", () => {
    openSpec().catch((err) => {
        setError(err instanceof Error ? err.message : "Could not open the specification.");
    });
});
document.querySelector("#spec-close").addEventListener("click", () => specDialog.close());
