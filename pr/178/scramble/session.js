import { solved_facelets } from "./generated/scramble.mjs";
import { hashMessage } from "./hash.js";
import { SOLVED_FACELETS, applyMove, isSolved, shortSolve, toCubejs, flipU, parseMove } from "./cube.js";
import { mapTraceToAlg, prefixAlg, projectAlgForPuzzle } from "../playroom/scramble-alg.js";
import {
    normalizePuzzleId,
    playroomDebugEnabled,
    puzzleHashes,
    resolveProductPuzzleId,
    writePuzzleSearchParam,
} from "../playroom/puzzles.js";
import { bindGrowFields } from "../shared/grow-field.js";
import { bindCappedInput } from "../shared/input-cap.js";
import { createLiveDigest } from "../shared/live-digest.js";
import {
    bindSegmented,
    bindTransport,
    openSpec,
    renderTeachCard,
    sessionScope,
    syncJumpButtons,
    teachPosition,
} from "../shared/session.js";
import { colorName, renderOutline } from "../shared/teach.js";

// Bounded by generated-module speed (Gen 2 ≈ 5 s at 4 KiB);
// rises as the spec/sudoc speedups land.
export const FILE_MAX_BYTES = 4 * 1024;
// A file's Digest and walk while it hashes: none yet.
const HASHING = { digest: [], trace: [] };

function formatSize(bytes) {
    return bytes < 1024 ? `${bytes} B` : `${+(bytes / 1024).toFixed(1)} KiB`;
}

const V2_TURNS = {
    0: "U R", 1: "U F", 2: "U L", 3: "U B",
    4: "D R", 5: "D F", 6: "R U", 7: "R D",
    8: "F U", 9: "F D", A: "B U", B: "F R",
    C: "L U", D: "F L", E: "R F", F: "R B",
};

export function createScrambleSession({
    view,
    specUrl,
    root = document,
    exposeTeach = false,
    puzzle = "3x3x3",
    swapPuzzle,
} = {}) {
    const { abort, listen, $, $$ } = sessionScope(root);

    const input = $("#message");
    const status = $("#status");
    const digestEl = $("#digest");
    const errorEl = $("#error");
    const speed = $("#speed");
    const teachEl = $("#teach");
    const tapeEl = $("#tape");
    const outlineEl = $("#outline");
    const ioNote = $("#io-note");
    const fileInput = $("#message-file-input");
    const fileChip = $("#message-file");
    bindGrowFields(root);

    const solved = solved_facelets();
    if (solved !== SOLVED_FACELETS) {
        throw new Error("The demo cube and the reference cube disagree on the solved pose.");
    }

    let version = 2;
    let encoding = "text";
    let puzzleId = resolveProductPuzzleId(puzzle);
    let trace = [];
    let mappedAlg = mapTraceToAlg([]);
    let projectedAlg = projectAlgForPuzzle(mappedAlg, puzzleId);
    let facelets = solved;
    let cursor = -1;
    let playing = false;
    let solving = false;
    let busy = false;
    let teaching = false;
    let job = 0;
    let solverReady = false;
    let messageBytes = [];
    let fileBytes = null;
    let fileAbort = null;
    const live = createLiveDigest();

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

    function digestValue() {
        if (!digestEl) return "";
        return digestEl.matches("input, textarea") ? digestEl.value : digestEl.textContent;
    }

    function setDigest(text) {
        if (!digestEl) return;
        if (digestEl.matches("input, textarea")) digestEl.value = text;
        else digestEl.textContent = text;
    }

    function digestHex(bytes) {
        const hex = bytes.map((b) => b.toString(16).padStart(2, "0")).join("").toUpperCase().slice(1);
        return hex ? `0x${hex}` : "";
    }

    function symbolWord(step) {
        return trace
            .filter((item) => item.kind === "move" && item.block === step.block)
            .sort((a, b) => a.index - b.index)
            .map((item) => item.move)
            .join("");
    }

    function viewedIndex() {
        return teaching ? cursor + 1 : cursor;
    }

    function captionFor(step) {
        if (!step) return "Solved start · white up, green front, red right";
        if (step.kind === "ruleB") return `Rule B · ${step.up} up, ${step.front} front`;
        if (step.kind === "closer") return `Closer · ${step.move}`;
        if (step.kind === "canonicalize") return "Seat white up, green front";
        if (version === 2) return `Symbol ${step.block + 1} · ${step.nybble} → ${symbolWord(step)} · ${step.move}`;
        return `Block ${step.block + 1} · ${step.nybble} → ${step.move}`;
    }

    function caption() {
        const visual = hashesThisPuzzle() ? "" : "Visual puzzle · ";
        if (teaching && viewedIndex() >= trace.length && trace.length) {
            return visual + (digestValue() ? `Digest · ${digestValue()}` : "The seated pose is the digest.");
        }
        const step = teaching
            ? (viewedIndex() < trace.length ? trace[viewedIndex()] : null)
            : (cursor < 0 ? null : trace[cursor]);
        return visual + captionFor(step);
    }

    function showStatus(text) {
        status.textContent = text;
    }

    function usesTimeline() {
        return typeof view.setAlg === "function" && typeof view.playLeaves === "function";
    }

    function hashesThisPuzzle() {
        return puzzleHashes(puzzleId);
    }

    function syncPuzzleChrome() {
        $$("[data-puzzle]").forEach((button) => {
            button.classList.toggle("on", normalizePuzzleId(button.dataset.puzzle) === puzzleId);
        });
        const note = $("#puzzle-note");
        if (note) {
            note.hidden = hashesThisPuzzle() || !playroomDebugEnabled();
            note.textContent = hashesThisPuzzle()
                ? ""
                : "Digest is 3×3 Scramble. This puzzle is visual.";
        }
        if (root?.dataset) root.dataset.puzzle = puzzleId;
        if (root.querySelector("[data-puzzle]")) {
            try {
                history.replaceState(null, "", writePuzzleSearchParam(puzzleId));
            } catch {
                // file: or test hosts may not have a URL
            }
        }
    }

    function showFace(next) {
        facelets = next;
        if (!usesTimeline()) view.paint?.(next);
    }

    function bindAlg() {
        if (!usesTimeline()) return;
        view.setAlg(projectedAlg.alg);
        view.setTempo?.(Number(speed?.value) || 1.4);
        void view.jumpToLeaf?.(-1);
    }

    function bindTimeline() {
        mappedAlg = mapTraceToAlg(trace);
        projectedAlg = projectAlgForPuzzle(mappedAlg, puzzleId);
        bindAlg();
    }

    function ensureTimeline() {
        live.ensureTimeline(bindTimeline);
    }

    function jumpViewToCursor() {
        if (!usesTimeline()) return;
        if (cursor < 0) void view.jumpToLeaf(-1);
        else void view.jumpToLeaf((projectedAlg.ranges[cursor]?.to ?? 1) - 1);
    }

    function settleView(opts) {
        view.settle?.(opts);
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
        const openAt = viewedIndex();
        for (const [title, items] of byRound) {
            sections.push({ title, items, open: items.some((item) => item.index === openAt) });
        }
        return sections;
    }

    function annotate(step, index) {
        const n = trace.length;
        if (!step && n && index >= n) {
            return {
                kicker: `done · ${n} steps`,
                title: "Seated digest",
                math: digestValue() || "The seated pose is the digest.",
                why: "The seated pose is the digest.",
                spec: "Closer and seat",
            };
        }
        const pos = !step || index < 0 ? `start · ${n} steps` : `step ${index + 1} of ${n}`;
        if (!step || index < 0) {
            return {
                kicker: pos,
                title: "Solved start",
                math: "White up, green front, red right.",
                why: "Step walks the padded tape one turn at a time.",
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
                    ? (version === 2
                        ? (step.nybble === "8"
                            ? "Evaluate appends marker nybble 8, then the cycle 6 0 7 1 until the tape is at least 12 nybbles."
                            : "Padding filler from the cycle 6 0 7 1 (not message). Tape must reach at least 12 nybbles.")
                        : (step.nybble === "8"
                            ? "Evaluate appends marker nybble 8, then n = (8 − len mod 8) mod 8 of 6 0 7 1 8 2 9 3, then that octet until the tape is at least 24 nybbles."
                            : "Padding filler from the cycle 6 0 7 1 8 2 9 3 (not message). Tape must reach at least 24 nybbles."))
                    : (version === 2
                        ? "Each nybble is two clockwise quarter turns, then Rule B."
                        : "Each nybble is one clockwise quarter turn. A block is 8 nybbles, then Rule B."),
                spec: version === 2 ? "scramble_v2" : "scramble_v1",
            };
        }
        if (step.kind === "ruleB") {
            return {
                kicker: pos,
                title: "Rule B",
                math: `Cubie (1,1,1) reads ${colorName(step.up)} up, ${colorName(step.front)} front.`,
                why: "Whole-cube rotation: seat the face center of that up color on Up (+Y) and the face center of that front color on Front (+Z).",
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

    function applyHighlight(step) {
        if (!step) {
            view.clearHighlights();
            return;
        }
        if (step.kind === "move" || step.kind === "closer") view.highlightLayer?.(parseMove(step.move).face);
        else if (step.kind === "ruleB") view.highlightRuleB?.(facelets, step.up, step.front);
        else if (step.kind === "canonicalize") view.highlightRuleB?.(facelets, "W", "G");
        else view.clearHighlights?.();
    }

    function refreshTeach() {
        const viewI = viewedIndex();
        const step = viewI >= 0 && viewI < trace.length ? trace[viewI] : null;
        const activeBlock = step && (step.kind === "move" || step.kind === "ruleB") ? step.block : -1;
        renderTape(activeBlock);
        const note = annotate(step, step ? viewI : (viewI >= trace.length && trace.length ? viewI : -1));
        renderTeachCard($("#teach-card"), note, showSpec);
        $("#teach-pos").textContent = teachPosition(viewI, trace.length);
        renderOutline(outlineEl, outlineSections(), step ? String(viewI) : "", (index) => {
            void jumpTo(index - 1, false);
        });
        syncJumpButtons(root, cursor, trace.length);
    }

    function setTeaching(on) {
        teaching = on;
        if (teachEl) teachEl.hidden = !on;
        if (outlineEl) outlineEl.hidden = !on;
        if (!on) view.clearHighlights?.();
    }

    function showPaused() {
        if (teaching) {
            const viewI = viewedIndex();
            if (viewI >= 0 && viewI < trace.length) {
                showFace(viewI === 0 ? solved : trace[viewI - 1].facelets);
                applyHighlight(trace[viewI]);
            } else if (trace.length) {
                showFace(trace[trace.length - 1].facelets);
                applyHighlight(null);
            } else {
                showFace(solved);
                applyHighlight(null);
            }
            showStatus(caption());
            refreshTeach();
            jumpViewToCursor();
            return;
        }
        if (cursor < 0) showFace(solved);
        else showFace(trace[cursor].facelets);
        showStatus(caption());
        jumpViewToCursor();
    }

    // Digest only. cubing.js setAlg / leave-trace wait for Play / Step / Skip to end.
    function showResult(bytes, result) {
        job += 1;
        markPlay(false);
        solving = false;
        busy = false;
        settleView();
        errorEl.textContent = "";
        messageBytes = bytes;
        trace = result.trace;
        mappedAlg = { alg: "", units: [], ranges: [] };
        projectedAlg = { alg: "", units: [], ranges: [], hash: hashesThisPuzzle(), dropped: 0 };
        setDigest(digestHex(result.digest));
        cursor = -1;
        live.afterDigest();
        setTeaching(false);
        view.pauseTimeline?.();
        view.resetTimeline?.();
        showFace(solved);
        showStatus(caption());
    }

    // Typed Message only; a picked file's Digest comes from hashFile.
    function refreshDigest() {
        if (fileBytes) return;
        let bytes;
        try {
            bytes = bytesOf(input.value);
        } catch (err) {
            errorEl.textContent = err.message;
            return;
        }
        showResult(bytes, hashMessage(version, bytes));
    }

    // Aborts the previous file read / hash; the new one stops once its signal aborts.
    function nextFileJob() {
        fileAbort?.abort();
        fileAbort = new AbortController();
        return fileAbort.signal;
    }

    // One update + evaluate on the generated module, in a Worker. If the Worker fails,
    // the page runs it and blocks (up to ~5 s at the cap in Gen 2).
    async function hashFile(signal) {
        const bytes = fileBytes;
        showResult(bytes, HASHING);
        fileChip.classList.add("is-hashing");
        let worker;
        try {
            const result = await new Promise((resolve) => {
                const fallback = () => resolve(new Promise((ok) => ok(hashMessage(version, bytes))));
                try {
                    const url = new URL("./hash-worker.js", import.meta.url);
                    worker = new Worker(url, { type: "module" });
                } catch {
                    return fallback();
                }
                signal.addEventListener("abort", () => worker.terminate());
                worker.onmessage = (event) => resolve(event.data);
                worker.onerror = fallback;
                worker.postMessage({ version, bytes });
            });
            if (!signal.aborted) showResult(bytes, result);
        } catch (err) {
            if (!signal.aborted) errorEl.textContent = err.message || "Could not hash this file.";
        } finally {
            worker?.terminate();
            if (!signal.aborted) fileChip.classList.remove("is-hashing");
        }
    }

    async function applyFile(file) {
        if (file.size > FILE_MAX_BYTES) {
            errorEl.textContent = `Files can be up to ${formatSize(FILE_MAX_BYTES)}.`;
            return;
        }
        const signal = nextFileJob();
        const bytes = new Uint8Array(await file.arrayBuffer());
        if (signal.aborted) return;
        $("#message-file-name").textContent = `${file.name} · ${formatSize(file.size)}`;
        fileChip.hidden = false;
        fileBytes = bytes;
        await hashFile(signal);
    }

    function clearFile() {
        fileAbort?.abort();
        fileBytes = null;
        fileChip.hidden = true;
        refreshDigest();
    }

    function duration(kind) {
        const pace = Number(speed.value);
        return (kind === "move" || kind === "closer" ? 700 : 900) / pace;
    }

    async function playStep(token) {
        if (cursor >= trace.length - 1) return false;
        const step = trace[cursor + 1];
        const from = facelets;
        const range = projectedAlg.ranges[cursor + 1];
        if (usesTimeline() && range) {
            await view.playLeaves(range.from, range.to);
        } else if (step.kind === "move" || step.kind === "closer") {
            await view.animateMove(step.move, duration(step.kind));
        } else if (step.kind === "ruleB") {
            await view.animateReorient(from, step.up, step.front, duration(step.kind));
        } else {
            await view.animateReorient(from, "W", "G", duration(step.kind));
        }
        if (token !== job) return false;
        cursor += 1;
        if (teaching) {
            showPaused();
            return true;
        }
        showFace(step.facelets);
        showStatus(caption());
        return true;
    }

    function markPlay(on) {
        playing = on;
        const playBtn = $("#play");
        playBtn?.classList.toggle("is-playing", on);
        if (playBtn?.classList.contains("icon-btn")) {
            playBtn.setAttribute("aria-label", on ? "Pause" : "Play");
            playBtn.title = on ? "Pause" : "Play";
        }
    }

    async function play() {
        if (solving || busy || !trace.length) return;
        if (playing) {
            markPlay(false);
            return;
        }
        ensureTimeline();
        markPlay(true);
        const token = job;
        while (playing && token === job && cursor < trace.length - 1) {
            const ok = await playStep(token);
            if (!ok) break;
        }
        markPlay(false);
    }

    function seek(index) {
        job += 1;
        busy = false;
        markPlay(false);
        cursor = index;
        showPaused();
    }

    async function jumpTo(index, animate) {
        if (trace.length === 0 || busy) return;
        const next = Math.max(-1, Math.min(trace.length - 1, index));
        if (animate && next === cursor + 1) {
            markPlay(false);
            busy = true;
            const token = job;
            await playStep(token);
            busy = false;
            return;
        }
        seek(next);
    }

    async function stepBy(dir) {
        if (!teaching) enterTeach();
        if (dir < 0) return jumpTo(cursor - 1, false);
        return jumpTo(cursor + 1, true);
    }

    function enterTeach() {
        if (trace.length === 0) refreshDigest();
        if (!trace.length) return;
        ensureTimeline();
        setTeaching(true);
        cursor = -1;
        markPlay(false);
        showPaused();
    }

    function skipToEnd() {
        if (solving) return;
        if (!trace.length) refreshDigest();
        if (!trace.length) return;
        ensureTimeline();
        setTeaching(false);
        seek(trace.length - 1);
        settleView();
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
        if (!hashesThisPuzzle()) {
            errorEl.textContent = "Solve is 3×3 only.";
            return;
        }
        if (solving) return;
        markPlay(false);
        solving = true;
        setTeaching(false);
        ensureTimeline();
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
            if (usesTimeline() && view.playMoves) {
                await view.playMoves(moves, { setup: prefixAlg(mappedAlg, cursor) });
                if (token !== job) return;
                view.setAlg(mappedAlg.alg);
                void view.jumpToLeaf?.(-1);
                current = solved;
                showFace(solved);
            } else {
                for (let i = 0; i < moves.length; i++) {
                    if (token !== job) return;
                    showStatus(`Solve ${i + 1}/${moves.length} · ${moves[i]}`);
                    await view.animateMove(moves[i], duration("move"));
                    if (token !== job) return;
                    current = applyMove(current, moves[i]);
                    showFace(current);
                }
            }
            if (!isSolved(current)) throw new Error("Solver returned a sequence that does not solve this cube.");
            showStatus(`Solve · ${moves.length} moves`);
        } catch (err) {
            if (token === job) errorEl.textContent = err.message || "Could not solve this cube.";
        } finally {
            if (token === job) solving = false;
        }
    }

    function versionSlice(markdown) {
        const start = markdown.indexOf("## scramble_v1");
        const mid = markdown.indexOf("## scramble_v2");
        const common = markdown.slice(0, start);
        const section = version === 1 ? markdown.slice(start, mid) : markdown.slice(mid);
        return common + section;
    }

    function showSpec(heading) {
        openSpec(root, specUrl, heading, versionSlice).catch((err) => {
            errorEl.textContent = err.message;
        });
    }

    bindSegmented(root, "version", (value) => {
        version = Number(value);
        const genLabel = $("#gen-label");
        if (genLabel) genLabel.textContent = `Gen ${version}`;
        if (fileBytes) void hashFile(nextFileJob());
        else refreshDigest();
    }, listen);

    bindSegmented(root, "encoding", (value) => {
        encoding = value;
        input.placeholder = encoding === "hex" ? "a7  or  0xA7" : "hello";
        refreshDigest();
    }, listen);

    async function applyPuzzle(nextRaw) {
        const nextId = resolveProductPuzzleId(nextRaw);
        if (nextId === puzzleId) {
            syncPuzzleChrome();
            return;
        }
        job += 1;
        markPlay(false);
        solving = false;
        busy = false;
        settleView();
        errorEl.textContent = "";
        if (typeof swapPuzzle === "function") {
            try {
                const nextView = await swapPuzzle(nextId);
                if (nextView) view = nextView;
            } catch (err) {
                errorEl.textContent = err.message || "Could not switch puzzle.";
                return;
            }
        }
        puzzleId = nextId;
        cursor = -1;
        syncPuzzleChrome();
        live.dropTimeline();
        if (teaching) {
            ensureTimeline();
            refreshTeach();
        }
        showFace(solved);
        showStatus(caption());
    }

    $$("[data-puzzle]").forEach((button) => {
        button.addEventListener("click", () => void applyPuzzle(button.dataset.puzzle), listen);
    });

    function reset() {
        job += 1;
        markPlay(false);
        solving = false;
        busy = false;
        cursor = -1;
        setTeaching(false);
        settleView();
        showFace(solved);
        jumpViewToCursor();
        showStatus(caption());
    }

    speed?.addEventListener("input", () => {
        view.setTempo?.(Number(speed.value) || 1);
    }, listen);
    $("#digest-btn")?.addEventListener("click", async () => {
        try {
            await navigator.clipboard.writeText(digestValue());
            showStatus("Digest copied");
        } catch {
            errorEl.textContent = "Could not copy the digest.";
        }
    }, listen);
    $("#solve")?.addEventListener("click", () => void solve(), listen);
    bindCappedInput(input, {
        noteEl: ioNote,
        onChange: () => refreshDigest(),
        signal: abort.signal,
    });
    $("#message-file-btn").addEventListener("click", () => fileInput.click(), listen);
    fileInput.addEventListener("change", () => {
        const file = fileInput.files[0];
        fileInput.value = "";
        if (file) void applyFile(file);
    }, listen);
    $("#message-file-clear").addEventListener("click", clearFile, listen);

    bindTransport(root, {
        play,
        step: () => {
            if (!teaching) enterTeach();
            else void stepBy(1);
        },
        skipToEnd,
        reset,
        showSpec,
        trace: () => trace,
        teaching: () => teaching,
        viewedIndex,
        stepBy,
        jumpTo,
        stageKey,
        roundKey,
    }, listen);

    showFace(solved);
    syncPuzzleChrome();
    refreshDigest();

    const api = {
        enterTeach,
        recompute: refreshDigest,
        setView(next) {
            if (next) view = next;
            live.dropTimeline();
            if (teaching) ensureTimeline();
        },
        setPuzzle(id) {
            return applyPuzzle(id);
        },
        reset,
        dispose() {
            fileAbort?.abort();
            job += 1;
            markPlay(false);
            solving = false;
            busy = false;
            setTeaching(false);
            settleView({ snap: true });
            view.pauseTimeline?.();
            view.resetTimeline?.();
            view.clearHighlights?.();
            abort.abort();
            if (exposeTeach && window.__teach) delete window.__teach;
        },
    };

    if (exposeTeach) {
        Object.assign(window, {
            __teach: {
                enter: enterTeach,
                jumpView: (index) => jumpTo(index - 1, false),
                steps: () => trace.map((step, index) => ({
                    index,
                    kind: step.kind,
                    nybble: step.nybble,
                    block: step.block,
                    move: step.move,
                    up: step.up,
                    front: step.front,
                })),
            },
        });
    }

    return api;
}
