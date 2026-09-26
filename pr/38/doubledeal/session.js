import { ecb_encrypt, ecb_decrypt, ctr_encrypt, ctr_decrypt, trace_ecb, trace_ctr, trace_decrypt, trace_ctr_decrypt } from "./generated/doubledeal.mjs";
import { decksToHex, decksToText, hexToDecks, randomHex, textToDecks, textToKey, textToNonce } from "./cards.js";
import {
    bindTeachKeys,
    cardName,
    headingId,
    nextGroup,
    renderOutline,
    setDisabled,
    stampHeadingIds,
} from "../shared/teach.js";

export function createDoubleDealSession({
    view,
    specUrl,
    root = document,
    exposeTeach = false,
    signal,
    liveDigest = false,
} = {}) {
    const abort = new AbortController();
    if (signal) {
        if (signal.aborted) abort.abort();
        else signal.addEventListener("abort", () => abort.abort(), { once: true });
    }
    const listen = { signal: abort.signal };
    const $ = (sel) => root.querySelector(sel);
    const $$ = (sel) => root.querySelectorAll(sel);

    const messageEl = $("#message");
    const keyEl = $("#key");
    const nonceEl = $("#nonce");
    const outputEl = $("#digest") || $("#output");
    const errorEl = $("#error");
    const nonceField = $("#nonce-field");
    const captionEl = $("#caption") || $("#status");
    const speedEl = $("#speed");
    const inputLabel = $("#input-label");
    const outputLabel = $("#output-label");
    const copyButton = $("#copy") || $("#digest-btn");
    const teachEl = $("#teach");
    const teachCard = $("#teach-card");
    const teachPos = $("#teach-pos");
    const outlineEl = $("#outline");

    let mode = "ecb";
    let direction = "encrypt";
    let trace = [];
    let cursor = -1;
    let playing = false;
    let busy = false;
    let teaching = false;
    let job = 0;
    let laidEnd = null;
    let snaps = null;
    let startMessage = null;
    let startKey = null;

    function outputValue() {
        if (!outputEl) return "";
        return outputEl.matches("input, textarea") ? outputEl.value : outputEl.textContent;
    }

    function setOutput(text) {
        if (!outputEl) return;
        if (outputEl.matches("input, textarea")) outputEl.value = text;
        else outputEl.textContent = text;
    }

    function setError(text) {
        if (errorEl) errorEl.textContent = text;
    }

    function stopPlay() {
        playing = false;
        job += 1;
        markPlay(false);
    }

    function markPlay(on) {
        playing = on;
        const playBtn = $("#play") || $("#start");
        playBtn?.classList.toggle("is-playing", on);
        if (playBtn?.classList.contains("icon-btn")) {
            playBtn.setAttribute("aria-label", on ? "Pause" : "Play");
            playBtn.title = on ? "Pause" : "Play";
        } else if (playBtn && playBtn.id === "play") {
            playBtn.textContent = on ? "Pause" : "Play";
        }
    }

    function readNonce() {
        return textToNonce(nonceEl?.value || "");
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
        if (step.kind === "pass" && step.flag === 2) return `${step.label} · proper rank cut on the key pile`;
        if (step.kind === "pass" && step.flag === 1) return `${step.label} · suit-rotate hand, then proper rank cut on the hand`;
        if (step.kind === "pass" && step.flag === 0) return `${step.label} · no proper rank cut`;
        if (step.kind === "unpass" && step.flag === 2) return `${step.label} · undo rank cut on the key pile`;
        if (step.kind === "unpass" && step.flag === 1) return `${step.label} · undo rank cut on the hand`;
        if (step.kind === "unpass") return step.label;
        return step.label;
    }

    function applyLabels() {
        const encrypting = direction === "encrypt";
        if (inputLabel) inputLabel.textContent = encrypting ? "Plaintext" : "Ciphertext";
        if (outputLabel) outputLabel.textContent = encrypting ? "Ciphertext" : "Plaintext";
        if (copyButton && !copyButton.classList.contains("icon-btn") && copyButton.id !== "digest-btn") {
            copyButton.textContent = "Copy";
        }
    }

    function stageKey(step) {
        if (step.kind === "place" || step.kind === "scan" || step.kind === "mark" || step.kind === "take") return `${step.label}::gridcycle`;
        if (step.kind === "sumrow") return `${step.label}::sumrow`;
        if (step.kind === "sumcol") return `${step.label}::sumcol`;
        if (step.kind === "shift") return `${step.label}::shift`;
        if (step.kind === "pass") return `${step.label}::pass`;
        if (step.kind === "unpass") return `${step.label}::unpass`;
        return `${step.label}::${step.kind}`;
    }

    function roundKey(step) {
        return step.label;
    }

    function specFor(step) {
        if (step.kind === "sumrow" || step.kind === "sumcol") return "4.2 SumRanks (SubBytes)";
        if (step.kind === "shift") return "4.3 ShiftRows";
        if (step.kind === "place" || step.kind === "scan" || step.kind === "mark" || step.kind === "take") return "3.5 GridCycle (MixColumns stand-in)";
        if (step.kind === "pass" || step.kind === "unpass") return "3.7 PassKey (F)";
        if (step.kind === "compose" || step.kind === "uncompose") return "3.6 Compose / InverseCompose";
        if (step.kind === "deal" || step.kind === "dealrm" || step.kind === "scoopcm" || step.kind === "scooprm") return "4.1 Deal / scoop conventions";
        if (step.kind === "reset") return "3.8 expand_keys";
        if (step.kind === "counter") return "5.2 CTR (pinned)";
        return "3.9 Rounds, encrypt, decrypt";
    }

    function viewedIndex() {
        return teaching ? cursor + 1 : cursor;
    }

    function isOpeningPlace(step) {
        const index = trace.indexOf(step);
        if (index <= 0) return step.row === 2 && step.col === 0;
        const prev = trace[index - 1];
        return prev.kind === "mark" && prev.label === step.label;
    }

    function finalNote(step, why) {
        if (String(step.label).includes("no GridCycle")) return `${why} Final round: SumRanks → ShiftRows → Compose; skip GridCycle.`;
        return why;
    }

    function passMath(step) {
        if (step.flag === 2) {
            return `Controller ${cardName(step.card)}. Suit-rotate the hand (if any), then proper rank cut on the key pile by ${step.total} (fallback). Controller on top of the key pile.`;
        }
        let math = `Controller ${cardName(step.card)} (suit ${step.row}, rank ${step.col}).`;
        if (step.amount > 0) math += ` Suit-rotate hand left by ${step.amount}.`;
        if (step.flag === 1) math += ` Proper rank cut on the hand by ${step.total}.`;
        if (step.flag === 0) math += ` No proper rank cut (hand empty or rank ≥ packet size).`;
        math += " Controller goes on top of the key pile.";
        return math;
    }

    function unpassMath(step) {
        const who = `Controller ${cardName(step.card)}.`;
        if (step.flag === 1) return `${who} Undo proper rank cut on the hand (bottom→top by rank), then undo suit-rotate on the hand; controller returns to the hand.`;
        if (step.flag === 2) return `${who} Undo proper rank cut on the key pile (bottom→top), then undo suit-rotate on the hand; controller returns to the hand.`;
        return `${who} No cut to undo; undo suit-rotate on the hand if needed; controller returns to the hand.`;
    }

    function analogue(step) {
        if (step.kind === "sumrow" || step.kind === "sumcol") return "SumRanks · SubBytes stand-in";
        if (step.kind === "shift") return "ShiftRows";
        if (step.kind === "place" || step.kind === "scan" || step.kind === "mark" || step.kind === "take") return "GridCycle · MixColumns stand-in";
        if (step.kind === "compose") return "Compose · AddRoundKey stand-in";
        if (step.kind === "uncompose") return "InverseCompose · AddRoundKey stand-in";
        if (step.kind === "pass") return "PassKey";
        if (step.kind === "unpass") return "Un-pass · PassKey inverse";
        return step.label;
    }

    function annotate(step, index) {
        const n = trace.length;
        if (!step && n && index >= n) {
            const encrypting = direction === "encrypt";
            const hex = outputValue() || "";
            return {
                kicker: `done · ${n} steps`,
                title: encrypting ? "Ciphertext" : "Plaintext",
                math: hex || (encrypting ? "The left deck is the ciphertext." : "The left deck is the plaintext."),
                why: encrypting
                    ? "The table shows the first block after the last operation."
                    : "The table shows the recovered first block.",
                spec: "3.9 Rounds, encrypt, decrypt",
            };
        }
        const kicker = !step || index < 0 ? `start · ${n} steps` : `step ${index + 1} of ${n} · ${step.label}`;
        if (!step || index < 0) {
            return { kicker, title: "Ready", math: "Plaintext on the left. Key on the right.", why: "Step through parks at the first operation without autoplay.", spec: "3.9 Rounds, encrypt, decrypt" };
        }
        if (step.kind === "sumrow") {
            const ranks = view.rowRanks(step.row);
            const listed = ranks.length ? ranks.join(" + ") + ` = ${step.total}` : `sum ${step.total}`;
            const inverse = step.amount < 0;
            return {
                kicker,
                title: analogue(step),
                math: inverse
                    ? `Row ${step.row + 1} ranks ${listed}. Rotate the other way by ${-step.amount}.`
                    : `Row ${step.row + 1} ranks ${listed}. ${step.total} mod 13 = ${step.amount}. Rotate left by ${step.amount}.`,
                why: inverse ? "Inverse SumRanks undoes the row rotate. The sum is unchanged." : "Each row rotates left by the sum of its ranks, modulo 13.",
                spec: specFor(step),
            };
        }
        if (step.kind === "sumcol") {
            const ranks = view.colRanks(step.col);
            const listed = ranks.length ? ranks.join(" + ") + ` = ${step.total}` : `sum ${step.total}`;
            const inverse = step.amount < 0;
            return {
                kicker,
                title: analogue(step),
                math: inverse
                    ? `Column ${step.col + 1} ranks ${listed}. Rotate the other way by ${-step.amount}.`
                    : `Column ${step.col + 1} ranks ${listed}. ${step.total} mod 4 = ${step.amount}. Cycle top→bottom ${step.amount}.`,
                why: inverse ? "Inverse SumRanks undoes columns first, then rows." : "After the rows, each column cycles by the sum of its ranks, modulo 4.",
                spec: specFor(step),
            };
        }
        if (step.kind === "shift") {
            return {
                kicker,
                title: analogue(step),
                math: step.amount === 0
                    ? "Row 1 stays. The idle pulse marks that it was considered."
                    : `Row ${step.row + 1} slides ${Math.abs(step.amount)} ${step.amount < 0 ? "back" : "left"}.`,
                why: "Fixed offsets 0, 1, 2, 3 — the AES ShiftRows analogue.",
                spec: specFor(step),
            };
        }
        if (step.kind === "scan") {
            return {
                kicker,
                title: analogue(step),
                math: `Overflow. CHaSeD marker on row ${step.row + 1} (suit index ${step.row}); scan left→right for a free seat. Card ${cardName(step.card)}.`,
                why: "Step target occupied: scan the row named by the CHaSeD overflow marker left→right for the first free seat, place there, then advance the marker ♣→♥→♠→♦. If that row is full, advance and try the next.",
                spec: specFor(step),
            };
        }
        if (step.kind === "place") {
            const opening = isOpeningPlace(step);
            return {
                kicker,
                title: analogue(step),
                math: step.flag === 1
                    ? `${cardName(step.card)} overflowed into seat (${step.row + 1}, ${step.col + 1}) via the CHaSeD marker scan (not the suit/rank step).`
                    : opening
                        ? `${cardName(step.card)} is placed on the start seat (2, 0) — no step yet.`
                        : `${cardName(step.card)} steps suit ${Math.floor(step.card / 13)} / rank ${(step.card % 13) + 1} to seat (${step.row + 1}, ${step.col + 1}).`,
                why: step.flag === 1
                    ? "Step target occupied: scan the row named by the CHaSeD overflow marker left→right for the first free seat, place there, then advance the marker ♣→♥→♠→♦. If that row is full, advance and try the next."
                    : opening
                        ? "The first card uses start seat (2, 0). Suit/rank stepping starts from the second card."
                        : "GridCycle walks from the Ace-of-Spades home seat (2, 0). Suit is the row step; rank is the column step.",
                spec: specFor(step),
            };
        }
        if (step.kind === "mark") {
            return {
                kicker,
                title: analogue(step),
                math: "Start seat (2, 0) — Ace-of-Spades home, positional.",
                why: "The walk begins at that seat, not by finding the Ace of Spades card.",
                spec: specFor(step),
            };
        }
        if (step.kind === "pass") {
            return {
                kicker,
                title: analogue(step),
                math: passMath(step),
                why: (step.flag === 2 ? "If the hand cannot take a proper rank cut, PassKey cuts the key pile instead. Not an error. " : "")
                    + "Deal controller C. Suit-rotate the remaining hand left by suit(C) mod hand size. Proper-cut only if rank(C) < packet size (hand, else key pile, else skip). Put C on top of the key pile.",
                spec: specFor(step),
            };
        }
        if (step.kind === "unpass") {
            return {
                kicker,
                title: analogue(step),
                math: unpassMath(step),
                why: "F⁻¹. Lift C off the key pile; undo cut; undo suit rotate; put C on the hand. Decrypt: six forward passes to K6, then one un-pass per remaining round to K0.",
                spec: specFor(step),
            };
        }
        if (step.kind === "compose") {
            const whitening = String(step.label).startsWith("Whitening");
            return {
                kicker,
                title: analogue(step),
                math: "Message cards are reindexed by the key deck: M[pos_K(j)] goes to slot j.",
                why: whitening
                    ? "Whitening: Compose with K0 before any PassKey. Still the keyed AddRoundKey stand-in; not inside a numbered round."
                    : "The only keyed layer in a round.",
                spec: specFor(step),
            };
        }
        if (step.kind === "uncompose") {
            return {
                kicker,
                title: analogue(step),
                math: "InverseCompose writes C[j] back to seat pos_K(j).",
                why: "Decrypt undoes Compose with the same round key.",
                spec: specFor(step),
            };
        }
        if (step.kind === "reset") {
            return {
                kicker,
                title: step.label,
                math: step.amount > 0 ? `Re-deal the master key, then PassKey ${step.amount} times.` : "Re-deal the master key as K0.",
                why: "This trace rebuilds the round key from the master by re-dealing and passing.",
                spec: specFor(step),
            };
        }
        if (step.kind === "counter") {
            return {
                kicker,
                title: "CTR counter deck",
                math: "Seats 0–38: Clubs+Hearts+Spades nonce. Seats 39–51: Diamonds factoradic counter.",
                why: "Only the diamond rail changes between block indices; nonce stays put.",
                spec: specFor(step),
            };
        }
        if (step.kind === "deal" || step.kind === "dealrm") {
            return {
                kicker,
                title: step.label,
                math: step.kind === "deal" ? "Deal column-major: down column 0, then 1, …" : "Deal row-major: across row 0, then 1, …",
                why: finalNote(step, "Column-major is the SumRanks table. Row-major is GridCycle inverse entry."),
                spec: specFor(step),
            };
        }
        if (step.kind === "scoopcm" || step.kind === "scooprm") {
            return {
                kicker,
                title: step.label,
                math: step.kind === "scoopcm" ? "Scoop column-major into a packet." : "Scoop row-major into a packet.",
                why: finalNote(step, "GridCycle output scoops row-major. SumRanks exits column-major."),
                spec: specFor(step),
            };
        }
        if (step.kind === "take") {
            return {
                kicker,
                title: analogue(step),
                math: `Lift ${cardName(step.card)} from (${step.row + 1}, ${step.col + 1}).`,
                why: "Inverse GridCycle reads by the same walk and gathers a packet.",
                spec: specFor(step),
            };
        }
        return {
            kicker,
            title: step.label,
            math: caption(step),
            why: "A table beat in the current round.",
            spec: specFor(step),
        };
    }

    function renderCard(note) {
        if (!teachCard) return;
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
                setError(err instanceof Error ? err.message : "Could not open the specification.");
            });
        });
        teachCard.append(kicker, title, math, why, spec);
    }

    function gridFrom(step) {
        const index = trace.indexOf(step);
        if (index <= 0) return { row: 2, col: 0 };
        for (let i = index - 1; i >= 0; i--) {
            const prev = trace[i];
            if (prev.kind === "place" || prev.kind === "take") return { row: prev.row, col: prev.col };
            if (prev.kind === "mark") return { row: 2, col: 0 };
            if (prev.label !== step.label) break;
        }
        return null;
    }

    function applyHighlight(step) {
        if (!step) {
            view.clearHighlights();
            return;
        }
        if (step.kind === "sumrow" || step.kind === "shift") view.highlightRow(step.row);
        else if (step.kind === "sumcol") view.highlightCol(step.col);
        else if (step.kind === "place" || step.kind === "take") {
            view.clearHighlights();
            const from = gridFrom(step);
            if (from) view.highlightSeat(from.row, from.col, 0x6b5340, "from");
            view.highlightSeat(step.row, step.col, step.flag === 1 ? 0xe7b15a : 0xc4a574);
        } else if (step.kind === "scan") view.highlightRow(step.row, 0xe7b15a);
        else if (step.kind === "mark") {
            view.clearHighlights();
            view.highlightSeat(2, 0);
        } else if (step.kind === "pass" || step.kind === "unpass") {
            view.clearHighlights();
            view.highlightCard(step.card, "key", step.flag === 2 ? 0xe7b15a : 0xc4a574);
        } else view.clearHighlights();
    }

    function outlineSections() {
        const sections = [];
        const byRound = new Map();
        trace.forEach((step, index) => {
            if (!byRound.has(step.label)) byRound.set(step.label, []);
            byRound.get(step.label).push({ step, index });
        });
        for (const [title, rows] of byRound) {
            const items = [];
            let lastStage = "";
            for (const { step, index } of rows) {
                const stage = stageKey(step);
                if (stage === lastStage && step.kind !== "sumrow" && step.kind !== "sumcol" && step.kind !== "shift") continue;
                lastStage = stage;
                let label = step.kind;
                if (step.kind === "sumrow") label = `SumRanks row ${step.row + 1}`;
                else if (step.kind === "sumcol") label = `SumRanks col ${step.col + 1}`;
                else if (step.kind === "shift") label = `ShiftRows row ${step.row + 1}`;
                else if (step.kind === "pass") label = `PassKey · ${rows.filter((r) => r.step.kind === "pass").length} controllers`;
                else if (step.kind === "unpass") label = `Un-pass · ${rows.filter((r) => r.step.kind === "unpass").length} controllers`;
                else if (step.kind === "place" || step.kind === "scan" || step.kind === "mark") label = "GridCycle";
                else if (step.kind === "take") label = "Inverse GridCycle";
                else if (step.kind === "compose") label = "Compose";
                else if (step.kind === "uncompose") label = "InverseCompose";
                else if (step.kind === "deal") label = "Deal col-major";
                else if (step.kind === "dealrm") label = "Deal row-major";
                else if (step.kind === "scoopcm") label = "Scoop col-major";
                else if (step.kind === "scooprm") label = "Scoop row-major";
                else if (step.kind === "reset") label = "Re-deal master key";
                items.push({ key: `${stage}:${index}`, label, index });
            }
            const openAt = viewedIndex();
            sections.push({ title, items, open: rows.some((row) => row.index === openAt) });
        }
        return sections;
    }

    function refreshTeach() {
        if (!teachCard) return;
        const viewI = viewedIndex();
        const step = viewI >= 0 && viewI < trace.length ? trace[viewI] : null;
        renderCard(annotate(step, step ? viewI : (viewI >= trace.length && trace.length ? viewI : -1)));
        if (teachPos) {
            teachPos.textContent = step
                ? `${viewI + 1} / ${trace.length}`
                : (viewI >= trace.length && trace.length ? `${trace.length} / ${trace.length}` : `0 / ${trace.length}`);
        }
        const currentKey = !step
            ? ""
            : `${stageKey(step)}:${(step.kind === "sumrow" || step.kind === "sumcol" || step.kind === "shift") ? viewI : firstIndexOfStage(viewI)}`;
        if (outlineEl) {
            renderOutline(outlineEl, outlineSections(), currentKey, (index) => {
                void jumpTo(index - 1, false);
            });
        }
        const atStart = cursor < 0;
        const atEnd = cursor >= trace.length - 1;
        $$("[data-jump]").forEach((button) => {
            const jump = button.dataset.jump;
            setDisabled(button, (jump === "back" || jump === "stage-back" || jump === "round-back") ? atStart : atEnd);
        });
    }

    function firstIndexOfStage(index) {
        if (index < 0) return 0;
        const key = stageKey(trace[index]);
        let i = index;
        while (i > 0 && stageKey(trace[i - 1]) === key) i -= 1;
        return i;
    }

    function setTeaching(on) {
        teaching = on;
        if (teachEl) teachEl.hidden = !on;
        if (outlineEl) outlineEl.hidden = !on;
        if (!on) {
            view.clearHighlights();
            view.frameTable?.();
        }
    }

    function ensureSnaps() {
        if (!startMessage || !startKey) return;
        if (snaps) return;
        view.showDecks(startMessage, startKey);
        snaps = new Array(trace.length + 1);
        snaps[0] = view.snapshot();
    }

    function getSnap(index) {
        ensureSnaps();
        if (!snaps) return null;
        const i = Math.max(0, Math.min(snaps.length - 1, index));
        if (snaps[i]) {
            view.restore(snaps[i]);
            return snaps[i];
        }
        let from = i;
        while (from > 0 && !snaps[from]) from -= 1;
        if (!snaps[from]) {
            view.showDecks(startMessage, startKey);
            snaps[0] = view.snapshot();
            from = 0;
        } else {
            view.restore(snaps[from]);
        }
        for (let k = from; k < i; k++) {
            view.applyInstant(trace[k]);
            if ((k + 1) % 16 === 0 || k + 1 === i) snaps[k + 1] = view.snapshot();
        }
        return snaps[i];
    }

    function showCaption(text) {
        if (captionEl) captionEl.textContent = text;
    }

    function showPaused() {
        if (teaching) {
            const viewI = viewedIndex();
            const snapI = viewI < 0 ? 0 : viewI;
            getSnap(snapI);
            const step = viewI >= 0 && viewI < trace.length ? trace[viewI] : null;
            if (step) showCaption(caption(step));
            else if (viewI >= trace.length) showCaption(direction === "encrypt" ? "Ciphertext on the left. Key on the right." : "Plaintext on the left. Key on the right.");
            applyHighlight(step);
            view.frameTeach?.(step ? step.kind : (viewI >= trace.length ? "compose" : "deal"));
            refreshTeach();
            return;
        }
        if (snaps) getSnap(cursor < 0 ? 0 : cursor + 1);
        const step = cursor >= 0 ? trace[cursor] : null;
        if (step) showCaption(caption(step));
    }

    function preview() {
        setError("");
        stopPlay();
        laidEnd = null;
        snaps = null;
        startMessage = null;
        startKey = null;
        trace = [];
        cursor = -1;
        setTeaching(false);
        let key;
        try {
            key = textToKey(keyEl?.value || "");
        } catch (err) {
            setError(err instanceof Error ? err.message : "That key could not be read.");
            return;
        }
        try {
            if (direction === "encrypt") {
                const blocks = textToDecks(messageEl?.value || "");
                view.showDecks(blocks[0], key);
                const extra = blocks.length > 1 ? ` First of ${blocks.length} blocks.` : "";
                showCaption(`Plaintext on the left. Key on the right.${extra}`);
                if (liveDigest) {
                    const result = mode === "ecb" ? ecb_encrypt(blocks, key) : ctr_encrypt(blocks, key, readNonce());
                    setOutput(decksToHex(result));
                }
                return;
            }
            if (!messageEl?.value.trim()) {
                showCaption("Key on the right. Ciphertext goes in the input.");
                if (liveDigest) setOutput("");
                return;
            }
            const blocks = hexToDecks(messageEl.value);
            view.showDecks(blocks[0], key);
            const extra = blocks.length > 1 ? ` First of ${blocks.length} blocks.` : "";
            showCaption(`Ciphertext on the left. Key on the right.${extra}`);
            if (liveDigest) {
                const result = mode === "ecb" ? ecb_decrypt(blocks, key) : ctr_decrypt(blocks, key, readNonce());
                setOutput(decksToText(result));
            }
        } catch (err) {
            if (liveDigest) setOutput("");
            if (direction === "encrypt" || liveDigest) {
                setError(err instanceof Error ? err.message : "That input could not be read.");
            }
        }
    }

    function computeTrace() {
        const key = textToKey(keyEl?.value || "");
        const nonce = mode === "ctr" ? readNonce() : [];
        if (direction === "encrypt") {
            const blocks = textToDecks(messageEl?.value || "");
            const result = mode === "ecb" ? ecb_encrypt(blocks, key) : ctr_encrypt(blocks, key, nonce);
            setOutput(decksToHex(result));
            trace = mode === "ecb" ? trace_ecb([blocks[0]], key) : trace_ctr([blocks[0]], key, nonce);
            startMessage = blocks[0];
            startKey = key;
            const extra = result.length > 1 ? ` First of ${result.length} blocks.` : "";
            laidEnd = { blocks: result, key, caption: `Ciphertext on the left. Key on the right.${extra}` };
            return { blocks, key, extra };
        }
        const blocks = hexToDecks(messageEl?.value || "");
        const result = mode === "ecb" ? ecb_decrypt(blocks, key) : ctr_decrypt(blocks, key, nonce);
        setOutput(decksToText(result));
        trace = mode === "ecb" ? trace_decrypt(blocks[0], key) : trace_ctr_decrypt([blocks[0]], key, nonce);
        startMessage = blocks[0];
        startKey = key;
        const extra = result.length > 1 ? ` First of ${result.length} blocks.` : "";
        laidEnd = { blocks: result, key, caption: `Plaintext on the left. Key on the right.${extra}` };
        return { blocks, key, extra };
    }

    async function playFrom(start) {
        markPlay(true);
        const token = ++job;
        for (let i = start; i < trace.length; i++) {
            if (!playing || token !== job) return;
            cursor = i;
            showCaption(caption(trace[i]));
            if (teaching) refreshTeach();
            await view.play(trace[i], Number(speedEl?.value || 1));
        }
        markPlay(false);
        if (token === job && laidEnd) {
            view.showDecks(laidEnd.blocks[0], laidEnd.key);
            showCaption(laidEnd.caption);
            snaps = null;
        }
    }

    async function start() {
        if (playing) {
            stopPlay();
            return;
        }
        setError("");
        laidEnd = null;
        snaps = null;
        setTeaching(false);
        try {
            const { blocks } = computeTrace();
            cursor = -1;
            view.showDecks(startMessage, startKey);
            if (direction === "encrypt") {
                showCaption(`Encrypting.${blocks.length > 1 ? ` Hex has ${blocks.length} blocks. The table plays the first.` : ""}`);
            } else {
                const walk = mode === "ecb"
                    ? (trace.some((item) => item.kind === "unpass")
                        ? "The master key is passed forward 6 times to K6, then un-passed back to K0."
                        : "The master key is dealt again and passed 6 times, then 5, then 4, then 3, then 2, then 1.")
                    : "The counter is encrypted, then the ciphertext is inverse-composed with that keystream.";
                const more = blocks.length > 1 ? ` The table plays the first of ${blocks.length} blocks.` : "";
                showCaption(`Decrypting. ${walk}${more}`);
            }
            playFrom(0);
        } catch (err) {
            setError(err instanceof Error ? err.message : "That input could not be read.");
        }
    }

    function enterTeach() {
        setError("");
        stopPlay();
        try {
            if (trace.length === 0) computeTrace();
            snaps = null;
            setTeaching(true);
            cursor = -1;
            showPaused();
        } catch (err) {
            setError(err instanceof Error ? err.message : "That input could not be read.");
        }
    }

    async function jumpTo(index, animate) {
        if (trace.length === 0 || busy) return;
        const next = Math.max(-1, Math.min(trace.length - 1, index));
        if (animate && next === cursor + 1) {
            markPlay(false);
            busy = true;
            const token = ++job;
            cursor = next;
            showCaption(caption(trace[cursor]));
            await view.play(trace[cursor], Number(speedEl?.value || 1));
            if (token !== job) {
                busy = false;
                return;
            }
            showPaused();
            busy = false;
            return;
        }
        stopPlay();
        cursor = next;
        showPaused();
    }

    async function stepBy(dir) {
        if (!teaching) enterTeach();
        if (dir < 0) return jumpTo(cursor - 1, false);
        return jumpTo(cursor + 1, true);
    }

    function renderMarkdown(markdown) {
        const lines = markdown.replace(/\r\n/g, "\n").split("\n");
        let html = "";
        let i = 0;
        const esc = (s) => s.replace(/[&<>]/g, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;" }[c]));
        const inline = (s) => esc(s)
            .replace(/`([^`]+)`/g, "<code>$1</code>")
            .replace(/\*\*([^*]+)\*\*/g, "<strong>$1</strong>")
            .replace(/\[([^\]]+)\]\(([^)]+)\)/g, '<a href="$2">$1</a>');
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
                const cells = (row) => row.split("|").slice(1, -1).map((cell) => cell.trim());
                const head = cells(rows[0]);
                const body = rows.slice(2).map(cells);
                html += "<table><thead><tr>" + head.map((cell) => `<th>${inline(cell)}</th>`).join("") + "</tr></thead><tbody>";
                for (const row of body) html += "<tr>" + row.map((cell) => `<td>${inline(cell)}</td>`).join("") + "</tr>";
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

    async function openSpec(heading) {
        const specDialog = $("#spec");
        const specBody = $("#spec-body");
        if (!specDialog || !specBody) throw new Error("The specification dialog is missing.");
        const href = specUrl || "./SPEC.md";
        const response = await fetch(href);
        if (!response.ok) throw new Error("The specification file is missing. Run tools/build.sh.");
        specBody.innerHTML = renderMarkdown(await response.text());
        stampHeadingIds(specBody);
        specDialog.showModal();
        if (heading) {
            const target = specBody.querySelector("#" + CSS.escape(headingId(heading)));
            if (target) target.scrollIntoView();
        }
    }

    $$("[data-mode]").forEach((button) => {
        button.addEventListener("click", () => {
            mode = button.dataset.mode;
            $$("[data-mode]").forEach((item) => item.classList.toggle("on", item === button));
            if (nonceField) nonceField.hidden = mode !== "ctr";
            preview();
        }, listen);
    });

    $$("[data-direction]").forEach((button) => {
        button.addEventListener("click", () => {
            const next = button.dataset.direction;
            if (next === direction) return;
            stopPlay();
            const typed = messageEl?.value || "";
            if (messageEl) messageEl.value = outputValue();
            setOutput(typed);
            direction = next;
            $$("[data-direction]").forEach((item) => item.classList.toggle("on", item === button));
            applyLabels();
            preview();
        }, listen);
    });

    $("#play")?.addEventListener("click", () => void start(), listen);
    $("#start")?.addEventListener("click", () => void start(), listen);
    $("#step-through")?.addEventListener("click", () => enterTeach(), listen);
    $("#stop")?.addEventListener("click", () => stopPlay(), listen);
    $("#reset")?.addEventListener("click", () => {
        stopPlay();
        busy = false;
        cursor = -1;
        setTeaching(false);
        preview();
    }, listen);
    $("#step")?.addEventListener("click", () => {
        if (trace.length === 0 || !teaching) {
            enterTeach();
            return;
        }
        setError("");
        void stepBy(1);
    }, listen);
    $("#random-key")?.addEventListener("click", () => {
        if (keyEl) keyEl.value = "0x" + randomHex(14);
        preview();
    }, listen);
    $("#random-nonce")?.addEventListener("click", () => {
        if (nonceEl) nonceEl.value = "0x" + randomHex(8);
        setError("");
        if (liveDigest) preview();
    }, listen);
    copyButton?.addEventListener("click", async () => {
        if (!outputValue()) {
            setError(direction === "encrypt" ? "There is no ciphertext to copy." : "There is no plaintext to copy.");
            return;
        }
        try {
            await navigator.clipboard.writeText(outputValue());
            setError("");
        } catch {
            setError("Could not copy the ciphertext.");
        }
    }, listen);
    messageEl?.addEventListener("input", preview, listen);
    keyEl?.addEventListener("input", preview, listen);
    nonceEl?.addEventListener("input", () => {
        if (liveDigest && mode === "ctr") preview();
    }, listen);

    $$("[data-jump]").forEach((button) => {
        button.addEventListener("click", () => {
            const jump = button.dataset.jump;
            const viewI = Math.max(0, viewedIndex());
            if (jump === "back") void stepBy(-1);
            else if (jump === "fwd") void stepBy(1);
            else if (jump === "stage-back") void jumpTo(nextGroup(trace, viewI, stageKey, -1) - 1, false);
            else if (jump === "stage-fwd") void jumpTo(nextGroup(trace, viewI, stageKey, 1) - 1, false);
            else if (jump === "round-back") void jumpTo(nextGroup(trace, viewI, roundKey, -1) - 1, false);
            else if (jump === "round-fwd") void jumpTo(nextGroup(trace, viewI, roundKey, 1) - 1, false);
        }, listen);
    });

    bindTeachKeys({
        step: (dir) => { if (teaching) void stepBy(dir); },
        stage: (dir) => {
            if (!teaching || !trace.length) return;
            void jumpTo(nextGroup(trace, Math.max(0, viewedIndex()), stageKey, dir) - 1, false);
        },
        home: () => { if (teaching) void jumpTo(-1, false); },
        end: () => { if (teaching && trace.length) void jumpTo(trace.length - 1, false); },
    }, listen);

    $$("[data-open-spec]").forEach((el) => {
        el.addEventListener("click", () => {
            openSpec().catch((err) => {
                setError(err instanceof Error ? err.message : "Could not open the specification.");
            });
        }, listen);
    });
    $("#spec-btn")?.addEventListener("click", () => {
        openSpec().catch((err) => {
            setError(err instanceof Error ? err.message : "Could not open the specification.");
        });
    }, listen);
    $("#spec-close")?.addEventListener("click", () => $("#spec")?.close(), listen);

    applyLabels();
    preview();

    const api = {
        enterTeach,
        preview,
        start,
        dispose() {
            stopPlay();
            busy = false;
            setTeaching(false);
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
                    label: step.label,
                    row: step.row,
                    col: step.col,
                    amount: step.amount,
                    total: step.total,
                    flag: step.flag,
                    card: step.card,
                })),
            },
        });
    }

    return api;
}
