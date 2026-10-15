/**
 * MegaDreifach session: the dock, the live digest and the show.
 *
 * The digest comes from the generated Hash in a worker (hasher.js). Play
 * asks the worker for the generated trace (trace_hash) and plays every
 * turn of a one-block message on the view: the
 * cook, the deal, 52 card steps, 26 echoes and the full 3-solve, never
 * truncated or time-lapsed. Longer messages are too long to trace: they
 * get the digest only, with no animation. No algorithm step is computed
 * here.
 */
import { bindGrowFields } from "../shared/grow-field.js";
import { bindCappedInput } from "../shared/input-cap.js";
import { openSpec, renderTeachCard, sessionScope } from "../shared/session.js";
import { bindSpeedSlider } from "../shared/speed.js";
import { bindTeachKeys, setDisabled } from "../shared/teach.js";
import { createHasher } from "./hasher.js";

const READY_STATUS = "Play shows every turn: cook, deal, 52 cards, 26 echoes, 3-solve.";
const DIGEST_ONLY_STATUS = "Digest only: too long to show turn for turn.";
const NO_TRACE_STATUS = "Digest only: this build has no trace to animate.";

function hexOf(bytes) {
    return Array.from(bytes, (b) => b.toString(16).padStart(2, "0")).join("");
}

export function createMegaDreifachSession({
    view,
    specUrl,
    root = document,
    exposeTeach = false,
    hasher = createHasher(),
    katsUrl = new URL("./generated/kats.json", import.meta.url).href,
} = {}) {
    const { abort, listen, $, $$ } = sessionScope(root);
    const input = $("#message");
    const digestEl = $("#digest");
    const statusEl = $("#status");
    const errorEl = $("#error");
    const animNote = $("#anim-note");
    const ioNote = $("#io-note");
    const teachEl = $("#teach");
    const teachCard = $("#teach-card");
    const teachPos = $("#teach-pos");
    const playBtn = $("#play");
    const katMenu = $("#kat-menu");
    bindGrowFields(root);

    let encoding = "text";
    let kat = null;
    let bytes = [];
    let gen = 0;
    let info = null; // { gen, digest, blocks }
    let show = null;
    let showGen = -1;
    let loading = null;
    let cursor = -1;
    let playing = false;
    let teaching = false;
    let job = 0;
    let disposed = false;
    let kats = [];

    function status(text) {
        if (statusEl) statusEl.textContent = text;
    }

    function error(text = "") {
        if (errorEl) errorEl.textContent = text;
    }

    function bytesOf(text) {
        if (encoding === "hex") {
            let body = text.trim().replace(/^0x/i, "").replace(/[\s_]/g, "");
            if (!body) return [];
            if (!/^[0-9a-fA-F]+$/.test(body)) throw new Error("Hex contains non-hex characters.");
            if (body.length % 2 === 1) body = `0${body}`;
            const out = [];
            for (let i = 0; i < body.length; i += 2) out.push(parseInt(body.slice(i, i + 2), 16));
            return out;
        }
        return Array.from(new TextEncoder().encode(text));
    }

    function hasMessage() {
        return Boolean(kat) || String(input?.value ?? "").length > 0;
    }

    function digested() {
        return Boolean(info && info.gen === gen);
    }

    function tooLong() {
        return digested() && info.blocks > info.traceBlocks;
    }

    // Animated only when the generated code has a trace and the message
    // is short enough to trace turn for turn (one block).
    function animatable() {
        return digested() && info.traced && !tooLong();
    }

    function syncControls() {
        const can = hasMessage() && animatable();
        for (const id of ["#play", "#step", "#skip-end"]) {
            setDisabled($(id), !can && !(show && id === "#play" && playing));
        }
        setDisabled($("#reset"), !show);
        root.querySelectorAll("[data-jump]").forEach((button) => {
            const back = button.dataset.jump.endsWith("back");
            setDisabled(button, !show || (back ? cursor < 0 : cursor >= show.beats.length - 1));
        });
        if (playBtn) {
            playBtn.classList.toggle("is-playing", playing);
            playBtn.setAttribute("aria-label", playing ? "Pause" : "Play");
            playBtn.title = playing ? "Pause" : "Play";
        }
        if (animNote) {
            const shown = digested() && hasMessage() && !animatable();
            animNote.hidden = !shown;
            animNote.textContent = !shown ? ""
                : tooLong()
                    ? `${info.blocks} blocks: too long to trace. The show plays a message of up to `
                        + `${info.oneBlock} bytes (one block, about 1,500 turns) turn for turn; `
                        + "the digest above comes from the generated code."
                    : "This build has no trace to animate, so the turns cannot be shown. "
                        + "The digest above comes from the generated Hash.";
        }
    }

    function describeReady() {
        if (!hasMessage()) return "";
        if (!info || info.gen !== gen) return "Hashing…";
        const blocks = `${info.blocks} block${info.blocks === 1 ? "" : "s"}`;
        if (kat) {
            const ok = hexOf(info.digest) === kat.digest_hex;
            const verdict = ok ? "digest matches the KAT file ✓" : "DIGEST DIFFERS FROM THE KAT FILE";
            return `Known answer “${kat.name}”, ${blocks}: ${verdict}`;
        }
        const how = tooLong() ? DIGEST_ONLY_STATUS : info.traced ? READY_STATUS : NO_TRACE_STATUS;
        return `${bytes.length} bytes · ${blocks} · ${how}`;
    }

    function dropShow() {
        job += 1;
        playing = false;
        show = null;
        showGen = -1;
        loading = null;
        cursor = -1;
        setTeaching(false);
        void view?.clearShow?.();
    }

    async function refreshDigest() {
        error("");
        const text = String(input?.value ?? "");
        let next;
        try {
            next = bytesOf(text);
        } catch (err) {
            gen += 1;
            info = null;
            if (digestEl) digestEl.value = "";
            error(err.message);
            dropShow();
            syncControls();
            return;
        }
        const same = next.length === bytes.length && next.every((b, i) => b === bytes[i]);
        bytes = next;
        if (!same || !info) {
            gen += 1;
            dropShow();
        }
        const mine = gen;
        if (!hasMessage()) {
            info = null;
            if (digestEl) digestEl.value = "";
            status("");
            syncControls();
            return;
        }
        if (info && info.gen === mine) {
            status(describeReady());
            syncControls();
            return;
        }
        status("Hashing…");
        syncControls();
        try {
            const reply = await hasher.digest(bytes.slice());
            if (disposed || mine !== gen) return;
            info = {
                gen: mine, digest: reply.digest, blocks: reply.blocks, oneBlock: reply.oneBlock,
                traceBlocks: reply.traceBlocks, traced: Boolean(reply.traced),
            };
            if (digestEl) digestEl.value = hexOf(reply.digest);
            status(describeReady());
        } catch (err) {
            if (mine === gen) error(err.message || "Hashing failed.");
        }
        syncControls();
    }

    async function ensureShow() {
        if (!hasMessage()) return false;
        if (!info || info.gen !== gen) await refreshDigest();
        if (!animatable()) return false;
        if (show && showGen === gen) return true;
        if (!loading) {
            const mine = gen;
            status("Tracing every turn…");
            loading = (async () => {
                const reply = await hasher.show(bytes.slice());
                if (disposed || mine !== gen || !reply.show) return false;
                await view.loadShow(reply.show);
                if (disposed || mine !== gen) return false;
                show = reply.show;
                showGen = mine;
                cursor = -1;
                return true;
            })().catch((err) => {
                error(err.message || "Could not trace the message.");
                return false;
            }).finally(() => {
                loading = null;
            });
        }
        const ok = await loading;
        syncControls();
        return Boolean(ok && show);
    }

    function captionAt(index) {
        const beat = show?.beats[index];
        if (!beat) return describeReady();
        return beat.caption.short;
    }

    function renderTeach() {
        if (!teaching || !teachCard) return;
        const beat = show?.beats[cursor];
        const note = beat ? beat.caption : {
            kicker: "Start",
            title: "Three solved puzzles and a deck",
            math: "",
            why: show
                ? "A will carry the hash, B its inverse; C stays solved. "
                    + "The deck deals one block's 52 cards; every turn is shown."
                : "A will carry the hash, B its inverse; C stays solved.",
            spec: "5.7 By hand: the cook and the 3-solve",
        };
        renderTeachCard(teachCard, note, (heading) => void showSpec(heading));
        if (teachPos) teachPos.textContent = show ? `${cursor + 1} / ${show.beats.length}` : "—";
    }

    function setTeaching(on) {
        teaching = on;
        if (teachEl) teachEl.hidden = !on;
        root.dataset && (root.dataset.teach = on ? "1" : "");
        renderTeach();
    }

    async function seek(index) {
        if (!show) return;
        job += 1;
        playing = false;
        cursor = Math.max(-1, Math.min(show.beats.length - 1, index));
        await view.seek(cursor);
        status(captionAt(cursor));
        renderTeach();
        syncControls();
    }

    async function playOne(mine) {
        cursor += 1;
        status(captionAt(cursor));
        renderTeach();
        syncControls();
        await view.playBeat(show.beats[cursor], cursor);
        return mine === job;
    }

    async function play() {
        if (playing) {
            playing = false;
            job += 1;
            syncControls();
            return;
        }
        if (!(await ensureShow())) return;
        if (cursor >= show.beats.length - 1) await seek(-1);
        const mine = ++job;
        playing = true;
        syncControls();
        while (playing && mine === job && cursor < show.beats.length - 1) {
            if (!(await playOne(mine))) break;
        }
        if (mine === job) {
            playing = false;
            if (cursor >= show.beats.length - 1) {
                status(`Done. A holds the digest ${hexOf(show.digest)}.`);
            }
            syncControls();
        }
    }

    async function step(dir = 1) {
        if (!(await ensureShow())) return;
        if (!teaching) setTeaching(true);
        if (playing) {
            playing = false;
            job += 1;
        }
        if (dir < 0) return seek(cursor - 1);
        if (cursor >= show.beats.length - 1) return;
        const mine = ++job;
        await playOne(mine);
        syncControls();
    }

    async function jumpGroup(dir, keyOf) {
        if (!(await ensureShow())) return;
        if (!teaching) setTeaching(true);
        const beats = show.beats;
        if (dir > 0) {
            // Finish the group the next beat belongs to.
            let q = cursor + 1;
            if (q >= beats.length) return;
            const key = keyOf(beats[q]);
            while (q < beats.length && keyOf(beats[q]) === key) q += 1;
            await seek(q - 1);
            return;
        }
        // Back to the start of the group just shown (or the one before).
        if (cursor < 0) return;
        let s = cursor;
        while (s > 0 && keyOf(beats[s - 1]) === keyOf(beats[s])) s -= 1;
        await seek(s - 1);
    }

    async function skipToEnd() {
        if (!(await ensureShow())) return;
        setTeaching(false);
        await seek(show.beats.length - 1);
        status(`Done. A holds the digest ${hexOf(show.digest)}.`);
    }

    async function reset() {
        error("");
        setTeaching(false);
        if (show) await seek(-1);
        status(describeReady());
        syncControls();
    }

    async function showSpec(heading) {
        try {
            await openSpec(root, specUrl, heading || "5.7 By hand: the cook and the 3-solve");
        } catch (err) {
            error(err.message);
        }
    }

    function setEncoding(next) {
        encoding = next === "hex" ? "hex" : "text";
        $$("[data-encoding]").forEach((b) => b.classList.toggle("on", b.dataset.encoding === encoding));
        if (input) input.placeholder = encoding === "hex" ? "Type hex bytes, e.g. 616263" : "Type a message to hash";
    }

    function pickKat(vector) {
        kat = vector;
        setEncoding("hex");
        if (input) input.value = vector.msg_hex;
        setKatOpen(false);
        info = null;
        void refreshDigest();
    }

    async function loadKats() {
        try {
            const response = await fetch(katsUrl);
            if (!response.ok) throw new Error("missing");
            const file = await response.json();
            kats = file.vectors || [];
        } catch {
            kats = [];
        }
        if (!katMenu) return;
        katMenu.replaceChildren();
        for (const vector of kats) {
            const button = document.createElement("button");
            button.type = "button";
            button.className = "kat-pick";
            button.dataset.kat = vector.name;
            const blocks = `${vector.n_blocks} block${vector.n_blocks === 1 ? "" : "s"}`;
            const suffix = vector.n_blocks > 1 ? " (digest only)" : "";
            button.textContent = `${vector.name} · ${vector.msg_len} B · ${blocks}${suffix}`;
            button.addEventListener("click", () => pickKat(vector), listen);
            katMenu.append(button);
        }
    }

    $$("[data-encoding]").forEach((button) => {
        button.addEventListener("click", () => {
            kat = null;
            setEncoding(button.dataset.encoding);
            void refreshDigest();
        }, listen);
    });
    function setKatOpen(open) {
        if (!katMenu) return;
        katMenu.hidden = !open;
        $("#kat")?.setAttribute("aria-expanded", open ? "true" : "false");
    }

    $("#kat")?.addEventListener("click", () => {
        if (!katMenu) return;
        setKatOpen(katMenu.hidden);
        if (!katMenu.hidden && !kats.length) void loadKats();
    }, listen);
    playBtn?.addEventListener("click", () => void play(), listen);
    $("#step")?.addEventListener("click", () => void step(1), listen);
    $("#skip-end")?.addEventListener("click", () => void skipToEnd(), listen);
    $("#reset")?.addEventListener("click", () => void reset(), listen);
    $("#spec-btn")?.addEventListener("click", () => void showSpec(), listen);
    $("#spec-close")?.addEventListener("click", () => $("#spec")?.close(), listen);
    $("#digest-btn")?.addEventListener("click", async () => {
        try {
            await navigator.clipboard.writeText(digestEl?.value || "");
            status("Digest copied");
        } catch {
            error("Could not copy the digest.");
        }
    }, listen);
    const byBlock = (beat) => String(beat?.block);
    const byStage = (beat) => beat?.stage ?? "";
    const jumps = {
        back: () => step(-1),
        fwd: () => step(1),
        "stage-back": () => jumpGroup(-1, byStage),
        "stage-fwd": () => jumpGroup(1, byStage),
        "round-back": () => jumpGroup(-1, byBlock),
        "round-fwd": () => jumpGroup(1, byBlock),
    };
    root.querySelectorAll("[data-jump]").forEach((button) => {
        button.addEventListener("click", () => void jumps[button.dataset.jump]?.(), listen);
    });
    bindTeachKeys({
        step: (dir) => { if (teaching) void step(dir); },
        stage: (dir) => { if (teaching) void jumpGroup(dir, byStage); },
        home: () => { if (teaching) void seek(-1); },
        end: () => { if (teaching && show) void seek(show.beats.length - 1); },
    }, listen);
    bindCappedInput(input, {
        noteEl: ioNote,
        onChange: () => {
            kat = null;
            void refreshDigest();
        },
        signal: abort.signal,
    });

    setEncoding("text");
    // The dock's speed (shared/speed.js); 1× is the stage's locked megaminx tempo.
    bindSpeedSlider(root, (multiplier) => view.setSpeed?.(multiplier), listen);
    void refreshDigest();

    const api = {
        refresh: refreshDigest,
        play,
        step,
        seek,
        skipToEnd,
        reset,
        pickKat: (name) => {
            const run = async () => {
                if (!kats.length) await loadKats();
                const vector = kats.find((v) => v.name === name);
                if (vector) pickKat(vector);
                return vector;
            };
            return run();
        },
        state: () => ({
            cursor,
            playing,
            teaching,
            beats: show?.beats.length ?? 0,
            blocks: info?.blocks ?? 0,
            traced: Boolean(info?.traced),
            animatable: animatable(),
            digest: info ? hexOf(info.digest) : "",
            kat: kat?.name ?? "",
            gen,
            hasShow: Boolean(show),
        }),
        dispose() {
            disposed = true;
            job += 1;
            playing = false;
            abort.abort();
            hasher.dispose?.();
            void view?.clearShow?.();
            if (exposeTeach && typeof window !== "undefined" && window.__drei) delete window.__drei;
        },
    };
    if (exposeTeach && typeof window !== "undefined") window.__drei = api;
    return api;
}
