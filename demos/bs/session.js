/**
 * BS session: the dock, the keys and the show.
 *
 * The seed (or "Roll keys") picks the dice faces; the worker runs the
 * generated trace_exchange on them and the view plays the show: one beat per
 * summary (each BUILD hole, each multiplication, start, tidy, clear and
 * shot). Step plays the step's own peg moves (expand.js), fast. A, B and K
 * come from the generated code. A known-answer vector replays its dice: T1
 * plays, T2 and T6 (workspaces of 2 and more grids) are checked only.
 */
import { bindGrowFields } from "../shared/grow-field.js";
import { openSpec, renderTeachCard, sessionScope } from "../shared/session.js";
import { bindSpeedSlider } from "../shared/speed.js";
import { bindTeachKeys, setDisabled } from "../shared/teach.js";
import { SPEC, captionFor } from "./captions.js";
import { createKeys } from "./keys.js";
import { randomSeed } from "./trace.js";

export const DEFAULT_SEED = "cryptoys";

export function createBsSession({
    view,
    specUrl,
    root = document,
    exposeTeach = false,
    keys = createKeys(),
    katsUrl = new URL("./generated/kats.json", import.meta.url).href,
    seed: firstSeed = DEFAULT_SEED,
} = {}) {
    const { abort, listen, $, $$ } = sessionScope(root);
    const seedEl = $("#seed");
    const outA = $("#out-a");
    const outB = $("#out-b");
    const outK = $("#out-k");
    const statusEl = $("#status");
    const errorEl = $("#error");
    const animNote = $("#anim-note");
    const teachEl = $("#teach");
    const teachCard = $("#teach-card");
    const teachPos = $("#teach-pos");
    const playBtn = $("#play");
    const katMenu = $("#kat-menu");
    bindGrowFields(root);

    let kat = null;
    let checked = null; // check-only vector result { A, B, K, Kb }
    let gen = 0;
    let show = null;
    let showGen = -1;
    let loading = null;
    let cursor = -1;
    let playing = false;
    let teaching = false;
    let job = 0;
    let disposed = false;
    let kats = [];
    let lastPlay = null; // { beats, ms, speed } of the last finished Play

    const status = (text) => { if (statusEl) statusEl.textContent = text; };
    const error = (text = "") => { if (errorEl) errorEl.textContent = text; };
    const seedText = () => String(seedEl?.value ?? "").trim();
    const playable = () => !kat || kat.tier === "T1";

    function setOutputs(r) {
        if (outA) outA.value = r?.A ?? "";
        if (outB) outB.value = r?.B ?? "";
        if (outK) outK.value = r?.K ?? "";
    }

    function verdict(r) {
        if (!kat || !r) return "";
        const ok = r.A === kat.public_a && r.B === kat.public_b && r.K === kat.secret_a && r.Kb === kat.secret_b;
        return ok ? "A, B and K match the file ✓" : "DIFFERS FROM THE KAT FILE";
    }

    function describeReady() {
        if (kat) {
            const r = show && showGen === gen ? show : checked;
            if (!r) return `Known answer “${kat.name}”…`;
            return `Known answer “${kat.name}” (${kat.tier}): ${verdict(r)}`;
        }
        if (!seedText()) return "Type a seed or roll the keys.";
        if (!show || showGen !== gen) return "Building the keys…";
        return `Seed “${seedText()}” · ${show.beats.length.toLocaleString("en")} steps`;
    }

    function syncControls() {
        const can = playable() && (Boolean(kat) || Boolean(seedText()));
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
            animNote.hidden = playable();
            animNote.textContent = playable() ? ""
                : `${kat.tier}'s workspace takes more than one grid (SPEC §6): checked by the generated exchange, not shown.`;
        }
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

    async function ensureShow() {
        if (!playable()) return false;
        if (!kat && !seedText()) return false;
        if (show && showGen === gen) return true;
        if (!loading) {
            const mine = gen;
            const seed = seedText();
            const vector = kat;
            status("Building the keys…");
            loading = (async () => {
                const reply = vector ? await keys.showVector(vector) : await keys.show(seed);
                if (disposed || mine !== gen) return false;
                if (!reply.show) throw new Error("This build has no trace to show.");
                await view.loadShow(reply.show);
                if (disposed || mine !== gen) return false;
                show = reply.show;
                showGen = mine;
                cursor = -1;
                setOutputs(show);
                return true;
            })().catch((err) => {
                if (mine === gen) error(err.message || "Could not build the keys.");
                return false;
            }).finally(() => {
                loading = null;
            });
        }
        const ok = await loading;
        status(describeReady());
        syncControls();
        return Boolean(ok && show);
    }

    async function refresh() {
        error("");
        gen += 1;
        checked = null;
        dropShow();
        setOutputs(null);
        syncControls();
        if (kat && !playable()) {
            const mine = gen;
            status(describeReady());
            try {
                const r = await keys.check(kat);
                if (disposed || mine !== gen) return;
                checked = r;
                setOutputs(r);
            } catch (err) {
                if (mine === gen) error(err.message || "The check failed.");
            }
            status(describeReady());
            syncControls();
            return;
        }
        await ensureShow();
    }

    function captionAt(index) {
        return captionFor(show, index)?.short ?? describeReady();
    }

    function renderTeach() {
        if (!teaching || !teachCard) return;
        const note = captionFor(show, cursor) ?? {
            kicker: "Start",
            title: "Two Battleship units and the key dice",
            math: show ? `${show.beats.length.toLocaleString("en")} steps` : "",
            why: "Each player builds a secret key grid with the dice, walks it into a public value, "
                + "copies the other's by calling the shots, and walks again to the shared secret K.",
            spec: SPEC.build,
        };
        renderTeachCard(teachCard, note, (heading) => void showSpec(heading));
        if (teachPos) teachPos.textContent = show ? `${cursor + 1} / ${show.beats.length}` : "—";
    }

    function setTeaching(on) {
        teaching = on;
        if (teachEl) teachEl.hidden = !on;
        if (root.dataset) root.dataset.teach = on ? "1" : "";
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

    async function playOne(mine, expanded) {
        cursor += 1;
        status(captionAt(cursor));
        renderTeach();
        syncControls();
        const beat = show.beats[cursor];
        if (expanded && view.playExpanded) {
            // An exchange step's peg moves come from the generated step_moves, one step at a time.
            const moves = beat.kind === "step" ? (await keys.moves(beat.step)).moves : null;
            if (mine !== job) return false;
            await view.playExpanded(beat, cursor, moves);
        } else await view.playBeat(beat, cursor);
        return mine === job;
    }

    function done() {
        status(`Done. A ${show.A} · B ${show.B} · K ${show.K}${kat ? ` · ${verdict(show)}` : ""}`);
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
        const from = cursor;
        const t0 = performance.now();
        while (playing && mine === job && cursor < show.beats.length - 1) {
            if (!(await playOne(mine, false))) break;
        }
        if (mine === job) {
            playing = false;
            if (cursor >= show.beats.length - 1) {
                lastPlay = { beats: cursor - from, ms: performance.now() - t0, speed: view.speed?.() ?? 1 };
                done();
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
        await playOne(mine, true);
        if (mine === job && cursor >= show.beats.length - 1) done();
        syncControls();
    }

    async function jumpGroup(dir, keyOf) {
        if (!(await ensureShow())) return;
        if (!teaching) setTeaching(true);
        const beats = show.beats;
        if (dir > 0) {
            let q = cursor + 1;
            if (q >= beats.length) return;
            const key = keyOf(beats[q]);
            while (q < beats.length && keyOf(beats[q]) === key) q += 1;
            await seek(q - 1);
            return;
        }
        if (cursor < 0) return;
        let s = cursor;
        while (s > 0 && keyOf(beats[s - 1]) === keyOf(beats[s])) s -= 1;
        await seek(s - 1);
    }

    async function skipToEnd() {
        if (!(await ensureShow())) return;
        setTeaching(false);
        await seek(show.beats.length - 1);
        done();
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
            await openSpec(root, specUrl, heading || SPEC.build);
        } catch (err) {
            error(err.message);
        }
    }

    function setSeed(next) {
        kat = null;
        if (seedEl) seedEl.value = next;
        return refresh();
    }

    function pickKat(vector) {
        kat = vector;
        if (seedEl) seedEl.value = "";
        setKatOpen(false);
        return refresh();
    }

    async function loadKats() {
        try {
            const response = await fetch(katsUrl);
            if (!response.ok) throw new Error("missing");
            const file = await response.json();
            kats = (file.vectors || []).filter((v) => v.kind === "exchange");
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
            button.textContent = `${vector.name}${vector.tier === "T1" ? "" : " (check only)"}`;
            button.addEventListener("click", () => void pickKat(vector), listen);
            katMenu.append(button);
        }
    }

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
    $("#roll")?.addEventListener("click", () => void setSeed(randomSeed()), listen);
    let typing = 0;
    seedEl?.addEventListener("input", () => {
        kat = null;
        clearTimeout(typing);
        typing = setTimeout(() => void refresh(), 250);
    }, listen);
    playBtn?.addEventListener("click", () => void play(), listen);
    $("#step")?.addEventListener("click", () => void step(1), listen);
    $("#skip-end")?.addEventListener("click", () => void skipToEnd(), listen);
    $("#reset")?.addEventListener("click", () => void reset(), listen);
    $("#spec-btn")?.addEventListener("click", () => void showSpec(), listen);
    $("#spec-close")?.addEventListener("click", () => $("#spec")?.close(), listen);
    $$("[data-copy]").forEach((button) => {
        button.addEventListener("click", async () => {
            try {
                await navigator.clipboard.writeText($(`#${button.dataset.copy}`)?.value || "");
                status("Copied");
            } catch {
                error("Could not copy.");
            }
        }, listen);
    });
    const byStage = (beat) => beat?.stage ?? "";
    const byPhase = (beat) => String(beat?.stage ?? "").split("-")[0];
    const jumps = {
        back: () => step(-1),
        fwd: () => step(1),
        "stage-back": () => jumpGroup(-1, byStage),
        "stage-fwd": () => jumpGroup(1, byStage),
        "round-back": () => jumpGroup(-1, byPhase),
        "round-fwd": () => jumpGroup(1, byPhase),
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

    // The dock's speed (shared/speed.js); 1× is the stage's locked tempo.
    bindSpeedSlider(root, (multiplier) => view.setSpeed?.(multiplier), listen);
    if (seedEl && !seedEl.value) seedEl.value = firstSeed;
    const first = refresh();

    const api = {
        ready: () => first,
        view: () => view,
        refresh,
        play,
        step,
        seek,
        skipToEnd,
        reset,
        setSeed,
        pickKat: async (name) => {
            if (!kats.length) await loadKats();
            const vector = kats.find((v) => v.name === name);
            if (vector) await pickKat(vector);
            return vector;
        },
        state: () => ({
            cursor,
            playing,
            teaching,
            beats: show?.beats.length ?? 0,
            seed: seedText(),
            kat: kat?.name ?? "",
            tier: kat?.tier ?? "T1",
            playable: playable(),
            A: outA?.value ?? "",
            B: outB?.value ?? "",
            K: outK?.value ?? "",
            verdict: verdict(show && showGen === gen ? show : checked),
            hasShow: Boolean(show),
            lastPlay,
            gen,
        }),
        dispose() {
            disposed = true;
            job += 1;
            playing = false;
            clearTimeout(typing);
            abort.abort();
            keys.dispose?.();
            void view?.clearShow?.();
            if (exposeTeach && typeof window !== "undefined" && window.__bs) delete window.__bs;
        },
    };
    if (exposeTeach && typeof window !== "undefined") window.__bs = api;
    return api;
}
