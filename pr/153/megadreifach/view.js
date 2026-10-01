/**
 * Standalone MegaDreifach view: three cubing.js TwistyPlayers side by
 * side and the block's deal as card images. Same view interface as the
 * playroom's drei-stage.js (loadShow / seek / playBeat / clearShow /
 * setTempo). Grips are named under A instead of drawn; the room draws
 * them. Nothing here computes the hash.
 */
import { cardAssetUrl, cardFile as faceFile } from "../doubledeal/table.js";
import { FACE_NAME, cardLabel } from "./minx.js";
import { HOME, PUZZLES, ffBlockAt, ffMillis } from "./plan.js";
import { setSetupPosition } from "./pattern.js";

const TWISTY_URL = "https://cdn.cubing.net/v0/js/cubing/twisty";
// MegaDreifach card ids are rank × 4 + suit (SPEC §3).
function cardFile(card) {
    return faceFile(card % 4, Math.floor(card / 4));
}

function frame() {
    return new Promise((resolve) => requestAnimationFrame(resolve));
}

function gripText(grip) {
    return `${FACE_NAME[grip.up]} up, ${FACE_NAME[grip.front]} front`;
}

export function mountTrio(root = document) {
    const hosts = {};
    for (const p of PUZZLES) hosts[p] = root.querySelector(`.minx[data-puzzle="${p}"] .minx-host`);
    const gripEl = root.querySelector('[data-grip="A"]');
    const dealEl = root.querySelector("#deal");
    const readEl = root.querySelector("#read");
    const players = {};
    let tempo = 1;
    let show = null;
    let leafAt = null;
    let gen = 0;
    let ready = null;
    let finalOn = false;
    const imgs = [];
    const trioEl = root.querySelector("#trio");
    const reduced = () => Boolean(globalThis.matchMedia?.("(prefers-reduced-motion: reduce)").matches);

    for (let i = 0; i < 52; i++) {
        const img = document.createElement("img");
        img.alt = "";
        img.src = cardAssetUrl("back-navy.png");
        img.className = "card is-away";
        dealEl?.append(img);
        imgs.push(img);
    }

    function load() {
        if (ready) return ready;
        ready = import(TWISTY_URL).then(({ TwistyPlayer }) => {
            for (const p of PUZZLES) {
                const player = new TwistyPlayer({
                    puzzle: "megaminx",
                    alg: "",
                    hintFacelets: "none",
                    backView: "none",
                    background: "none",
                    controlPanel: "none",
                    tempoScale: tempo,
                });
                hosts[p]?.append(player);
                players[p] = player;
            }
        });
        return ready;
    }

    async function timeline(p) {
        const m = players[p].experimentalModel;
        const [indexer, info] = await Promise.all([m.indexer.get(), m.detailedTimelineInfo.get()]);
        return { indexer, info };
    }

    async function jumpToLeaf(p, index) {
        const player = players[p];
        player.pause();
        if (index < 0) {
            player.jumpToStart();
            return;
        }
        const { indexer } = await timeline(p);
        const leaf = Math.min(index, indexer.numAnimatedLeaves() - 1);
        player.experimentalModel.timestampRequest.set(indexer.indexToMoveStartTimestamp(leaf) + indexer.moveDuration(leaf));
    }

    async function playLeaves(p, from, to, mine) {
        const player = players[p];
        const { indexer } = await timeline(p);
        const startTs = indexer.indexToMoveStartTimestamp(from);
        const endTs = indexer.indexToMoveStartTimestamp(to - 1) + indexer.moveDuration(to - 1);
        player.experimentalModel.timestampRequest.set(startTs);
        await frame();
        player.play();
        const deadline = performance.now() + 30000;
        while (performance.now() < deadline && mine === gen) {
            const info = await player.experimentalModel.detailedTimelineInfo.get();
            if (info.timestamp >= endTs - 2) break;
            await frame();
        }
        player.pause();
        player.experimentalModel.timestampRequest.set(endTs);
    }

    function setGrip(grip) {
        if (gripEl) gripEl.textContent = gripText(grip);
    }

    function layDeal(deal, faceUp) {
        imgs.forEach((img, i) => {
            img.classList.toggle("is-away", !deal);
            if (!deal) return;
            const up = i < faceUp;
            img.src = cardAssetUrl(up ? cardFile(deal[i]) : "back-navy.png");
            img.alt = up ? cardLabel(deal[i]) : "face down";
            img.classList.toggle("is-up", up);
        });
    }

    function stateAt(index) {
        let grip = { ...HOME };
        let deal = null;
        let faceUp = 0;
        for (let i = 0; i <= index; i++) {
            const beat = show.beats[i];
            if (beat.kind === "deal") {
                deal = beat.deal;
                faceUp = 0;
            } else if (beat.kind === "card") {
                faceUp = beat.pos;
            } else if (beat.next) grip = beat.next; // spin, grip, home
            else if (beat.kind === "gather") deal = null;
        }
        return { grip, deal, faceUp };
    }

    // From the fast-forward on, the puzzles show the trace's final positions
    // (A = h, B = h⁻¹, C solved) as setup states with empty algs; before it,
    // the block-1 alg timeline.
    async function setFinal(on) {
        if (on === finalOn) return;
        finalOn = on;
        for (const p of PUZZLES) {
            const player = players[p];
            player.pause();
            player.alg = on ? "" : show.moves[p].join(" ");
            await setSetupPosition(player, on ? show.final[p] ?? null : null, show.faceTurns);
            if (on) player.jumpToStart();
        }
    }

    // Fast-forward: the puzzles spin in a blur and the deal shuffles face
    // down while the counter runs; no turns or card faces of those blocks
    // are shown. They settle on the real final positions.
    async function fastForward(beat, mine, progress) {
        const quick = reduced();
        const total = quick ? 0 : ffMillis(beat.from, beat.to, tempo);
        if (total) {
            trioEl?.classList.add("is-ff");
            dealEl?.classList.add("is-ff");
            layDeal(Array.from({ length: 52 }, (_, i) => i), 0);
            const start = performance.now();
            let shown = -1;
            while (mine === gen) {
                const t = Math.min(1, (performance.now() - start) / total);
                const block = ffBlockAt(t, beat.from, beat.to);
                if (block !== shown) progress?.(shown = block);
                if (t >= 1) break;
                await frame();
            }
        }
        if (mine === gen) await setFinal(true);
        trioEl?.classList.remove("is-ff");
        dealEl?.classList.remove("is-ff");
        layDeal(null, 0);
        if (mine === gen) progress?.(beat.to);
    }

    function readText(beat) {
        return `Noon ${beat.read.corner ? "corner" : "edge"}: ${FACE_NAME[beat.c1]}, ${FACE_NAME[beat.c2]}.`;
    }

    return {
        async loadShow(next) {
            await load();
            gen += 1;
            if (finalOn && show) await setFinal(false);
            finalOn = false;
            for (const p of PUZZLES) await setSetupPosition(players[p], null);
            show = next;
            leafAt = { A: [], B: [], C: [] };
            const now = { A: 0, B: 0, C: 0 };
            next.beats.forEach((beat, i) => {
                for (const p of PUZZLES) {
                    if (beat.ranges[p]) now[p] = beat.ranges[p][1];
                    leafAt[p][i] = now[p];
                }
            });
            for (const p of PUZZLES) {
                players[p].alg = next.moves[p].join(" ");
                players[p].tempoScale = tempo;
            }
            await this.seek(-1);
        },
        async seek(index) {
            gen += 1;
            if (!show) return;
            const atEnd = Boolean(show.final) && index >= show.ffAt;
            await setFinal(atEnd);
            if (!atEnd) await Promise.all(PUZZLES.map((p) => jumpToLeaf(p, (index < 0 ? 0 : leafAt[p][index]) - 1)));
            const st = stateAt(index);
            setGrip(st.grip);
            layDeal(st.deal, st.faceUp);
            if (readEl) readEl.textContent = "";
        },
        async playBeat(beat, _index, { progress } = {}) {
            const mine = ++gen;
            if (beat.kind === "ff") {
                if (readEl) readEl.textContent = "";
                await fastForward(beat, mine, progress);
                return;
            }
            if (beat.kind === "deal") layDeal(beat.deal, 0);
            if (beat.kind === "card") {
                const img = imgs[beat.pos - 1];
                img.src = cardAssetUrl(cardFile(beat.card));
                img.alt = cardLabel(beat.card);
                img.classList.add("is-up", "is-live");
                setTimeout(() => img.classList.remove("is-live"), 600);
            }
            if (readEl && beat.kind === "read") readEl.textContent = readText(beat);
            else if (readEl && beat.kind !== "turn") readEl.textContent = "";
            await Promise.all(PUZZLES.map((p) => (beat.ranges[p] ? playLeaves(p, beat.ranges[p][0], beat.ranges[p][1], mine) : null)));
            if (beat.next) setGrip(beat.next);
            if (beat.kind === "gather") layDeal(null, 0);
        },
        async clearShow() {
            gen += 1;
            show = null;
            layDeal(null, 0);
            setGrip(HOME);
            if (readEl) readEl.textContent = "";
            finalOn = false;
            trioEl?.classList.remove("is-ff");
            dealEl?.classList.remove("is-ff");
            if (!ready) return;
            await ready;
            for (const p of PUZZLES) {
                players[p].alg = "";
                await setSetupPosition(players[p], null);
                players[p].jumpToStart();
            }
        },
        setTempo(next) {
            tempo = Number(next) || 1;
            for (const p of PUZZLES) if (players[p]) players[p].tempoScale = tempo;
        },
        load,
    };
}
