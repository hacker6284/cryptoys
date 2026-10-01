/**
 * Standalone MegaDreifach view: three cubing.js TwistyPlayers side by
 * side and the block's deal as card images. Same view interface as the
 * playroom's drei-stage.js (loadShow / seek / playBeat / clearShow /
 * setTempo). Grips are named under A instead of drawn; the room draws
 * them. Nothing here computes the hash.
 */
import { cardAssetUrl } from "../doubledeal/table.js";
import { FACE_NAME, cardLabel } from "./minx.js";
import { HOME, PUZZLES } from "./plan.js";

const TWISTY_URL = "https://cdn.cubing.net/v0/js/cubing/twisty";
const SUIT_FILE = ["club", "heart", "spade", "diamond"];
const RANK_FILE = ["1", "2", "3", "4", "5", "6", "7", "8", "9", "10", "jack", "queen", "king"];

function cardFile(card) {
    return `${SUIT_FILE[card % 4]}_${RANK_FILE[Math.floor(card / 4)]}.png`;
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
    const imgs = [];

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

    function readText(beat) {
        return `Noon ${beat.read.corner ? "corner" : "edge"}: ${FACE_NAME[beat.c1]}, ${FACE_NAME[beat.c2]}.`;
    }

    return {
        async loadShow(next) {
            await load();
            gen += 1;
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
            await Promise.all(PUZZLES.map((p) => jumpToLeaf(p, (index < 0 ? 0 : leafAt[p][index]) - 1)));
            const st = stateAt(index);
            setGrip(st.grip);
            layDeal(st.deal, st.faceUp);
            if (readEl) readEl.textContent = "";
        },
        async playBeat(beat) {
            const mine = ++gen;
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
            if (!ready) return;
            await ready;
            for (const p of PUZZLES) {
                players[p].alg = "";
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
