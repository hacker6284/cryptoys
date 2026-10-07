import * as THREE from "three";
import { DREI_DEAL, DREI_HELD_X, DREI_ROW_Z, DREI_SEAT_XZ, MINX } from "./constants.js";
import { measureLocalBox } from "./motion.js";
import { adoptTwistyPuzzle, createTwistySeat } from "./twisty-rig.js";
import { stageCubeView } from "./cube-stage.js";
import { timing as MINX_TURN } from "../anim/megaminx/index.js";
import { box as deckBox, card as deckCard, deal as deckDeal } from "../anim/deck/index.js";
import { CARD_STEPS, PUZZLES } from "../megadreifach/plan.js";
import { FACE_NORMAL, pieceDirection } from "../megadreifach/minx.js";
import { pacedWait, skipMs } from "../shared/pacer.js";

/**
 * MegaDreifach v3's toys in the room: three cubing.js megaminxes standing
 * on the felt in a row (B | A | C), the DEAL deck's tuck box one gap left
 * of B, the held card's seat one gap right of C, and the block's deal
 * laid face down on the felt in front, four rows of thirteen at real
 * size with 4 mm between cards (nothing overlaps). The session hands this
 * view the show (megaminx/plan.js, built from the sudoc-generated trace)
 * and it plays each beat exactly: cubing.js plays every face turn,
 * lifted and set down by playroom/cube-stage.js with the library's
 * megaminx timing (demos/anim/megaminx); the cards move with
 * demos/anim/deck (box flap, deal law, card turnOver / move / straight).
 * It computes nothing about the hash.
 */

const CARD_T = 0.00135; // unbox-rig.js (a known exception to real size: 52 × 1.35 mm fills the box)
// The deal's hop: DoubleDeal's liftHop (doubledeal/table.js, 0.9 table
// units of 63 / 0.56 mm), the height the locked grid deal arcs to.
const DEAL_HOP = 0.9 * (0.063 / 0.56);
// The tuck box (anim/deck/box BH): a card standing in it clears the mouth
// when its centre is half a card plus clearM above the box's top.
const BOX_H = deckBox.BH;
const CARD_D = 0.088;

/**
 * MegaDreifach's megaminx toys. The shelf toy `drei` is A alone (its
 * origin on the surface it stands on, the row's centre); B and C are toys
 * of their own (`dreiB`, `dreiC`) that wait in the toy chest and come out
 * to their places in the row on enter. All three stand straight on the
 * felt: no tray, no cups, no labels. Seats adopt cubing.js later.
 */
export function createDreiToy() {
    const group = new THREE.Group();
    group.name = "drei";
    const seats = {};
    const extras = {};
    for (const p of PUZZLES) {
        const seat = createTwistySeat({ puzzle: "megaminx" });
        const [x, z] = DREI_SEAT_XZ[p];
        seat.group.name = `minx-${p}`;
        seat.base = 0;
        if (p === "A") {
            seat.group.position.set(x, MINX / 2, z);
            group.add(seat.group);
        } else {
            const toy = new THREE.Group();
            toy.name = `drei${p}`;
            seat.group.position.set(0, MINX / 2, 0);
            toy.add(seat.group);
            toy.userData.keepFitted = () => seat.group.userData.keepFitted?.();
            extras[`drei${p}`] = toy;
        }
        seats[p] = seat;
    }
    group.userData.keepFitted = () => seats.A.group.userData.keepFitted?.();
    return { group, seats, extras };
}

/** Deal slot `index` (0 … 51; far row first, left to right) in the deal group's frame. */
export function slotLocal(index) {
    const row = Math.floor(index / DREI_DEAL.cols);
    const col = index % DREI_DEAL.cols;
    return {
        x: (col - (DREI_DEAL.cols - 1) / 2) * DREI_DEAL.colPitch,
        y: CARD_T / 2 + 0.0002,
        z: DREI_DEAL.farZ + row * DREI_DEAL.rowPitch,
    };
}

/** The held card's seat in the deal group's frame (one gap right of C, on the row's line). */
export function heldLocal() {
    return { x: DREI_HELD_X, y: CARD_T / 2 + 0.0002, z: DREI_ROW_Z };
}

function easeInOutQuad(t) {
    return t < 0.5 ? 2 * t * t : 1 - ((-2 * t + 2) ** 2) / 2;
}

/**
 * @param world    playroom world (toys.drei, toys.deck3 in place)
 * @param drei     createDreiToy() result
 * setDeck(rig): the createUnboxRig() deck, its 52 cards in card-id order.
 */
export function stageDrei(world, drei, { prefersReducedMotion } = {}) {
    const rigs = {};
    const views = {};
    let deck = null;
    let tempo = MINX_TURN.speed;
    let show = null;
    let leafAt = null;
    let gen = 0;
    let adoptPromise = null;
    // The deal group: its origin on the felt at the den (constants.js
    // layout is from DEN), unrotated.
    const dealGroup = new THREE.Group();
    dealGroup.name = "drei-deal";
    let dealt = null; // { block, deal, up: Set<index>, held: bool }
    const FACE_DOWN = new THREE.Quaternion().setFromAxisAngle(new THREE.Vector3(0, 0, 1), Math.PI);
    const FACE_UP = new THREE.Quaternion();

    // ---- marks: the face turned (a ring) and the pieces named (dots) ---

    function dot(color) {
        const m = new THREE.Mesh(
            new THREE.SphereGeometry(0.005, 16, 12),
            new THREE.MeshBasicMaterial({ color, depthTest: false, transparent: true, opacity: 0.95 }),
        );
        m.renderOrder = 10;
        const halo = new THREE.Mesh(
            new THREE.RingGeometry(0.0068, 0.0092, 24),
            new THREE.MeshBasicMaterial({ color, side: THREE.DoubleSide, depthTest: false, transparent: true, opacity: 0.85 }),
        );
        halo.renderOrder = 10;
        m.add(halo);
        m.userData.halo = halo;
        m.visible = false;
        return m;
    }
    const edgeDot = dot(0xfff1c9);
    const cornerDot = dot(0x7fd6ff);

    const rings = {};
    function ringFor(p) {
        if (rings[p]) return rings[p];
        const geo = new THREE.RingGeometry(0.0085, 0.0122, 40);
        const ring = new THREE.Mesh(geo, new THREE.MeshBasicMaterial({
            color: 0xffc36b, side: THREE.DoubleSide, transparent: true, opacity: 0.95,
            polygonOffset: true, polygonOffsetFactor: -2,
        }));
        const ghost = new THREE.Mesh(geo, new THREE.MeshBasicMaterial({
            color: 0xffc36b, side: THREE.DoubleSide, transparent: true, opacity: 0.28, depthTest: false,
        }));
        ring.renderOrder = 9;
        ghost.renderOrder = 9;
        ring.add(ghost);
        ring.name = `ring-${p}`;
        ring.visible = false;
        drei.seats[p].lift.add(ring);
        rings[p] = ring;
        return ring;
    }
    const Z = new THREE.Vector3(0, 0, 1);
    const nrm = new THREE.Vector3();
    function showRing(p, face) {
        if (face === undefined || face < 0) return;
        const ring = ringFor(p);
        const n = FACE_NORMAL[face];
        nrm.set(n[0], n[1], n[2]).normalize();
        // On the face's centre cap, a hair above the sticker (inradius 35 mm).
        ring.position.copy(nrm).multiplyScalar(MINX / 2 + 0.0006);
        ring.quaternion.setFromUnitVectors(Z, nrm);
        ring.visible = true;
    }
    function hideRings() {
        for (const p of PUZZLES) if (rings[p]) rings[p].visible = false;
    }
    function placeDot(m, faces, r) {
        if (!faces || faces.length < 2) return;
        const dir = pieceDirection(faces);
        m.position.set(dir[0] * r, dir[1] * r, dir[2] * r);
        m.userData.halo.lookAt(m.position.clone().multiplyScalar(3));
        if (m.parent !== drei.seats.A.lift) drei.seats.A.lift.add(m);
        m.visible = true;
    }
    function showPieces(marks) {
        if (!marks) return;
        // Edge pieces' stickers sit about 38 mm out, corners about 41 mm.
        placeDot(edgeDot, marks.edge, 0.0395);
        placeDot(cornerDot, marks.corner, 0.0425);
    }
    function hideMarks() {
        edgeDot.visible = false;
        cornerDot.visible = false;
        hideRings();
    }

    // ---- puzzles ------------------------------------------------------

    function reduced() {
        return Boolean(prefersReducedMotion?.());
    }

    function cardTempo() {
        return tempo / MINX_TURN.speed;
    }

    // duration: already at the dock's speed. Faster than 1× and shorter
    // than a frame, a motion jumps to its end and its time passes on the
    // pacer's clock (a wait: no frame floor).
    function tween(duration, step, mine = gen, { floor = true } = {}) {
        if (!duration || reduced()) {
            step(1);
            return Promise.resolve(mine === gen);
        }
        const speed = cardTempo();
        const skip = skipMs(duration * speed, speed, { floor });
        if (skip !== null) {
            step(1);
            return pacedWait(skip).then(() => mine === gen);
        }
        return new Promise((resolve) => {
            const start = performance.now();
            function tick(now) {
                if (mine !== gen) return resolve(false);
                const t = Math.min(1, (now - start) / duration);
                step(t);
                if (t < 1) requestAnimationFrame(tick);
                else resolve(true);
            }
            requestAnimationFrame(tick);
        });
    }

    function wait(duration, mine = gen) {
        return tween(reduced() ? 0 : duration, () => {}, mine, { floor: false });
    }

    // A clock for the library's moves that stops with this stage's beats.
    function runner(mine) {
        return (ms, step) => tween(ms, (t) => step(t * ms), mine);
    }

    function measureRest(p) {
        // Local TRS only (the fit wrapper centres the puzzle on the lift
        // origin): the puzzle's lowest point, resting on a face.
        const seat = drei.seats[p];
        const box = measureLocalBox(seat.fit);
        const drop = -box?.min?.y;
        if (!Number.isFinite(drop) || drop <= 0 || drop > MINX) return;
        const y = seat.base + drop;
        seat.group.userData.seatedY = y;
        if (!seat.group.userData.easeBusy) seat.group.position.y = y;
        views[p]?.rememberSeated();
    }

    function adopt() {
        if (adoptPromise) return adoptPromise;
        adoptPromise = Promise.all(PUZZLES.map(async (p) => {
            const seat = drei.seats[p];
            // Made at the locked tempo (its 1×); the dock's speed comes via setTempo.
            const rig = await adoptTwistyPuzzle(seat, {
                puzzle: "megaminx",
                tempoScale: MINX_TURN.speed,
                onFitChange() {
                    measureRest(p);
                },
            });
            if (typeof rig.setAlg !== "function" || typeof rig.playLeaves !== "function") {
                rig.dispose?.();
                throw new Error("cubing.js rig missing timeline API");
            }
            rigs[p] = rig;
            // Lift, turn, settle: the library's megaminx face turn (LOCKED
            // timing). Sound is on hold, so no voice.
            views[p] = stageCubeView(rig, { poses: null, prefersReducedMotion, timing: MINX_TURN, voice: null });
            views[p].setSpeed(cardTempo());
            measureRest(p);
            return rig;
        })).then(() => rigs).catch((err) => {
            adoptPromise = null;
            throw err;
        });
        return adoptPromise;
    }

    function settlePuzzles({ snap = true } = {}) {
        for (const p of PUZZLES) views[p]?.settle({ snap });
    }

    // ---- cards ----------------------------------------------------------

    function ensureDealGroup() {
        if (!dealGroup.parent) world.scene.add(dealGroup);
        const den = world.table.den;
        dealGroup.position.set(den.x, world.table.feltTopY + 0.0005, den.z);
        dealGroup.rotation.set(0, 0, 0);
        dealGroup.updateMatrixWorld(true);
    }

    const tmp = new THREE.Vector3();
    function vec(o) {
        return new THREE.Vector3(o.x, o.y, o.z);
    }

    function setCard(card, local, faceUp) {
        const mesh = deck.cards[card];
        if (mesh.parent !== dealGroup) dealGroup.attach(mesh);
        mesh.position.set(local.x, local.y, local.z);
        mesh.quaternion.copy(faceUp ? FACE_UP : FACE_DOWN);
        mesh.visible = true;
    }

    function restowCards() {
        dealt = null;
        if (!deck) return;
        deck.restow();
        deck.group.visible = true;
    }

    /** Snap the deal to a state: `up` = indices face up, `held` = card 52 on its seat. */
    function snapDeal(st) {
        if (!deck || !show) return;
        ensureDealGroup();
        const beat = show.beats.find((b) => b.kind === "deal" && b.block === st.block);
        deck.restow();
        beat.deal.forEach((card, i) => {
            if (i === CARD_STEPS - 1 && st.held) setCard(card, heldLocal(), true);
            else setCard(card, slotLocal(i), st.up.has(i));
        });
        dealt = { block: st.block, deal: beat.deal, up: new Set(st.up), held: st.held };
    }

    // Cards inside the box. unbox-rig's packet is 52 × 1.35 mm thick (its
    // known exception to real size), deeper than the 20 mm box, so it stays
    // hidden; a card being dealt or gathered stands inside the box in one
    // of eleven 1.4 mm lanes (by its place in the deal, so the cards in
    // flight at once never share a lane), and is seen only above the mouth.
    const LANES = 11;
    function inBoxLocal(i) {
        return new THREE.Vector3(0, 0.001, ((i % LANES) - (LANES - 1) / 2) * 0.0014);
    }
    function mouthLocal(i) {
        const p = inBoxLocal(i);
        p.y = 0.001 + BOX_H / 2 + CARD_D / 2 + deckCard.settings.straight.clearM;
        return p;
    }
    const STAND = new THREE.Quaternion().setFromEuler(new THREE.Euler(Math.PI / 2, 0, 0));

    async function dealCards(beat, mine) {
        if (!deck) return;
        ensureDealGroup();
        deck.restow();
        const run = runner(mine);
        const pace = deckDeal.timing.pace * cardTempo();
        await deckBox.openFlap(deck, { tempo: cardTempo(), run });
        if (mine !== gen) return;
        dealt = { block: beat.block, deal: beat.deal, up: new Set(), held: false };
        // deck/deal's law: card i leaves at i × dealStaggerMs ÷ pace and
        // slides (easeInOutQuad, hopping sin(πu) × DoubleDeal's liftHop)
        // to its seat in dealMs ÷ pace. Out of a box, each card first
        // slides straight up out of the mouth (deck/card straight).
        const flight = deckDeal.timing.dealMs / pace;
        const stagger = deckDeal.timing.dealStaggerMs / pace;
        await Promise.all(beat.deal.map(async (card, i) => {
            if (!(await wait(stagger * i, mine)) && stagger * i) return;
            const mesh = deck.cards[card];
            deck.group.add(mesh);
            mesh.position.copy(inBoxLocal(i));
            mesh.quaternion.copy(STAND);
            mesh.visible = true;
            if (!(await deckCard.straight(mesh, mouthLocal(i), { tempo: cardTempo(), run }))) return;
            dealGroup.attach(mesh);
            const from = mesh.position.clone();
            const fromQ = mesh.quaternion.clone();
            const to = vec(slotLocal(i));
            await tween(flight, (u) => {
                const s = easeInOutQuad(u);
                mesh.position.lerpVectors(from, to, s);
                mesh.position.y += Math.sin(Math.PI * u) * DEAL_HOP;
                mesh.quaternion.slerpQuaternions(fromQ, FACE_DOWN, s);
            }, mine);
        }));
        if (mine !== gen) return;
        await deckBox.closeFlap(deck, { tempo: cardTempo(), run });
    }

    async function turnCard(index, faceUp, mine) {
        if (!deck || !dealt) return;
        const mesh = deck.cards[dealt.deal[index]];
        if (mesh.parent !== dealGroup) setCard(dealt.deal[index], slotLocal(index), !faceUp);
        const ok = await deckCard.turnOver(mesh, { faceUp, tempo: cardTempo(), run: runner(mine) });
        if (!ok) return;
        if (faceUp) dealt.up.add(index);
        else dealt.up.delete(index);
    }

    async function holdCard(mine) {
        if (!deck || !dealt) return;
        const mesh = deck.cards[dealt.deal[CARD_STEPS - 1]];
        const ok = await deckCard.move(mesh, vec(heldLocal()), FACE_UP, { tempo: cardTempo(), run: runner(mine) });
        if (ok) dealt.held = true;
    }

    async function gatherCards(mine) {
        if (!dealt || !deck) {
            restowCards();
            return;
        }
        const run = runner(mine);
        const cards = dealt.deal.slice().reverse();
        await deckBox.openFlap(deck, { tempo: cardTempo(), run });
        if (mine !== gen) return;
        // Last dealt first, one after another (deal stagger), each hopping
        // to the box's mouth standing and sliding down into its place.
        const stagger = deckDeal.timing.dealStaggerMs / (deckDeal.timing.pace * cardTempo());
        await Promise.all(cards.map(async (card, i) => {
            if (i && !(await wait(stagger * i, mine))) return;
            const mesh = deck.cards[card];
            deck.group.attach(mesh);
            if (!(await deckCard.move(mesh, mouthLocal(i), STAND, { tempo: cardTempo(), run }))) return;
            if (!(await deckCard.straight(mesh, inBoxLocal(i), { tempo: cardTempo(), run }))) return;
            // Down in the box: out of sight until restow puts it back in the packet.
            mesh.visible = false;
        }));
        if (mine !== gen) return;
        await deckBox.closeFlap(deck, { tempo: cardTempo(), run });
        if (mine !== gen) return;
        restowCards();
    }

    // ---- show -----------------------------------------------------------

    function computeLeafAt() {
        leafAt = { A: [], B: [], C: [] };
        const now = { A: 0, B: 0, C: 0 };
        show.beats.forEach((beat, i) => {
            for (const p of PUZZLES) {
                if (beat.ranges[p]) now[p] = beat.ranges[p][1];
                leafAt[p][i] = now[p];
            }
        });
    }

    function stateAt(index) {
        let block = -1;
        let up = new Set();
        let held = false;
        let onTable = false;
        for (let i = 0; i <= index; i++) {
            const beat = show.beats[i];
            if (beat.kind === "deal") {
                block = beat.block;
                up = new Set();
                held = false;
                onTable = true;
            } else if (beat.kind === "card") {
                up.add(beat.pos - 1);
            } else if (beat.kind === "hold") {
                held = true;
            } else if (beat.kind === "count") {
                up.delete(CARD_STEPS - 1 - beat.counter);
            } else if (beat.kind === "gather") {
                onTable = false;
            }
        }
        return { block, up, held, onTable };
    }

    async function jumpRigs(index) {
        await Promise.all(PUZZLES.map((p) => {
            const leaves = index < 0 ? 0 : leafAt[p][index];
            return rigs[p]?.jumpToLeaf(leaves - 1);
        }));
    }

    /** Highlight what beat `index` did: the face turned, or the pieces named. */
    function markBeat(beat) {
        if (!beat) return;
        if (beat.marks) showPieces(beat.marks);
        else if (beat.face !== undefined) showRing(beat.puzzle ?? "A", beat.face);
        else if (beat.kind === "solve") {
            const last = beat.turns[beat.turns.length - 1];
            for (const p of [beat.leader, ...beat.copies]) showRing(p, last[0]);
        }
    }

    // Puzzles keep what they were turned to (SPEC §5.7: a puzzle is only
    // solved by undoing). On leave each keeps its turns since it was last
    // solved; the next enter undoes them in the scene.
    const leftover = { A: [], B: [], C: [] };
    let cursor = -1;

    function hasLeftover() {
        return PUZZLES.some((p) => leftover[p].length);
    }

    function keepTurns() {
        if (!show || !leafAt) return;
        const at = Math.min(cursor, show.beats.length - 1);
        for (const p of PUZZLES) {
            const n = at < 0 ? 0 : leafAt[p][at];
            leftover[p].push(...show.moves[p].slice(0, n));
        }
        show = null;
        leafAt = null;
        cursor = -1;
        for (const p of PUZZLES) {
            const rig = rigs[p];
            if (!rig) continue;
            rig.pause?.();
            rig.setAlg(leftover[p].join(" "));
            void rig.jumpToLeaf(leftover[p].length - 1);
        }
    }

    function inverseMove(move) {
        return move.endsWith("'") ? move.slice(0, -1) : `${move}'`;
    }

    /**
     * Undo every leftover turn in the scene: each puzzle plays its turns
     * backwards, literally, one after another, at the dock's tempo.
     * Reduced motion snaps.
     */
    async function resetPuzzles({ snap = false } = {}) {
        if (!hasLeftover()) return;
        await adopt();
        const mine = ++gen;
        hideMarks();
        const quick = snap || reduced();
        await Promise.all(PUZZLES.map(async (p) => {
            const turns = leftover[p];
            if (!turns.length) return;
            const back = turns.slice().reverse().map(inverseMove);
            rigs[p].setAlg([...turns, ...back].join(" "));
            await rigs[p].jumpToLeaf(turns.length - 1);
            if (quick) return;
            await views[p].playLeaves(turns.length, turns.length * 2);
        }));
        for (const p of PUZZLES) {
            leftover[p] = [];
            if (!rigs[p]) continue;
            if (mine === gen || quick) {
                rigs[p].setAlg("");
                void rigs[p].jumpToLeaf(-1);
            }
        }
    }

    async function loadShow(next) {
        await adopt();
        keepTurns();
        await resetPuzzles();
        gen += 1;
        show = next;
        computeLeafAt();
        for (const p of PUZZLES) {
            rigs[p].setAlg(next.moves[p].join(" "));
            rigs[p].setTempo(tempo);
        }
        await seek(-1);
    }

    async function seek(index) {
        gen += 1;
        hideMarks();
        if (!show) return;
        cursor = index;
        settlePuzzles();
        await jumpRigs(index);
        const st = stateAt(index);
        if (st.onTable) snapDeal(st);
        else restowCards();
        markBeat(show.beats[index]);
    }

    /** Leave: stop, keep every puzzle as it is, send the cards home. */
    async function clearShow() {
        gen += 1;
        hideMarks();
        keepTurns();
        settlePuzzles();
        restowCards();
    }

    async function play(p, range, mine, { onLeaf } = {}) {
        if (!range || mine !== gen) return;
        await views[p].playLeaves(range[0], range[1], { onLeaf });
    }

    async function playBeat(beat, index) {
        const mine = ++gen;
        hideMarks();
        if (Number.isInteger(index)) cursor = index;
        switch (beat.kind) {
        case "cook":
        case "turn":
        case "echo":
            showRing(beat.puzzle ?? "A", beat.face);
            await play(beat.puzzle ?? "A", beat.ranges[beat.puzzle ?? "A"], mine);
            break;
        case "deal":
            await dealCards(beat, mine);
            break;
        case "card":
            // The step's card turns face up where it lies, then its turn.
            await turnCard(beat.pos - 1, true, mine);
            if (mine !== gen) return;
            showRing("A", beat.face);
            await play("A", beat.ranges.A, mine);
            break;
        case "name":
        case "look":
            showPieces(beat.marks);
            await wait(900 / cardTempo(), mine);
            break;
        case "hold":
            await holdCard(mine);
            break;
        case "count":
            await turnCard(CARD_STEPS - 1 - beat.counter, false, mine);
            break;
        case "done-w":
            await wait(700 / cardTempo(), mine);
            break;
        case "solve": {
            const first = beat.ranges[beat.leader][0];
            const targets = [beat.leader, ...beat.copies];
            const mark = (i) => {
                const turn = beat.turns[i - first];
                if (turn) for (const p of targets) showRing(p, turn[0]);
            };
            await Promise.all(targets.map((p) => play(p, beat.ranges[p], mine, {
                onLeaf: p === beat.leader ? mark : undefined,
            })));
            break;
        }
        case "gather":
            await gatherCards(mine);
            break;
        default:
            break;
        }
    }

    function setTempo(next) {
        tempo = Number(next) || MINX_TURN.speed;
        for (const p of PUZZLES) {
            if (views[p]) views[p].setSpeed(cardTempo());
            else rigs[p]?.setTempo(tempo);
        }
    }

    /** The dock's speed (shared/speed.js): 1× is the library's megaminx tempo (1.4). */
    function setSpeed(multiplier) {
        setTempo(MINX_TURN.speed * multiplier);
    }

    /** Enter beat: A, B, C hop in turn so the trio reads as three toys. */
    async function rollCall(clock, enterGen) {
        const hop = async (p, delay) => {
            if (delay) await clock.wait(delay, enterGen);
            const lift = drei.seats[p].lift;
            await clock.tween(420, (t) => {
                lift.position.y = Math.sin(Math.PI * t) * 0.03;
            }, { generation: enterGen, ease: (t) => t });
            lift.position.y = 0;
        };
        await Promise.all([hop("B", 0), hop("A", 170), hop("C", 340)]);
    }

    function settle() {
        gen += 1;
        hideMarks();
        for (const p of PUZZLES) {
            rigs[p]?.pause?.();
            drei.seats[p].lift.position.y = 0;
        }
        settlePuzzles();
    }

    /** How long gatherCards takes at the current tempo (the leave's follow shot waits for it). */
    function gatherMs() {
        const k = Math.max(0.25, cardTempo());
        const flap = (deckBox.flap.open.ms + deckBox.flap.close.ms) / k;
        const stagger = (51 * deckDeal.timing.dealStaggerMs) / (deckDeal.timing.pace * cardTempo());
        return Math.round(flap + stagger + (deckCard.settings.move.ms + deckCard.settings.straight.ms) / k);
    }

    function dispose() {
        clearShow();
        dealGroup.parent?.remove(dealGroup);
    }

    return {
        group: drei.group,
        adopt,
        rigs,
        views,
        loadShow,
        seek,
        playBeat,
        clearShow,
        resetPuzzles,
        get hasLeftover() {
            return hasLeftover();
        },
        setTempo,
        setSpeed,
        get tempo() {
            return tempo;
        },
        rollCall,
        settle,
        restowCards,
        setDeck(next) {
            deck = next;
        },
        /** Leave beat: any dealt cards go home to the box. */
        gather() {
            return gatherCards(++gen);
        },
        dispose,
        gatherMs,
        get dealt() {
            return dealt;
        },
        dealGroup,
        rememberSeated() {
            drei.group.userData.seatedY = drei.group.position.y;
        },
    };
}
