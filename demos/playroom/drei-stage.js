import * as THREE from "three";
import { ASSET_BASE, DREI_SEAT_XZ, DREI_TRAY, MINX } from "./constants.js";
import { measureLocalBox } from "./motion.js";
import { adoptTwistyPuzzle, createTwistySeat } from "./twisty-rig.js";
import { HOME, PUZZLES } from "../megadreifach/plan.js";
import { cardFaceIndex, gripQuaternion, pieceDirection } from "../megadreifach/minx.js";

/**
 * MegaDreifach's toys in the room: a wooden tray holding three cubing.js
 * megaminxes (A front, B back-left, C back-right) and a real 52-card deck
 * whose deal is laid on the felt in four rows of thirteen. The session
 * hands this view the show (plan.js) and it plays each beat exactly:
 * cubing.js plays the face turns (by colour, so grips never change an
 * alg); the view rotates A's `lift` group for the re-grips and King
 * spins, marks the piece read, and takes or turns each card as it
 * drives its step. It computes nothing about the hash.
 */

const TRAY = DREI_TRAY;
// Seat centres on the tray (tray-local x, z).
const SEAT_XZ = DREI_SEAT_XZ;
// A is held in the air for its 88 steps; turning puzzles rise clear of the tray.
const HOLD_Y = 0.085;
const TURN_Y = 0.03;
const CARD_T = 0.00135;
// The deal: 4 rows × 13, read left to right, far row first.
// Pitch leaves each card's index corner showing (63 × 88 mm cards).
const COL_PITCH = 0.025;
const ROW_PITCH = 0.05;
export const DEAL_OFFSET = { x: 0, z: 0.2 };

function woodMaterial(color) {
    return new THREE.MeshStandardMaterial({ color, roughness: 0.82, metalness: 0 });
}

const ROLE = { A: "carries h", B: "holds h⁻¹", C: "stays solved" };
// Steep faces: they catch less of the pendant straight above.
const TENT = { w: 0.034, h: 0.021, lean: 0.24 };

let paperMaps = null;
function loadPaper() {
    if (paperMaps || typeof document === "undefined") return paperMaps;
    const loader = new THREE.TextureLoader();
    const url = (path) => new URL(path, ASSET_BASE).href;
    const load = (path, color) => {
        const tex = loader.load(url(path));
        if (color) tex.colorSpace = THREE.SRGBColorSpace;
        return tex;
    };
    paperMaps = {
        white: new Promise((resolve) => {
            const image = new Image();
            image.onload = () => resolve(image);
            image.onerror = () => resolve(null);
            image.src = url("textures/paper001/Color.jpg");
        }),
        normal: load("textures/paper001/NormalGL.jpg", false),
        kraft: load("textures/paper005/Color.jpg", true),
    };
    return paperMaps;
}

// Canvas label on the white ambientCG paper: the letter and its role.
function tentLabel(letter) {
    const canvas = document.createElement("canvas");
    canvas.width = 256;
    canvas.height = 160;
    const tex = new THREE.CanvasTexture(canvas);
    tex.colorSpace = THREE.SRGBColorSpace;
    const draw = (paper) => {
        const g = canvas.getContext("2d");
        g.fillStyle = "#f3ecdf";
        g.fillRect(0, 0, 256, 160);
        if (paper) {
            g.globalAlpha = 0.55;
            g.drawImage(paper, 0, 0, 256, 160);
            g.globalAlpha = 1;
        }
        g.strokeStyle = "#8a6a44";
        g.lineWidth = 3;
        g.strokeRect(9, 9, 238, 142);
        g.fillStyle = "#2b1d12";
        g.textAlign = "center";
        g.font = "600 88px Georgia,serif";
        g.fillText(letter, 128, 96);
        g.font = "22px ui-monospace,monospace";
        g.fillText(ROLE[letter], 128, 134);
        tex.needsUpdate = true;
    };
    draw(null);
    loadPaper()?.white.then(draw);
    return tex;
}

/** A folded paper tent card (two leaning faces), label on both faces. */
function createTent(letter) {
    const group = new THREE.Group();
    group.name = `tent-${letter}`;
    const maps = loadPaper();
    const label = new THREE.MeshStandardMaterial({
        map: tentLabel(letter),
        normalMap: maps?.normal ?? null,
        // Paper under the pendant blows out at full albedo.
        color: 0xc2c2c2,
        roughness: 1,
        metalness: 0,
    });
    const inside = new THREE.MeshStandardMaterial({
        map: maps?.kraft ?? null,
        color: maps ? 0xffffff : 0xb08a5a,
        roughness: 0.95,
        metalness: 0,
        side: THREE.BackSide,
    });
    const face = new THREE.PlaneGeometry(TENT.w, TENT.h);
    for (const dir of [1, -1]) {
        const leaf = new THREE.Group();
        // Hinge at the ridge; each face leans out by TENT.lean.
        leaf.position.y = Math.cos(TENT.lean) * TENT.h;
        // Same lean for both; the back face is the front one turned 180°.
        leaf.rotation.set(-TENT.lean, dir > 0 ? 0 : Math.PI, 0, "YXZ");
        for (const mat of [label, inside]) {
            const mesh = new THREE.Mesh(face, mat);
            mesh.position.y = -TENT.h / 2;
            // Inside a hair behind the label, so the two never z-fight.
            if (mat === inside) mesh.position.z = -0.0004;
            mesh.castShadow = true;
            mesh.receiveShadow = true;
            leaf.add(mesh);
        }
        group.add(leaf);
    }
    return group;
}

/**
 * The shelf toy is the tray with A in its cup; B and C are toys of their
 * own (`dreiB`, `dreiC`) that wait in the toy chest and fly to their
 * cups on enter. One megaminx on the shelf. Seats adopt cubing.js later.
 */
export function createDreiToy() {
    const group = new THREE.Group();
    group.name = "drei";
    const tray = new THREE.Mesh(new THREE.BoxGeometry(TRAY.w, TRAY.h, TRAY.d), woodMaterial(0x2b1d15));
    tray.position.y = TRAY.h / 2;
    tray.castShadow = true;
    tray.receiveShadow = true;
    group.add(tray);
    const lip = new THREE.Mesh(
        new THREE.BoxGeometry(TRAY.w + 0.01, 0.004, TRAY.d + 0.01),
        woodMaterial(0x21160f),
    );
    lip.position.y = 0.002;
    lip.receiveShadow = true;
    group.add(lip);
    const seats = {};
    const extras = {};
    for (const p of PUZZLES) {
        const seat = createTwistySeat({ edge: MINX });
        const [x, z] = SEAT_XZ[p];
        seat.group.name = `minx-${p}`;
        seat.base = p === "A" ? TRAY.h : 0;
        if (p === "A") {
            seat.group.position.set(x, TRAY.h + MINX * 0.42, z);
        } else {
            // Its own toy: origin on the cup (tray top), puzzle above it.
            const toy = new THREE.Group();
            toy.name = `drei${p}`;
            seat.group.position.set(0, MINX * 0.42, 0);
            toy.add(seat.group);
            toy.userData.keepFitted = () => seat.group.userData.keepFitted?.();
            extras[`drei${p}`] = toy;
        }
        const cup = new THREE.Mesh(
            new THREE.CylinderGeometry(0.026, 0.03, 0.003, 32),
            woodMaterial(0x1a110b),
        );
        cup.position.set(x, TRAY.h + 0.0015, z);
        cup.receiveShadow = true;
        group.add(cup);
        if (typeof document !== "undefined") {
            const tent = createTent(p);
            tent.position.set(x - 0.047, TRAY.h, z + 0.03);
            tent.rotation.y = 0.35;
            group.add(tent);
        }
        if (p === "A") group.add(seat.group);
        seats[p] = seat;
    }
    group.userData.keepFitted = () => seats.A.group.userData.keepFitted?.();
    return { group, seats, extras };
}

function frame() {
    return new Promise((resolve) => requestAnimationFrame(resolve));
}

function easeInOut(t) {
    return t < 0.5 ? 2 * t * t : 1 - ((-2 * t + 2) ** 2) / 2;
}

function slotLocal(index) {
    const row = Math.floor(index / 13);
    const col = index % 13;
    return {
        x: (col - 6) * COL_PITCH,
        // Later cards and nearer rows lie on top.
        y: CARD_T / 2 + 0.0002 + col * 0.00032 + row * 0.0045,
        z: (row - 1.5) * ROW_PITCH,
    };
}

/**
 * @param world    playroom world (toys.drei, toys.deck3 in place)
 * @param drei     createDreiToy() result
 * setDeck(rig): the createUnboxRig() deck, its 52 cards in card-id order.
 */
export function stageDrei(world, drei, { prefersReducedMotion } = {}) {
    const rigs = {};
    let deck = null;
    let sound = null;
    const hear = (name) => sound?.play(name);
    let tempo = 1;
    let show = null;
    let leafAt = null;
    let gen = 0;
    let adoptPromise = null;
    const heldQuat = new THREE.Quaternion();
    const q0 = new THREE.Quaternion();
    const q1 = new THREE.Quaternion();
    const restY = { A: 0, B: 0, C: 0 };
    const dealGroup = new THREE.Group();
    dealGroup.name = "drei-deal";
    let dealt = null; // { block, faceUp: Set }

    const marker = new THREE.Mesh(
        new THREE.SphereGeometry(0.0042, 16, 12),
        new THREE.MeshBasicMaterial({ color: 0xfff1c9, depthTest: false, transparent: true, opacity: 0.95 }),
    );
    marker.renderOrder = 10;
    marker.visible = false;
    const halo = new THREE.Mesh(
        new THREE.RingGeometry(0.0055, 0.0075, 24),
        new THREE.MeshBasicMaterial({ color: 0xffc36b, side: THREE.DoubleSide, depthTest: false, transparent: true }),
    );
    halo.renderOrder = 10;
    marker.add(halo);

    function reduced() {
        return Boolean(prefersReducedMotion?.());
    }

    function ms(base) {
        return reduced() ? 0 : Math.max(40, base / Math.max(0.25, tempo));
    }

    function tween(duration, step, mine = gen) {
        if (!duration) {
            step(1);
            return Promise.resolve(true);
        }
        return new Promise((resolve) => {
            const start = performance.now();
            function tick(now) {
                if (mine !== gen) return resolve(false);
                const t = Math.min(1, (now - start) / duration);
                step(easeInOut(t));
                if (t < 1) requestAnimationFrame(tick);
                else resolve(true);
            }
            requestAnimationFrame(tick);
        });
    }

    function wait(duration, mine = gen) {
        return tween(duration, () => {}, mine);
    }

    function measureRest(p) {
        // Local TRS only (the fit wrapper centres the puzzle on the lift
        // origin): the puzzle's lowest point, resting on its D face.
        const seat = drei.seats[p];
        const box = measureLocalBox(seat.fit);
        const drop = -box?.min?.y;
        if (!Number.isFinite(drop) || drop <= 0 || drop > MINX) return;
        seat.group.position.y = seat.base + 0.0015 + drop;
    }

    function adopt() {
        if (adoptPromise) return adoptPromise;
        adoptPromise = Promise.all(PUZZLES.map(async (p) => {
            const seat = drei.seats[p];
            const rig = await adoptTwistyPuzzle(seat, {
                puzzle: "megaminx",
                tempoScale: tempo,
                onFitChange() {
                    measureRest(p);
                },
            });
            if (typeof rig.setAlg !== "function" || typeof rig.playLeaves !== "function") {
                rig.dispose?.();
                throw new Error("cubing.js rig missing timeline API");
            }
            rigs[p] = rig;
            measureRest(p);
            return rig;
        })).then(() => rigs).catch((err) => {
            adoptPromise = null;
            throw err;
        });
        return adoptPromise;
    }

    function setGrip(grip) {
        const q = gripQuaternion(grip.up, grip.front);
        drei.seats.A.lift.quaternion.set(q[0], q[1], q[2], q[3]);
    }

    async function gripTo(grip, duration, { hop = 0.012 } = {}) {
        const lift = drei.seats.A.lift;
        const q = gripQuaternion(grip.up, grip.front);
        q0.copy(lift.quaternion);
        q1.set(q[0], q[1], q[2], q[3]);
        const baseY = lift.position.y;
        if (q0.angleTo(q1) > 1e-3) hear("regrip");
        return tween(duration, (t) => {
            lift.quaternion.slerpQuaternions(q0, q1, t);
            lift.position.y = baseY + Math.sin(Math.PI * t) * hop;
        });
    }

    function liftTo(p, y, duration) {
        const lift = drei.seats[p].lift;
        const from = lift.position.y;
        if (Math.abs(from - y) < 1e-4) return Promise.resolve(true);
        return tween(duration, (t) => {
            lift.position.y = from + (y - from) * t;
        });
    }

    function showMarker(read) {
        const faces = [read.held, read.noon];
        if (read.corner && read.third >= 0) faces.push(read.third);
        const dir = pieceDirection(faces);
        const r = MINX * (read.corner ? 0.56 : 0.5);
        marker.position.set(dir[0] * r, dir[1] * r, dir[2] * r);
        halo.lookAt(marker.position.clone().multiplyScalar(3));
        if (marker.parent !== drei.seats.A.lift) drei.seats.A.lift.add(marker);
        marker.visible = true;
    }

    function hideMarker() {
        marker.visible = false;
    }

    // ---- cards ----------------------------------------------------------

    function ensureDealGroup() {
        if (dealGroup.parent) return;
        world.scene.add(dealGroup);
    }

    function placeDealGroup() {
        const toy = world.toys.drei;
        dealGroup.position.set(
            toy.position.x + DEAL_OFFSET.x,
            world.table.feltTopY + 0.0005,
            toy.position.z + DEAL_OFFSET.z,
        );
        dealGroup.rotation.set(0, 0, 0);
        dealGroup.updateMatrixWorld(true);
    }

    function cardMesh(card) {
        return deck.cards[card];
    }

    function setCardSlot(card, index, faceUp) {
        const mesh = cardMesh(card);
        if (mesh.parent !== dealGroup) dealGroup.attach(mesh);
        const s = slotLocal(index);
        mesh.position.set(s.x, s.y, s.z);
        mesh.rotation.set(0, 0, faceUp ? 0 : Math.PI);
        mesh.quaternion.setFromEuler(mesh.rotation);
        mesh.visible = true;
    }

    function restowCards() {
        dealt = null;
        if (!deck) return;
        deck.restow();
        deck.group.visible = true;
        dealt = null;
    }

    function snapDeal(block, faceUpCount) {
        if (!deck) return;
        ensureDealGroup();
        placeDealGroup();
        const beat = show.beats.find((b) => b.kind === "deal" && b.block === block);
        beat.deal.forEach((card, i) => setCardSlot(card, i, i < faceUpCount));
        deck.packet.visible = true;
        dealt = { block, faceUp: faceUpCount };
    }

    async function dealCards(beat, mine) {
        if (!deck) return;
        ensureDealGroup();
        placeDealGroup();
        deck.packet.visible = true;
        const flap = ms(260);
        await tween(flap, (t) => deck.setFlap(t), mine);
        const start = new THREE.Vector3();
        deck.group.getWorldPosition(start);
        dealGroup.worldToLocal(start);
        start.y += 0.05;
        const stagger = ms(38);
        const flight = ms(320);
        const jobs = beat.deal.map((card, i) => (async () => {
            if (stagger) await wait(stagger * i, mine);
            if (mine !== gen) return;
            const mesh = cardMesh(card);
            dealGroup.attach(mesh);
            hear("deal");
            const from = mesh.position.clone();
            const fromQ = mesh.quaternion.clone();
            const s = slotLocal(i);
            const toQ = new THREE.Quaternion().setFromEuler(new THREE.Euler(0, 0, Math.PI));
            await tween(flight, (t) => {
                const arc = Math.sin(Math.PI * t) * 0.05;
                mesh.position.set(
                    from.x + (s.x - from.x) * t,
                    from.y + (s.y - from.y) * t + arc,
                    from.z + (s.z - from.z) * t,
                );
                mesh.quaternion.slerpQuaternions(fromQ, toQ, t);
            }, mine);
        })());
        await Promise.all(jobs);
        await tween(flap, (t) => deck.setFlap(1 - t), mine);
        if (mine === gen) dealt = { block: beat.block, faceUp: 0 };
    }

    async function turnCard(beat, mine) {
        if (!deck) return;
        const index = beat.pos - 1;
        const mesh = cardMesh(beat.card);
        if (mesh.parent !== dealGroup) setCardSlot(beat.card, index, false);
        const s = slotLocal(index);
        const fromQ = mesh.quaternion.clone();
        const toQ = new THREE.Quaternion();
        await tween(ms(300), (t) => {
            mesh.position.y = s.y + Math.sin(Math.PI * t) * 0.04;
            mesh.quaternion.slerpQuaternions(fromQ, toQ, t);
        }, mine);
        mesh.position.y = s.y;
        hear("felt");
        if (dealt) dealt.faceUp = beat.pos;
    }

    async function gatherCards(mine) {
        if (!dealt || !deck || !show) {
            restowCards();
            return;
        }
        const target = new THREE.Vector3();
        deck.group.getWorldPosition(target);
        dealGroup.worldToLocal(target);
        const cards = show.beats.find((b) => b.kind === "deal" && b.block === dealt.block).deal;
        const flight = ms(420);
        const stagger = ms(10);
        await tween(ms(200), (t) => deck.setFlap(t), mine);
        await Promise.all(cards.map((card, i) => (async () => {
            if (stagger) await wait(stagger * i, mine);
            const mesh = cardMesh(card);
            if (i % 6 === 0) hear("deal");
            const from = mesh.position.clone();
            await tween(flight, (t) => {
                mesh.position.set(
                    from.x + (target.x - from.x) * t,
                    from.y + (target.y + 0.02 - from.y) * t + Math.sin(Math.PI * t) * 0.03,
                    from.z + (target.z - from.z) * t,
                );
            }, mine);
        })()));
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
        let grip = { ...HOME };
        let held = false;
        let block = -1;
        let faceUp = 0;
        let onTable = false;
        for (let i = 0; i <= index; i++) {
            const beat = show.beats[i];
            if (beat.kind === "deal") {
                held = true;
                block = beat.block;
                faceUp = 0;
                onTable = true;
            } else if (beat.kind === "card") {
                faceUp = beat.pos;
                grip = { ...beat.next };
            } else if (beat.kind === "f3") {
                grip = { ...beat.next };
            } else if (beat.kind === "home") {
                grip = { ...HOME };
                held = false;
            } else if (beat.kind === "gather") {
                onTable = false;
            }
        }
        return { grip, held, block, faceUp, onTable };
    }

    async function jumpRigs(index) {
        await Promise.all(PUZZLES.map((p) => {
            const leaves = index < 0 ? 0 : leafAt[p][index];
            return rigs[p]?.jumpToLeaf(leaves - 1);
        }));
    }

    async function loadShow(next) {
        await adopt();
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
        hideMarker();
        if (!show) return clearShow();
        await jumpRigs(index);
        const st = stateAt(index);
        setGrip(st.grip);
        drei.seats.A.lift.position.y = st.held ? HOLD_Y : restY.A;
        drei.seats.B.lift.position.y = restY.B;
        drei.seats.C.lift.position.y = restY.C;
        if (st.onTable) snapDeal(st.block, st.faceUp);
        else restowCards();
    }

    async function clearShow() {
        gen += 1;
        show = null;
        hideMarker();
        for (const p of PUZZLES) {
            const rig = rigs[p];
            if (!rig) continue;
            rig.pause?.();
            rig.setAlg("");
            void rig.jumpToLeaf(-1);
            drei.seats[p].lift.position.y = restY[p];
        }
        drei.seats.A.lift.quaternion.identity();
        restowCards();
    }

    // Only the puzzle whose turns are being read out clicks; copies are silent.
    async function play(p, range, mine, { voiced = true } = {}) {
        if (!range || mine !== gen) return;
        await rigs[p].playLeaves(range[0], range[1], voiced ? { onLeaf: () => hear("turn") } : {});
    }

    async function raiseFor(beat, mine) {
        const moving = PUZZLES.filter((p) => beat.ranges[p]);
        const held = beat.kind === "card" || beat.kind === "f3";
        await Promise.all(PUZZLES.map((p) => {
            if (p === "A" && held) return liftTo("A", HOLD_Y, ms(200));
            const want = moving.includes(p) ? TURN_Y : restY[p];
            return liftTo(p, want, ms(200));
        }));
        return mine === gen;
    }

    async function playBeat(beat) {
        const mine = ++gen;
        hideMarker();
        switch (beat.kind) {
        case "cook":
            await raiseFor(beat, mine);
            await play(beat.puzzle, beat.ranges[beat.puzzle], mine);
            break;
        case "deal":
            await Promise.all([
                raiseFor({ ranges: {} }, mine),
                dealCards(beat, mine),
            ]);
            if (mine === gen) await liftTo("A", HOLD_Y, ms(420));
            break;
        case "card": {
            await liftTo("A", HOLD_Y, ms(200));
            await turnCard(beat, mine);
            const [a0, a1] = beat.ranges.A;
            await play("A", [a0, a0 + 1], mine);
            if (beat.spunGrip) await gripTo(beat.spunGrip, ms(520), { hop: 0 });
            if (mine !== gen) return;
            showMarker(beat.read);
            await wait(ms(360), mine);
            await play("A", [a0 + 1, a1], mine);
            hideMarker();
            if (mine === gen) await gripTo(beat.next, ms(480));
            break;
        }
        case "f3": {
            await liftTo("A", HOLD_Y, ms(200));
            await play("A", beat.ranges.A, mine);
            if (mine !== gen) return;
            showMarker(beat.read);
            await wait(ms(300), mine);
            hideMarker();
            if (mine === gen) await gripTo(beat.next, ms(420));
            break;
        }
        case "home":
            await gripTo(HOME, ms(620));
            if (mine === gen) await liftTo("A", restY.A, ms(360));
            break;
        case "solve":
            await raiseFor(beat, mine);
            await Promise.all(PUZZLES.map((p) => play(p, beat.ranges[p], mine, { voiced: p === beat.leader })));
            break;
        case "gather":
            await Promise.all([
                raiseFor({ ranges: {} }, mine),
                gatherCards(mine),
            ]);
            break;
        default:
            break;
        }
    }

    function setTempo(next) {
        tempo = Number(next) || 1;
        for (const p of PUZZLES) rigs[p]?.setTempo(tempo);
    }

    /** Enter beat: A, B, C hop in turn so the trio reads as three toys. */
    async function rollCall(clock, enterGen) {
        const hop = async (p, delay) => {
            if (delay) await clock.wait(delay, enterGen);
            const lift = drei.seats[p].lift;
            await clock.tween(420, (t) => {
                lift.position.y = restY[p] + Math.sin(Math.PI * t) * 0.03;
            }, { generation: enterGen, ease: (t) => t });
            lift.position.y = restY[p];
        };
        await Promise.all([hop("A", 0), hop("B", 170), hop("C", 340)]);
    }

    function settle() {
        gen += 1;
        hideMarker();
        for (const p of PUZZLES) {
            rigs[p]?.pause?.();
            drei.seats[p].lift.position.y = restY[p];
        }
    }

    function dispose() {
        clearShow();
        dealGroup.parent?.remove(dealGroup);
    }

    return {
        group: drei.group,
        adopt,
        rigs,
        loadShow,
        seek,
        playBeat,
        clearShow,
        setTempo,
        rollCall,
        settle,
        restowCards,
        setDeck(next) {
            deck = next;
        },
        setSound(next) {
            sound = next;
        },
        /** Leave beat: any dealt cards fly home to the box. */
        gather() {
            return gatherCards(++gen);
        },
        dispose,
        get dealt() {
            return dealt;
        },
        rememberSeated() {
            drei.group.userData.seatedY = drei.group.position.y;
        },
    };
}

export { COL_PITCH, ROW_PITCH, slotLocal, HOLD_Y, TRAY };
