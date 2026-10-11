/**
 * BS on the playroom table: two Battleship travel units, lids up, and the
 * key dice (constants.js BS layout, every piece at its real size).
 *
 *   - Each player's ocean grid is the key grid: BUILD lays the fleet and a
 *     peg in every hole (SPEC §4.2); the walk cursor is two Destroyers on
 *     the grid's frame (§4.3).
 *   - The lid's target grid is the workspace (SPEC §6, T1): X in rows A–B,
 *     Y in C–D, the product strip S in E–H (its holes 36–37 overflow into
 *     row I), C in I–J, registers in columns 1–9; column 10 is the control
 *     lane (hole 5: calling; hole 10: where the walk is).
 *   - The dice: the row cup's five d10s, the hole die (d12) and the d6,
 *     and their cup.
 *
 * Play runs one beat per summary of the generated trace (bs.sudo
 * trace_exchange): the registers jump from one summary to the next. Step
 * plays that step's own moves, one after another, fast: a hole of BUILD's
 * from its BuildRead, an exchange step's peg moves from the generated
 * step_moves (worker.js), placed on the lid by bs/expand.js.
 * Moves are the library's own (anim/peg, anim/ship, anim/dice), played on
 * the dock's speed with the pacer's frame skipping.
 *
 * The models load by path (BS_MODELS) so updated GLBs drop in by name.
 */
import * as THREE from "three";
import * as peg from "../anim/peg/index.js";
import * as ship from "../anim/ship/index.js";
import * as dice from "../anim/dice/index.js";
import { createStageTime } from "./stage-time.js";
import { BS_DICE, BS_GRID as G, REAL_SIZES } from "./constants.js";
import { lidMoves } from "../bs/expand.js";

const MODELS = new URL("../bs/assets/models/", import.meta.url);
export const BS_MODELS = {
    red: "bs_unit_red.glb",
    blue: "bs_unit_blue.glb",
    pegs: "bs_pegs.glb",
    ships: "bs_ships.glb",
    d10: "facehunter_d10_22mm.glb",
    d12: "facehunter_d12_19mm_box.glb",
    d6: "facehunter_d6_16mm.glb",
    cup: "proc_dice_cup_83x102mm.glb",
};

// The unit GLB's grids: constants.js BS_GRID (one source with the microdemos).
const { pitch: PITCH, x0: X0, oceanZ0: OCEAN_Z0, plateY: PLATE_Y, deckUp: DECK_UP, lidZ0: LID_Z0, lidFaceY: LID_FACE_Y } = G;

// 1×: a Play beat's hold after its moves (ms); the moves' own lengths are
// the library entries' at their `tempos.play`.
export const BEAT_HOLD_MS = 45;
const READ_MS = 160;

const SHIP_NODE = {
    Carrier: "ship_carrier_5",
    Battleship: "ship_battleship_4",
    Cruiser: "ship_cruiser_3",
    Sub: "ship_submarine_3",
    Destroyer: "ship_destroyer_2",
};
const D10_TINT = [0xd8443c, 0xf08a2c, 0xf2cf3a, 0x4caf50, 0x3f7fd8]; // red, orange, yellow, green, blue
const D10_YAW = [0.3, -0.5, 0.9, 0.1, -0.8];
const D12_YAW = 0.4;
const D6_YAW = 0.25;
const DEFAULT_FACES = { d10: [1, 2, 3, 4, 5], d12: 12, d6: 6 };

// ---- pure layout (tested in bs-layout.test.mjs) ------------------------

/**
 * Workspace cell (row × 10 + column) of register r's hole h, T1 (SPEC §6):
 * r is a generated Reg, "X" | "Y" | "C" | "Strip". The strip's holes 36–37
 * overflow into row I, columns 1–2, which are C's holes 0–1 (the strip only
 * reaches them in a nudged public-walk product, while C is still empty).
 */
export function workspaceCell(r, h) {
    const row = Math.floor(h / 9);
    const col = h % 9;
    if (r === "X") return row * 10 + col;
    if (r === "Y") return (2 + row) * 10 + col;
    if (r === "C") return (8 + row) * 10 + col;
    if (r === "Strip") return h < 36 ? (4 + row) * 10 + col : 80 + (h - 36);
    throw new Error(`no register ${r}`);
}

/** Control-lane hole k (1 … 10): column 10, row k. */
export function laneCell(k) {
    return (k - 1) * 10 + 9;
}

/** The 100 workspace cells of one player: registers { x, y, c } and the lane. */
export function workspaceCells(ws, lane5 = 0, lane10 = 0) {
    const cells = new Int8Array(100);
    for (const [r, reg] of [["X", ws.x], ["Y", ws.y], ["C", ws.c]]) {
        if (!reg) continue;
        for (let h = 0; h < reg.length; h++) if (reg[h]) cells[workspaceCell(r, h)] = reg[h];
    }
    if (lane5) cells[laneCell(5)] = lane5;
    if (lane10) cells[laneCell(10)] = lane10;
    return cells;
}

/**
 * Per beat and player: the walk cursor's hole (−1: off the grid) and the
 * control lane (hole 5: 1 while calling; hole 10: 0 ship pass, 2 a 3-holer's
 * extra cell to come, 1 peg pass), after that beat.
 */
export function boardMarks(show) {
    const B = show.beats.length;
    const out = [0, 1].map(() => ({ cursor: new Int16Array(B).fill(-1), lane5: new Int8Array(B), lane10: new Int8Array(B), step: new Int32Array(B).fill(-1), built: new Int16Array(B) }));
    // The next step of the same player, for each step.
    const next = new Int32Array(show.steps.length).fill(-1);
    const seen = [-1, -1];
    for (let i = show.steps.length - 1; i >= 0; i--) {
        const p = show.steps[i].player;
        next[i] = seen[p];
        seen[p] = i;
    }
    const cur = [{ cursor: -1, lane5: 0, lane10: 0, step: -1, built: 0 }, { cursor: -1, lane5: 0, lane10: 0, step: -1, built: 0 }];
    show.beats.forEach((beat, i) => {
        const p = beat.player;
        const c = cur[p];
        if (beat.kind === "build") {
            c.built += 1;
            c.cursor = c.built < show.reads[p].length ? show.reads[p][beat.read].hole : -1;
        } else {
            const st = show.steps[beat.step];
            c.step = beat.step;
            const walk = st.op === "Start" || st.op === "Square" || st.op === "Cube" || st.op === "TimesBase";
            if (walk && st.cell >= 0) {
                const holes = show.holes[p];
                const h = holes[st.cell];
                c.cursor = h < 0 ? 0 : h % 100;
                c.lane10 = h >= 100 ? 1 : h >= 0 && holes[st.cell + 1] === h ? 2 : 0;
            } else {
                c.cursor = -1;
                c.lane10 = 0;
            }
            const calling = st.op === "Clear" || st.op === "Call";
            c.lane5 = calling && next[beat.step] >= 0 && show.steps[next[beat.step]].op === "Call" ? 1 : 0;
        }
        for (const q of [0, 1]) {
            out[q].cursor[i] = cur[q].cursor;
            out[q].lane5[i] = cur[q].lane5;
            out[q].lane10[i] = cur[q].lane10;
            out[q].step[i] = cur[q].step;
            out[q].built[i] = cur[q].built;
        }
    });
    return out;
}

/**
 * The walk cursor at key-grid hole h (unit frame, metres): two Destroyers,
 * one on the letter strip (lying along the rows' axis, z) and one on the
 * number strip (along x). Each marks its row or column with one end, the
 * end toward the corner of A1 in the grid's near half and the other end in
 * its far half, so the pair stays apart even at A1. { row, col }: each
 * piece's centre { x, z } and footprint { x0, x1, z0, z1 }.
 */
export function cursorPoses(h) {
    const L = REAL_SIZES.bsShip.destroyer;
    const W = REAL_SIZES.bsShip.w;
    const r = Math.floor(h / 10);
    const c = h % 10;
    const shift = (k) => (k < 5 ? 1 : -1) * (L - PITCH) / 2;
    const row = { x: G.frameLeftX, z: OCEAN_Z0 + r * PITCH + shift(r) };
    const col = { x: X0 + c * PITCH + shift(c), z: G.frameTopZ };
    row.foot = { x0: row.x - W / 2, x1: row.x + W / 2, z0: row.z - L / 2, z1: row.z + L / 2 };
    col.foot = { x0: col.x - L / 2, x1: col.x + L / 2, z0: col.z - W / 2, z1: col.z + W / 2 };
    return { row, col };
}

/** The dice faces showing after beat `index`: the last row cup's settled d10s, the last d12 and d6. */
export function diceFacesAt(show, index) {
    let d10 = null;
    let d12 = null;
    let d6 = null;
    for (let i = Math.min(index, show.beats.length - 1); i >= 0 && (!d10 || !d12 || !d6); i--) {
        const beat = show.beats[i];
        if (beat.kind !== "build") continue;
        const read = show.reads[beat.player][beat.read];
        if (!d10 && read.cup.length) d10 = settled(read.cup);
        if (!d12 && read.d12.length) d12 = read.d12[read.d12.length - 1];
        if (!d6 && read.d6.length) d6 = read.d6[read.d6.length - 1];
    }
    return { d10: d10 ?? DEFAULT_FACES.d10.slice(), d12: d12 ?? DEFAULT_FACES.d12, d6: d6 ?? DEFAULT_FACES.d6 };
}

/** The five faces a row cup settles on (zero faces are thrown again). */
export function settled(cup) {
    return cup.filter((f) => f !== 0);
}

// ---- the toys -------------------------------------------------------------

function loadGlb(loader, file) {
    return new Promise((resolve, reject) => loader.load(new URL(file, MODELS).href, resolve, undefined, reject));
}

function shadows(root) {
    root.traverse((o) => {
        if (o.isMesh) {
            o.castShadow = true;
            o.receiveShadow = true;
        }
    });
}

/**
 * The BS toys as empty groups (world.toys bs, bsB, bsDice, bsCup) and load(), which
 * fills them with the models. Each group's origin is where it stands.
 */
export function createBsToys() {
    const units = [new THREE.Group(), new THREE.Group()];
    units[0].name = "bs";
    units[1].name = "bsB";
    const diceToy = new THREE.Group();
    diceToy.name = "bsDice";
    const cupToy = new THREE.Group();
    cupToy.name = "bsCup";
    let loading = null;
    function load() {
        loading ??= (async () => {
            // Loaded here: node tests stub three's addons with empty modules.
            const { GLTFLoader } = await import("three/addons/loaders/GLTFLoader.js");
            const loader = new GLTFLoader();
            const files = await Promise.all(Object.entries(BS_MODELS).map(async ([k, f]) => [k, await loadGlb(loader, f)]));
            const g = Object.fromEntries(files);
            const parts = { units: [], templates: {}, dice: {} };
            for (const [p, key] of [[0, "red"], [1, "blue"]]) {
                const root = g[key].scene;
                shadows(root);
                units[p].add(root);
                const lid = root.getObjectByName("lid_pivot");
                parts.units.push({ root, lid });
            }
            const pw = g.pegs.scene.getObjectByName("peg_white");
            const pr = g.pegs.scene.getObjectByName("peg_red");
            parts.templates.peg = { geometry: pw.geometry, materials: [null, pw.material, pr.material] };
            parts.templates.ships = {};
            for (const [kind, node] of Object.entries(SHIP_NODE)) {
                const o = g.ships.scene.getObjectByName(node);
                o.position.set(0, 0, 0);
                parts.templates.ships[kind] = o;
            }
            // The dice cup and the dice as built (real size; bs-layout.test checks).
            const cup = g.cup.scene;
            shadows(cup);
            cupToy.add(cup);
            const dieOf = (gltf, tint) => {
                const node = gltf.scene.children[0];
                const holder = new THREE.Group();
                const mesh = node.clone();
                if (tint !== undefined) {
                    // The atlas is white numerals on dark grey: the body takes
                    // the tint and the numerals glow white from the atlas.
                    const atlas = mesh.material.map;
                    mesh.material = new THREE.MeshStandardMaterial({
                        color: tint, roughness: 0.45, metalness: 0,
                        emissive: 0xffffff, emissiveMap: atlas, emissiveIntensity: 0.85,
                    });
                }
                mesh.material.side = THREE.FrontSide;
                mesh.castShadow = true;
                holder.add(mesh);
                holder.userData.mesh = mesh;
                diceToy.add(holder);
                return holder;
            };
            parts.dice.d10 = D10_TINT.map((tint, k) => {
                const die = dieOf(g.d10, tint);
                die.position.set(BS_DICE.d10[k], 0, 0);
                return die;
            });
            parts.dice.d12 = dieOf(g.d12);
            parts.dice.d12.position.set(BS_DICE.d12, 0, 0);
            parts.dice.d6 = dieOf(g.d6);
            parts.dice.d6.position.set(BS_DICE.d6, 0, 0);
            return parts;
        })();
        return loading;
    }
    return { units, dice: diceToy, cup: cupToy, load };
}

// ---- the stage ----------------------------------------------------------------

/**
 * The BS view: stageBs(world, toys) → { loadShow, seek, playBeat,
 * playExpanded, clearShow, setSpeed, speed, settle, rememberSeated, ready }.
 */
export function stageBs(world, toys, { prefersReducedMotion = () => false } = {}) {
    let parts = null;
    let show = null;
    let marks = null;
    let index = -1;
    let speed = 1;
    let gen = 0;
    const units = [];
    const AX_UP = new THREE.Vector3(0, 1, 0);
    const AX_LID = new THREE.Vector3(0, -1, 0);
    const restCache = new Map();

    const ready = toys.load().then((p) => {
        parts = p;
        p.units.forEach((u, i) => units.push(rigUnit(u, i)));
        for (const name of ["bs", "bsB", "bsDice", "bsCup"]) {
            const toy = world.toys?.[name];
            if (toy && !toy.userData.flightBusy && toy.userData.seatSurface !== "table") world.shelfHome?.(name);
        }
        showDice(DEFAULT_FACES);
        return p;
    });

    const seats = { sea: [], deck: [], lid: [] };
    for (let h = 0; h < 100; h++) {
        const x = X0 + (h % 10) * PITCH;
        seats.sea.push(new THREE.Vector3(x, PLATE_Y, OCEAN_Z0 + Math.floor(h / 10) * PITCH));
        seats.deck.push(new THREE.Vector3(x, PLATE_Y + DECK_UP, OCEAN_Z0 + Math.floor(h / 10) * PITCH));
        seats.lid.push(new THREE.Vector3(x, LID_FACE_Y, LID_Z0 - Math.floor(h / 10) * PITCH));
    }

    /** Key-grid hole h's peg seat (in a ship's deck hole when covered), unit frame. Shared: copy, never change. */
    function oceanSeat(h, covered) {
        return covered ? seats.deck[h] : seats.sea[h];
    }

    /** Workspace cell's peg seat, lid_pivot frame. Shared: copy, never change. */
    function lidSeat(cell) {
        return seats.lid[cell];
    }

    function makePeg(parent) {
        const t = parts.templates.peg;
        const mesh = new THREE.Mesh(t.geometry, t.materials[1]);
        mesh.castShadow = true;
        mesh.visible = false;
        parent.add(mesh);
        return mesh;
    }

    function colour(mesh, c) {
        if (c) mesh.material = parts.templates.peg.materials[c];
        mesh.visible = c > 0;
    }

    function makeShip(kind) {
        const mesh = parts.templates.ships[kind].clone();
        mesh.castShadow = true;
        mesh.visible = false;
        return mesh;
    }

    // A piece lying on `holes` (from the trace), its bow as the ship says.
    function shipPose(s, holes) {
        const at = oceanSeat(holes[0], false).clone().add(oceanSeat(holes[holes.length - 1], false)).multiplyScalar(0.5);
        at.y = PLATE_Y;
        const rotY = s.down ? (s.bow_last ? -Math.PI / 2 : Math.PI / 2) : (s.bow_last ? 0 : Math.PI);
        return { at, rotY };
    }

    function rigUnit({ root, lid }, p) {
        const ocean = Array.from({ length: 100 }, (_, h) => {
            const m = makePeg(root);
            m.position.copy(oceanSeat(h, false));
            return m;
        });
        const lidPegs = Array.from({ length: 100 }, (_, cell) => {
            const m = makePeg(lid);
            m.rotation.x = Math.PI;
            m.position.copy(lidSeat(cell));
            return m;
        });
        const fleet = new THREE.Group();
        fleet.name = `bs-fleet-${p}`;
        root.add(fleet);
        // The walk cursor: two Destroyers on the frame (letters, numbers).
        const rowCursor = makeShip("Destroyer");
        rowCursor.rotation.y = -Math.PI / 2;
        const colCursor = makeShip("Destroyer");
        root.add(rowCursor, colCursor);
        return {
            root, lid, ocean, lidPegs, fleet, rowCursor, colCursor,
            ships: [],
            temp: null,
            cells: new Int8Array(100),
            key: new Int8Array(100),
            covered: new Uint8Array(100),
            shown: 0,
            cursor: -1,
        };
    }

    function cursorAt(h) {
        const { row, col } = cursorPoses(h);
        return { row: new THREE.Vector3(row.x, PLATE_Y, row.z), col: new THREE.Vector3(col.x, PLATE_Y, col.z) };
    }

    // ---- dice ----

    function restY(holder, kind, face) {
        const key = `${kind}:${face}`;
        if (!restCache.has(key)) restCache.set(key, dice.restHeight(holder.userData.mesh, kind, face, THREE.Quaternion, THREE.Vector3));
        return restCache.get(key);
    }

    function setDie(holder, kind, face, yaw) {
        holder.quaternion.copy(dice.restQuaternion(kind, face, yaw, THREE.Quaternion, THREE.Vector3));
        holder.position.y = restY(holder, kind, face) + 0.0002;
        holder.userData.face = face;
    }

    function showDice(faces) {
        if (!parts) return;
        parts.dice.d10.forEach((d, k) => setDie(d, "d10", faces.d10[k] ?? DEFAULT_FACES.d10[k], D10_YAW[k]));
        setDie(parts.dice.d12, "d12", faces.d12, D12_YAW);
        setDie(parts.dice.d6, "d6", faces.d6, D6_YAW);
    }

    function rollDie(holder, kind, face, yaw, tempo, run) {
        return dice.roll(holder, kind, face, { yaw, tempo, run, landY: restY(holder, kind, face) + 0.0002 })
            .then((ok) => { holder.userData.face = face; return ok; });
    }

    // ---- time ----

    const time = createStageTime({ current: (mine) => mine === gen, speed: () => speed, reduced: () => Boolean(prefersReducedMotion()) });

    // A clock for the library's moves (ms at 1× dock speed) that stops with this stage's beats.
    function runner() {
        const mine = gen;
        return (ms, step) => time.tween(ms / speed, (t) => step(t * ms), mine);
    }

    function hold(ms1x) {
        return time.wait(ms1x / speed, gen);
    }

    // ---- state ----

    function wsOf(p, i) {
        const s = i >= 0 ? marks[p].step[i] : -1;
        return s < 0 ? {} : show.steps[s];
    }

    function cellsAt(p, i) {
        if (i < 0) return new Int8Array(100);
        return workspaceCells(wsOf(p, i), marks[p].lane5[i], marks[p].lane10[i]);
    }

    function emptyGrid() {
        return { pegs: new Int8Array(100), covered: new Uint8Array(100) };
    }

    function keyAt(p, i) {
        const count = i >= 0 ? marks[p].built[i] : 0;
        const grid = emptyGrid();
        let ships = 0;
        for (let r = 0; r < count; r++) {
            const read = show.reads[p][r];
            if (read.ship.length) ships += 1;
            for (const h of read.covered) grid.covered[h] = 1;
            grid.pegs[read.hole] = read.peg;
        }
        return { grid, ships };
    }

    function renderUnit(p, i) {
        const u = units[p];
        if (!u) return;
        const cells = show ? cellsAt(p, i) : new Int8Array(100);
        for (let c = 0; c < 100; c++) {
            const m = u.lidPegs[c];
            m.position.copy(lidSeat(c));
            colour(m, cells[c]);
        }
        u.cells = cells;
        const { grid, ships } = show ? keyAt(p, i) : { grid: emptyGrid(), ships: 0 };
        for (let h = 0; h < 100; h++) {
            const m = u.ocean[h];
            u.covered[h] = grid.covered[h] ? 1 : 0;
            u.key[h] = grid.pegs[h];
            m.position.copy(oceanSeat(h, grid.covered[h]));
            colour(m, grid.pegs[h]);
        }
        if (u.temp) {
            u.fleet.remove(u.temp);
            u.temp = null;
        }
        u.ships.forEach((m, j) => {
            const pose = m.userData.pose;
            m.position.copy(pose.at);
            m.rotation.set(0, pose.rotY, 0);
            m.visible = j < ships;
        });
        u.shown = ships;
        placeCursor(u, show && i >= 0 ? marks[p].cursor[i] : -1);
    }

    function placeCursor(u, h) {
        u.cursor = h;
        u.rowCursor.visible = h >= 0;
        u.colCursor.visible = h >= 0;
        if (h < 0) return;
        const c = cursorAt(h);
        u.rowCursor.position.copy(c.row);
        u.colCursor.position.copy(c.col);
    }

    async function moveCursor(u, h, tempo, run) {
        if (h === u.cursor) return;
        if (h < 0 || u.cursor < 0) {
            placeCursor(u, h);
            return;
        }
        const c = cursorAt(h);
        u.cursor = h;
        await Promise.all([ship.move(u.rowCursor, c.row, { tempo, run }), ship.move(u.colCursor, c.col, { tempo, run })]);
    }

    function render(i) {
        index = i;
        renderUnit(0, i);
        renderUnit(1, i);
        showDice(show ? diceFacesAt(show, i) : DEFAULT_FACES);
    }

    function buildFleet() {
        units.forEach((u, p) => {
            for (const m of u.ships) u.fleet.remove(m);
            u.ships = [];
            if (!show) return;
            for (const read of show.reads[p]) {
                if (!read.ship.length) continue;
                const s = read.ship[0];
                const m = makeShip(s.kind);
                m.userData.pose = shipPose(s, read.covered);
                u.fleet.add(m);
                u.ships.push(m);
            }
        });
    }

    // ---- animated changes ----

    async function animateCells(u, target, tempo, run) {
        const out = [];
        const into = [];
        for (let c = 0; c < 100; c++) {
            if (u.cells[c] === target[c]) continue;
            if (u.cells[c]) out.push(c);
            if (target[c]) into.push(c);
        }
        await Promise.all(out.map((c) => peg.remove(u.lidPegs[c], AX_LID, { tempo, run })));
        for (const c of out) u.cells[c] = 0;
        await Promise.all(into.map((c) => {
            colour(u.lidPegs[c], target[c]);
            u.cells[c] = target[c];
            return peg.insert(u.lidPegs[c], lidSeat(c), AX_LID, { tempo, run });
        }));
    }

    async function playBuildBeat(beat, i, mine) {
        const p = beat.player;
        const u = units[p];
        const read = show.reads[p][beat.read];
        const run = runner();
        const T = { peg: peg.settings.tempos.play, ship: ship.settings.tempos.play, dice: dice.settings.tempos.play };
        const rolls = [];
        if (read.cup.length) {
            settled(read.cup).forEach((f, k) => rolls.push(rollDie(parts.dice.d10[k], "d10", f, D10_YAW[k], T.dice, run)));
        }
        if (read.d12.length) rolls.push(rollDie(parts.dice.d12, "d12", read.d12[read.d12.length - 1], D12_YAW, T.dice, run));
        if (read.d6.length) rolls.push(rollDie(parts.dice.d6, "d6", read.d6[read.d6.length - 1], D6_YAW, T.dice, run));
        rolls.push(moveCursor(u, read.hole, T.ship, run));
        await Promise.all(rolls);
        if (mine !== gen) return;
        const moves = [];
        if (read.ship.length) {
            const m = u.ships[u.shown];
            u.shown += 1;
            for (const h of read.covered) u.covered[h] = 1;
            m.rotation.set(0, m.userData.pose.rotY, 0);
            moves.push(ship.place(m, m.userData.pose.at, { tempo: T.ship, run }));
        }
        await Promise.all(moves);
        if (mine !== gen) return;
        if (read.peg) {
            const m = u.ocean[read.hole];
            colour(m, read.peg);
            u.key[read.hole] = read.peg;
            await peg.insert(m, oceanSeat(read.hole, u.covered[read.hole]), AX_UP, { tempo: T.peg, run });
        }
    }

    async function playStepBeat(beat, i) {
        const p = beat.player;
        const u = units[p];
        const run = runner();
        const T = { peg: peg.settings.tempos.play, ship: ship.settings.tempos.play };
        await Promise.all([
            animateCells(u, cellsAt(p, i), T.peg, run),
            moveCursor(u, marks[p].cursor[i], T.ship, run),
        ]);
    }

    async function playBeat(beat, i) {
        await ready;
        if (!show) return;
        const mine = ++gen;
        if (index !== i - 1) render(i - 1);
        if (beat.kind === "build") await playBuildBeat(beat, i, mine);
        else await playStepBeat(beat, i);
        if (mine !== gen) return;
        await hold(BEAT_HOLD_MS);
        if (mine !== gen) return;
        render(i);
    }

    // Step: the summary's own moves, one after another.
    async function expandBuildBeat(beat, i, mine) {
        const p = beat.player;
        const u = units[p];
        const read = show.reads[p][beat.read];
        const run = runner();
        const T = { peg: peg.settings.tempos.step, ship: ship.settings.tempos.step, dice: dice.settings.tempos.step };
        await moveCursor(u, read.hole, T.ship, run);
        let piece = null;
        for (const m of read.moves) {
            if (mine !== gen) return;
            if (m.case === "Throw") await rollDie(parts.dice.d10[m.die], "d10", m.face, D10_YAW[m.die], T.dice, run);
            else if (m.case === "HoleDie") await rollDie(parts.dice.d12, "d12", m.face, D12_YAW, T.dice, run);
            else if (m.case === "Grow" || m.case === "Pick") await rollDie(parts.dice.d6, "d6", m.face, D6_YAW, T.dice, run);
            else if (m.case === "Piece") {
                if (piece) {
                    await ship.lift(piece, { tempo: T.ship, run });
                    u.fleet.remove(piece);
                }
                piece = makeShip(m.ship.kind);
                const pose = shipPose(m.ship, m.holes);
                piece.rotation.set(0, pose.rotY, 0);
                u.fleet.add(piece);
                u.temp = piece;
                await ship.place(piece, pose.at, { tempo: T.ship, run });
            } else if (m.case === "ReadDie") {
                await hold(READ_MS / T.dice);
            } else if (m.case === "PutPeg") {
                for (const h of read.covered) u.covered[h] = 1;
                const mesh = u.ocean[m.hole];
                colour(mesh, m.colour);
                await peg.insert(mesh, oceanSeat(m.hole, m.in_ship), AX_UP, { tempo: T.peg, run });
            }
        }
    }

    async function expandStepBeat(beat, i, mine, moves) {
        const p = beat.player;
        const u = units[p];
        const run = runner();
        const T = { peg: peg.settings.tempos.step, ship: ship.settings.tempos.step };
        // The lane and the cursor first (where the board is), then the pegs.
        const lane = new Int8Array(u.cells);
        lane[laneCell(5)] = marks[p].lane5[i];
        lane[laneCell(10)] = marks[p].lane10[i];
        await Promise.all([animateCells(u, lane, T.peg, run), moveCursor(u, marks[p].cursor[i], T.ship, run)]);
        for (const m of lidMoves(moves ?? [], workspaceCell)) {
            if (mine !== gen) return;
            if (m.t === "set") {
                const mesh = u.lidPegs[m.cell];
                if (m.from) await peg.remove(mesh, AX_LID, { tempo: T.peg, run });
                u.cells[m.cell] = m.into;
                if (m.into) {
                    colour(mesh, m.into);
                    await peg.insert(mesh, lidSeat(m.cell), AX_LID, { tempo: T.peg, run });
                }
            } else {
                const mesh = u.lidPegs[m.from];
                await peg.slide(mesh, lidSeat(m.from), lidSeat(m.to), AX_LID, { tempo: T.peg, run });
                mesh.position.copy(lidSeat(m.from));
                colour(mesh, 0);
                u.cells[m.from] = 0;
                colour(u.lidPegs[m.to], m.colour);
                u.lidPegs[m.to].position.copy(lidSeat(m.to));
                u.cells[m.to] = m.colour;
            }
        }
    }

    // moves: an exchange step's peg moves (generated step_moves); BUILD's are in the show.
    async function playExpanded(beat, i, moves) {
        await ready;
        if (!show) return;
        const mine = ++gen;
        if (index !== i - 1) render(i - 1);
        if (beat.kind === "build") await expandBuildBeat(beat, i, mine);
        else await expandStepBeat(beat, i, mine, moves);
        if (mine !== gen) return;
        render(i);
    }

    return {
        ready: () => ready,
        async loadShow(next) {
            await ready;
            gen += 1;
            show = next;
            marks = boardMarks(show);
            buildFleet();
            render(-1);
        },
        async seek(i) {
            await ready;
            gen += 1;
            if (show) render(i);
        },
        playBeat,
        playExpanded,
        async clearShow() {
            gen += 1;
            show = null;
            marks = null;
            if (!parts) return;
            buildFleet();
            render(-1);
        },
        setSpeed(multiplier) {
            speed = Math.max(0.01, Number(multiplier) || 1);
        },
        speed: () => speed,
        settle() {
            gen += 1;
            if (parts) render(index);
        },
        rememberSeated() {},
        /** For checks: the board as drawn (lid cells, key pegs, ships shown, cursor) per player. */
        board: () => units.map((u) => ({ cells: Array.from(u.cells), key: Array.from(u.key), ships: u.shown, cursor: u.cursor })),
        index: () => index,
    };
}
