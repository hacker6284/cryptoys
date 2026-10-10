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
 * plays that step's own peg moves (bs/expand.js), one after another, fast.
 * Moves are the library's own (anim/peg, anim/ship, anim/dice), played on
 * the dock's speed with the pacer's frame skipping.
 *
 * The models load by path (BS_MODELS) so updated GLBs drop in by name.
 */
import * as THREE from "three";
import * as peg from "../anim/peg/index.js";
import * as ship from "../anim/ship/index.js";
import * as dice from "../anim/dice/index.js";
import { pacedWait, skipMs } from "../shared/pacer.js";
import { BS_DICE, REAL_SIZES } from "./constants.js";
import { OP, SHIP_LEN, emptyGrid, emptyWorkspace, expandBuild, expandStep } from "../bs/expand.js";

const MODELS = new URL("../bs/assets/models/", import.meta.url);
export const BS_MODELS = {
    red: "bs_unit_red.glb",
    blue: "bs_unit_blue.glb",
    pegs: "bs_pegs.glb",
    ships: "bs_ships.glb",
    d10: "facehunter_d10_22mm.glb",
    d12: "facehunter_d12_19mm.glb",
    d6: "facehunter_d6_16mm.glb",
    cup: "proc_dice_cup_95mm.glb",
};

// The unit GLB's grids (Scrounger's pack README §3; lid frame from
// bs_unit_render.py): hole centres at the measured 13.333 mm pitch.
const PITCH = REAL_SIZES.bsPitch.m;
const X0 = -0.06393; // column 1
const OCEAN_Z0 = -0.04683; // ocean row A (nearest the hinge)
const PLATE_Y = 0.0124; // ocean plate top
const DECK_UP = 0.006; // a peg in a ship's deck hole sits this much higher
const LID_Z0 = 0.135833; // target-grid row A, lid_pivot frame (farthest from the hinge)
const LID_FACE_Y = 0.005; // target-grid face, lid_pivot frame (pegs point −y)
const FRAME_LEFT_X = -0.0761; // the ocean grid's letter strip
const FRAME_TOP_Z = -0.059; // its number strip

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

/** Workspace cell (row × 10 + column) of register r's hole h, T1 (SPEC §6). */
export function workspaceCell(r, h) {
    const row = Math.floor(h / 9);
    const col = h % 9;
    if (r === "x") return row * 10 + col;
    if (r === "y") return (2 + row) * 10 + col;
    if (r === "c") return (8 + row) * 10 + col;
    if (r === "s") return h < 36 ? (4 + row) * 10 + col : 80 + (h - 36);
    throw new Error(`no register ${r}`);
}

/** Control-lane hole k (1 … 10): column 10, row k. */
export function laneCell(k) {
    return (k - 1) * 10 + 9;
}

/** The 100 workspace cells of one player: registers x, y, c (strip s optional) and the lane. */
export function workspaceCells(ws, lane5 = 0, lane10 = 0) {
    const cells = new Int8Array(100);
    for (const r of ["x", "y", "c", "s"]) {
        const reg = ws[r];
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
            const walk = st.op === OP.start || st.op === OP.square || st.op === OP.cube || st.op === OP.hit;
            if (walk && st.cell >= 0) {
                const holes = show.holes[p];
                const h = holes[st.cell];
                c.cursor = h < 0 ? 0 : h % 100;
                c.lane10 = h >= 100 ? 1 : h >= 0 && holes[st.cell + 1] === h ? 2 : 0;
            } else {
                c.cursor = -1;
                c.lane10 = 0;
            }
            const calling = st.op === OP.clear || st.op === OP.shot;
            c.lane5 = calling && next[beat.step] >= 0 && show.steps[next[beat.step]].op === OP.shot ? 1 : 0;
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
            // The dice cup at its sourced height; the dice as built (real size).
            const cup = g.cup.scene;
            const box = new THREE.Box3().setFromObject(cup);
            cup.scale.setScalar(REAL_SIZES.diceCup.m / (box.max.y - box.min.y));
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

/** The transmission fallback (Scrounger's pack README §3): plain transparency on the grid plates. */
export function useGlassFallback(root, on = true) {
    root.traverse((o) => {
        if (!o.isMesh) return;
        for (const m of Array.isArray(o.material) ? o.material : [o.material]) {
            if (!m || !("transmission" in m)) continue;
            if (on && m.transmission > 0) {
                m.userData.transmission = m.transmission;
                m.transmission = 0;
                m.transparent = true;
                m.opacity = 0.45;
                m.needsUpdate = true;
            } else if (!on && m.userData.transmission) {
                m.transmission = m.userData.transmission;
                m.transparent = false;
                m.opacity = 1;
                m.needsUpdate = true;
            }
        }
    });
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

    function shipPose(s, len) {
        const L = len ?? SHIP_LEN[s.kind];
        const first = s.row * 10 + s.col;
        const last = first + (L - 1) * (s.down ? 10 : 1);
        const at = oceanSeat(first, false).clone().add(oceanSeat(last, false)).multiplyScalar(0.5);
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

    function cursorPoses(h) {
        return {
            row: new THREE.Vector3(FRAME_LEFT_X, PLATE_Y, OCEAN_Z0 + Math.floor(h / 10) * PITCH),
            col: new THREE.Vector3(X0 + (h % 10) * PITCH, PLATE_Y, FRAME_TOP_Z),
        };
    }

    // ---- dice ----

    function restY(holder, kind, face) {
        const key = `${kind}:${face}`;
        if (restCache.has(key)) return restCache.get(key);
        const mesh = holder.userData.mesh;
        const q = dice.restQuaternion(kind, face, 0, THREE.Quaternion, THREE.Vector3);
        const pos = mesh.geometry.attributes.position;
        const v = new THREE.Vector3();
        let min = Infinity;
        for (let i = 0; i < pos.count; i++) {
            v.fromBufferAttribute(pos, i).multiply(mesh.scale).applyQuaternion(mesh.quaternion).applyQuaternion(q);
            min = Math.min(min, v.y);
        }
        restCache.set(key, -min);
        return -min;
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

    function runner() {
        const mine = gen;
        const reduced = Boolean(prefersReducedMotion());
        return (ms, step) => {
            if (mine !== gen) return Promise.resolve(false);
            const skip = reduced ? 0 : skipMs(ms, speed);
            if (skip !== null) {
                step(ms);
                return (skip > 0 ? pacedWait(skip) : Promise.resolve()).then(() => mine === gen);
            }
            const real = ms / speed;
            return new Promise((resolve) => {
                const t0 = performance.now();
                const tick = () => {
                    if (mine !== gen) {
                        resolve(false);
                        return;
                    }
                    const t = Math.min(real, performance.now() - t0);
                    step(t * speed);
                    if (t >= real) resolve(true);
                    else requestAnimationFrame(tick);
                };
                requestAnimationFrame(tick);
            });
        };
    }

    function hold(ms1x) {
        const mine = gen;
        if (prefersReducedMotion()) return Promise.resolve(mine === gen);
        return pacedWait(ms1x / speed).then(() => mine === gen);
    }

    // ---- state ----

    function wsOf(p, i) {
        const s = i >= 0 ? marks[p].step[i] : -1;
        if (s < 0) return emptyWorkspace(show.n);
        const st = show.steps[s];
        return { x: st.x.slice(), y: st.y.slice(), c: st.c.slice(), s: new Array(2 * show.n + 2).fill(0) };
    }

    function cellsAt(p, i) {
        if (i < 0) return new Int8Array(100);
        return workspaceCells(wsOf(p, i), marks[p].lane5[i], marks[p].lane10[i]);
    }

    function keyAt(p, i) {
        const count = i >= 0 ? marks[p].built[i] : 0;
        const grid = emptyGrid();
        let ships = 0;
        for (let r = 0; r < count; r++) {
            const read = show.reads[p][r];
            if (read.ship.length) {
                ships += 1;
                const s = read.ship[0];
                for (let t = 0; t < SHIP_LEN[s.kind]; t++) grid.covered[s.row * 10 + s.col + t * (s.down ? 10 : 1)] = true;
            }
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
        const c = cursorPoses(h);
        u.rowCursor.position.copy(c.row);
        u.colCursor.position.copy(c.col);
    }

    async function moveCursor(u, h, tempo, run) {
        if (h === u.cursor) return;
        if (h < 0 || u.cursor < 0) {
            placeCursor(u, h);
            return;
        }
        const c = cursorPoses(h);
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
                m.userData.pose = shipPose(s);
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
            for (const h of shipHolesOf(read.ship[0])) u.covered[h] = 1;
            moves.push(ship.place(m, m.userData.pose.at, { tempo: T.ship, run }).then(() => {
                m.rotation.set(0, m.userData.pose.rotY, 0);
            }));
            m.rotation.set(0, m.userData.pose.rotY, 0);
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

    function shipHolesOf(s) {
        return Array.from({ length: SHIP_LEN[s.kind] }, (_, t) => s.row * 10 + s.col + t * (s.down ? 10 : 1));
    }

    async function playStepBeat(beat, i, mine) {
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
        else await playStepBeat(beat, i, mine);
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
        const grid = keyAt(p, i - 1).grid;
        await moveCursor(u, read.hole, T.ship, run);
        let piece = null;
        for (const m of expandBuild(grid, read)) {
            if (mine !== gen) return;
            if (m.t === "d10") await rollDie(parts.dice.d10[m.die], "d10", m.face, D10_YAW[m.die], T.dice, run);
            else if (m.t === "d12") await rollDie(parts.dice.d12, "d12", m.face, D12_YAW, T.dice, run);
            else if (m.t === "d6") await rollDie(parts.dice.d6, "d6", m.face, D6_YAW, T.dice, run);
            else if (m.t === "ship") {
                if (piece) {
                    await ship.lift(piece, { tempo: T.ship, run });
                    u.fleet.remove(piece);
                }
                piece = makeShip(m.kind);
                const pose = shipPose(m, m.len);
                piece.rotation.set(0, pose.rotY, 0);
                u.fleet.add(piece);
                u.temp = piece;
                await ship.place(piece, pose.at, { tempo: T.ship, run });
            } else if (m.t === "read") {
                await hold(READ_MS / T.dice);
            } else if (m.t === "peg") {
                if (read.ship.length) for (const h of shipHolesOf(read.ship[0])) u.covered[h] = 1;
                const mesh = u.ocean[m.hole];
                colour(mesh, m.colour);
                await peg.insert(mesh, oceanSeat(m.hole, m.inShip), AX_UP, { tempo: T.peg, run });
            }
        }
    }

    async function expandStepBeat(beat, i, mine) {
        const p = beat.player;
        const u = units[p];
        const run = runner();
        const T = { peg: peg.settings.tempos.step, ship: ship.settings.tempos.step };
        const st = show.steps[beat.step];
        const ws = [wsOf(0, i - 1), wsOf(1, i - 1)];
        const moves = expandStep(ws, st, { n: show.n, toll: show.toll }, { cellValue: beat.cellValue, shared: beat.shared });
        // The lane and the cursor first (where the board is), then the pegs.
        const lane = new Int8Array(u.cells);
        lane[laneCell(5)] = marks[p].lane5[i];
        lane[laneCell(10)] = marks[p].lane10[i];
        await Promise.all([animateCells(u, lane, T.peg, run), moveCursor(u, marks[p].cursor[i], T.ship, run)]);
        for (const m of moves) {
            if (mine !== gen) return;
            if (m.t === "set") {
                const c = workspaceCell(m.r, m.h);
                const mesh = u.lidPegs[c];
                if (m.from) await peg.remove(mesh, AX_LID, { tempo: T.peg, run });
                u.cells[c] = m.to;
                if (m.to) {
                    colour(mesh, m.to);
                    await peg.insert(mesh, lidSeat(c), AX_LID, { tempo: T.peg, run });
                }
            } else if (m.t === "slide") {
                const a = workspaceCell(m.from.r, m.from.h);
                const b = workspaceCell(m.to.r, m.to.h);
                const mesh = u.lidPegs[a];
                await peg.slide(mesh, lidSeat(a), lidSeat(b), AX_LID, { tempo: T.peg, run });
                mesh.position.copy(lidSeat(a));
                colour(mesh, 0);
                u.cells[a] = 0;
                colour(u.lidPegs[b], m.colour);
                u.lidPegs[b].position.copy(lidSeat(b));
                u.cells[b] = m.colour;
            }
        }
    }

    async function playExpanded(beat, i) {
        await ready;
        if (!show) return;
        const mine = ++gen;
        if (index !== i - 1) render(i - 1);
        if (beat.kind === "build") await expandBuildBeat(beat, i, mine);
        else await expandStepBeat(beat, i, mine);
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
        glassFallback(on = true) {
            for (const u of units) useGlassFallback(u.root, on);
        },
    };
}
