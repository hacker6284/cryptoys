import { mountMicro } from "../shared/micro.js";
import { GLTFLoader } from "three/addons/loaders/GLTFLoader.js";
import { DEN } from "../../playroom/constants.js";
import { easeInOutCubic, easeOutCubic } from "../../playroom/beat-clock.js";

// New primitive (no demo code yet): shake a dice cup and pour polyhedral
// dice into a felt tray. Kept simple: a scripted shake and pour, and a
// small fixed-step simulation (gravity, bounces, tray walls, rolling to
// rest on a face) run once per loop, so the first felt hit (the landing
// contact) is known before anything moves.
const MODELS = new URL("../models/", import.meta.url);
const DT = 1 / 240;
const G = 9.81;
const COLORS = [0xb8322c, 0xd0702a, 0xd8b23a, 0x2f8a5a, 0x2f5f9a, 0x6a3f8f, 0xf1ead8];
const SETS = {
    poly: ["d4", "d6", "d8", "d12", "d20", "d20b"],
    d6: ["d6", "d6", "d6", "d6", "d6"],
    d20: ["d20", "d20b"],
};
const SIZE = { d4: 0.0125, d6: 0.0085, d8: 0.0105, d12: 0.0105, d20: 0.0115, d20b: 0.0115 };

let THREE = null;
let tray = null;
let cup = null;
let cupPivot = null;
const dice = [];
let raf = 0;
let feltY = 0;
const TRAY = { x: 0, z: 0, hx: 0.1216, hz: 0.0816 };
const CUP_HOME = { x: 0.175, y: 0.1, z: 0.0 };

function pipTexture(n) {
    const c = document.createElement("canvas");
    c.width = c.height = 128;
    const g = c.getContext("2d");
    g.fillStyle = "#f3ecdc";
    g.fillRect(0, 0, 128, 128);
    g.fillStyle = "#1d1a17";
    const at = { 1: [[64, 64]], 2: [[36, 36], [92, 92]], 3: [[34, 34], [64, 64], [94, 94]], 4: [[36, 36], [92, 36], [36, 92], [92, 92]], 5: [[34, 34], [94, 34], [64, 64], [34, 94], [94, 94]], 6: [[36, 32], [92, 32], [36, 64], [92, 64], [36, 96], [92, 96]] }[n];
    for (const [x, y] of at) {
        g.beginPath();
        g.arc(x, y, 11, 0, Math.PI * 2);
        g.fill();
    }
    const tex = new THREE.CanvasTexture(c);
    tex.colorSpace = THREE.SRGBColorSpace;
    return tex;
}

function makeDie(kind, i) {
    const s = SIZE[kind];
    let geo;
    let mat;
    if (kind === "d6") {
        geo = new THREE.BoxGeometry(s * 2, s * 2, s * 2);
        mat = [1, 6, 2, 5, 3, 4].map((n) => new THREE.MeshStandardMaterial({ map: pipTexture(n), roughness: 0.38 }));
    } else {
        geo = kind === "d4" ? new THREE.TetrahedronGeometry(s)
            : kind === "d8" ? new THREE.OctahedronGeometry(s)
                : kind === "d12" ? new THREE.DodecahedronGeometry(s)
                    : new THREE.IcosahedronGeometry(s);
        mat = new THREE.MeshStandardMaterial({ color: COLORS[i % COLORS.length], roughness: 0.32, metalness: 0.02, flatShading: true });
    }
    const mesh = new THREE.Mesh(geo, mat);
    mesh.castShadow = true;
    mesh.receiveShadow = true;
    // Face normals (outward) and the inradius: rest height and settling.
    const pos = geo.attributes.position;
    const normals = [];
    const a = new THREE.Vector3();
    const b = new THREE.Vector3();
    const c = new THREE.Vector3();
    let inradius = Infinity;
    const count = geo.index ? geo.index.count : pos.count;
    for (let t = 0; t < count; t += 3) {
        const idx = (k) => (geo.index ? geo.index.getX(t + k) : t + k);
        a.fromBufferAttribute(pos, idx(0));
        b.fromBufferAttribute(pos, idx(1));
        c.fromBufferAttribute(pos, idx(2));
        const n = new THREE.Vector3().subVectors(b, a).cross(new THREE.Vector3().subVectors(c, a)).normalize();
        const d = n.dot(a);
        if (d < 0) n.negate();
        inradius = Math.min(inradius, Math.abs(d));
        if (!normals.some((m) => m.dot(n) > 0.999)) normals.push(n);
    }
    geo.computeBoundingSphere();
    return { mesh, normals, inradius, outer: geo.boundingSphere.radius, frames: [], kind };
}

function rng(seed) {
    let s = seed >>> 0;
    return () => {
        s = (s * 1664525 + 1013904223) >>> 0;
        return s / 4294967296;
    };
}

/** Cup pose at time t (ms) into the loop: shake, then pour. */
function cupPose(T, t) {
    const pose = { x: CUP_HOME.x, y: CUP_HOME.y, z: CUP_HOME.z, tilt: 0, roll: 0 };
    if (t < T.shakeMs) {
        const u = t / 1000;
        const env = Math.sin(Math.PI * Math.min(1, t / T.shakeMs));
        const w = 2 * Math.PI * T.shakeHz;
        pose.x += Math.sin(w * u) * (T.shakeAmp / 1000) * env;
        pose.y += Math.abs(Math.sin(w * u * 0.5)) * (T.shakeAmp / 2000) * env;
        pose.roll = Math.sin(w * u + 0.6) * (T.shakeTilt * Math.PI / 180) * env;
        return pose;
    }
    const p = Math.min(1, (t - T.shakeMs) / T.pourMs);
    const k = easeInOutCubic(p);
    pose.tilt = k * (T.pourAngle * Math.PI / 180);
    pose.x -= k * 0.05;
    pose.y += k * 0.03;
    return pose;
}

function applyCup(pose) {
    cupPivot.position.set(TRAY.x + pose.x, feltY + pose.y, TRAY.z + pose.z);
    cupPivot.rotation.set(pose.roll * 0.3, 0, pose.tilt + pose.roll);
}

/** Simulate every die from the release; returns the first felt hit (ms from release). */
function simulate(T, seed) {
    const rand = rng(seed);
    const restY = feltY + 0.0075;
    const releaseT = T.shakeMs + T.pourMs * T.releaseAt;
    const before = cupPose(T, releaseT - 8);
    const at = cupPose(T, releaseT);
    applyCup(at);
    cupPivot.updateMatrixWorld(true);
    const mouth = new THREE.Vector3(0, 0.0995, 0).applyMatrix4(cupPivot.matrixWorld);
    const vCup = new THREE.Vector3((at.x - before.x) / 0.008, (at.y - before.y) / 0.008, 0);
    let first = Infinity;
    let last = 0;
    const states = dice.map((d, i) => {
        const p = mouth.clone().add(new THREE.Vector3((rand() - 0.5) * 0.02, -0.004 * i, (rand() - 0.5) * 0.03));
        const v = vCup.clone().multiplyScalar(0.3).add(new THREE.Vector3(-0.12 - rand() * 0.22, rand() * 0.15, (rand() - 0.5) * 0.3));
        const q = new THREE.Quaternion().setFromEuler(new THREE.Euler(rand() * 6.3, rand() * 6.3, rand() * 6.3));
        const w = new THREE.Vector3(rand() - 0.5, rand() - 0.5, rand() - 0.5).multiplyScalar(40);
        d.frames = [];
        return { d, p, v, q, w, delay: i * 0.012, rest: false, rolling: false, settle: null };
    });
    const steps = Math.ceil(3 / DT);
    const tmpQ = new THREE.Quaternion();
    const down = new THREE.Vector3(0, -1, 0);
    for (let n = 0; n <= steps; n++) {
        const time = n * DT;
        for (const s of states) {
            const { d } = s;
            if (time >= s.delay && !s.rest) {
                const floor = restY + d.inradius;
                if (!s.rolling) s.v.y -= G * DT;
                s.p.addScaledVector(s.v, DT);
                const ang = s.w.length();
                if (ang > 1e-6) s.q.premultiply(tmpQ.setFromAxisAngle(s.w.clone().divideScalar(ang), ang * DT));
                // Tray walls.
                const lim = { x: TRAY.hx - d.outer, z: TRAY.hz - d.outer };
                for (const ax of ["x", "z"]) {
                    const c = ax === "x" ? TRAY.x : TRAY.z;
                    if (s.p.y < restY + 0.03 && Math.abs(s.p[ax] - c) > lim[ax]) {
                        s.p[ax] = c + Math.sign(s.p[ax] - c) * lim[ax];
                        s.v[ax] *= -0.45;
                    }
                }
                if (!s.rolling && s.p.y <= floor && s.v.y < 0) {
                    first = Math.min(first, time);
                    s.p.y = floor;
                    s.v.y = -s.v.y * T.restitution;
                    s.v.x *= 0.72;
                    s.v.z *= 0.72;
                    s.w.multiplyScalar(0.6);
                    if (s.v.y < 0.12) {
                        s.rolling = true;
                        s.v.y = 0;
                    }
                }
                if (s.rolling) {
                    s.p.y = floor;
                    const decay = Math.exp(-T.friction * DT);
                    s.v.x *= decay;
                    s.v.z *= decay;
                    // Rolling: spin follows the slide, then the die settles onto a face.
                    s.w.set(s.v.z, 0, -s.v.x).divideScalar(Math.max(d.inradius, 1e-3));
                    const speed = Math.hypot(s.v.x, s.v.z);
                    if (speed < 0.05) {
                        if (!s.settle) {
                            let best = null;
                            let bestDot = -2;
                            for (const nrm of d.normals) {
                                const wn = nrm.clone().applyQuaternion(s.q);
                                const dot = wn.dot(down);
                                if (dot > bestDot) {
                                    bestDot = dot;
                                    best = wn;
                                }
                            }
                            const fix = new THREE.Quaternion().setFromUnitVectors(best, down);
                            s.settle = { from: s.q.clone(), to: fix.multiply(s.q.clone()), t: 0 };
                        }
                        s.w.set(0, 0, 0);
                        s.settle.t = Math.min(1, s.settle.t + DT / 0.12);
                        s.q.slerpQuaternions(s.settle.from, s.settle.to, easeOutCubic(s.settle.t));
                        if (s.settle.t >= 1 && speed < 0.004) {
                            s.rest = true;
                            last = Math.max(last, time);
                        }
                    }
                }
            }
            if (n % 2 === 0) d.frames.push(time < s.delay ? null : { p: s.p.clone(), q: s.q.clone() });
        }
        // Dice keep apart (cheap sphere push).
        for (let i = 0; i < states.length; i++) {
            for (let j = i + 1; j < states.length; j++) {
                const A = states[i];
                const B = states[j];
                if (time < A.delay || time < B.delay) continue;
                const min = (A.d.outer + B.d.outer) * 0.85;
                const dx = B.p.x - A.p.x;
                const dz = B.p.z - A.p.z;
                const dist = Math.hypot(dx, dz);
                if (dist < min && Math.abs(A.p.y - B.p.y) < min) {
                    const push = (min - dist) / 2 / Math.max(dist, 1e-4);
                    A.p.x -= dx * push;
                    A.p.z -= dz * push;
                    B.p.x += dx * push;
                    B.p.z += dz * push;
                    if (A.rest) A.rest = false;
                    if (B.rest) B.rest = false;
                }
            }
        }
    }
    return { firstMs: Number.isFinite(first) ? first * 1000 : 0, lastMs: (last || 1.5) * 1000, releaseMs: releaseT };
}

function animate(duration, step) {
    cancelAnimationFrame(raf);
    return new Promise((resolve) => {
        const start = performance.now();
        const tick = (now) => {
            const t = now - start;
            step(t);
            if (t < duration) raf = requestAnimationFrame(tick);
            else resolve();
        };
        raf = requestAnimationFrame(tick);
    });
}

function showFrame(ms) {
    const i = Math.floor(ms / (DT * 2000));
    for (const d of dice) {
        const f = d.frames[Math.min(i, d.frames.length - 1)];
        d.mesh.visible = Boolean(f);
        if (f) {
            d.mesh.position.copy(f.p);
            d.mesh.quaternion.copy(f.q);
        }
    }
}

let loopIndex = 0;

void mountMicro({
    id: "dice-cup",
    title: "Dice cup: shake and pour",
    summary: "A leather dice cup shakes, then pours polyhedral dice into the felt tray. Separate shake, pour/slam and settle sounds: the landing contact is the first die to hit the felt, the settle contact the last die coming to rest.",
    source: "new (no demo code yet) · models: Scrounger bs-ecbs procedural cup + felt tray; dice are three.js polyhedra",
    camera: { position: [DEN.x + 0.24, 1.1, DEN.z + 0.52], target: [DEN.x + 0.075, 0.82, DEN.z], fov: 36 },
    timingTitle: "Timing (starting values: no demo code yet)",
    loopGapMs: 700,
    choices: [{ key: "set", label: "Dice", value: "poly", options: [["poly", "polyhedral (d4 d6 d8 d12 d20 d20)"], ["d6", "five d6"], ["d20", "two d20"]] }],
    timing: [
        { key: "shakeMs", label: "shakeMs", min: 0, max: 2500, step: 10, value: 900, unit: " ms" },
        { key: "shakeHz", label: "shake rate", min: 2, max: 12, step: 0.5, value: 6.5, unit: " Hz" },
        { key: "shakeAmp", label: "shake travel", min: 0, max: 40, step: 1, value: 14, unit: " mm" },
        { key: "shakeTilt", label: "shake tilt", min: 0, max: 30, step: 1, value: 9, unit: "°" },
        { key: "pourMs", label: "pourMs", min: 100, max: 1500, step: 10, value: 520, unit: " ms" },
        { key: "pourAngle", label: "pour angle", min: 60, max: 160, step: 1, value: 118, unit: "°" },
        { key: "releaseAt", label: "release (of pour)", min: 0.2, max: 1, step: 0.01, value: 0.55, unit: "" },
        { key: "restitution", label: "bounce", min: 0, max: 0.7, step: 0.01, value: 0.32, unit: "" },
        { key: "friction", label: "felt friction", min: 0.5, max: 12, step: 0.1, value: 4.5, unit: "/s" },
        { key: "holdMs", label: "dice rest for", min: 0, max: 3000, step: 50, value: 900, unit: " ms" },
    ],
    slots: [
        { name: "shake", label: "Cup shake", contact: "the shake starts", from: [["dice-cup", "shake"]], gapMs: 300, voices: 2 },
        { name: "land", label: "Dice land", contact: "the first die hits the felt", from: [["dice-cup", "pour-slam"]], gapMs: 300, voices: 2 },
        { name: "settle", label: "Dice settle", contact: "the last die comes to rest", from: [["dice-cup", "settle"]], gapMs: 300, voices: 2 },
    ],
    async setup(ctx) {
        THREE = ctx.THREE;
        ctx.status("Loading the cup and tray…");
        const loader = new GLTFLoader();
        const load = (file) => loader.loadAsync(new URL(file, MODELS).href).then((g) => g.scene);
        [tray, cup] = await Promise.all([load("proc_dice_tray_felt_260x180.glb"), load("proc_dice_cup_95mm.glb")]);
        for (const obj of [tray, cup]) {
            obj.traverse((n) => {
                if (n.isMesh) {
                    n.castShadow = true;
                    n.receiveShadow = true;
                    if (n.material) {
                        n.material.side = THREE.DoubleSide;
                        // The felt inset sits on the tray floor: keep it in front (no z-fight).
                        if (/felt/i.test(n.material.name)) {
                            n.material.color.setHex(0x1f5a3c);
                            n.material.polygonOffset = true;
                            n.material.polygonOffsetFactor = -2;
                            n.material.polygonOffsetUnits = -4;
                        }
                    }
                }
            });
        }
        feltY = ctx.world.table.feltTopY + 0.0005;
        TRAY.x = DEN.x;
        TRAY.z = DEN.z;
        tray.position.set(TRAY.x, feltY, TRAY.z);
        ctx.world.scene.add(tray);
        cupPivot = new THREE.Group();
        cupPivot.name = "micro-dice-cup";
        cupPivot.add(cup);
        ctx.world.scene.add(cupPivot);
    },
    stop() {
        cancelAnimationFrame(raf);
    },
    async reset(ctx) {
        for (const d of dice.splice(0)) d.mesh.parent?.remove(d.mesh);
        SETS[ctx.choice("set")].forEach((kind, i) => {
            const d = makeDie(kind, i);
            d.mesh.visible = false;
            ctx.world.scene.add(d.mesh);
            dice.push(d);
        });
        applyCup(cupPose(this.T(ctx), 0));
    },
    T(ctx) {
        const out = {};
        for (const k of ["shakeMs", "shakeHz", "shakeAmp", "shakeTilt", "pourMs", "pourAngle", "releaseAt", "restitution", "friction", "holdMs"]) out[k] = ctx.timing(k);
        return out;
    },
    async cycle(ctx) {
        const gen = ctx.alive;
        const T = this.T(ctx);
        const { firstMs, lastMs, releaseMs } = simulate(T, 1234 + loopIndex * 7919);
        loopIndex += 1;
        for (const d of dice) d.mesh.visible = false;
        applyCup(cupPose(T, 0));
        const landAt = releaseMs + firstMs;
        const contacts = [["shake", 0], ["land", landAt], ["settle", releaseMs + lastMs]];
        const lead = ctx.leadIn(contacts);
        if (lead && !(await ctx.wait(lead))) return;
        if (gen !== ctx.alive) return;
        const t0 = performance.now();
        for (const [slot, at] of contacts) ctx.contact(slot, t0 + at);
        const total = releaseMs + 2600;
        await animate(total, (t) => {
            if (gen !== ctx.alive) return;
            applyCup(cupPose(T, Math.min(t, T.shakeMs + T.pourMs)));
            if (t >= releaseMs) showFrame(t - releaseMs);
        });
        if (gen !== ctx.alive) return;
        // Cup back upright; dice stay until the next loop.
        await animate(400, (t) => {
            const k = easeInOutCubic(Math.min(1, t / 400));
            const end = cupPose(T, T.shakeMs + T.pourMs);
            applyCup({ ...end, x: end.x + (CUP_HOME.x - end.x) * k, y: end.y + (CUP_HOME.y - end.y) * k, tilt: end.tilt * (1 - k) });
        });
        await ctx.wait(T.holdMs);
    },
    config(ctx) {
        return {
            demo: "dice-cup (new primitive)",
            paste: "DICE_CUP → the future dice demo; sounds → a demos/shared/sound.js table (offsetMs is relative to each contact)",
            DICE_CUP: this.T(ctx),
        };
    },
});
