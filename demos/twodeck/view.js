import * as THREE from "three";
import { OrbitControls } from "three/addons/controls/OrbitControls.js";
import {
    CARD_D,
    CARD_W,
    KEY_X,
    MESSAGE_X,
    ROW_PITCH,
    cell,
    edgeGap,
    restingClearance,
} from "./layout.js";

const SUIT_FILE = ["club", "heart", "spade", "diamond"];
const RANK_FILE = ["1", "2", "3", "4", "5", "6", "7", "8", "9", "10", "jack", "queen", "king"];

function loadImage(url) {
    return new Promise((resolve, reject) => {
        const image = new Image();
        image.onload = () => resolve(image);
        image.onerror = () => reject(new Error(`Could not load ${url}`));
        image.src = url;
    });
}

function paintTexture(image, anisotropy) {
    const canvas = document.createElement("canvas");
    canvas.width = image.width;
    canvas.height = image.height;
    const g = canvas.getContext("2d");
    g.fillStyle = "#fffdf8";
    g.fillRect(0, 0, canvas.width, canvas.height);
    g.drawImage(image, 0, 0);
    const texture = new THREE.CanvasTexture(canvas);
    texture.colorSpace = THREE.SRGBColorSpace;
    texture.anisotropy = anisotropy;
    return texture;
}

function gridPos(row, col, centerX) {
    const at = cell(row, col, centerX);
    return new THREE.Vector3(at.x, 0.04, at.z);
}

function pilePos(side, index, count) {
    const x = side === "hand" ? MESSAGE_X : KEY_X;
    const along = (index - (count - 1) / 2) * 0.04;
    return new THREE.Vector3(x + along, 0.03 + index * 0.008, 2.4);
}

// PassKey's two piles stay on the key side, in front of that grid. The message
// deck is still laid out during the decrypt schedule, so the hand cannot sit
// on the message's seats.
const PASS_Z = 1.5 * ROW_PITCH + CARD_D + 0.6;
const PASS_HAND_X = KEY_X - 1.55;
const PASS_KEY_X = KEY_X + 1.55;

function passPile(which, index, count) {
    const x = which === "hand" ? PASS_HAND_X : PASS_KEY_X;
    const along = (index - (count - 1) / 2) * 0.04;
    return new THREE.Vector3(x + along, 0.03 + index * 0.008, PASS_Z);
}

function rowPos(which, index) {
    const z = which === "key" ? -3.4 : which === "out" ? 3.4 : 0;
    return new THREE.Vector3((index - 25.5) * 0.22, which === "out" ? 0.08 : 0.04, z);
}

function meshBox(mesh) {
    return {
        minX: mesh.position.x - CARD_W / 2,
        maxX: mesh.position.x + CARD_W / 2,
        minZ: mesh.position.z - CARD_D / 2,
        maxZ: mesh.position.z + CARD_D / 2,
    };
}

export async function mountTable(canvas, messageOrder, keyOrder) {
    const renderer = new THREE.WebGLRenderer({ canvas, antialias: true, alpha: true });
    renderer.setPixelRatio(Math.min(window.devicePixelRatio, 2));
    const anisotropy = renderer.capabilities.getMaxAnisotropy();
    const faceImages = await Promise.all(SUIT_FILE.flatMap((suit) => RANK_FILE.map((rank) => loadImage(`./vendor/cards/${suit}_${rank}.png`))));
    const [navyImage, redImage] = await Promise.all([
        loadImage("./vendor/cards/back-navy.png"),
        loadImage("./vendor/cards/back-red.png"),
    ]);
    const faces = faceImages.map((image) => paintTexture(image, anisotropy));
    const navy = paintTexture(navyImage, anisotropy);
    const red = paintTexture(redImage, anisotropy);

    const scene = new THREE.Scene();
    scene.background = new THREE.Color(0x10241c);
    const camera = new THREE.PerspectiveCamera(36, 1, 0.1, 200);
    camera.position.set(0, 18, 14);
    const controls = new OrbitControls(camera, canvas);
    controls.target.set(0, 0, 0);
    controls.enableDamping = true;
    controls.dampingFactor = 0.08;
    controls.autoRotate = false;
    controls.minDistance = 6;
    controls.maxDistance = 90;
    controls.maxPolarAngle = Math.PI / 2 - 0.04;
    controls.update();
    let follow = true;
    controls.addEventListener("start", () => {
        follow = false;
    });
    scene.add(new THREE.AmbientLight(0xffffff, 0.72));
    const lamp = new THREE.DirectionalLight(0xfff6e8, 1.45);
    lamp.position.set(-6, 22, 10);
    scene.add(lamp);
    const fill = new THREE.DirectionalLight(0xd6e4f5, 0.55);
    fill.position.set(8, 12, -6);
    scene.add(fill);
    const feltRadius = Math.hypot(KEY_X + 6 * (CARD_W + 0.07) + CARD_W, 6) + 2;
    const felt = new THREE.Mesh(
        new THREE.CircleGeometry(feltRadius, 96),
        new THREE.MeshStandardMaterial({ color: 0x1b5c45, roughness: 1 }),
    );
    felt.rotation.x = -Math.PI / 2;
    felt.position.y = -0.05;
    scene.add(felt);

    const marker = new THREE.Mesh(
        new THREE.BoxGeometry(CARD_W, 0.01, CARD_D),
        new THREE.MeshBasicMaterial({ color: 0xf2d48a, transparent: true, opacity: 0 }),
    );
    marker.position.y = 0.01;
    scene.add(marker);

    function makeDeck(back) {
        const meshes = [];
        for (let id = 0; id < 52; id++) {
            const face = new THREE.MeshStandardMaterial({ map: faces[id], roughness: 0.86 });
            const backMat = new THREE.MeshStandardMaterial({ map: back, roughness: 0.9 });
            const edge = new THREE.MeshStandardMaterial({ color: 0xf7f1e6, roughness: 0.95 });
            const mesh = new THREE.Mesh(new THREE.BoxGeometry(CARD_W, 0.018, CARD_D), [edge, edge, face, backMat, edge, edge]);
            mesh.position.set(0, 0.04, 0);
            scene.add(mesh);
            meshes.push(mesh);
        }
        return meshes;
    }

    const message = makeDeck(navy);
    const key = makeDeck(red);
    const grid = [Array(13).fill(null), Array(13).fill(null), Array(13).fill(null), Array(13).fill(null)];
    let packet = [];
    let pace = 1;
    let generation = 0;

    function faceUp(mesh) { mesh.rotation.set(0, 0, 0); }
    function faceDown(mesh) { mesh.rotation.set(Math.PI, 0, 0); }

    function tween(ms, step) {
        const gen = generation;
        const scaled = ms / pace;
        return new Promise((resolve) => {
            const start = performance.now();
            function tick(now) {
                if (gen !== generation) {
                    resolve();
                    return;
                }
                const t = Math.min(1, (now - start) / scaled);
                const eased = t < 0.5 ? 2 * t * t : 1 - ((-2 * t + 2) ** 2) / 2;
                step(eased);
                if (t < 1) requestAnimationFrame(tick);
                else resolve();
            }
            requestAnimationFrame(tick);
        });
    }

    function moveTo(mesh, pos, ms, lift) {
        const from = mesh.position.clone();
        const hop = lift ? 0.9 : 0.25;
        return tween(ms, (t) => {
            mesh.position.lerpVectors(from, pos, t);
            mesh.position.y = pos.y + Math.sin(Math.PI * t) * hop;
        });
    }

    function clearGrid() {
        for (let r = 0; r < 4; r++) {
            for (let c = 0; c < 13; c++) grid[r][c] = null;
        }
    }

    function seatPacket(order, deck, major) {
        clearGrid();
        packet = order.map((id) => deck[id]);
        return Promise.all(order.map((id, index) => new Promise((resolve) => {
            const mesh = deck[id];
            faceUp(mesh);
            const row = major === "row" ? Math.floor(index / 13) : index % 4;
            const col = major === "row" ? index % 13 : Math.floor(index / 4);
            grid[row][col] = mesh;
            setTimeout(() => {
                moveTo(mesh, gridPos(row, col, MESSAGE_X), 260, true).then(resolve);
            }, index * (36 / pace));
        })));
    }

    async function slideRow(row, amount, ms) {
        if (amount % 13 === 0) {
            const mesh = grid[row][6];
            if (mesh) {
                const y = mesh.position.y;
                await tween(ms, (t) => {
                    mesh.position.y = y + Math.sin(Math.PI * t) * 0.18;
                });
            }
            return;
        }
        const next = Array(13).fill(null);
        const jobs = [];
        for (let c = 0; c < 13; c++) {
            const mesh = grid[row][c];
            if (!mesh) continue;
            const dest = (c - amount + 130) % 13;
            next[dest] = mesh;
            jobs.push(moveTo(mesh, gridPos(row, dest, MESSAGE_X), ms, false));
        }
        grid[row] = next;
        await Promise.all(jobs);
    }

    async function beltColumn(col, amount, ms) {
        if (amount % 4 === 0) return;
        const next = [null, null, null, null];
        const jobs = [];
        for (let r = 0; r < 4; r++) {
            const mesh = grid[r][col];
            if (!mesh) continue;
            const dest = ((r + amount) % 4 + 4) % 4;
            next[dest] = mesh;
            jobs.push(moveTo(mesh, gridPos(dest, col, MESSAGE_X), ms, true));
        }
        for (let r = 0; r < 4; r++) grid[r][col] = next[r];
        await Promise.all(jobs);
    }

    async function scoop(major) {
        const jobs = [];
        const sequence = [];
        if (major === "col") {
            for (let c = 0; c < 13; c++) {
                for (let r = 0; r < 4; r++) sequence.push(grid[r][c]);
            }
        } else {
            for (let r = 0; r < 4; r++) {
                for (let c = 0; c < 13; c++) sequence.push(grid[r][c]);
            }
        }
        clearGrid();
        packet = [];
        sequence.forEach((mesh, index) => {
            if (!mesh) return;
            packet.push(mesh);
            jobs.push(moveTo(mesh, pilePos("hand", index, 52), major === "col" ? 240 : 300, major !== "col"));
        });
        await Promise.all(jobs);
    }

    async function placeCard(step, ms) {
        const mesh = message[step.card];
        faceUp(mesh);
        const target = gridPos(step.row, step.col, MESSAGE_X);
        if (step.flag === 1) {
            const drop = target.clone();
            drop.y = 1.4;
            mesh.position.copy(drop);
            await moveTo(mesh, target, ms, false);
        } else {
            await moveTo(mesh, target, ms, true);
        }
        grid[step.row][step.col] = mesh;
        marker.material.opacity = 0;
    }

    async function showScan(row) {
        marker.material.opacity = 0.85;
        marker.material.color.setHex(0xf2d48a);
        for (let c = 0; c < 13; c++) {
            await tween(8, (t) => {
                marker.position.copy(gridPos(row, c, MESSAGE_X));
                marker.position.y = 0.02;
                marker.material.opacity = 0.35 + 0.5 * (1 - t);
            });
        }
    }

    async function uncompose(step, ms) {
        const jobs = [];
        step.key.forEach((id, index) => {
            faceUp(key[id]);
            jobs.push(moveTo(key[id], rowPos("key", index), ms, false));
        });
        step.message.forEach((id, index) => {
            faceUp(message[id]);
            jobs.push(moveTo(message[id], rowPos("message", index), ms, false));
        });
        await Promise.all(jobs);
        for (let j = 0; j < 52; j++) {
            const seat = step.key.indexOf(j);
            const card = step.message[j];
            key[j].position.y = 0.45;
            message[card].position.y = 0.45;
            await moveTo(message[card], rowPos("out", seat), ms * 0.45, true);
            key[j].position.y = 0.04;
        }
    }

    async function resetKey(step, ms) {
        await Promise.all(step.key.map((id, index) => {
            faceUp(key[id]);
            const row = Math.floor(index / 13);
            const col = index % 13;
            return moveTo(key[id], gridPos(row, col, KEY_X), ms, false);
        }));
    }

    async function takeCard(step, ms) {
        const mesh = message[step.card];
        faceUp(mesh);
        if (grid[step.row][step.col] === mesh) grid[step.row][step.col] = null;
        await moveTo(mesh, pilePos("hand", step.amount, 52), ms, true);
    }

    async function compose(step, ms) {
        const jobs = [];
        step.key.forEach((id, index) => {
            faceUp(key[id]);
            jobs.push(moveTo(key[id], rowPos("key", index), ms, false));
        });
        step.message.forEach((id, index) => {
            faceUp(message[id]);
            jobs.push(moveTo(message[id], rowPos("message", index), ms, false));
        });
        await Promise.all(jobs);
        for (let j = 0; j < 52; j++) {
            const seat = step.key.indexOf(j);
            const card = step.message[seat];
            key[j].position.y = 0.45;
            message[card].position.y = 0.45;
            await moveTo(message[card], rowPos("out", j), ms * 0.45, true);
            key[j].position.y = 0.04;
        }
    }

    async function pass(step, ms) {
        const controller = key[step.card];
        faceUp(controller);
        await moveTo(controller, new THREE.Vector3(0, 1.1, 0), ms, false);
        const handIds = step.hand.slice();
        const keyIds = step.key.slice();
        if (step.amount > 0) {
            const spinning = handIds.slice(0, step.amount);
            await Promise.all(spinning.map((id) => moveTo(key[id], new THREE.Vector3(PASS_HAND_X, 0.9, PASS_Z), ms * 0.6, false)));
        }
        if (step.flag === 2) marker.material.color.setHex(0xe7b15a);
        await Promise.all([
            ...handIds.map((id, index) => {
                faceDown(key[id]);
                return moveTo(key[id], passPile("hand", index, handIds.length), ms, false);
            }),
            ...keyIds.map((id, index) => {
                if (id !== step.card) faceDown(key[id]);
                return moveTo(key[id], passPile("key", index, keyIds.length), ms, id === step.card);
            }),
        ]);
        faceUp(controller);
        marker.material.opacity = 0;
    }

    function laidOut(order, deck, centerX) {
        if (order.length !== 52) throw new Error("Each deck on the table is 52 cards.");
        const seen = new Set(order);
        if (seen.size !== 52) throw new Error("A deck on the table repeated a card.");
        order.forEach((id, index) => {
            const mesh = deck[id];
            faceUp(mesh);
            const row = Math.floor(index / 13);
            const col = index % 13;
            mesh.position.copy(gridPos(row, col, centerX));
        });
    }

    function showDecks(nextMessage, nextKey) {
        generation += 1;
        clearGrid();
        marker.material.opacity = 0;
        laidOut(nextMessage, message, MESSAGE_X);
        laidOut(nextKey, key, KEY_X);
        const gap = measure().between;
        if (!(gap > 0)) throw new Error("The two decks overlap on the table.");
    }

    function measure() {
        const messageBoxes = message.map(meshBox);
        const keyBoxes = key.map(meshBox);
        let within = Infinity;
        for (const deck of [messageBoxes, keyBoxes]) {
            for (let i = 0; i < deck.length; i++) {
                for (let j = i + 1; j < deck.length; j++) within = Math.min(within, edgeGap(deck[i], deck[j]));
            }
        }
        let between = Infinity;
        for (const a of messageBoxes) {
            for (const b of keyBoxes) between = Math.min(between, edgeGap(a, b));
        }
        return { within, between, designed: restingClearance() };
    }

    async function play(step, nextPace) {
        pace = nextPace || 1;
        const ms = 280;
        if (step.kind === "reset") {
            await resetKey(step, ms);
            return;
        }
        if (step.kind === "pass") {
            await pass(step, ms);
            return;
        }
        if (step.kind === "counter") {
            await seatPacket(step.message, message);
            await Promise.all(step.message.slice(39).map((id) => {
                const mesh = message[id];
                const lifted = mesh.position.clone();
                lifted.y = 0.55;
                return moveTo(mesh, lifted, 180, false);
            }));
            return;
        }
        if (step.kind === "deal") {
            await seatPacket(step.message, message, "col");
            return;
        }
        if (step.kind === "dealrm") {
            await seatPacket(step.message, message, "row");
            return;
        }
        if (step.kind === "sumrow" || step.kind === "shift") {
            await slideRow(step.row, step.amount, step.kind === "shift" ? 320 : 380);
            return;
        }
        if (step.kind === "sumcol") {
            await beltColumn(step.col, step.amount, 300);
            return;
        }
        if (step.kind === "scoopcm") {
            await scoop("col");
            return;
        }
        if (step.kind === "scooprm") {
            await scoop("row");
            return;
        }
        if (step.kind === "mark") {
            clearGrid();
            marker.material.opacity = 0.9;
            marker.material.color.setHex(0xf2d48a);
            marker.position.copy(gridPos(2, 0, MESSAGE_X));
            marker.position.y = 0.02;
            await tween(180, () => {});
            return;
        }
        if (step.kind === "scan") {
            await showScan(step.row);
            return;
        }
        if (step.kind === "place") {
            await placeCard(step, step.flag === 1 ? 160 : 240);
            return;
        }
        if (step.kind === "take") {
            await takeCard(step, 200);
            return;
        }
        if (step.kind === "uncompose") {
            await uncompose(step, ms);
            return;
        }
        if (step.kind === "compose") {
            await compose(step, ms);
        }
    }

    function frameTable() {
        const dir = new THREE.Vector3(0, 1.25, 1).normalize();
        const points = [];
        for (const center of [MESSAGE_X, KEY_X]) {
            for (const col of [0, 12]) {
                for (const row of [0, 3]) {
                    const at = gridPos(row, col, center);
                    for (const sx of [-1, 1]) {
                        for (const sz of [-1, 1]) {
                            points.push(at.clone().add(new THREE.Vector3(sx * CARD_W / 2, 0, sz * CARD_D / 2)));
                        }
                    }
                }
            }
        }
        let lo = 4;
        let hi = 140;
        let best = hi;
        for (let i = 0; i < 28; i++) {
            const dist = (lo + hi) / 2;
            camera.position.copy(dir).multiplyScalar(dist);
            camera.lookAt(0, 0, 0);
            camera.updateMatrixWorld(true);
            const inside = points.every((point) => {
                const ndc = point.clone().project(camera);
                return ndc.z < 1 && Math.abs(ndc.x) < 0.92 && Math.abs(ndc.y) < 0.78;
            });
            if (inside) {
                best = dist;
                hi = dist;
            } else {
                lo = dist;
            }
        }
        camera.position.copy(dir).multiplyScalar(best);
        camera.lookAt(0, 0, 0);
        camera.updateMatrixWorld(true);
        controls.target.set(0, 0, 0);
        controls.update();
    }

    let frame = 0;
    let lastW = 0;
    let lastH = 0;
    function resize() {
        const width = canvas.clientWidth;
        const height = canvas.clientHeight;
        if (width === 0 || height === 0 || (width === lastW && height === lastH)) return;
        lastW = width;
        lastH = height;
        camera.aspect = width / height;
        camera.updateProjectionMatrix();
        renderer.setSize(width, height, false);
        if (follow) frameTable();
    }
    function loop() {
        frame = requestAnimationFrame(loop);
        resize();
        controls.update();
        renderer.render(scene, camera);
    }

    showDecks(messageOrder, keyOrder);
    resize();
    loop();

    function dispose() {
        cancelAnimationFrame(frame);
        controls.dispose();
        renderer.dispose();
    }

    return { showDecks, play, measure, dispose };
}
