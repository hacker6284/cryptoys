import * as THREE from "three";
import { OrbitControls } from "three/addons/controls/OrbitControls.js";
import { SPOTS, parseMove, quarterSpin } from "./cube.js";

const COLOR = {
    W: 0xf4f1ea,
    Y: 0xe2c44b,
    R: 0xc13b3b,
    O: 0xd46a2e,
    B: 0x2f5f9a,
    G: 0x2f8a5a,
};
const PLASTIC = 0x141418;
const AXIS = { xp: 0, xn: 1, yp: 2, yn: 3, zp: 4, zn: 5 };
const CENTERS = [
    [4, 0, 1, 0],
    [13, 1, 0, 0],
    [22, 0, 0, 1],
    [31, 0, -1, 0],
    [40, -1, 0, 0],
    [49, 0, 0, -1],
];

function centerOf(facelets, color) {
    for (const [index, x, y, z] of CENTERS) {
        if (facelets[index] === color) return [x, y, z];
    }
    return null;
}

function orientMatrix(up, front) {
    const [ux, uy, uz] = up;
    const [fx, fy, fz] = front;
    if (ux === 0 && uy === 1 && uz === 0 && fx === 0 && fy === 0 && fz === 1) return null;
    const cx = uy * fz - uz * fy;
    const cy = uz * fx - ux * fz;
    const cz = ux * fy - uy * fx;
    const m = new THREE.Matrix4();
    m.set(
        cx, cy, cz, 0,
        ux, uy, uz, 0,
        fx, fy, fz, 0,
        0, 0, 0, 1,
    );
    return m;
}

export function mountCube(canvas) {
    const renderer = new THREE.WebGLRenderer({ canvas, antialias: true, alpha: true });
    renderer.setPixelRatio(Math.min(window.devicePixelRatio, 2));
    const scene = new THREE.Scene();
    const camera = new THREE.PerspectiveCamera(32, 1, 0.1, 100);
    camera.position.set(4.2, 4.6, 6.4);
    const controls = new OrbitControls(camera, canvas);
    controls.target.set(0, 0, 0);
    controls.enableDamping = true;
    controls.dampingFactor = 0.08;
    controls.autoRotate = false;
    controls.minDistance = 4;
    controls.maxDistance = 20;
    controls.update();
    scene.add(new THREE.AmbientLight(0xffffff, 0.72));
    const key = new THREE.DirectionalLight(0xffffff, 1.4);
    key.position.set(4, 8, 5);
    scene.add(key);
    const fill = new THREE.DirectionalLight(0x9bb7ff, 0.35);
    fill.position.set(-5, 2, -3);
    scene.add(fill);

    const group = new THREE.Group();
    scene.add(group);
    const meshes = new Map();
    for (let x = -1; x <= 1; x++) {
        for (let y = -1; y <= 1; y++) {
            for (let z = -1; z <= 1; z++) {
                if (x === 0 && y === 0 && z === 0) continue;
                const materials = [];
                for (let i = 0; i < 6; i++) {
                    materials.push(new THREE.MeshStandardMaterial({ color: PLASTIC, roughness: 0.45, metalness: 0.04 }));
                }
                const mesh = new THREE.Mesh(new THREE.BoxGeometry(0.94, 0.94, 0.94), materials);
                mesh.position.set(x * 1.02, y * 1.02, z * 1.02);
                mesh.userData.home = mesh.position.clone();
                mesh.userData.slot = { x, y, z };
                group.add(mesh);
                meshes.set(`${x},${y},${z}`, mesh);
            }
        }
    }

    let frame = 0;
    function resize() {
        const width = canvas.clientWidth;
        const height = canvas.clientHeight;
        if (width === 0 || height === 0) return;
        camera.aspect = width / height;
        camera.updateProjectionMatrix();
        renderer.setSize(width, height, false);
    }
    function loop() {
        frame = requestAnimationFrame(loop);
        resize();
        controls.update();
        renderer.render(scene, camera);
    }
    loop();

    function paint(facelets) {
        group.quaternion.identity();
        for (const mesh of meshes.values()) {
            mesh.position.copy(mesh.userData.home);
            mesh.quaternion.identity();
            mesh.rotation.set(0, 0, 0);
            mesh.scale.set(1, 1, 1);
            for (const mat of mesh.material) mat.emissive.setHex(0x000000);
        }
        SPOTS.forEach(([x, y, z, axis], i) => {
            const mesh = meshes.get(`${x},${y},${z}`);
            mesh.material[AXIS[axis]].color.setHex(COLOR[facelets[i]]);
        });
    }

    function clearHighlights() {
        for (const mesh of meshes.values()) {
            mesh.scale.set(1, 1, 1);
            for (const mat of mesh.material) mat.emissive.setHex(0x000000);
        }
    }

    function glow(mesh, hex, scale) {
        mesh.scale.setScalar(scale || 1);
        for (const mat of mesh.material) mat.emissive.setHex(hex);
    }

    function highlightLayer(face) {
        clearHighlights();
        for (const mesh of meshesOn(face)) glow(mesh, 0x3d3118, 1.02);
    }

    function highlightCubie(x, y, z) {
        clearHighlights();
        const mesh = meshes.get(`${x},${y},${z}`);
        if (!mesh) return;
        glow(mesh, 0x5a4520, 1.08);
        mesh.material[AXIS.yp].emissive.setHex(0xc4a574);
        mesh.material[AXIS.zp].emissive.setHex(0xc4a574);
    }

    function meshesOn(face) {
        const out = [];
        for (const mesh of meshes.values()) {
            const { x, y, z } = mesh.userData.slot;
            const hit = (face === 0 && y === 1) || (face === 1 && y === -1) || (face === 2 && x === 1)
                || (face === 3 && x === -1) || (face === 4 && z === 1) || (face === 5 && z === -1);
            if (hit) out.push(mesh);
        }
        return out;
    }

    function tween(ms, step) {
        return new Promise((resolve) => {
            const start = performance.now();
            function tick(now) {
                const t = Math.min(1, (now - start) / ms);
                const eased = t < 0.5 ? 2 * t * t : 1 - ((-2 * t + 2) ** 2) / 2;
                step(eased);
                if (t < 1) requestAnimationFrame(tick);
                else resolve();
            }
            requestAnimationFrame(tick);
        });
    }

    async function animateMove(move, ms) {
        const { face, turns } = parseMove(move);
        const spin = quarterSpin(face);
        const angle = spin.sign * (Math.PI / 2) * turns;
        const axis = new THREE.Vector3(spin.axis === "x" ? 1 : 0, spin.axis === "y" ? 1 : 0, spin.axis === "z" ? 1 : 0);
        const chosen = meshesOn(face);
        const pivot = new THREE.Group();
        group.add(pivot);
        for (const mesh of chosen) pivot.attach(mesh);
        await tween(ms, (t) => pivot.setRotationFromAxisAngle(axis, angle * t));
        for (const mesh of chosen) group.attach(mesh);
        group.remove(pivot);
    }

    async function animateReorient(from, up, front, ms) {
        const matrix = orientMatrix(centerOf(from, up), centerOf(from, front));
        if (!matrix) return;
        const quat = new THREE.Quaternion().setFromRotationMatrix(matrix);
        await tween(ms, (t) => {
            group.quaternion.identity();
            group.quaternion.slerp(quat, t);
        });
    }

    function dispose() {
        cancelAnimationFrame(frame);
        controls.dispose();
        renderer.dispose();
    }

    return { paint, animateMove, animateReorient, highlightLayer, highlightCubie, clearHighlights, dispose };
}
