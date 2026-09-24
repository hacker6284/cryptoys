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

// Cubie 0.94 + pitch 1.02 → bounding edge ≈ 2.98 in the standalone camera.
const ABSTRACT_EDGE = 2.98;

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

/**
 * Live cube used by the standalone page and the playroom adapter.
 * `edge` is the physical bounding size in world units (57 mm in the room).
 */
export function createCubeRig({ edge = ABSTRACT_EDGE, castShadow = false } = {}) {
    const root = new THREE.Group();
    const group = new THREE.Group();
    root.add(group);
    const scale = edge / ABSTRACT_EDGE;
    const cubie = 0.94 * scale;
    const pitch = 1.02 * scale;

    const meshes = new Map();
    for (let x = -1; x <= 1; x++) {
        for (let y = -1; y <= 1; y++) {
            for (let z = -1; z <= 1; z++) {
                if (x === 0 && y === 0 && z === 0) continue;
                const materials = [];
                for (let i = 0; i < 6; i++) {
                    materials.push(new THREE.MeshStandardMaterial({
                        color: PLASTIC,
                        roughness: 0.55,
                        metalness: 0.04,
                    }));
                }
                const mesh = new THREE.Mesh(new THREE.BoxGeometry(cubie, cubie, cubie), materials);
                mesh.position.set(x * pitch, y * pitch, z * pitch);
                mesh.castShadow = castShadow;
                mesh.receiveShadow = castShadow;
                mesh.userData.home = mesh.position.clone();
                mesh.userData.slot = { x, y, z };
                group.add(mesh);
                meshes.set(`${x},${y},${z}`, mesh);
            }
        }
    }

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
            const mat = mesh.material[AXIS[axis]];
            mat.color.setHex(COLOR[facelets[i]]);
            mat.needsUpdate = true;
        });
    }

    function clearHighlights() {
        for (const mesh of meshes.values()) {
            mesh.scale.set(1, 1, 1);
            for (const mat of mesh.material) mat.emissive.setHex(0x000000);
        }
    }

    function glow(mesh, hex, scaleValue) {
        mesh.scale.setScalar(scaleValue || 1);
        for (const mat of mesh.material) mat.emissive.setHex(hex);
    }

    function highlightLayer(face) {
        clearHighlights();
        const axis = face === 0 ? "yp" : face === 1 ? "yn" : face === 2 ? "xp" : face === 3 ? "xn" : face === 4 ? "zp" : "zn";
        for (const mesh of meshesOn(face)) {
            glow(mesh, 0x5a3d12, 1.05);
            mesh.material[AXIS[axis]].emissive.setHex(0xc4a574);
        }
    }

    function highlightCubie(x, y, z) {
        clearHighlights();
        const mesh = meshes.get(`${x},${y},${z}`);
        if (!mesh) return;
        glow(mesh, 0x3d3118, 1.04);
    }

    function highlightRuleB(facelets, up, front) {
        clearHighlights();
        const probe = meshes.get("1,1,1");
        if (probe) glow(probe, 0x3d3118, 1.03);
        const upAt = centerOf(facelets, up);
        const frontAt = centerOf(facelets, front);
        if (upAt) {
            const mesh = meshes.get(upAt.join(","));
            if (mesh) glow(mesh, 0xc4a574, 1.14);
        }
        if (frontAt) {
            const mesh = meshes.get(frontAt.join(","));
            if (mesh) glow(mesh, 0xe6c48a, 1.14);
        }
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
        group.traverse((object) => {
            if (!object.isMesh) return;
            object.geometry?.dispose();
            const mats = Array.isArray(object.material) ? object.material : [object.material];
            for (const mat of mats) mat?.dispose();
        });
        if (root.parent) root.parent.remove(root);
    }

    return {
        group: root,
        inner: group,
        paint,
        animateMove,
        animateReorient,
        highlightLayer,
        highlightCubie,
        highlightRuleB,
        clearHighlights,
        dispose,
    };
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

    const rig = createCubeRig();
    scene.add(rig.group);

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

    function dispose() {
        cancelAnimationFrame(frame);
        controls.dispose();
        renderer.dispose();
        rig.dispose();
    }

    return {
        paint: rig.paint,
        animateMove: rig.animateMove,
        animateReorient: rig.animateReorient,
        highlightLayer: rig.highlightLayer,
        highlightCubie: rig.highlightCubie,
        highlightRuleB: rig.highlightRuleB,
        clearHighlights: rig.clearHighlights,
        dispose,
    };
}
