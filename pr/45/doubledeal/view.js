import * as THREE from "three";
import { OrbitControls } from "three/addons/controls/OrbitControls.js";
import { CARD_W, KEY_X, MESSAGE_X } from "./layout.js";
import { createCardTable, loadCardTextures, PASS_Z } from "./table.js";

export async function mountTable(canvas, messageOrder, keyOrder) {
    const renderer = new THREE.WebGLRenderer({ canvas, antialias: true, alpha: true });
    renderer.setPixelRatio(Math.min(window.devicePixelRatio, 2));
    const anisotropy = renderer.capabilities.getMaxAnisotropy();
    const { faces, navy, red } = await loadCardTextures(anisotropy);

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

    const table = createCardTable({ parent: scene, faces, navy, red });

    function framePoints(points, target, yTop) {
        const dir = new THREE.Vector3(0, 1.35, 1).normalize();
        const look = target || new THREE.Vector3(0, 0, 0);
        const top = yTop ?? 0.78;
        let lo = 3;
        let hi = 140;
        let best = hi;
        for (let i = 0; i < 28; i++) {
            const dist = (lo + hi) / 2;
            camera.position.copy(look).add(dir.clone().multiplyScalar(dist));
            camera.lookAt(look);
            camera.updateMatrixWorld(true);
            const inside = points.every((point) => {
                const ndc = point.clone().project(camera);
                return ndc.z < 1 && Math.abs(ndc.x) < 0.9 && ndc.y < top && ndc.y > -0.7;
            });
            if (inside) {
                best = dist;
                hi = dist;
            } else {
                lo = dist;
            }
        }
        camera.position.copy(look).add(dir.clone().multiplyScalar(best));
        camera.lookAt(look);
        camera.updateMatrixWorld(true);
        controls.target.copy(look);
        controls.update();
    }

    function frameTable() {
        follow = true;
        framePoints(table.tablePoints(), new THREE.Vector3(0, 0, 0), 0.78);
    }

    function frameTeach(kind) {
        follow = false;
        if (kind === "pass" || kind === "unpass" || kind === "reset") {
            framePoints(table.teachPoints(kind), new THREE.Vector3(KEY_X, 0, PASS_Z * 0.35), 0.42);
            return;
        }
        if (kind === "compose" || kind === "uncompose") {
            framePoints(table.teachPoints(kind), new THREE.Vector3(0, 0, 0), 0.42);
            return;
        }
        framePoints(table.teachPoints(kind), new THREE.Vector3(MESSAGE_X, 0, 0), 0.42);
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

    table.showDecks(messageOrder, keyOrder);
    resize();
    loop();

    function dispose() {
        cancelAnimationFrame(frame);
        controls.dispose();
        table.dispose({ textures: true });
        renderer.dispose();
    }

    return {
        showDecks: table.showDecks,
        play: table.play,
        measure: table.measure,
        snapshot: table.snapshot,
        restore: table.restore,
        applyInstant: table.applyInstant,
        frameTeach,
        frameTable,
        highlightRow: table.highlightRow,
        highlightCol: table.highlightCol,
        highlightSeat: table.highlightSeat,
        highlightCard: table.highlightCard,
        clearHighlights: table.clearHighlights,
        rowRanks: table.rowRanks,
        colRanks: table.colRanks,
        dispose,
    };
}
