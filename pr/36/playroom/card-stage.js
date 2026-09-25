import * as THREE from "three";
import { createCardTable } from "../doubledeal/table.js";
import { DEAL_SCALE } from "./constants.js";

const HANDOFF_MS = 240;

function prefersReducedMotion() {
    return Boolean(window.matchMedia?.("(prefers-reduced-motion: reduce)")?.matches);
}

function easeInOut(t) {
    return t < 0.5 ? 2 * t * t : 1 - ((-2 * t + 2) ** 2) / 2;
}

export function setTreeOpacity(root, opacity) {
    if (!root) return;
    root.traverse((node) => {
        if (!node.isMesh) return;
        const mats = Array.isArray(node.material) ? node.material : [node.material];
        for (const mat of mats) {
            if (!mat) continue;
            mat.transparent = opacity < 0.999;
            mat.opacity = opacity;
            if ("depthWrite" in mat) mat.depthWrite = opacity > 0.92;
        }
    });
    root.userData.fade = opacity;
}

export function fadeTree(root, to, { ms = HANDOFF_MS, snap = false } = {}) {
    if (!root) return Promise.resolve();
    if (snap || prefersReducedMotion() || ms <= 0) {
        setTreeOpacity(root, to);
        return Promise.resolve();
    }
    const from = Number.isFinite(root.userData.fade) ? root.userData.fade : (to > 0.5 ? 0 : 1);
    return new Promise((resolve) => {
        const start = performance.now();
        function tick(now) {
            const t = Math.min(1, (now - start) / ms);
            const o = from + (to - from) * easeInOut(t);
            setTreeOpacity(root, o);
            if (t < 1) requestAnimationFrame(tick);
            else resolve();
        }
        requestAnimationFrame(tick);
    });
}

/**
 * Playroom-only card table: the standalone DoubleDeal meshes, scaled
 * onto the felt. Camera stay/orbit is the pose controller's job.
 */
export function stageCardTable(world, textures, { poses, snap = false } = {}) {
    const group = new THREE.Group();
    group.position.set(world.table.den.x, world.table.feltTopY + 0.003, world.table.den.z);
    group.scale.setScalar(DEAL_SCALE);
    world.scene.add(group);

    const table = createCardTable({
        parent: group,
        faces: textures.faces,
        navy: textures.navy,
        red: textures.red,
    });
    if (!snap) setTreeOpacity(group, 0);

    const look = new THREE.Vector3();
    function tableTarget() {
        return group.getWorldPosition(look);
    }

    function frameTeach() {
        poses?.frame?.(tableTarget);
    }

    function frameTable() {
        poses?.releaseFrame?.();
    }

    function dispose() {
        poses?.releaseFrame?.();
        table.dispose();
        group.parent?.remove(group);
    }

    return {
        group,
        showDecks: table.showDecks,
        play: table.play,
        measure: table.measure,
        snapshot: table.snapshot,
        restore: table.restore,
        applyInstant: table.applyInstant,
        highlightRow: table.highlightRow,
        highlightCol: table.highlightCol,
        highlightSeat: table.highlightSeat,
        highlightCard: table.highlightCard,
        clearHighlights: table.clearHighlights,
        rowRanks: table.rowRanks,
        colRanks: table.colRanks,
        frameTeach,
        frameTable,
        rememberSeated() {},
        settle() {
            frameTable();
        },
        fadeIn(opts) {
            return fadeTree(group, 1, opts);
        },
        fadeOut(opts) {
            return fadeTree(group, 0, opts);
        },
        dispose,
    };
}
