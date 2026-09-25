import * as THREE from "three";
import { createCardTable } from "../doubledeal/table.js";
import { DEAL_SCALE } from "./constants.js";

/**
 * Playroom-only card table: the standalone DoubleDeal meshes, scaled
 * onto the felt. Camera stay/orbit is the pose controller's job.
 *
 * No opacity fades. Show/hide is a hard `visible` cut.
 */
export function stageCardTable(world, textures, { poses, visible = true } = {}) {
    const group = new THREE.Group();
    group.position.set(world.table.den.x, world.table.feltTopY + 0.003, world.table.den.z);
    group.scale.setScalar(DEAL_SCALE);
    group.visible = visible;
    world.scene.add(group);

    const table = createCardTable({
        parent: group,
        faces: textures.faces,
        navy: textures.navy,
        red: textures.red,
    });

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
        show() {
            group.visible = true;
        },
        hide() {
            group.visible = false;
        },
        dispose,
    };
}
