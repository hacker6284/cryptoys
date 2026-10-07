import * as THREE from "three";
import { TABLE_PACE, createCardTable } from "../doubledeal/table.js";
import { DEAL_SCALE } from "./constants.js";

/**
 * Playroom-only card table: the standalone DoubleDeal meshes, scaled
 * onto the felt. Camera stay/orbit is the pose controller's job.
 *
 * No opacity fades. Enter lays the 4×13 from the two physical decks —
 * cards start hidden and stream from the boxes, never a hide-prop /
 * show-table snap.
 */
export function stageCardTable(world, textures, { poses, visible = true, layout = null } = {}) {
    const group = new THREE.Group();
    // layout (doubledeal/real-layout.js REAL_LAYOUT): real-size cards whose
    // bottoms rest liftM above the felt; else the standalone table at DEAL_SCALE.
    group.position.set(world.table.den.x, world.table.feltTopY + (layout ? layout.liftM : 0.003), world.table.den.z);
    group.scale.setScalar(layout ? layout.scale : DEAL_SCALE);
    group.visible = visible;
    world.scene.add(group);

    const table = createCardTable({
        parent: group,
        faces: textures.faces,
        navy: textures.navy,
        red: textures.red,
        ...(layout ? { layout } : {}),
    });
    table.setCardsVisible(false);

    const scratch = new THREE.Vector3();
    // The dock's speed (shared/speed.js): 1× plays at TABLE_PACE.
    let speed = 1;

    function pileAtWorld(messageOrder, keyOrder, messageWorld, keyWorld) {
        group.updateMatrixWorld(true);
        const messageAt = messageWorld
            ? group.worldToLocal(scratch.copy(messageWorld)).clone()
            : null;
        const keyAt = keyWorld
            ? group.worldToLocal(scratch.copy(keyWorld)).clone()
            : null;
        table.pileDecks(messageOrder, keyOrder, messageAt, keyAt);
    }

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
        play: (step) => table.play(step, TABLE_PACE * speed, TABLE_PACE),
        setSpeed(multiplier) {
            speed = multiplier;
        },
        measure: table.measure,
        snapshot: table.snapshot,
        restore: table.restore,
        applyInstant: table.applyInstant,
        highlightRow: table.highlightRow,
        highlightCol: table.highlightCol,
        highlightSeat: table.highlightSeat,
        highlightCard: table.highlightCard,
        clearHighlights: table.clearHighlights,
        frameTeach,
        frameTable,
        rememberSeated() {},
        settle() {
            frameTable();
        },
        pileAtWorld,
        cardsOf: table.cardsOf,
        setCardsVisible: table.setCardsVisible,
        seatLocal: table.seatLocal,
        show() {
            group.visible = true;
        },
        hide() {
            group.visible = false;
        },
        dispose,
    };
}
