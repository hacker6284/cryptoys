import { DEAL_SCALE, GATHER_MS } from "./constants.js";
import { easeInOutCubic, lerp } from "./beat-clock.js";
import { hopTo } from "./motion.js";
import { HAND_FACE_INDEXES, MSG_FACE_INDEXES } from "./unbox-hand.js";

/**
 * Lay the live 4×13 from the two physical decks. Message cards stream
 * from the toy-chest box; key cards stream from the shelf KEY box.
 * Each short unbox packet continues into its seats by shrinking
 * into place — no hide-prop / show-table cut, no material dissolve.
 */
export async function formSessionTable({
    table,
    clock,
    gen,
    messageOrder,
    keyOrder,
    keyBox,
    messageBox,
    packet,
    msgPacket,
}) {
    if (!table || !messageOrder?.length || !keyOrder?.length) return;

    table.group.visible = true;
    table.pileAtWorld(messageOrder, keyOrder, messageBox, keyBox);

    const packetFaces = new Set(packet?.cards?.length ? HAND_FACE_INDEXES : []);
    const msgFaces = new Set(msgPacket?.cards?.length ? MSG_FACE_INDEXES : []);
    const keyMeshes = table.cardsOf("key");
    const msgMeshes = table.cardsOf("message");
    for (const id of packetFaces) {
        if (keyMeshes[id]) keyMeshes[id].visible = false;
    }
    for (const id of msgFaces) {
        if (msgMeshes[id]) msgMeshes[id].visible = false;
    }

    const jobs = [];

    messageOrder.forEach((id, index) => {
        if (msgFaces.has(id)) return;
        const mesh = msgMeshes[id];
        if (!mesh) return;
        const to = table.seatLocal("message", index);
        jobs.push(hopSeat(mesh, to, clock, gen, {
            delay: 11 * index,
            ms: 440,
            lift: 0.32,
        }));
    });

    keyOrder.forEach((id, index) => {
        if (packetFaces.has(id)) return;
        const mesh = keyMeshes[id];
        if (!mesh) return;
        const to = table.seatLocal("key", index);
        jobs.push(hopSeat(mesh, to, clock, gen, {
            delay: 11 * index + 36,
            ms: 440,
            lift: 0.32,
        }));
    });

    function shrinkPacket(rig, faceIds, side, order, meshes) {
        if (!rig?.cards) return;
        rig.cards.forEach((hero, i) => {
            const faceId = faceIds[i];
            const seatIndex = order.indexOf(faceId);
            const destIndex = seatIndex >= 0 ? seatIndex : i;
            const seatLocal = table.seatLocal(side, destIndex);
            const seatWorld = table.group.localToWorld(seatLocal.clone());
            jobs.push(shrinkHero(hero, seatWorld, clock, gen, {
                delay: 28 * i,
                ms: 620,
            }).then(() => {
                const live = meshes[faceId];
                if (live) {
                    live.position.copy(seatLocal);
                    live.rotation.set(0, 0, 0);
                    live.visible = true;
                }
                hero.visible = false;
            }));
        });
    }

    shrinkPacket(packet, HAND_FACE_INDEXES, "key", keyOrder, keyMeshes);
    shrinkPacket(msgPacket, MSG_FACE_INDEXES, "message", messageOrder, msgMeshes);

    await Promise.all(jobs);
    table.showDecks(messageOrder, keyOrder);
}

function localFromWorld(group, world) {
    if (!world || !group?.worldToLocal) return { x: 0, y: 0.04, z: 0 };
    const v = group.position.clone();
    v.set(world.x, world.y, world.z);
    group.worldToLocal(v);
    return { x: v.x, y: v.y, z: v.z };
}

function eachCard(meshes, fn) {
    if (!meshes) return;
    if (Array.isArray(meshes)) {
        meshes.forEach(fn);
        return;
    }
    Object.values(meshes).forEach(fn);
}

/**
 * Reverse of formSessionTable: cards hop back toward the two boxes,
 * then hide. No dissolve, no instant 104-card vanish.
 */
export async function gatherSessionTable({
    table,
    clock,
    gen,
    keyBox,
    messageBox,
} = {}) {
    if (!table?.group || !clock) return;
    table.group.updateMatrixWorld?.(true);
    const keyAt = localFromWorld(table.group, keyBox);
    const msgAt = localFromWorld(table.group, messageBox || keyBox);
    const jobs = [];
    let n = 0;
    function pile(meshes, dest) {
        eachCard(meshes, (mesh) => {
            if (!mesh?.visible) return;
            const i = n++;
            jobs.push(hopTo(mesh, {
                x: dest.x,
                y: dest.y + 0.03,
                z: dest.z,
            }, clock, gen, {
                delay: Math.min(4 * i, 160),
                ms: Math.max(360, GATHER_MS - 160),
                lift: 2.6,
                ease: easeInOutCubic,
            }).then(() => {
                mesh.visible = false;
            }));
        });
    }
    pile(table.cardsOf?.("key"), keyAt);
    pile(table.cardsOf?.("message"), msgAt);
    await Promise.all(jobs);
    table.setCardsVisible?.(false);
}

function hopSeat(mesh, dest, clock, gen, opts) {
    mesh.visible = true;
    return hopTo(mesh, dest, clock, gen, opts);
}

function shrinkHero(mesh, dest, clock, gen, { delay = 0, ms = 620 } = {}) {
    return (async () => {
        if (delay) await clock.wait(delay, gen);
        const from = mesh.position.clone();
        const fromScale = mesh.scale.x || 1;
        await clock.tween(ms, (t) => {
            const k = easeInOutCubic(t);
            mesh.position.lerpVectors(from, dest, k);
            mesh.position.y = lerp(from.y, dest.y, k) + Math.sin(Math.PI * t) * 0.05;
            mesh.scale.setScalar(lerp(fromScale, DEAL_SCALE, k));
        }, { ease: (t) => t, generation: gen });
    })();
}
