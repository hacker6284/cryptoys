import { DEAL_SCALE } from "./constants.js";
import { easeInOutCubic, lerp } from "./beat-clock.js";
import { hopTo } from "./motion.js";
import { HAND_FACE_INDEXES } from "./unbox-hand.js";

/**
 * Lay the live 4×13 from the two physical decks. Message cards stream
 * from the toy-chest box; key cards stream from the shelf KEY box.
 * The short unbox packet continues into its key seats by shrinking
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
}) {
    if (!table || !messageOrder?.length || !keyOrder?.length) return;

    table.group.visible = true;
    table.pileAtWorld(messageOrder, keyOrder, messageBox, keyBox);

    const packetFaces = new Set(packet?.cards?.length ? HAND_FACE_INDEXES : []);
    const keyMeshes = table.cardsOf("key");
    const msgMeshes = table.cardsOf("message");
    for (const id of packetFaces) {
        if (keyMeshes[id]) keyMeshes[id].visible = false;
    }

    const jobs = [];

    messageOrder.forEach((id, index) => {
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

    if (packet?.cards) {
        packet.cards.forEach((hero, i) => {
            const faceId = HAND_FACE_INDEXES[i];
            const seatIndex = keyOrder.indexOf(faceId);
            const destIndex = seatIndex >= 0 ? seatIndex : i;
            const seatLocal = table.seatLocal("key", destIndex);
            const seatWorld = table.group.localToWorld(seatLocal.clone());
            jobs.push(shrinkHero(hero, seatWorld, clock, gen, {
                delay: 28 * i,
                ms: 620,
            }).then(() => {
                const live = keyMeshes[faceId];
                if (live) {
                    live.position.copy(seatLocal);
                    live.rotation.set(0, 0, 0);
                    live.visible = true;
                }
                hero.visible = false;
            }));
        });
    }

    await Promise.all(jobs);
    table.showDecks(messageOrder, keyOrder);
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
