import * as THREE from "three";
import { CARD_W } from "./constants.js";
import { easeInOutCubic, easeOutCubic, easeOutQuart, lerp } from "./beat-clock.js";
import { CARD_T } from "./unbox-rig.js";

export function createDealerKey(world) {
    const keyLight = new THREE.SpotLight(0xffc898, 0, 2.4, Math.PI / 5.4, 0.5, 1.15);
    keyLight.position.set(world.table.den.x + 0.16, 1.16, world.table.den.z + 0.30);
    keyLight.target.position.set(world.table.den.x, world.table.feltTopY + 0.04, world.table.den.z);
    world.scene.add(keyLight);
    world.scene.add(keyLight.target);
    return keyLight;
}

export function disposeDealerKey(world, keyLight) {
    if (!keyLight) return;
    world?.scene?.remove(keyLight);
    if (keyLight.target) world?.scene?.remove(keyLight.target);
    keyLight.dispose?.();
}

function feltY(world) {
    return world.table.feltTopY + CARD_T * 0.55;
}

function cardSeat(index, count, origin, surfaceY) {
    const mid = (count - 1) / 2;
    const u = count === 1 ? 0 : (index - mid) / mid;
    return {
        x: origin.x + (index - mid) * (CARD_W + 0.0075),
        y: surfaceY,
        z: origin.z + 0.20 + 0.014 * (1 - u * u),
        rx: 0,
        ry: u * 0.05,
        rz: (index % 2 === 0 ? -1 : 1) * 0.012,
    };
}

function hopTo(mesh, dest, clock, gen, { ms = 520, lift = 0.08, ease = easeInOutCubic } = {}) {
    const from = mesh.position.clone();
    const fromR = mesh.rotation.clone();
    return clock.tween(ms, (t) => {
        mesh.position.lerpVectors(from, dest, t);
        mesh.position.y = lerp(from.y, dest.y, t) + Math.sin(Math.PI * t) * lift;
        mesh.rotation.set(
            lerp(fromR.x, dest.rx, t),
            lerp(fromR.y, dest.ry, t),
            lerp(fromR.z, dest.rz, t),
        );
        mesh.quaternion.setFromEuler(mesh.rotation);
    }, { ease, generation: gen });
}

function mark(beat) {
    const root = typeof document !== "undefined" ? document.documentElement : null;
    if (root?.dataset?.playroomDebug === "1") root.dataset.beat = beat;
}

export function tableOrigin(world) {
    return {
        x: world.table.den.x,
        y: world.table.feltTopY,
        z: world.table.den.z,
    };
}

function restPose(world, name) {
    if (world.getBoxRestPose) return world.getBoxRestPose(name);
    const origin = tableOrigin(world);
    const side = name === "deck2" ? -1 : 1;
    return {
        position: {
            x: origin.x + side * 0.78,
            y: origin.y + 0.047,
            z: origin.z - 0.34,
        },
        rotation: { x: 0, y: side * 0.2, z: 0 },
    };
}

function slideBox(group, dest, clock, gen, { ms = 760, lift = 0.05 } = {}) {
    const from = group.position.clone();
    const fromR = group.rotation.clone();
    const to = dest.position;
    const toR = dest.rotation;
    return clock.tween(ms, (t) => {
        group.position.lerpVectors(from, to, t);
        group.position.y = lerp(from.y, to.y, t) + Math.sin(Math.PI * t) * lift;
        group.rotation.set(
            lerp(fromR.x, toR.x, t),
            lerp(fromR.y, toR.y, t),
            lerp(fromR.z, toR.z, t),
        );
        group.quaternion.setFromEuler(group.rotation);
    }, { ease: easeInOutCubic, generation: gen });
}

export async function restBoxes({ world, clock, gen, names = ["deck", "deck2"] } = {}) {
    const jobs = names.map((name) => {
        const toy = world.toys[name];
        if (!toy) return Promise.resolve();
        return slideBox(toy, restPose(world, name), clock, gen, { ms: 520, lift: 0.03 });
    });
    await Promise.all(jobs);
}

/**
 * Physical take: hold the landed KEY tuck-box, open the flap, extract
 * a short packet, set the empty sleeve standing on the felt, hop eight
 * faces. Camera stays with the room story — this file does not snap
 * named shots. Does not write the live 4×13 seats.
 */
export async function playPhysical({ world, rig, poses, clock, gen, keyLight }) {
    const origin = tableOrigin(world);
    const surfaceY = feltY(world);

    mark("settle");
    await clock.wait(90, gen);
    if (clock.dead(gen)) return;

    mark("unbox-hold");
    await clock.tween(320, (t) => {
        if (keyLight) keyLight.intensity = lerp(0.2, 2.15, t);
        rig.innerGlow.intensity = lerp(0, 0.55, t);
    }, { ease: easeOutCubic, generation: gen });
    if (clock.dead(gen)) return;

    mark("flap");
    rig.packet.visible = true;
    await clock.tween(680, (t) => {
        rig.setFlap(t);
        if (keyLight) keyLight.intensity = lerp(2.15, 2.55, t);
    }, { ease: easeOutCubic, generation: gen });
    await clock.wait(120, gen);
    if (clock.dead(gen)) return;

    mark("extract");
    const packet = rig.packet;
    packet.visible = true;
    const fromY = packet.position.y;
    await clock.tween(760, (t) => {
        packet.position.y = lerp(fromY, 0.086, easeOutQuart(t));
        // Top card leads a few millimetres so the stack is not a brick.
        for (let i = 0; i < rig.cards.length; i++) {
            const lead = (i / Math.max(1, rig.cards.length - 1)) * 0.006 * t;
            rig.cards[i].position.y = 0.001 + lead;
        }
    }, { ease: (t) => t, generation: gen });
    if (clock.dead(gen)) return;

    mark("lay");
    world.scene.attach(packet);
    const layFrom = {
        x: packet.position.x,
        y: packet.position.y,
        z: packet.position.z,
        rx: packet.rotation.x,
        ry: packet.rotation.y,
        rz: packet.rotation.z,
    };
    const layTo = {
        x: origin.x,
        y: surfaceY + CARD_T * rig.cards.length * 0.5 + 0.002,
        z: origin.z + 0.07,
        rx: -Math.PI / 2,
        ry: 0.08,
        rz: 0,
    };
    await clock.tween(600, (t) => {
        packet.position.set(
            lerp(layFrom.x, layTo.x, t),
            lerp(layFrom.y, layTo.y, t) + Math.sin(Math.PI * t) * 0.04,
            lerp(layFrom.z, layTo.z, t),
        );
        packet.rotation.set(
            lerp(layFrom.rx, layTo.rx, t),
            lerp(layFrom.ry, layTo.ry, t),
            lerp(layFrom.rz, layTo.rz, t),
        );
        packet.quaternion.setFromEuler(packet.rotation);
    }, { ease: easeInOutCubic, generation: gen });
    if (clock.dead(gen)) return;

    mark("aside");
    const rest = restPose(world, "deck");
    const slide = slideBox(rig.group, rest, clock, gen, { ms: 780, lift: 0.055 });

    mark("deal");
    const dests = rig.cards.map((_, i) => cardSeat(i, rig.cards.length, origin, surfaceY));
    const jobs = [slide];
    for (let i = 0; i < rig.cards.length; i++) {
        const mesh = rig.cards[i];
        const dest = dests[i];
        jobs.push((async () => {
            await clock.wait(64 * i, gen);
            world.scene.attach(mesh);
            await hopTo(mesh, dest, clock, gen, {
                ms: 560,
                lift: 0.07,
                ease: easeOutCubic,
            });
        })());
    }
    await Promise.all(jobs);
    if (clock.dead(gen)) return;

    if (keyLight) {
        await clock.tween(280, (t) => {
            keyLight.intensity = lerp(keyLight.intensity, 0.45, t);
        }, { generation: gen });
    }
    mark("dealt");
}
