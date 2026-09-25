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

function playShot(poses, name, clock, gen, opts = {}) {
    if (!poses?.playTo) return Promise.resolve();
    if (clock.dead(gen)) {
        poses.snap?.(name);
        return Promise.resolve();
    }
    return poses.playTo(name, opts);
}

export function tableOrigin(world) {
    return {
        x: world.table.den.x,
        y: world.table.feltTopY,
        z: world.table.den.z,
    };
}

export function recedeSleevePose(world, boxY) {
    const origin = tableOrigin(world);
    return {
        x: origin.x - 0.16,
        y: boxY - 0.006,
        z: origin.z - 0.02,
        rx: 0.15,
        ry: 0.22,
        rz: 0.38,
    };
}

/**
 * Physical take: hold the landed KEY tuck-box, open the flap, extract
 * a short packet, recede the sleeve, hop eight faces, pull to the
 * seated DoubleDeal lean. Does not write the live 4×13 seats.
 */
export async function playPhysical({ world, rig, poses, clock, gen, keyLight, trackBox }) {
    const origin = tableOrigin(world);
    const surfaceY = feltY(world);

    mark("settle");
    await clock.wait(360, gen);
    if (clock.dead(gen)) return;

    mark("unbox-hold");
    await playShot(poses, "unbox", clock, gen, { duration: 640 });
    await clock.tween(420, (t) => {
        if (keyLight) keyLight.intensity = lerp(0.2, 2.15, t);
        rig.innerGlow.intensity = lerp(0, 0.55, t);
    }, { ease: easeOutCubic, generation: gen });
    if (clock.dead(gen)) return;

    mark("flap");
    rig.packet.visible = true;
    await clock.tween(720, (t) => {
        rig.setFlap(t);
        if (keyLight) keyLight.intensity = lerp(2.15, 2.55, t);
    }, { ease: easeOutCubic, generation: gen });
    await clock.wait(180, gen);
    if (clock.dead(gen)) return;

    mark("extract");
    const packet = rig.packet;
    packet.visible = true;
    const fromY = packet.position.y;
    await clock.tween(780, (t) => {
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
    await clock.tween(640, (t) => {
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

    mark("recede");
    const boxFrom = rig.group.position.clone();
    const boxRot = rig.group.rotation.clone();
    const recedeTo = recedeSleevePose(world, boxFrom.y);
    const recede = playShot(poses, "unbox_deal", clock, gen, {
        duration: 1100,
        track: trackBox,
    });
    const slide = clock.tween(900, (t) => {
        rig.group.position.set(
            lerp(boxFrom.x, recedeTo.x, t),
            lerp(boxFrom.y, recedeTo.y, t),
            lerp(boxFrom.z, recedeTo.z, t),
        );
        rig.group.rotation.set(
            lerp(boxRot.x, recedeTo.rx, t),
            lerp(boxRot.y, recedeTo.ry, t),
            lerp(boxRot.z, recedeTo.rz, t),
        );
        rig.group.quaternion.setFromEuler(rig.group.rotation);
        if (keyLight) keyLight.intensity = lerp(2.55, 1.1, t);
        rig.innerGlow.intensity = lerp(0.55, 0, t);
    }, { ease: easeInOutCubic, generation: gen });

    mark("deal");
    const dests = rig.cards.map((_, i) => cardSeat(i, rig.cards.length, origin, surfaceY));
    const jobs = [recede, slide];
    for (let i = 0; i < rig.cards.length; i++) {
        const mesh = rig.cards[i];
        const dest = dests[i];
        jobs.push((async () => {
            await clock.wait(70 * i, gen);
            world.scene.attach(mesh);
            await hopTo(mesh, dest, clock, gen, {
                ms: 540,
                lift: 0.07,
                ease: easeOutCubic,
            });
        })());
    }
    await Promise.all(jobs);
    if (clock.dead(gen)) return;

    mark("pull");
    await playShot(poses, "doubledeal", clock, gen, { duration: 980 });
    if (keyLight) {
        await clock.tween(400, (t) => {
            keyLight.intensity = lerp(keyLight.intensity, 0.35, t);
        }, { generation: gen });
    }
    mark("done");
}
