import * as THREE from "three";
import { CARD_W, DEN } from "../playroom/constants.js";
import { POSES } from "../playroom/poses.js";
import { CARD_T } from "./deck-rig.js";
import { easeInOut, easeInOutCubic, easeOutCubic, easeOutQuart, lerp } from "./timeline.js";

export const SPIKE_SHOTS = {
    landing: {
        position: new THREE.Vector3(...POSES.landing.position),
        target: new THREE.Vector3(...POSES.landing.target),
        fov: POSES.landing.fov,
    },
    shelf: {
        position: new THREE.Vector3(...POSES.shelf.position),
        target: new THREE.Vector3(...POSES.shelf.target),
        fov: POSES.shelf.fov,
    },
    // Travel with the box; keep the table in frame so an empty close-up
    // cannot land before the prop does (the #29 shelf-hold lesson).
    travel: {
        position: new THREE.Vector3(DEN.x + 0.48, 1.24, DEN.z + 0.92),
        target: new THREE.Vector3(DEN.x, 0.86, DEN.z),
        fov: 32,
    },
    // Three-quarter of the landed 67 mm box — front label + closed flap.
    unbox: {
        position: new THREE.Vector3(DEN.x + 0.12, 0.95, DEN.z + 0.34),
        target: new THREE.Vector3(DEN.x, 0.83, DEN.z),
        fov: 26,
    },
    deal: {
        position: new THREE.Vector3(DEN.x + 0.20, 1.08, DEN.z + 0.62),
        target: new THREE.Vector3(DEN.x, 0.82, DEN.z + 0.12),
        fov: 28,
    },
    seated: {
        position: new THREE.Vector3(...POSES.doubledeal.position),
        target: new THREE.Vector3(...POSES.doubledeal.target),
        fov: POSES.doubledeal.fov,
    },
};

const look = new THREE.Vector3();

export function applyShot(camera, shot) {
    camera.position.copy(shot.position);
    camera.fov = shot.fov;
    camera.up.set(0, 1, 0);
    look.copy(shot.target);
    camera.lookAt(look);
    camera.updateProjectionMatrix();
}

export function captureShot(camera) {
    const target = new THREE.Vector3();
    camera.getWorldDirection(target);
    target.multiplyScalar(1.2).add(camera.position);
    return {
        position: camera.position.clone(),
        target,
        fov: camera.fov,
    };
}

export function playShot(camera, to, clock, gen, {
    ms = 900,
    delay = 0,
    track = null,
    ease = easeInOutCubic,
} = {}) {
    const fromPos = camera.position.clone();
    const fromTarget = look.clone();
    const fromFov = camera.fov;
    const toPos = to.position.clone();
    const toTarget = to.target.clone();
    const toFov = to.fov;
    const tracked = new THREE.Vector3();

    async function run() {
        if (delay > 0) await clock.wait(delay, gen);
        await clock.tween(ms, (t) => {
            camera.position.lerpVectors(fromPos, toPos, t);
            camera.fov = lerp(fromFov, toFov, t);
            if (track && t < 0.74) {
                const p = track();
                if (p) look.set(p.x, p.y, p.z);
                else look.lerpVectors(fromTarget, toTarget, t);
            } else if (track) {
                const p = track();
                if (p) {
                    tracked.set(p.x, p.y, p.z);
                    look.lerpVectors(tracked, toTarget, (t - 0.74) / 0.26);
                } else {
                    look.lerpVectors(fromTarget, toTarget, t);
                }
            } else {
                look.lerpVectors(fromTarget, toTarget, t);
            }
            camera.up.set(0, 1, 0);
            camera.lookAt(look);
            camera.updateProjectionMatrix();
        }, { ease, generation: gen });
        if (!track) applyShot(camera, to);
    }
    return run();
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

function hopTo(mesh, dest, clock, gen, { ms = 520, lift = 0.08, ease = easeInOut } = {}) {
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
    const root = document.documentElement;
    if (root) root.dataset.beat = beat;
}

export function tableOrigin(world) {
    return {
        x: world.table.den.x,
        y: world.table.feltTopY,
        z: world.table.den.z,
    };
}

export async function finishTableau(world, rig, camera, keyLight) {
    const origin = tableOrigin(world);
    const surfaceY = feltY(world);
    applyShot(camera, SPIKE_SHOTS.seated);
    rig.setFlap(1);
    rig.setSleeveOpacity(0.0);
    rig.group.position.set(origin.x - 0.16, origin.y + 0.012, origin.z - 0.02);
    rig.group.rotation.set(0.15, 0.2, 0.35);
    if (keyLight) keyLight.intensity = 0.35;
    rig.innerGlow.intensity = 0;
    const dests = rig.cards.map((_, i) => cardSeat(i, rig.cards.length, origin, surfaceY));
    for (let i = 0; i < rig.cards.length; i++) {
        const mesh = rig.cards[i];
        world.scene.attach(mesh);
        mesh.position.set(dests[i].x, dests[i].y, dests[i].z);
        mesh.rotation.set(dests[i].rx, dests[i].ry, dests[i].rz);
        mesh.quaternion.setFromEuler(mesh.rotation);
        mesh.visible = true;
    }
    mark("done");
}

export async function playPhysical({ world, rig, camera, clock, gen, keyLight, trackBox }) {
    const origin = tableOrigin(world);
    const surfaceY = feltY(world);

    mark("settle");
    await clock.wait(360, gen);
    if (clock.dead(gen)) return;

    mark("unbox-hold");
    await playShot(camera, SPIKE_SHOTS.unbox, clock, gen, { ms: 640, ease: easeInOutCubic });
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
    const recede = playShot(camera, SPIKE_SHOTS.deal, clock, gen, { ms: 1100, track: trackBox });
    const slide = clock.tween(900, (t) => {
        rig.group.position.set(
            lerp(boxFrom.x, origin.x - 0.16, t),
            lerp(boxFrom.y, boxFrom.y - 0.006, t),
            lerp(boxFrom.z, origin.z - 0.02, t),
        );
        rig.group.rotation.set(
            lerp(boxRot.x, 0.15, t),
            lerp(boxRot.y, 0.22, t),
            lerp(boxRot.z, 0.38, t),
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
    await playShot(camera, SPIKE_SHOTS.seated, clock, gen, { ms: 980 });
    if (keyLight) {
        await clock.tween(400, (t) => {
            keyLight.intensity = lerp(keyLight.intensity, 0.35, t);
        }, { generation: gen });
    }
    mark("done");
}

export async function playBloom({ world, rig, camera, clock, gen, keyLight }) {
    const origin = tableOrigin(world);
    const surfaceY = feltY(world);

    mark("settle");
    await clock.wait(300, gen);
    if (clock.dead(gen)) return;

    mark("unbox-hold");
    await playShot(camera, SPIKE_SHOTS.unbox, clock, gen, { ms: 700 });
    await clock.tween(480, (t) => {
        if (keyLight) keyLight.intensity = lerp(0.15, 3.1, t);
        rig.innerGlow.intensity = lerp(0, 1.6, t);
        rig.sleeve.traverse((node) => {
            if (!node.isMesh || !node.material) return;
            const mats = Array.isArray(node.material) ? node.material : [node.material];
            for (const mat of mats) {
                if (!mat?.emissive) continue;
                mat.emissive.setHex(0xd48630);
                mat.emissiveIntensity = 0.55 * t;
            }
        });
    }, { ease: easeOutCubic, generation: gen });
    if (clock.dead(gen)) return;

    mark("bloom");
    rig.packet.visible = true;
    world.scene.attach(rig.packet);
    const dests = rig.cards.map((_, i) => cardSeat(i, rig.cards.length, origin, surfaceY));
    const bloom = clock.tween(1100, (t) => {
        rig.setSleeveOpacity(1 - easeInOut(t) * 0.92);
        rig.setFlap(t * 0.35);
        if (keyLight) keyLight.intensity = lerp(3.1, 1.6, t);
        rig.innerGlow.intensity = lerp(1.6, 0.2, t);
    }, { ease: (t) => t, generation: gen });

    const rises = rig.cards.map((mesh, i) => (async () => {
        await clock.wait(48 * i, gen);
        world.scene.attach(mesh);
        const dest = dests[i];
        const mid = (rig.cards.length - 1) / 2;
        const u = (i - mid) / Math.max(1, mid);
        const from = mesh.position.clone();
        const fromR = mesh.rotation.clone();
        await clock.tween(820, (t) => {
            const fan = Math.sin(Math.PI * Math.min(1, t * 1.15));
            mesh.position.set(
                lerp(from.x, dest.x, t),
                lerp(from.y, dest.y, t) + fan * 0.11,
                lerp(from.z, dest.z, t),
            );
            mesh.rotation.set(
                lerp(fromR.x, dest.rx, t),
                lerp(fromR.y, dest.ry, t) + fan * u * 0.35,
                lerp(fromR.z, dest.rz, t),
            );
            mesh.quaternion.setFromEuler(mesh.rotation);
        }, { ease: easeOutCubic, generation: gen });
    })());

    const cam = playShot(camera, SPIKE_SHOTS.deal, clock, gen, { ms: 1400, delay: 280 });
    await Promise.all([bloom, cam, ...rises]);
    if (clock.dead(gen)) return;

    mark("dissolve");
    const boxFrom = rig.group.position.clone();
    await clock.tween(520, (t) => {
        rig.setSleeveOpacity(0.08 * (1 - t));
        rig.group.position.y = lerp(boxFrom.y, boxFrom.y - 0.01, t);
        if (keyLight) keyLight.intensity = lerp(1.6, 0.45, t);
        rig.innerGlow.intensity = lerp(0.2, 0, t);
    }, { generation: gen });
    rig.setSleeveOpacity(0);
    if (clock.dead(gen)) return;

    mark("pull");
    await playShot(camera, SPIKE_SHOTS.seated, clock, gen, { ms: 900 });
    mark("done");
}
