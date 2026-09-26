import * as THREE from "three";
import { CARD_W } from "./constants.js";
import { easeInOutCubic, easeOutCubic, easeOutQuart, lerp } from "./beat-clock.js";
import { hopTo, markBeat, seatToys } from "./motion.js";
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

export function tableOrigin(world) {
    return {
        x: world.table.den.x,
        y: world.table.feltTopY,
        z: world.table.den.z,
    };
}

export function packetOrigin(world, name = "deck") {
    const origin = tableOrigin(world);
    if (name === "deck2") {
        return {
            x: origin.x - 0.30,
            y: origin.y,
            z: origin.z + 0.02,
        };
    }
    return origin;
}

export async function restBoxes({ world, clock, gen, names = ["deck", "deck2"] } = {}) {
    await seatToys(world, clock, gen, names, { ms: 520, lift: 0.03 });
}

function busy(rig, on) {
    if (!rig) return;
    if (rig.group) rig.group.userData.unboxBusy = on;
    if (rig.packet) rig.packet.userData.unboxBusy = on;
}

/**
 * Shared physical unbox: hold the landed tuck-box, open the flap,
 * extract a short packet, rest the empty sleeve, hop the faces.
 * KEY and MSG both use this — no closed-box fly-in for the second deck.
 * Camera stays with the room story — this file does not snap named shots.
 */
export async function playUnbox({
    world,
    rig,
    clock,
    gen,
    keyLight,
    name = "deck",
    origin,
} = {}) {
    if (!rig || !world) return;
    const pile = origin || packetOrigin(world, name);
    const surfaceY = feltY(world);

    busy(rig, true);
    markBeat(name === "deck2" ? "msg-settle" : "settle");
    await clock.wait(90, gen);
    if (clock.dead(gen)) {
        busy(rig, false);
        return;
    }

    markBeat(name === "deck2" ? "msg-unbox-hold" : "unbox-hold");
    await clock.tween(320, (t) => {
        if (keyLight) keyLight.intensity = lerp(keyLight.intensity || 0.2, 2.15, t);
        if (rig.innerGlow) rig.innerGlow.intensity = lerp(0, 0.55, t);
    }, { ease: easeOutCubic, generation: gen });
    if (clock.dead(gen)) {
        busy(rig, false);
        return;
    }

    markBeat(name === "deck2" ? "msg-flap" : "flap");
    rig.packet.visible = true;
    await clock.tween(680, (t) => {
        rig.setFlap(t);
        if (keyLight) keyLight.intensity = lerp(2.15, 2.55, t);
    }, { ease: easeOutCubic, generation: gen });
    await clock.wait(120, gen);
    if (clock.dead(gen)) {
        busy(rig, false);
        return;
    }

    markBeat(name === "deck2" ? "msg-extract" : "extract");
    const packet = rig.packet;
    packet.visible = true;
    packet.userData.unboxBusy = true;
    const fromY = packet.position.y;
    await clock.tween(760, (t) => {
        packet.position.y = lerp(fromY, 0.086, easeOutQuart(t));
        // Top card leads a few millimetres so the stack is not a brick.
        for (let i = 0; i < rig.cards.length; i++) {
            const lead = (i / Math.max(1, rig.cards.length - 1)) * 0.006 * t;
            rig.cards[i].position.y = 0.001 + lead;
        }
    }, { ease: (t) => t, generation: gen });
    if (clock.dead(gen)) {
        busy(rig, false);
        return;
    }

    markBeat(name === "deck2" ? "msg-lay" : "lay");
    world.scene.attach(packet);
    const layTo = {
        x: pile.x,
        y: surfaceY + CARD_T * rig.cards.length * 0.5 + 0.002,
        z: pile.z + 0.07,
        rx: -Math.PI / 2,
        ry: name === "deck2" ? -0.08 : 0.08,
        rz: 0,
    };
    await hopTo(packet, layTo, clock, gen, { ms: 600, lift: 0.04, ease: easeInOutCubic });
    if (clock.dead(gen)) {
        busy(rig, false);
        return;
    }

    markBeat(name === "deck2" ? "msg-aside" : "aside");
    const rest = world.getBoxRestPose?.(name);
    const slide = rest
        ? hopTo(rig.group, rest, clock, gen, { ms: 780, lift: 0.055, ease: easeInOutCubic })
        : Promise.resolve();

    markBeat(name === "deck2" ? "msg-deal" : "deal");
    const dests = rig.cards.map((_, i) => cardSeat(i, rig.cards.length, pile, surfaceY));
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
    if (clock.dead(gen)) {
        busy(rig, false);
        return;
    }

    if (keyLight) {
        await clock.tween(280, (t) => {
            keyLight.intensity = lerp(keyLight.intensity, 0.45, t);
        }, { generation: gen });
    }
    markBeat(name === "deck2" ? "msg-dealt" : "dealt");
    busy(rig, false);
}

/** KEY-only wrapper — same physical take as `playUnbox`. */
export async function playPhysical(opts) {
    return playUnbox({ ...opts, name: opts?.name || "deck" });
}

/**
 * Two physical unboxes on one continuous path. MSG flap starts while
 * KEY is still extracting / dealing so the second deck is pulled out
 * of its box, not flown in closed.
 */
export async function playDualUnbox({
    world,
    key,
    msg,
    clock,
    gen,
    keyLight,
} = {}) {
    const keyJob = playUnbox({
        world,
        rig: key,
        clock,
        gen,
        keyLight,
        name: "deck",
    });
    // Let KEY finish extract so the follow-cam can sit on that box
    // before MSG pulls the lens to the second sleeve.
    await clock.wait(1880, gen);
    if (clock.dead(gen)) {
        await keyJob;
        return;
    }
    const msgJob = msg
        ? playUnbox({
            world,
            rig: msg,
            clock,
            gen,
            name: "deck2",
        })
        : Promise.resolve();
    await Promise.all([keyJob, msgJob]);
}

/**
 * Close the tuck-box flap, then restow the packet. Used on leave so
 * the sleeve does not snap shut before the toys fly home.
 */
export async function playRestow({ rig, clock, gen, ms = 380 } = {}) {
    if (!rig) return;
    const from = Math.abs(rig.flapPivot?.rotation?.x || 0) / 2.15;
    if (clock && gen != null && from > 0.01 && !clock.dead(gen)) {
        await clock.tween(ms, (t) => {
            rig.setFlap?.(from * (1 - t));
        }, { ease: easeInOutCubic, generation: gen });
    }
    rig.restow?.();
    if (rig.group) rig.group.userData.unboxBusy = false;
    if (rig.packet) rig.packet.userData.unboxBusy = false;
}
