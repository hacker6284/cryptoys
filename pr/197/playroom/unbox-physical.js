import * as THREE from "three";
import { CARD_W } from "./constants.js";
import { easeInOutCubic, easeOutCubic, easeOutQuart, lerp } from "./beat-clock.js";
import { hopTo, markBeat, seatToys } from "./motion.js";
import { CARD_T } from "./unbox-rig.js";

export function createDealerKey(world) {
    const keyLight = new THREE.SpotLight(0xffc898, 0, 2.4, Math.PI / 5.4, 0.5, 1.15);
    keyLight.position.set(world.table.den.x + 0.16, 1.16, world.table.den.z + 0.30);
    keyLight.target.position.set(world.table.den.x, world.table.feltTopY + 0.04, world.table.den.z);
    return world.lights.add("dealerKey", keyLight);
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
 * Unbox beat timings (ms at 1×) and easing names. One mutable object so
 * the microdemos (demos/micro/doubledeal-*) can tune it live; tuned
 * values paste straight back here.
 */
export const UNBOX_TIMING = {
    settleMs: 90,
    holdMs: 320,
    flapMs: 680,
    flapEase: "easeOutCubic",
    flapPauseMs: 120,
    extractMs: 760,
    extractEase: "easeOutQuart",
    extractRise: 0.086,
    extractLead: 0.006,
    layMs: 600,
    layLift: 0.04,
    layEase: "easeInOutCubic",
    asideMs: 780,
    asideLift: 0.055,
    asideEase: "easeInOutCubic",
    dealStaggerMs: 64,
    dealMs: 560,
    dealLift: 0.07,
    dealEase: "easeOutCubic",
    dimMs: 280,
};

export const UNBOX_EASES = {
    easeOutCubic,
    easeInOutCubic,
    easeOutQuart,
    linear: (t) => t,
};

function easeOf(name, fallback) {
    return UNBOX_EASES[name] || fallback;
}

/** Flap opens (the tuck tab lifts); the packet shows inside. */
export async function unboxFlap({ rig, clock, gen, keyLight, name = "deck", timing = UNBOX_TIMING } = {}) {
    markBeat(name === "deck2" ? "msg-flap" : "flap");
    rig.packet.visible = true;
    await clock.tween(timing.flapMs, (t) => {
        rig.setFlap(t);
        if (keyLight && !clock.dead(gen)) keyLight.intensity = lerp(2.15, 2.55, t);
    }, { ease: easeOf(timing.flapEase, easeOutCubic), generation: gen });
}

/** The short packet rises out of the open sleeve. */
export async function unboxExtract({ rig, clock, gen, name = "deck", timing = UNBOX_TIMING } = {}) {
    markBeat(name === "deck2" ? "msg-extract" : "extract");
    const packet = rig.packet;
    packet.visible = true;
    packet.userData.unboxBusy = true;
    const fromY = packet.position.y;
    const rise = easeOf(timing.extractEase, easeOutQuart);
    await clock.tween(timing.extractMs, (t) => {
        packet.position.y = lerp(fromY, timing.extractRise, rise(t));
        // Top card leads a few millimetres so the stack is not a brick.
        for (let i = 0; i < rig.cards.length; i++) {
            const lead = (i / Math.max(1, rig.cards.length - 1)) * timing.extractLead * t;
            rig.cards[i].position.y = 0.001 + lead;
        }
    }, { ease: (t) => t, generation: gen });
}

/** The packet is laid face-down on the felt in front of the box. */
export async function unboxLay({ world, rig, clock, gen, name = "deck", pile, timing = UNBOX_TIMING } = {}) {
    markBeat(name === "deck2" ? "msg-lay" : "lay");
    const packet = rig.packet;
    world.scene.attach(packet);
    const layTo = {
        x: pile.x,
        y: feltY(world) + CARD_T * rig.cards.length * 0.5 + 0.002,
        z: pile.z + 0.07,
        rx: -Math.PI / 2,
        ry: name === "deck2" ? -0.08 : 0.08,
        rz: 0,
    };
    await hopTo(packet, layTo, clock, gen, { ms: timing.layMs, lift: timing.layLift, ease: easeOf(timing.layEase, easeInOutCubic) });
}

/** The empty sleeve hops aside to its rest pose. */
export function unboxAside({ world, rig, clock, gen, name = "deck", timing = UNBOX_TIMING } = {}) {
    markBeat(name === "deck2" ? "msg-aside" : "aside");
    const rest = world.getBoxRestPose?.(name);
    return rest
        ? hopTo(rig.group, rest, clock, gen, { ms: timing.asideMs, lift: timing.asideLift, ease: easeOf(timing.asideEase, easeInOutCubic) })
        : Promise.resolve();
}

/** The packet's cards hop face-up into a short fan, one every stagger. */
export function unboxDeal({ world, rig, clock, gen, name = "deck", pile, timing = UNBOX_TIMING } = {}) {
    markBeat(name === "deck2" ? "msg-deal" : "deal");
    const surfaceY = feltY(world);
    const dests = rig.cards.map((_, i) => cardSeat(i, rig.cards.length, pile, surfaceY));
    const jobs = [];
    for (let i = 0; i < rig.cards.length; i++) {
        const mesh = rig.cards[i];
        const dest = dests[i];
        jobs.push((async () => {
            await clock.wait(timing.dealStaggerMs * i, gen);
            world.scene.attach(mesh);
            await hopTo(mesh, dest, clock, gen, {
                ms: timing.dealMs,
                lift: timing.dealLift,
                ease: easeOf(timing.dealEase, easeOutCubic),
            });
        })());
    }
    return Promise.all(jobs);
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
    timing = UNBOX_TIMING,
} = {}) {
    if (!rig || !world) return;
    const pile = origin || packetOrigin(world, name);
    const beat = { world, rig, clock, gen, keyLight, name, pile, timing };

    busy(rig, true);
    markBeat(name === "deck2" ? "msg-settle" : "settle");
    await clock.wait(timing.settleMs, gen);
    if (clock.dead(gen)) {
        busy(rig, false);
        return;
    }

    markBeat(name === "deck2" ? "msg-unbox-hold" : "unbox-hold");
    await clock.tween(timing.holdMs, (t) => {
        if (keyLight && !clock.dead(gen)) keyLight.intensity = lerp(keyLight.intensity || 0.2, 2.15, t);
        if (rig.innerGlow && !clock.dead(gen)) rig.innerGlow.intensity = lerp(0, 0.55, t);
    }, { ease: easeOutCubic, generation: gen });
    if (clock.dead(gen)) {
        busy(rig, false);
        return;
    }

    await unboxFlap(beat);
    await clock.wait(timing.flapPauseMs, gen);
    if (clock.dead(gen)) {
        busy(rig, false);
        return;
    }

    await unboxExtract(beat);
    if (clock.dead(gen)) {
        busy(rig, false);
        return;
    }

    await unboxLay(beat);
    if (clock.dead(gen)) {
        busy(rig, false);
        return;
    }

    const slide = unboxAside(beat);
    await Promise.all([slide, unboxDeal(beat)]);
    if (clock.dead(gen)) {
        busy(rig, false);
        return;
    }

    if (keyLight) {
        await clock.tween(timing.dimMs, (t) => {
            if (!clock.dead(gen)) keyLight.intensity = lerp(keyLight.intensity, 0.45, t);
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
