/**
 * Tuck-box rigs for the box microdemos, built the way the playroom
 * DoubleDeal / MegaDreifach adapters build them (playroom/adapters.js).
 */
import { loadCardTextures } from "../../doubledeal/table.js";
import { createInnerGlow, createUnboxRig } from "../../playroom/unbox-rig.js";
import { pickHandTextures, pickMsgTextures } from "../../playroom/unbox-hand.js";

export const LOOKS = {
    KEY: { label: "KEY", bodyHex: "#6b1e1e", pick: pickHandTextures },
    MSG: { label: "MSG", bodyHex: "#1a2a44", pick: pickMsgTextures },
    // MegaDreifach's DEAL deck (adapters.js on keynote/megadreifach-demo).
    DEAL: { label: "DEAL", bodyHex: "#3a2140", pick: pickHandTextures },
};

/** Before the light registry is sealed: the sleeve glow for `name`. */
export function addGlow(world, name) {
    try {
        world.lights.get(`glow:${name}`);
    } catch {
        world.lights.add(`glow:${name}`, createInnerGlow());
    }
}

let texturesPromise = null;
export async function buildBox(world, name, look = "KEY") {
    texturesPromise ||= loadCardTextures(4);
    const textures = await texturesPromise;
    const spec = LOOKS[look] || LOOKS.KEY;
    const rig = await createUnboxRig({
        anisotropy: Math.min(8, world.renderer?.capabilities?.getMaxAnisotropy?.() || 4),
        textures: spec.pick(textures),
        sharedMaps: true,
        label: spec.label,
        bodyHex: spec.bodyHex,
        innerGlow: world.lights.get(`glow:${name}`),
    });
    const prev = world.toys[name];
    world.replaceToy(name, rig.group);
    prev?.parent?.remove(prev);
    return rig;
}

/** adapters.js restowOne: cards back in the packet, packet in the box. */
export function restowBox(rig) {
    for (const mesh of rig.cards) {
        if (mesh.parent && mesh.parent !== rig.packet) rig.packet.attach(mesh);
    }
    if (rig.packet.parent !== rig.group) rig.group.add(rig.packet);
    rig.restow();
    rig.group.visible = true;
    rig.group.userData.unboxBusy = false;
    rig.packet.userData.unboxBusy = false;
}

export const EASE_OPTIONS = [["easeOutCubic", "easeOutCubic"], ["easeInOutCubic", "easeInOutCubic"], ["easeOutQuart", "easeOutQuart"], ["linear", "linear"]];
