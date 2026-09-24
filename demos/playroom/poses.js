import { DEN } from "./constants.js";

// Named person-camera poses. Horizon stays level (no roll).
// `lean` is a stub for a later look-down over the felt; DoubleDeal/Scramble
// will specialize it once those adapters sit in the room.

export const POSES = {
    landing: {
        position: [2.55, 2.05, 3.2],
        target: [-0.1, 0.85, -0.2],
        fov: 40,
        overlays: { title: true, menu: true },
    },
    seated: {
        position: [DEN.x, 1.28, DEN.z + 1.35],
        target: [DEN.x, 0.78, DEN.z],
        fov: 38,
        overlays: { title: true, menu: false },
    },
    lean: {
        position: [DEN.x, 1.55, DEN.z + 1.55],
        target: [DEN.x, 0.78, DEN.z],
        fov: 36,
        overlays: { title: true, menu: false },
    },
};

const ALIASES = {
    landing: "landing",
    three_q: "landing",
    seated: "seated",
    arrive_table: "seated",
    a4_seated: "seated",
    lean: "lean",
    lean_msg: "lean",
};

export function resolvePoseName(raw, fallback = "landing") {
    if (raw == null || raw === "") return fallback;
    const key = String(raw).trim().toLowerCase();
    if (ALIASES[key]) return ALIASES[key];
    if (POSES[key]) return key;
    return fallback;
}
