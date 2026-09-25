import { DEN } from "./constants.js";

// Named person-camera poses. Horizon stays level (no roll).
// Scramble and DoubleDeal each lean on their toy without leaving the room.

export const POSES = {
    landing: {
        position: [2.55, 2.05, 3.2],
        target: [-0.1, 0.85, -0.2],
        fov: 40,
        overlays: { title: true, menu: true },
    },
    // Close enough that a 57 mm cube leaving its slot actually reads.
    shelf: {
        position: [0.22, 1.46, -0.92],
        target: [-0.55, 1.30, -2.15],
        fov: 34,
        overlays: { title: true, menu: false },
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
    // Lean on the cube but keep the table rim and a sliver of room in frame.
    scramble: {
        position: [DEN.x + 0.32, 1.20, DEN.z + 0.78],
        target: [DEN.x, 0.80, DEN.z],
        fov: 28,
        overlays: { title: true, menu: false, teach: true },
    },
    // Lean over both scaled decks. Wider than scramble so the 4×13
    // grids read; still a seated look, not a showroom pull-back.
    doubledeal: {
        position: [DEN.x, 1.62, DEN.z + 1.42],
        target: [DEN.x, 0.77, DEN.z],
        fov: 40,
        overlays: { title: true, menu: false, teach: true },
    },
};

const ALIASES = {
    landing: "landing",
    three_q: "landing",
    shelf: "shelf",
    shelf_cube: "shelf",
    seated: "seated",
    arrive_table: "seated",
    a4_seated: "seated",
    lean: "lean",
    lean_msg: "lean",
    scramble: "scramble",
    lean_cube: "scramble",
    doubledeal: "doubledeal",
    lean_deck: "doubledeal",
};

export function resolvePoseName(raw, fallback = "landing") {
    if (raw == null || raw === "") return fallback;
    const key = String(raw).trim().toLowerCase();
    if (ALIASES[key]) return ALIASES[key];
    if (POSES[key]) return key;
    return fallback;
}
