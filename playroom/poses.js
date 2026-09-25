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
    // Same seated-lean family as scramble (height / distance / FOV).
    // A hair more z and 2° more FOV so both grids still read.
    doubledeal: {
        position: [DEN.x + 0.28, 1.22, DEN.z + 0.96],
        target: [DEN.x, 0.80, DEN.z],
        fov: 30,
        overlays: { title: true, menu: false, teach: true },
    },
    // Travel with the box so a tight unbox close-up cannot land on
    // empty felt (the #29 shelf-hold lesson). Quiet chrome — no teach.
    unbox_travel: {
        position: [DEN.x + 0.48, 1.24, DEN.z + 0.92],
        target: [DEN.x, 0.86, DEN.z],
        fov: 32,
        overlays: { title: true, menu: false },
    },
    // Three-quarter of the landed 67 mm KEY tuck-box.
    unbox: {
        position: [DEN.x + 0.12, 0.95, DEN.z + 0.34],
        target: [DEN.x, 0.83, DEN.z],
        fov: 26,
        overlays: { title: true, menu: false },
    },
    unbox_deal: {
        position: [DEN.x + 0.20, 1.08, DEN.z + 0.62],
        target: [DEN.x, 0.82, DEN.z + 0.12],
        fov: 28,
        overlays: { title: true, menu: false },
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
    unbox_travel: "unbox_travel",
    unbox: "unbox",
    unbox_deal: "unbox_deal",
};

export function resolvePoseName(raw, fallback = "landing") {
    if (raw == null || raw === "") return fallback;
    const key = String(raw).trim().toLowerCase();
    if (ALIASES[key]) return ALIASES[key];
    if (POSES[key]) return key;
    return fallback;
}
