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
    // Close enough that the shelf cube leaving its slot actually reads.
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
    // MegaDreifach v3: the whole table at real size, deck box | B A C |
    // held card on the back line and the 13 × 4 deal (0.87 m wide) in
    // front, ~45° down, aimed right of the set's centre so it sits in the
    // frame's left part, clear of the dock on the right.
    drei: {
        position: [DEN.x + 0.16, 1.78, DEN.z + 0.94],
        target: [DEN.x + 0.16, 0.78, DEN.z - 0.11],
        fov: 32,
        overlays: { title: true, menu: false, teach: true },
        // Phones: steeper, centred on the whole set, aimed below it so
        // the set sits above the transport and dock.
        portrait: {
            position: [DEN.x, 2.55, DEN.z + 0.95],
            target: [DEN.x, 0.76, DEN.z + 0.12],
            fov: 50,
        },
    },
    // Legacy named travel shot. Production enter uses followTo and
    // does not snap or ease through this pose.
    unbox_travel: {
        position: [DEN.x + 0.48, 1.24, DEN.z + 0.92],
        target: [DEN.x, 0.86, DEN.z],
        fov: 32,
        overlays: { title: true, menu: false },
    },
    // Kept as an alias family. Production enter does not snap here.
    unbox: {
        position: [DEN.x + 0.36, 1.12, DEN.z + 0.74],
        target: [DEN.x, 0.84, DEN.z],
        fov: 30,
        overlays: { title: true, menu: false },
    },
    unbox_deal: {
        position: [DEN.x + 0.32, 1.16, DEN.z + 0.84],
        target: [DEN.x, 0.82, DEN.z + 0.04],
        fov: 30,
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
    drei: "drei",
    megadreifach: "drei",
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
