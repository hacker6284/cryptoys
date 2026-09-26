/**
 * Scramble product puzzle modes. 3×3 is the hash toy.
 * Megaminx / pyraminx are visual — see scramble-alg.js projection.
 */

export const PUZZLES = {
    "3x3x3": { id: "3x3x3", label: "3×3", short: "3×3", alg: "", hash: true },
    megaminx: { id: "megaminx", label: "Megaminx", short: "Mega", alg: "", hash: false },
    pyraminx: { id: "pyraminx", label: "Pyraminx", short: "Pyra", alg: "", hash: false },
};

export const PUZZLE_IDS = Object.keys(PUZZLES);

const PUZZLE_ALIASES = {
    "3x3": "3x3x3",
    "3x3x3": "3x3x3",
    cube: "3x3x3",
    mega: "megaminx",
    megaminx: "megaminx",
    minx: "megaminx",
    pyra: "pyraminx",
    pyraminx: "pyraminx",
};

export function normalizePuzzleId(raw, fallback = "3x3x3") {
    const key = String(raw || "").trim().toLowerCase();
    if (PUZZLE_ALIASES[key]) return PUZZLE_ALIASES[key];
    return PUZZLES[key] ? key : fallback;
}

export function puzzleHashes(id) {
    return Boolean(PUZZLES[normalizePuzzleId(id)]?.hash);
}

export function readPuzzleSearchParam(search = location.search) {
    try {
        return normalizePuzzleId(new URLSearchParams(search).get("puzzle"));
    } catch {
        return "3x3x3";
    }
}

export function writePuzzleSearchParam(id, href = location.href) {
    const url = new URL(href);
    const norm = normalizePuzzleId(id);
    if (norm === "3x3x3") url.searchParams.delete("puzzle");
    else url.searchParams.set("puzzle", norm);
    return `${url.pathname}${url.search}${url.hash}`;
}
