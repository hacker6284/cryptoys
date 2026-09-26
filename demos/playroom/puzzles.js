/**
 * Scramble product puzzle modes. 3×3 is the hash toy.
 * Megaminx / pyraminx are visual — see scramble-alg.js projection.
 *
 * Product dock is 3×3 only. Mega / Pyra chrome and `?puzzle=` deep
 * links require the room debug flag (`?debug=1`, same as flight /
 * beat debug on `document.documentElement.dataset.playroomDebug`).
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

export function playroomDebugEnabled(search = typeof location !== "undefined" ? location.search : "") {
    try {
        return new URLSearchParams(search).get("debug") === "1";
    } catch {
        return false;
    }
}

/** Product hash toy. Alt puzzles only resolve when `?debug=1`. */
export function resolveProductPuzzleId(raw, search = typeof location !== "undefined" ? location.search : "") {
    if (!playroomDebugEnabled(search)) return "3x3x3";
    return normalizePuzzleId(raw);
}

export function puzzleHashes(id) {
    return Boolean(PUZZLES[normalizePuzzleId(id)]?.hash);
}

export function readPuzzleSearchParam(search = location.search) {
    try {
        return resolveProductPuzzleId(new URLSearchParams(search).get("puzzle"), search);
    } catch {
        return "3x3x3";
    }
}

export function writePuzzleSearchParam(id, href = location.href) {
    const url = new URL(href);
    const norm = normalizePuzzleId(id);
    if (norm === "3x3x3" || !playroomDebugEnabled(url.search)) url.searchParams.delete("puzzle");
    else url.searchParams.set("puzzle", norm);
    return `${url.pathname}${url.search}${url.hash}`;
}
