/**
 * cubing.js move timing, shared by the twisty-puzzle turn entries:
 * which sound slot a move uses and when its detent clicks land.
 */

export function amountOf(move) {
    const m = /^([A-Za-z]+)(\d*)('?)$/.exec(String(move));
    return m ? Number(m[2] || 1) : 1;
}

/** Sound slot for a move: whole-puzzle rotation, or a face turn of 1, 2 or 3+ clicks. */
export function slotOf(move) {
    if (/^[xyz]/.test(String(move))) return "rotation";
    const n = amountOf(move);
    return n === 1 ? "single" : n === 2 ? "double" : "triple";
}

/** cubing.js default move durations (ms at tempo 1): 1 → 1000, 2 → 1500, more → 2000. */
export function cubingMs(amount) {
    return amount === 1 ? 1000 : amount === 2 ? 1500 : 2000;
}

/** cubing.js eases every move with smootherStep (Cube3D and PG3D `ease`). */
export function smootherStep(x) {
    return x * x * x * (10 - x * (15 - 6 * x));
}

function inverseSmootherStep(y) {
    let lo = 0;
    let hi = 1;
    for (let i = 0; i < 40; i++) {
        const mid = (lo + hi) / 2;
        if (smootherStep(mid) < y) lo = mid;
        else hi = mid;
    }
    return (lo + hi) / 2;
}

/**
 * Detent click times for an `amount`-click turn, in ms relative to the
 * end of the leaf (the face seats on the last click): click k lands
 * when the eased angle crosses k/amount.
 */
export function clickTimes(amount, tempo) {
    const total = cubingMs(amount) / tempo;
    const out = [];
    for (let k = 1; k <= amount; k++) out.push((inverseSmootherStep(k / amount) - 1) * total);
    return out;
}

/** The slots every twisty turn entry has (gap and voice cap keep fast play a patter). */
export function twistySlots() {
    const perClick = (amount) => ({ slot: "single", clicks: (tempo) => clickTimes(amount, tempo) });
    return [
        { name: "single", gapMs: 55, voices: 3, jitter: 0.06 },
        { name: "double", gapMs: 55, voices: 3, jitter: 0.06, perClick: perClick(2) },
        { name: "triple", gapMs: 55, voices: 3, jitter: 0.06, perClick: perClick(3) },
        { name: "rotation", gapMs: 140, voices: 2 },
        { name: "lift", gapMs: 140, voices: 2 },
        { name: "settle", gapMs: 140, voices: 2 },
    ];
}
