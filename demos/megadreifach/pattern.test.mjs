// pattern.js: the Position → cubing.js bridge, built from the generated
// face turns. CI has no cubing.js, so the "cubing" side here is the
// generated turns relabelled by a random piece numbering and orientation
// offsets; the bridge must find that relabelling from the 12 turns alone
// and then agree with it on random words. (Against the real cubing.js
// megaminx kpuzzle it agrees on 200 random 40-turn words, checked locally.)
import assert from "node:assert/strict";
import { positionBridge } from "./pattern.js";
import { loadGenerated } from "./gen.test-helper.mjs";

const gen = await loadGenerated();
if (!gen) {
    console.log("pattern.test: SKIP (run tools/build.sh)");
    process.exit(0);
}

let seed = 7;
const rand = (n) => {
    seed = (seed * 1103515245 + 12345) % 2147483648;
    return seed % n;
};
function shuffle(n) {
    const a = [...Array(n).keys()];
    for (let i = n - 1; i > 0; i--) {
        const j = rand(i + 1);
        [a[i], a[j]] = [a[j], a[i]];
    }
    return a;
}

// A fake cubing.js: piece s of the generated numbering is piece sigma[s]
// here, and orientations are shifted by per-slot offsets (k = 2 flips the
// corner twist direction).
function fakeCubing(k) {
    const orbit = (n, m, perm, ori, kk) => {
        const sigma = shuffle(n);
        const u = Array.from({ length: n }, () => rand(m));
        return (pos) => {
            const permutation = new Array(n);
            const orientationDelta = new Array(n);
            for (let s = 0; s < n; s++) {
                const from = pos[perm][s];
                permutation[sigma[s]] = sigma[from];
                orientationDelta[sigma[s]] = (((kk * pos[ori][s] + u[s] - u[from]) % m) + m) % m;
            }
            return { permutation, orientationDelta };
        };
    };
    const corners = orbit(20, 3, "cp", "co", k);
    const edges = orbit(30, 2, "ep", "eo", 1);
    return (pos) => ({
        CORNERS: corners(pos),
        EDGES: edges(pos),
        CENTERS: { permutation: [...Array(12).keys()], orientationDelta: new Array(12).fill(0) },
    });
}

const faceTurns = [...Array(12).keys()].map((f) => gen.faceTurn(gen.identity(), f, 1));
for (const k of [1, 2]) {
    const cubing = fakeCubing(k);
    const bridge = positionBridge(faceTurns, faceTurns.map(cubing));
    for (let trial = 0; trial < 30; trial++) {
        let p = gen.identity();
        for (let i = 0; i < 30; i++) p = gen.faceTurn(p, rand(12), 1 + rand(4));
        const got = bridge(p);
        const want = cubing(p);
        assert.deepEqual(got.CORNERS, want.CORNERS);
        assert.deepEqual(got.EDGES, want.EDGES);
        assert.deepEqual(got.CENTERS.orientationDelta, new Array(12).fill(0));
    }
    // The final positions of a real fast-forward map too (and solved is solved).
    const trace = gen.host.trace_hash(new Array(56).fill(109));
    const last = trace.blocks.at(-1);
    assert.deepEqual(bridge(last.h_next).CORNERS, cubing(last.h_next).CORNERS);
    assert.deepEqual(bridge(last.h_next_inv).EDGES, cubing(last.h_next_inv).EDGES);
    assert.deepEqual(bridge(gen.identity()).CORNERS.permutation, [...Array(20).keys()]);
}

// A turn table that disagrees with the generated turns is refused.
const wrong = faceTurns.map((t, f) => (f === 3 ? faceTurns[4] : t));
assert.throws(() => positionBridge(faceTurns, wrong.map(fakeCubing(1))), /bridge/);

console.log("pattern.test: ok");
