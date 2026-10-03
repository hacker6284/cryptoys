// MegaDreifach v3 (ZP26) statistics harness. It drives only the sudoc JS build of the normative
// v3/megadreifach.sudo: every block is the build's dm_step (= compose(h, em_block(h, deal))), and
// every group operation is the build's compose / inverse / identity / iv_cook12 / opposites. This
// file implements no part of W, E_m or the Davies-Meyer step. It samples inputs, counts and runs the
// statistics.
//
// Usage, from the repo root:
//   sudoc build --target js -o /tmp/megadreifach-v3 primitives/hash/megadreifach/v3/megadreifach.sudo
//   MD3_OUT=/tmp/megadreifach-v3 node proofs/megadreifach/security/v3/harness/zp26_stats.mjs COMMAND [--workers W]
//   MD3_OUT=/tmp/megadreifach-v3 node proofs/megadreifach/security/v3/harness/zp26_stats.mjs --check LOG [COMMAND]
// COMMAND:
//   selfcheck            harness checks against the build (sampler legality, y == HashDeckBodyFrom, laws)
//   bench   N SEED0      N blocks of em_block on uniform (h, deal): blocks/s
//   d2      N SEED0      D2: secret uniform h, uniform deal, cards 51 and 52 swapped; z = y^-1 y''
//   d1      N SEED0      D1 (left, Q = W(h)^-1 W(gh)) and D1' (right, W(hg) W(h)^-1) on the same samples;
//                        g a uniform 2-edge flip, W(h) = h^-1 y h^-1
//   merge   N SEED0      adjacent swaps at deal positions 1, 2, 13, 26, 27, 39, 50, 51, IV and uniform start,
//                        N per (start, position): differing output slots and output collisions
//   d3      N SEED0      telescoping pair at deal positions 51, 52 (both orders), pair classes same/opp/KA/rand,
//                        IV and uniform start, N per (start, class): output collisions
//   ci      SEED0        a small fixed slice: d2 400, d1 200, merge 25 and d3 50 (tools/generate-demos.sh, --check)
// Work is split into chunks whose size depends only on N; chunk c uses the seed SEED0 + c, so results do
// not depend on the worker count. Every line of output is deterministic except the lines starting with "# time".
// Output starts with "# command: COMMAND". --check LOG COMMAND runs COMMAND and compares its whole output
// (that first line included) with the log, ignoring the "# time" lines; without COMMAND it runs the
// command on the log's first line. It prints "OK <log>" or "STALE <log>" (exit 1).
import { Worker, isMainThread, parentPort, workerData } from "node:worker_threads";
import { readFileSync } from "node:fs";
import { join } from "node:path";
import { fileURLToPath } from "node:url";

const OUT = (isMainThread ? process.env.MD3_OUT : workerData.out) || "/tmp/megadreifach-v3";
const impl = await import(join(OUT, "_megadreifach_impl.mjs"));
const rt = await import(join(OUT, "_sudo_rt.mjs"));

// ------------------------------------------------------------------ bridge to the build (no logic)
const toPos = (p) => rt.rec(new impl.Position(rt.lst(p[0].map(BigInt)), rt.lst(p[1].map(BigInt)),
    rt.lst(p[2].map(BigInt)), rt.lst(p[3].map(BigInt))));
const fromPos = (p) => [[...p.cp].map(Number), [...p.co].map(Number), [...p.ep].map(Number), [...p.eo].map(Number)];
const deal = (d) => rt.lst(d.map(BigInt));
const comp = (a, b) => impl.compose(a, b);
const inv = (a) => impl.inverse(a);
const block = (h, d) => impl.dm_step(h, deal(d));                 // y = h * E_m(h) = h W h: the build's dm_step
const OPP = [...impl.opposites].map(Number);

// ------------------------------------------------------------------ seeded PRNG (xoshiro128**)
function rng(seed) {
    let s = seed >>> 0;
    const sm = () => {                                              // splitmix32 to fill the state
        s = (s + 0x9e3779b9) >>> 0;
        let z = s;
        z = Math.imul(z ^ (z >>> 16), 0x85ebca6b) >>> 0;
        z = Math.imul(z ^ (z >>> 13), 0xc2b2ae35) >>> 0;
        return (z ^ (z >>> 16)) >>> 0;
    };
    let a = sm(), b = sm(), c = sm(), d = sm();
    const next = () => {
        const r = Math.imul(((Math.imul(b, 5) << 7) | (Math.imul(b, 5) >>> 25)) >>> 0, 9) >>> 0;
        const t = (b << 9) >>> 0;
        c ^= a; d ^= b; b ^= c; a ^= d; c ^= t;
        d = ((d << 11) | (d >>> 21)) >>> 0;
        a >>>= 0; b >>>= 0; c >>>= 0;
        return r;
    };
    const below = (n) => {                                          // uniform in [0, n), rejection
        const lim = Math.floor(4294967296 / n) * n;
        for (;;) { const x = next(); if (x < lim) return x % n; }
    };
    const shuffle = (xs) => { for (let j = xs.length - 1; j > 0; j--) { const r = below(j + 1); [xs[j], xs[r]] = [xs[r], xs[j]]; } return xs; };
    const sample2 = (n) => { const x = below(n); let y = below(n - 1); if (y >= x) y++; return [x, y]; };
    return { below, shuffle, sample2 };
}

const range = (n) => [...Array(n).keys()];
function cycles(p) {                                                 // cycle lengths of a permutation
    const seen = new Array(p.length).fill(false);
    const out = [];
    for (let i = 0; i < p.length; i++) {
        if (seen[i]) continue;
        let L = 0;
        for (let j = i; !seen[j]; j = p[j]) { seen[j] = true; L++; }
        out.push(L);
    }
    return out;
}
const parity = (p) => cycles(p).reduce((s, L) => s + L - 1, 0) & 1;
const cycleType = (p) => cycles(p).sort((x, y) => y - x).join(",");
// A uniform legal position: even corner and edge permutations, corner twists summing to 0 mod 3,
// edge flips summing to 0 mod 2 (the legality of v2 §4, which the sudo's position_to_bytes ranks).
function uniformH(R) {
    const cp = R.shuffle(range(20));
    if (parity(cp)) [cp[0], cp[1]] = [cp[1], cp[0]];
    const ep = R.shuffle(range(30));
    if (parity(ep)) [ep[0], ep[1]] = [ep[1], ep[0]];
    const co = range(19).map(() => R.below(3));
    co.push((3 - (co.reduce((x, y) => x + y, 0) % 3)) % 3);
    const eo = range(29).map(() => R.below(2));
    eo.push(eo.reduce((x, y) => x + y, 0) % 2);
    return [cp, co, ep, eo];
}
const uniformDeal = (R) => R.shuffle(range(52));
function flip2(R) {                                                  // a uniform 2-edge flip g
    const [e1, e2] = R.sample2(30);
    const eo = new Array(30).fill(0);
    eo[e1] = 1; eo[e2] = 1;
    return [range(20), new Array(20).fill(0), range(30), eo];
}

// ------------------------------------------------------------------ statistics of a quotient z
const fixC = (z) => { let k = 0; for (let s = 0; s < 20; s++) k += z[0][s] === s; return k; };
const fixE = (z) => { let k = 0; for (let s = 0; s < 30; s++) k += z[2][s] === s; return k; };
const same = (a, b) => a.every((xs, i) => xs.every((x, j) => x === b[i][j]));
const diffSlots = (a, b) => { let k = 0; for (let s = 0; s < 20; s++) k += a[0][s] !== b[0][s] || a[1][s] !== b[1][s]; for (let s = 0; s < 30; s++) k += a[2][s] !== b[2][s] || a[3][s] !== b[3][s]; return k; };
const IDENTITY = fromPos(impl.identity());
const moved = (z) => diffSlots(z, IDENTITY);                         // slots not at identity (orientation counted)

const inc = (o, k, v = 1) => { o[k] = (o[k] || 0) + v; };
function newSide() { return { n: 0, pred: 0, fe: 0, fc: 0, mv: 0, mv2: 0, he: {}, hc: {}, ce: {}, cc: {} }; }
function acc(r, zp, ident) {
    const z = fromPos(zp);
    const a1 = fixE(z), a2 = fixC(z), m = moved(z);
    r.n++; r.pred += ident; r.fe += a1 >= 2; r.fc += a2 >= 2; r.mv += m; r.mv2 += m * m;
    inc(r.he, a1); inc(r.hc, a2); inc(r.ce, cycleType(z[2])); inc(r.cc, cycleType(z[0]));
    return [a2 >= 2 ? 1 : 0, m];
}
function mergeObj(a, b) {
    if (typeof a === "number") return a + b;
    if (Array.isArray(a)) return a.map((x, i) => mergeObj(x, b[i]));
    const o = { ...a };
    for (const k of Object.keys(b)) o[k] = k in o ? mergeObj(o[k], b[k]) : b[k];
    return o;
}

const POS = [1, 2, 13, 26, 27, 39, 50, 51];
const CLASSES = ["same", "opp", "KA", "rand"];
function telePair(R, cls) {
    if (cls === "same") { const r = R.below(12); const [s1, s2] = R.sample2(4); return [4 * r + s1, 4 * r + s2]; }
    if (cls === "opp") { const r = R.below(12); return [4 * r + R.below(4), 4 * OPP[r] + R.below(4)]; }
    if (cls === "KA") return [48 + R.below(4), R.below(4)];
    return R.sample2(52);
}

// One chunk of work per test: (job = {test, n, seed, start?, pos?, cls?}, R = the chunk's PRNG).
const startOf = (job, R) => (job.start === "IV" ? impl.iv_cook12() : toPos(uniformH(R)));
const WORK = {
    bench(job, R) {
        for (let i = 0; i < job.n; i++) impl.em_block(toPos(uniformH(R)), deal(uniformDeal(R)));
        return { n: job.n };
    },
    d2(job, R) {
        const r = newSide();
        for (let i = 0; i < job.n; i++) {
            const h = toPos(uniformH(R));
            const d = uniformDeal(R);
            const d2 = [...d];
            [d2[50], d2[51]] = [d2[51], d2[50]];
            acc(r, comp(inv(block(h, d)), block(h, d2)), 0);
        }
        return r;
    },
    d1(job, R) {
        const A = newSide(), B = newSide(), pr = { dfc: 0, dfc2: 0 };
        for (let i = 0; i < job.n; i++) {
            const K = uniformDeal(R);
            const h = toPos(uniformH(R));
            const g = toPos(flip2(R));
            const cardPhaseW = (x) => { const xi = inv(x); return comp(xi, comp(block(x, K), xi)); };   // W(x) = x^-1 y x^-1
            const Wh = cardPhaseW(h), Whi = inv(Wh);
            const W2 = cardPhaseW(comp(g, h));
            const W3 = cardPhaseW(comp(h, g));
            const whA = fromPos(Wh);
            const [leftFixC2] = acc(A, comp(Whi, W2), same(fromPos(W2), whA) ? 1 : 0);
            const [rightFixC2] = acc(B, comp(W3, Whi), same(fromPos(W3), whA) ? 1 : 0);
            pr.dfc += leftFixC2 - rightFixC2; pr.dfc2 += (leftFixC2 - rightFixC2) ** 2;
        }
        return { A, B, pr };
    },
    merge(job, R) {
        const hist = new Array(51).fill(0);
        let coll = 0;
        for (let i = 0; i < job.n; i++) {
            const h = startOf(job, R);
            const d = uniformDeal(R);
            const d2 = [...d];
            [d2[job.pos - 1], d2[job.pos]] = [d2[job.pos], d2[job.pos - 1]];
            const k = diffSlots(fromPos(block(h, d)), fromPos(block(h, d2)));
            hist[k]++;
            coll += k === 0;
        }
        return { hist, coll };
    },
    d3(job, R) {
        let coll = 0;
        for (let i = 0; i < job.n; i++) {
            const h = startOf(job, R);
            const [a, b] = telePair(R, job.cls);
            const rest = R.shuffle(range(52).filter((c) => c !== a && c !== b));
            coll += same(fromPos(block(h, [...rest, a, b])), fromPos(block(h, [...rest, b, a])));
        }
        return { n: job.n, coll };
    },
};
function work(job) {
    if (!(job.test in WORK)) throw new Error(`unknown test ${job.test}`);
    return WORK[job.test](job, rng(job.seed));
}

// ------------------------------------------------------------------ exact reference laws (uniform G)
function factorial(n) { let f = 1n; for (let i = 2n; i <= BigInt(n); i++) f *= i; return f; }
function choose(n, k) { return factorial(n) / (factorial(k) * factorial(n - k)); }
function ratio(a, b) { return Number((a * 10n ** 30n) / b) / 1e30; }
function fixLaw(n) {                                                 // fixed points of a uniform element of A_n
    const D = [1n, 0n];
    for (let m = 2; m <= n; m++) D.push(BigInt(m - 1) * (D[m - 1] + D[m - 2]));
    const even = [1n];
    for (let m = 1; m <= n; m++) even.push((D[m] + (m % 2 === 1 ? 1n : -1n) * BigInt(m - 1)) / 2n);
    const tot = factorial(n) / 2n;
    return range(n + 1).map((j) => ratio(choose(n, j) * even[n - j], tot));
}
function zfixLaw(n, q) {                                             // slots fixed with orientation 0
    const fl = fixLaw(n), out = new Array(n + 1).fill(0);
    fl.forEach((p, m) => { for (let j = 0; j <= m; j++) out[j] += p * Number(choose(m, j)) * (1 / q) ** j * ((q - 1) / q) ** (m - j); });
    return out;
}
function movedLaw() {
    const lc = zfixLaw(20, 3), le = zfixLaw(30, 2), law = new Array(51).fill(0);
    lc.forEach((pa, a) => le.forEach((pb, b) => { law[50 - a - b] += pa * pb; }));
    return law;
}
function classProbs(n) {                                             // P(cycle type) for uniform A_n: 2 / z_lambda
    const out = {};
    const parts = function* (m, mx) { if (m === 0) { yield []; return; } for (let k = Math.min(m, mx); k > 0; k--) for (const r of parts(m - k, k)) yield [k, ...r]; };
    for (const lam of parts(n, n)) {
        if (lam.reduce((s, k) => s + k - 1, 0) % 2) continue;
        let z = 1n;
        for (const k of new Set(lam)) { const m = lam.filter((x) => x === k).length; z *= BigInt(k) ** BigInt(m) * factorial(m); }
        out[lam.join(",")] = ratio(2n, z);
    }
    return out;
}
function lgamma(x) {                                                 // Lanczos
    const g = 7, c = [0.99999999999980993, 676.5203681218851, -1259.1392167224028, 771.32342877765313, -176.61502916214059,
        12.507343278686905, -0.13857109526572012, 9.9843695780195716e-6, 1.5056327351493116e-7];
    if (x < 0.5) return Math.log(Math.PI / Math.sin(Math.PI * x)) - lgamma(1 - x);
    x -= 1;
    let a = c[0];
    const t = x + g + 0.5;
    for (let i = 1; i < 9; i++) a += c[i] / (x + i);
    return 0.5 * Math.log(2 * Math.PI) + (x + 0.5) * Math.log(t) - t + Math.log(a);
}
function gammaQ(a, x) {                                              // regularized upper incomplete gamma
    if (x <= 0) return 1;
    if (x < a + 1) {
        let sum = 1 / a, del = sum, ap = a;
        for (let i = 0; i < 1000; i++) { ap += 1; del *= x / ap; sum += del; if (Math.abs(del) < Math.abs(sum) * 1e-15) break; }
        return 1 - sum * Math.exp(-x + a * Math.log(x) - lgamma(a));
    }
    let b = x + 1 - a, c = 1e300, d = 1 / b, h = d;
    for (let i = 1; i < 1000; i++) {
        const an = -i * (i - a);
        b += 2; d = an * d + b; if (Math.abs(d) < 1e-300) d = 1e-300; c = b + an / c; if (Math.abs(c) < 1e-300) c = 1e-300;
        d = 1 / d; const del = d * c; h *= del; if (Math.abs(del - 1) < 1e-15) break;
    }
    return Math.exp(-x + a * Math.log(x) - lgamma(a)) * h;
}
const chi2sf = (x, dof) => gammaQ(dof / 2, x / 2);
function histChi(cnt, law, top) {                                    // bins 0..top-1, top+ pooled
    const n = Object.values(cnt).reduce((s, v) => s + v, 0);
    let x2 = 0, seen = 0;
    for (let j = 0; j < top; j++) { const e = law[j] * n, o = cnt[j] || 0; seen += o; x2 += (o - e) ** 2 / e; }
    const e = (1 - law.slice(0, top).reduce((s, v) => s + v, 0)) * n;
    x2 += (n - seen - e) ** 2 / e;
    return chi2sf(x2, top);
}
function cycChi(cnt, probs, minexp = 20) {
    const n = Object.values(cnt).reduce((s, v) => s + v, 0);
    const big = Object.keys(probs).filter((k) => probs[k] * n >= minexp);
    let x2 = 0, pe = n, po = n;
    for (const k of big) { const e = probs[k] * n, o = cnt[k] || 0; x2 += (o - e) ** 2 / e; pe -= e; po -= o; }
    let dof = big.length - 1;
    if (pe > 1e-9) { x2 += (po - pe) ** 2 / pe; dof += 1; }
    return [x2, dof, chi2sf(x2, dof)];
}
function wilson(k, n) {
    if (k === 0) return [0, 1 - 0.05 ** (1 / n)];
    const z = 1.96, p = k / n, den = 1 + (z * z) / n;
    const mid = (p + (z * z) / (2 * n)) / den, half = (z * Math.sqrt((p * (1 - p)) / n + (z * z) / (4 * n * n))) / den;
    return [mid - half, mid + half];
}

// ------------------------------------------------------------------ driver
async function pool(jobs, w) {
    const res = new Array(jobs.length);
    const ws = range(Math.min(w, jobs.length)).map(() => new Worker(fileURLToPath(import.meta.url), { workerData: { out: OUT } }));
    let next = 0;
    await Promise.all(ws.map((wk) => new Promise((resolve, reject) => {
        const feed = () => { if (next >= jobs.length) { wk.terminate(); resolve(); return; } const i = next++; wk.once("message", (r) => { res[i] = r; feed(); }); wk.postMessage(jobs[i]); };
        wk.on("error", reject);
        feed();
    })));
    return res;
}
// Chunk size depends on N only (at most 2500, at least 8 chunks when N allows), never on the workers.
const chunkSize = (n) => Math.min(2500, Math.max(1, Math.ceil(n / 8)));
function chunks(test, n, seed0, extra = {}) {
    const size = chunkSize(n), k = Math.ceil(n / size), out = [];
    for (let c = 0; c < k; c++) out.push({ test, n: Math.min(size, n - c * size), seed: seed0 + c, ...extra });
    return out;
}
const fixed = (x, d = 5) => x.toFixed(d);
const signed = (x, d = 5) => (x >= 0 ? "+" : "") + x.toFixed(d);
const twoSig = (x) => x.toPrecision(2);

// The exact reference laws of a uniform element of G (main thread only; the workers only count).
function referenceLaws() {
    const fixE = fixLaw(30), fixC = fixLaw(20), moved = movedLaw();
    return {
        fixE, fixC, moved,
        p2E: 1 - fixE[0] - fixE[1], p2C: 1 - fixC[0] - fixC[1],
        movedMean: moved.reduce((s, p, k) => s + k * p, 0),
        cycleE: classProbs(30), cycleC: classProbs(20),
    };
}
const LAWS = isMainThread ? referenceLaws() : null;

function showSide(tag, r, withPred) {
    const n = r.n, out = [];
    const [lo, hi] = wilson(r.fe, n), [loc, hic] = wilson(r.fc, n);
    const m = r.mv / n, sd = Math.sqrt(Math.max(r.mv2 / n - m * m, 0) * n / (n - 1));
    const mfe = Object.entries(r.he).reduce((s, [k, v]) => s + k * v, 0) / n, mfc = Object.entries(r.hc).reduce((s, [k, v]) => s + k * v, 0) / n;
    if (withPred) { const [a, b] = wilson(r.pred, n); out.push(`${tag} n=${n}: exact prediction ${r.pred}/${n} [${twoSig(a)}, ${twoSig(b)}]`); }
    out.push(`${tag} n=${n}: P(fixE>=2) ${fixed(r.fe / n)} [${fixed(lo)}, ${fixed(hi)}] adv ${signed(r.fe / n - LAWS.p2E)} | P(fixC>=2) ${fixed(r.fc / n)} [${fixed(loc)}, ${fixed(hic)}] adv ${signed(r.fc / n - LAWS.p2C)}`);
    out.push(`${tag} n=${n}: mean fixE ${fixed(mfe, 4)}, mean fixC ${fixed(mfc, 4)} (ideal 1 +- ${fixed(1.96 / Math.sqrt(n), 4)}) | mean moved ${fixed(m, 4)} +- ${fixed(1.96 * sd / Math.sqrt(n), 4)} (ideal ${fixed(LAWS.movedMean, 4)}, diff ${signed(m - LAWS.movedMean, 4)})`);
    const xe = cycChi(r.ce, LAWS.cycleE), xc = cycChi(r.cc, LAWS.cycleC);
    out.push(`${tag} n=${n}: chi2 fixE-hist p=${twoSig(histChi(r.he, LAWS.fixE, 5))}, fixC-hist p=${twoSig(histChi(r.hc, LAWS.fixC, 5))} | cycle type E ${fixed(xe[0], 1)}/${xe[1]} p=${twoSig(xe[2])}, C ${fixed(xc[0], 1)}/${xc[1]} p=${twoSig(xc[2])}`);
    return out;
}

// The tests: each runs its chunks on the pool, prints its lines and returns the number of blocks.
const TESTS = {
    async bench(N, seed0, w, emit) {
        await pool(chunks("bench", N, seed0), w);
        emit(`bench: ${N} blocks of em_block on uniform (h, deal), seeds ${seed0}+chunk`);
        return { label: "bench", blocks: N };
    },
    async d2(N, seed0, w, emit) {
        const R = (await pool(chunks("d2", N, seed0), w)).reduce(mergeObj);
        emit(`D2 ZP26: secret uniform h, uniform deal, cards 51 and 52 swapped; N=${N}, seeds ${seed0}+chunk (chunk ${chunkSize(N)})`);
        showSide("D2", R, false).forEach(emit);
        return { label: "D2", blocks: 2 * N };
    },
    async d1(N, seed0, w, emit) {
        const R = (await pool(chunks("d1", N, seed0), w)).reduce(mergeObj);
        emit(`D1 + D1' ZP26: uniform deal K, uniform h, uniform 2-edge flip g; same samples; N=${N}, seeds ${seed0}+chunk (chunk ${chunkSize(N)})`);
        showSide("D1 ", R.A, true).forEach(emit);
        showSide("D1'", R.B, true).forEach(emit);
        const n = N, avgE = (R.A.fe + R.B.fe) / (2 * n) - LAWS.p2E, avgC = (R.A.fc + R.B.fc) / (2 * n) - LAWS.p2C;
        const md = R.pr.dfc / n, sdd = Math.sqrt(Math.max(R.pr.dfc2 / n - md * md, 0) * n / (n - 1));
        emit(`D1+D1' averaged: P(fixE>=2) adv ${signed(avgE)}, P(fixC>=2) adv ${signed(avgC)} (HEUR pooling); paired D1 - D1' P(fixC>=2) ${signed(md)} +- ${fixed(1.96 * sdd / Math.sqrt(n))}`);
        return { label: "D1", blocks: 3 * N };
    },
    async merge(N, seed0, w, emit) {
        const jobs = [];
        for (const start of ["IV", "rand"]) for (const pos of POS) jobs.push(...chunks("merge", N, seed0 + (start === "IV" ? 0 : 10000) + 100 * pos, { start, pos }));
        const res = await pool(jobs, w);
        emit(`merge ZP26: adjacent swap at deal positions ${POS.join(", ")}, IV and uniform start, N=${N} each; seeds ${seed0} + 10000*[uniform] + 100*position + chunk`);
        const law = LAWS.moved, bins = [[0, 40], [41, 44], [45, 46], [47, 47], [48, 48], [49, 49], [50, 50]];
        let tot = 0, coll = 0;
        for (const start of ["IV", "rand"]) {
            let H = new Array(51).fill(0);
            for (const pos of POS) {
                const rs = res.filter((_, i) => jobs[i].start === start && jobs[i].pos === pos);
                const h = rs.map((r) => r.hist).reduce(mergeObj), c = rs.reduce((s, r) => s + r.coll, 0), n = h.reduce((s, v) => s + v, 0);
                H = mergeObj(H, h); tot += n; coll += c;
                emit(`  ${start.padEnd(4)} swap at ${String(pos).padStart(2)}: mean differing slots ${fixed(h.reduce((s, v, k) => s + k * v, 0) / n, 4)}, collisions ${c}`);
            }
            const n = H.reduce((s, v) => s + v, 0);
            emit(`  ${start.padEnd(4)} differing output slots: mean ${fixed(H.reduce((s, v, k) => s + k * v, 0) / n, 4)} (ideal ${fixed(LAWS.movedMean, 4)}); ` +
                bins.map(([a, b]) => `[${a}-${b}] ${fixed(H.slice(a, b + 1).reduce((s, v) => s + v, 0) / n)} (ideal ${fixed(law.slice(a, b + 1).reduce((s, v) => s + v, 0))})`).join("; "));
        }
        emit(`merge ZP26: ${tot} adjacent-swap pairs; output collisions ${coll}; 0-hit 95% bound per pair ${(1 - 0.05 ** (1 / tot)).toExponential(1)}`);
        return { label: "merge", blocks: 2 * tot };
    },
    async d3(N, seed0, w, emit) {
        const jobs = [];
        ["IV", "rand"].forEach((start, si) => CLASSES.forEach((cls, ci) => jobs.push(...chunks("d3", N, seed0 + 100 * (4 * si + ci), { start, cls }))));
        const res = await pool(jobs, w);
        emit(`D3 ZP26: telescoping pair at deal positions 51, 52 (both orders), IV and uniform start, N=${N} per (start, class); seeds ${seed0} + 100*(4*start + class) + chunk`);
        let tot = 0, coll = 0;
        for (const start of ["IV", "rand"]) for (const cls of CLASSES) {
            const rs = res.filter((_, i) => jobs[i].start === start && jobs[i].cls === cls);
            const n = rs.reduce((s, r) => s + r.n, 0), c = rs.reduce((s, r) => s + r.coll, 0);
            tot += n; coll += c;
            emit(`  start ${start.padEnd(4)} pair ${cls.padEnd(4)} n=${n}: output collisions ${c} (0-hit 95% bound ${(1 - 0.05 ** (1 / n)).toExponential(1)})`);
        }
        emit(`D3 ZP26: ${tot} pairs; output collisions ${coll}`);
        return { label: "D3", blocks: 2 * tot };
    },
};

async function runTest(test, N, seed0, w, emit) {
    const t0 = performance.now();
    const { label, blocks } = await TESTS[test](N, seed0, w, emit);
    const s = (performance.now() - t0) / 1000;
    emit(`# time ${label}: ${s.toFixed(1)} s, ${blocks} blocks, ${(blocks / s).toFixed(1)} blocks/s, ${w} workers`);
}

async function selfcheck(emit) {
    const api = await import(join(OUT, "megadreifach.mjs"));
    const R = rng(20261002);
    let legal = 0, digest = 0;
    for (let i = 0; i < 8; i++) {
        const hs = uniformH(R), h = toPos(hs), d = uniformDeal(R);
        // the sampler's positions are group elements of the build: h * h^-1 = id, and rankable
        legal += same(fromPos(comp(h, inv(h))), IDENTITY) && impl.position_to_bytes(h).length === 29;
        // the harness's y = h * E_m(h) is the build's HashDeckBodyFrom output
        const y = [...impl.position_to_bytes(block(h, d))].map(Number);
        const want = api.HashDeckBodyFrom(d, { cp: hs[0], co: hs[1], ep: hs[2], eo: hs[3] });
        digest += y.every((x, j) => x === want[j]);
    }
    // the sampler's legality matches the build's face turns: a random face-turn word from the identity
    // satisfies the same constraints (twists 0 mod 3, flips 0 mod 2, even permutations)
    let words = 0;
    for (let i = 0; i < 8; i++) {
        let g = impl.identity();
        for (let t = 0; t < 40; t++) g = impl.face_turn(g, BigInt(R.below(12)), BigInt(1 + R.below(4)));
        const z = fromPos(g);
        words += z[1].reduce((s, v) => s + v, 0) % 3 === 0 && z[3].reduce((s, v) => s + v, 0) % 2 === 0 && !parity(z[0]) && !parity(z[2]);
    }
    const sums = [LAWS.fixE, LAWS.fixC, LAWS.moved, Object.values(LAWS.cycleE), Object.values(LAWS.cycleC)].map((l) => Math.abs(l.reduce((s, v) => s + v, 0) - 1) < 1e-12);
    emit(`selfcheck: sampler positions are build group elements ${legal}/8; y == HashDeckBodyFrom ${digest}/8; face-turn words legal ${words}/8; reference laws sum to 1: ${sums.every(Boolean)}`);
    emit(`ideal (uniform G): P(fixE>=2) ${fixed(LAWS.p2E, 6)}, P(fixC>=2) ${fixed(LAWS.p2C, 6)}, mean moved ${fixed(LAWS.movedMean, 4)}`);
    if (legal !== 8 || digest !== 8 || words !== 8 || !sums.every(Boolean)) throw new Error("selfcheck failed");
}

// The commands: their argument names, and what they run after the self-check.
const int = (x) => { if (!/^\d+$/.test(x ?? "")) throw new Error(`expected a non-negative integer, got ${x}`); return parseInt(x, 10); };
const COMMANDS = {
    selfcheck: { args: [], run: async () => {} },
    bench: { args: ["N", "SEED0"], run: (a, w, emit) => runTest("bench", int(a[0]), int(a[1]), w, emit) },
    d2: { args: ["N", "SEED0"], run: (a, w, emit) => runTest("d2", int(a[0]), int(a[1]), w, emit) },
    d1: { args: ["N", "SEED0"], run: (a, w, emit) => runTest("d1", int(a[0]), int(a[1]), w, emit) },
    merge: { args: ["N", "SEED0"], run: (a, w, emit) => runTest("merge", int(a[0]), int(a[1]), w, emit) },
    d3: { args: ["N", "SEED0"], run: (a, w, emit) => runTest("d3", int(a[0]), int(a[1]), w, emit) },
    ci: {
        args: ["SEED0"],
        run: async (a, w, emit) => {
            const s0 = int(a[0]);
            await runTest("d2", 400, s0, w, emit);
            await runTest("d1", 200, s0 + 100000, w, emit);
            await runTest("merge", 25, s0 + 200000, w, emit);
            await runTest("d3", 50, s0 + 300000, w, emit);
        },
    },
};
const usage = () => "usage: zp26_stats.mjs COMMAND [--workers W] | --check LOG [COMMAND]; COMMAND is " +
    Object.entries(COMMANDS).map(([k, c]) => [k, ...c.args].join(" ")).join(" | ");

async function run(args, w, emit) {
    const [name, ...rest] = args;
    const command = COMMANDS[name];
    if (!command || rest.length !== command.args.length) throw new Error(usage());
    emit(`# command: ${args.join(" ")}`);
    await selfcheck(emit);
    await command.run(rest, w, emit);
}

async function main() {
    const args = process.argv.slice(2);
    let w = 4;
    const wi = args.indexOf("--workers");
    if (wi >= 0) { w = int(args[wi + 1]); args.splice(wi, 2); }
    if (args[0] === "--check") {
        const logPath = args[1];
        if (!logPath) throw new Error(usage());
        const old = readFileSync(logPath, "utf8").split("\n");
        const cmd = args.length > 2 ? args.slice(2) : old[0].replace(/^# command: /, "").split(" ");
        const lines = [];
        await run(cmd, w, (s) => lines.push(s));
        const keep = (xs) => xs.filter((s) => s !== "" && !s.startsWith("# time"));
        const a = keep(old), b = keep(lines);
        if (a.length === b.length && a.every((s, i) => s === b[i])) { console.log(`OK ${logPath}`); return; }
        console.log(`STALE ${logPath}`);
        b.forEach((s) => console.error(s));
        process.exit(1);
    }
    await run(args, w, (s) => console.log(s));
}

if (!isMainThread) {
    parentPort.on("message", (job) => parentPort.postMessage(work(job)));
} else {
    await main();
}
