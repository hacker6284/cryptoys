// DoubleDeal-CBC-Sandwich v2 on MegaDreifach v3 (ZP26): the two tests that broke the Sandwich
// MAC's assumptions on MegaDreifach v2 (SPEC §8), re-run on v3. Hand-written harness code: it
// drives ONLY a sudoc JS build of a MegaDreifach sudo ($MD_OUT, default /tmp/megadreifach-v3).
// Every block is the build's dm_step (v3: y = compose(h, em_block(h, deal))), and every group
// operation is the build's compose / inverse / iv_cook12. This file implements no part of W,
// E_m or the Davies-Meyer step; it samples inputs, counts and prints statistics.
// The deprecated v2 sudo has no dm_step; on a v2 build (the positive control) a block is the
// build's compose(h, em_block(h, deal)), the same two calls v2's Hash makes per block.
//
// Usage, from the repo root:
//   sudoc build --target js -o /tmp/megadreifach-v3 primitives/hash/megadreifach/v3/megadreifach.sudo
//   MD_OUT=/tmp/megadreifach-v3 node proofs/doubledeal-cbc-hmac/security/sandwich_v3_stats.mjs COMMAND [--workers W]
//   MD_OUT=/tmp/megadreifach-v3 node proofs/doubledeal-cbc-hmac/security/sandwich_v3_stats.mjs --check LOG [COMMAND]
// COMMAND:
//   a1 N SEED0   A1 / Yasuda f'(v) = f(v, m), m = K turned over, K a uniform secret deck (SPEC §8):
//                y1 = f'(h) at uniform h; W := (h^-1 y1) h^-1; h2 = h with two random edge
//                orientations flipped; accept iff f'(h2) == h2 W h2. Ideal: 1/|G| ~ 2^-225.9.
//   e1 N SEED0   A2 / E1 swap 51-52: secret uniform h, uniform deck D, D' = D with cards 51 and 52
//                swapped; z = f(h,D)^-1 f(h,D'); fixed edge / corner slots of z.
//   e3 N SEED0   E3 the Sandwich itself: t = f*(IV-COOK12, [K, D, L, K turned over]), t' the same
//                with D's last two cards swapped; K, D uniform, L = [1,0,2..51] (a fixed stand-in for
//                the length deck); z = t^-1 t'.
//   ci SEED0     a small fixed slice: a1 400, e1 400, e3 100 (tools/generate-demos.sh, --check)
// Chunks of 500 use the seed SEED0 + c, so results do not depend on the worker count. Every line
// of output is deterministic except the lines starting with "# time". Output starts with
// "# command: COMMAND". --check LOG COMMAND runs COMMAND and compares its whole output (that first
// line included) with the log, ignoring the "# time" lines; without COMMAND it runs the command on
// the log's first line. It prints "OK <log>" or "STALE <log>" (exit 1).
import { Worker, isMainThread, parentPort, workerData } from "node:worker_threads";
import { readFileSync } from "node:fs";
import { join } from "node:path";
import { fileURLToPath } from "node:url";

const OUT = (isMainThread ? process.env.MD_OUT : workerData.out) || "/tmp/megadreifach-v3";
const impl = await import(join(OUT, "_megadreifach_impl.mjs"));
const rt = await import(join(OUT, "_sudo_rt.mjs"));

// ------------------------------------------------------------------ bridge to the build (no logic)
const toPos = (p) => rt.rec(new impl.Position(rt.lst(p[0].map(BigInt)), rt.lst(p[1].map(BigInt)),
    rt.lst(p[2].map(BigInt)), rt.lst(p[3].map(BigInt))));
const fromPos = (p) => [[...p.cp].map(Number), [...p.co].map(Number), [...p.ep].map(Number), [...p.eo].map(Number)];
const deal = (d) => rt.lst(d.map(BigInt));
const comp = (a, b) => impl.compose(a, b);
const inv = (a) => impl.inverse(a);
const HAS_DM = typeof impl.dm_step === "function";
const block = HAS_DM
    ? (h, d) => impl.dm_step(h, deal(d))                            // v3: the build's Davies-Meyer step
    : (h, d) => comp(h, impl.em_block(h, deal(d)));                 // v2 control: the build's own two calls
const casc = (h, decks) => { for (const d of decks) h = block(h, d); return h; };
const bytesOf = (p) => [...impl.position_to_bytes(p)].map(Number);
const bodyFrom = (d, h) => [...impl.HashDeckBodyFrom(deal(d), h)].map(Number);
const HAS_DECKS = typeof impl.HashDecksBody === "function";
const decksBody = (ds) => [...impl.HashDecksBody(rt.lst(ds.map(deal)))].map(Number);
const hex = (xs) => xs.map((x) => x.toString(16).padStart(2, "0")).join("");

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
    const below = (n) => { const lim = Math.floor(4294967296 / n) * n; for (;;) { const x = next(); if (x < lim) return x % n; } };
    const shuffle = (xs) => { for (let j = xs.length - 1; j > 0; j--) { const r = below(j + 1); [xs[j], xs[r]] = [xs[r], xs[j]]; } return xs; };
    const sample2 = (n) => { const x = below(n); let y = below(n - 1); if (y >= x) y++; return [x, y]; };
    return { below, shuffle, sample2 };
}

// ------------------------------------------------------------------ sampling and counting
const range = (n) => [...Array(n).keys()];
const parity = (p) => {
    const seen = new Array(p.length).fill(false); let s = 0;
    for (let i = 0; i < p.length; i++) { if (seen[i]) continue; let L = 0; for (let j = i; !seen[j]; j = p[j]) { seen[j] = true; L++; } s += L - 1; }
    return s & 1;
};
// A uniform legal position: even corner and edge permutations, corner twists summing to 0 mod 3,
// edge flips summing to 0 mod 2 (the legality the build's position_to_bytes ranks).
function uniformH(R) {
    const cp = R.shuffle(range(20)); if (parity(cp)) [cp[0], cp[1]] = [cp[1], cp[0]];
    const ep = R.shuffle(range(30)); if (parity(ep)) [ep[0], ep[1]] = [ep[1], ep[0]];
    const co = range(19).map(() => R.below(3)); co.push((3 - (co.reduce((x, y) => x + y, 0) % 3)) % 3);
    const eo = range(29).map(() => R.below(2)); eo.push(eo.reduce((x, y) => x + y, 0) % 2);
    return [cp, co, ep, eo];
}
const uniformDeal = (R) => R.shuffle(range(52));
const turnedOver = (K) => [...K].reverse();                         // seat i gets K[51 - i]
const LDECK = [1, 0, ...range(52).slice(2)];
const swapLast2 = (d) => { const e = [...d]; [e[50], e[51]] = [e[51], e[50]]; return e; };
const fixC = (z) => { let k = 0; for (let s = 0; s < 20; s++) k += z[0][s] === s; return k; };
const fixE = (z) => { let k = 0; for (let s = 0; s < 30; s++) k += z[2][s] === s; return k; };
const same = (a, b) => a.every((xs, i) => xs.every((x, j) => x === b[i][j]));
const eqArr = (a, b) => a.length === b.length && a.every((x, i) => x === b[i]);

function pairStats() { return { n: 0, fe2: 0, fc2: 0, fe: 0, fe2s: 0, fc: 0, fc2s: 0, eq: 0, chk: 0, chk2: 0 }; }
function addZ(r, zp) {
    const z = fromPos(zp); const e = fixE(z), c = fixC(z);
    r.n++; r.fe2 += e >= 2; r.fc2 += c >= 2; r.fe += e; r.fe2s += e * e; r.fc += c; r.fc2s += c * c;
}
const WORK = {
    a1(job, R) {
        const r = { n: 0, acc: 0, same: 0, chk: 0 };
        for (let i = 0; i < job.n; i++) {
            const m = turnedOver(uniformDeal(R));                   // f'(v) = f(v, K turned over), K secret
            const h = toPos(uniformH(R));
            const y1 = block(h, m);                                 // query 1
            if (i === 0) { if (!eqArr(bytesOf(y1), bodyFrom(m, h))) throw new Error("y1 != HashDeckBodyFrom"); r.chk++; }
            const hi = inv(h);
            const W = comp(comp(hi, y1), hi);                       // h^-1 y1 = W h  =>  W = (h^-1 y1) h^-1
            const [cp, co, ep, eo] = fromPos(h);
            const [a, b] = R.sample2(30);
            eo[a] ^= 1; eo[b] ^= 1;                                 // two edge orientations flipped (legal)
            const h2 = toPos([cp, co, ep, eo]);
            const y2 = block(h2, m);                                // query 2
            const ok = same(fromPos(y2), fromPos(comp(h2, comp(W, h2))));
            const h2i = inv(h2);
            const sw = same(fromPos(comp(comp(h2i, y2), h2i)), fromPos(W)); // ground truth: W unchanged by the flip
            if (ok !== sw) throw new Error("accept != (W unchanged)");
            r.n++; r.acc += ok; r.same += sw;
        }
        return r;
    },
    e1(job, R) {
        const r = pairStats();
        for (let i = 0; i < job.n; i++) {
            const h = toPos(uniformH(R)), d = uniformDeal(R);
            const y = block(h, d), y2 = block(h, swapLast2(d));
            if (i === 0) { if (!eqArr(bytesOf(y2), bodyFrom(swapLast2(d), h))) throw new Error("y' != HashDeckBodyFrom"); r.chk++; }
            r.eq += same(fromPos(y), fromPos(y2));
            addZ(r, comp(inv(y), y2));
        }
        return r;
    },
    e3(job, R) {
        const r = pairStats();
        const IV = impl.iv_cook12();
        for (let i = 0; i < job.n; i++) {
            const K = uniformDeal(R), D = uniformDeal(R), KT = turnedOver(K);
            const pre = casc(IV, [K, D, LDECK]), pre2 = casc(IV, [K, swapLast2(D), LDECK]);
            const t = block(pre, KT), t2 = block(pre2, KT);
            if (i === 0) {
                if (!eqArr(bytesOf(t), bodyFrom(KT, pre))) throw new Error("t != HashDeckBodyFrom");
                r.chk++;
                if (HAS_DECKS) {                                    // the MAC's own primitive (DDCH mac_tag)
                    if (!eqArr(bytesOf(t), decksBody([K, D, LDECK, KT]))) throw new Error("t != HashDecksBody");
                    r.chk2++;
                }
            }
            r.eq += same(fromPos(t), fromPos(t2));
            addZ(r, comp(inv(t), t2));
        }
        return r;
    },
};

// ------------------------------------------------------------------ reference laws and reports
// Fixed points of a uniform element of A_n (edges: A_30, corners: A_20), exact in BigInt.
function factorial(n) { let f = 1n; for (let i = 2n; i <= BigInt(n); i++) f *= i; return f; }
function choose(n, k) { return factorial(n) / (factorial(k) * factorial(n - k)); }
function fixLaw(n) {
    const D = [1n, 0n]; for (let m = 2; m <= n; m++) D.push(BigInt(m - 1) * (D[m - 1] + D[m - 2]));
    const even = [1n]; for (let m = 1; m <= n; m++) even.push((D[m] + (m % 2 === 1 ? 1n : -1n) * BigInt(m - 1)) / 2n);
    const tot = factorial(n) / 2n;
    return range(n + 1).map((j) => Number((choose(n, j) * even[n - j] * 10n ** 30n) / tot) / 1e30);
}
function wilson(k, n) {
    const z = 1.959964, p = k / n, d = 1 + z * z / n, c = (p + z * z / (2 * n)) / d;
    const h = z * Math.sqrt(p * (1 - p) / n + z * z / (4 * n * n)) / d;
    return [c - h, c + h];
}
const f4 = (x) => x.toFixed(4), sg = (x) => (x >= 0 ? "+" : "") + x.toFixed(4);
function report(test, r, emit) {
    if (test === "a1") {
        const [lo, hi] = wilson(r.acc, r.n);
        const ub = r.acc === 0 ? 1 - Math.pow(0.05, 1 / r.n) : hi;
        emit(`A1 (f' = f(., K turned over), 2-edge-flip prediction): accepted ${r.acc}/${r.n} = ${(r.acc / r.n).toExponential(3)}; ` +
            `95% CI (Wilson) [${lo.toExponential(2)}, ${hi.toExponential(2)}]` + (r.acc === 0 ? `; exact one-sided 95% upper bound ${ub.toExponential(2)}` : ""));
        emit(`  accepted == (W unchanged by the flip) in every game; W unchanged ${r.same}/${r.n}; ideal 1/|G| ~ 2^-225.9`);
        emit(`  self-check y1 == build HashDeckBodyFrom: ${r.chk} chunks`);
        return;
    }
    const pE = fixLaw(30), pC = fixLaw(20);
    const iE = 1 - pE[0] - pE[1], iC = 1 - pC[0] - pC[1];
    emit(`${test.toUpperCase()}: ` + (test === "e1"
        ? "secret uniform h, uniform deck D, D' = D with cards 51 and 52 swapped; z = f(h,D)^-1 f(h,D')"
        : "t = f*(IV-COOK12, [K, D, L, K turned over]), t' with D's cards 51 and 52 swapped; z = t^-1 t'"));
    for (const [nm, k, s, s2, ideal] of [["fixE", r.fe2, r.fe, r.fe2s, iE], ["fixC", r.fc2, r.fc, r.fc2s, iC]]) {
        const [lo, hi] = wilson(k, r.n), m = s / r.n, sd = Math.sqrt((s2 - r.n * m * m) / (r.n - 1));
        emit(`  ${nm}: n=${r.n} P(${nm}>=2) = ${f4(k / r.n)} [${f4(lo)},${f4(hi)}] ideal ${ideal.toFixed(6)} adv ${sg(k / r.n - ideal)} ` +
            `(95% half-width ${f4((hi - lo) / 2)}); mean ${f4(m)} +- ${f4(1.96 * sd / Math.sqrt(r.n))} (ideal 1)`);
    }
    emit(`  equal outputs (collisions): ${r.eq}/${r.n}; self-check vs build HashDeckBodyFrom: ${r.chk} chunks` +
        (test === "e3" ? `; vs build HashDecksBody: ${HAS_DECKS ? `${r.chk2} chunks` : "not in this build"}` : ""));
}

// ------------------------------------------------------------------ driver
const CH = 500;
async function pool(test, N, seed0, w) {
    const jobs = range(Math.ceil(N / CH)).map((c) => ({ test, n: Math.min(CH, N - c * CH), seed: seed0 + c }));
    let total = null, next = 0, done = 0;
    const merge = (a, b) => { if (!a) return b; for (const k of Object.keys(b)) a[k] += b[k]; return a; };
    await new Promise((resolve, reject) => {
        for (let k = 0; k < Math.min(w, jobs.length); k++) {
            const wk = new Worker(fileURLToPath(import.meta.url), { workerData: { out: OUT } });
            wk.on("error", reject);
            wk.on("message", (r) => {
                total = merge(total, r); done++;
                if (done === jobs.length) resolve();
                if (next < jobs.length) wk.postMessage(jobs[next++]); else wk.terminate();
            });
            wk.postMessage(jobs[next++]);
        }
    });
    return { total, chunks: jobs.length };
}
async function runTest(test, N, seed0, w, emit) {
    const t0 = performance.now();
    const { total, chunks } = await pool(test, N, seed0, w);
    emit(`${test} N=${N} SEED0=${seed0}: ${chunks} chunks of <= ${CH}, chunk c uses seed SEED0 + c`);
    report(test, total, emit);
    emit(`# time ${test}: ${((performance.now() - t0) / 1000).toFixed(1)} s, ${w} workers`);
}
function header(emit) {
    // A deterministic fingerprint of the build, so a log says which MegaDreifach it ran on.
    const id = range(52);
    emit(`build: HashDeckBody(new-deck order) = ${hex([...impl.HashDeckBody(deal(id))].map(Number))}; ` +
        `block = ${HAS_DM ? "build dm_step" : "build compose(h, em_block(h, deal)) (no dm_step: a v2 build)"}; ` +
        `HashDecksBody ${HAS_DECKS ? "present" : "absent"}`);
    const R = rng(20261004);
    let ok = 0;
    for (let i = 0; i < 8; i++) {
        const h = toPos(uniformH(R)), d = uniformDeal(R);
        ok += same(fromPos(comp(h, inv(h))), fromPos(impl.identity())) && eqArr(bytesOf(block(h, d)), bodyFrom(d, h));
    }
    emit(`selfcheck: sampler positions are build group elements and block == build HashDeckBodyFrom: ${ok}/8`);
    if (ok !== 8) throw new Error("selfcheck failed");
}
const int = (x) => { if (!/^\d+$/.test(x ?? "")) throw new Error(`expected a non-negative integer, got ${x}`); return parseInt(x, 10); };
const COMMANDS = {
    a1: { args: ["N", "SEED0"], run: (a, w, emit) => runTest("a1", int(a[0]), int(a[1]), w, emit) },
    e1: { args: ["N", "SEED0"], run: (a, w, emit) => runTest("e1", int(a[0]), int(a[1]), w, emit) },
    e3: { args: ["N", "SEED0"], run: (a, w, emit) => runTest("e3", int(a[0]), int(a[1]), w, emit) },
    ci: {
        args: ["SEED0"],
        run: async (a, w, emit) => {
            const s0 = int(a[0]);
            await runTest("a1", 400, s0, w, emit);
            await runTest("e1", 400, s0 + 100000, w, emit);
            await runTest("e3", 100, s0 + 200000, w, emit);
        },
    },
};
const usage = () => "usage: sandwich_v3_stats.mjs COMMAND [--workers W] | --check LOG [COMMAND]; COMMAND is " +
    Object.entries(COMMANDS).map(([k, c]) => [k, ...c.args].join(" ")).join(" | ");
async function run(args, w, emit) {
    const [name, ...rest] = args;
    const command = COMMANDS[name];
    if (!command || rest.length !== command.args.length) throw new Error(usage());
    emit(`# command: ${args.join(" ")}`);
    header(emit);
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
    parentPort.on("message", (job) => parentPort.postMessage(WORK[job.test](job, rng(job.seed))));
} else {
    await main();
}
