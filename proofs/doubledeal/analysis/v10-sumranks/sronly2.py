"""SumRanks-step-only worst-pair swap survival over all 1326 transpositions for any variant in
candidates.VARIANTS (uses cand.c sr_only_var). A swap survives if SumRanks(swap(x)) == swap(SumRanks(x)).
Stage 1: all pairs x N1 decks; stage 2: top 5 re-measured with fresh seeds at N2 decks.
usage: python3 sronly2.py N1 N2 v9,SR3,W1,... > sronly2.log"""
import sys, ctypes, numpy as np, cport
from multiprocessing import Pool
from candidates import VARIANTS
N1, N2 = int(sys.argv[1]), int(sys.argv[2]); NAMESV = sys.argv[3].split(",")
NAMES = [r + s for s in "♣♥♠♦" for r in "A23456789TJQK"]
PAIRS = [(x, y) for x in range(52) for y in range(x + 1, 52)]
L = cport._L
L.sr_only_var.argtypes = [ctypes.c_int, cport._P, cport._P, cport._PL]
def count(a):
    var, x, y, n, seed = a
    L.set_var(var); rng = np.random.default_rng(seed)
    sig = np.arange(52, dtype=np.int32); sig[x], sig[y] = y, x
    out = np.zeros(1, np.int64); done = 0
    while done < n:
        b = min(100_000, n - done); ds = cport.rand_perms(rng, b); L.sr_only_var(b, ds, sig, out); done += b
    return int(out[0])
if __name__ == "__main__":
    print(f"# SumRanks-only swap survival; stage 1: 1326 pairs x {N1} decks (sd at 1/64: {np.sqrt(1/64*63/64/N1):.1e}); "
          f"stage 2: top 5 at {N2} decks, fresh seeds. Benchmark 1/64 = 0.0156. Same decks for every variant.")
    print("variant  pairs>0  pairs>1/64  stage-1 max (pair)        worst re-measured (95%)          top-5 re-measured")
    with Pool(8) as pool:
        for name in NAMESV:
            var = VARIANTS[name]
            p = np.array(pool.map(count, [(var, x, y, N1, 5 + 52 * x + y) for x, y in PAIRS], chunksize=4)) / N1
            np.save(f"sronly2_{name}.npy", p)
            top = np.argsort(-p)[:5]; n2 = (N2 // 8) * 8
            re = pool.map(count, [(var, PAIRS[i][0], PAIRS[i][1], N2 // 8, 10**6 + 1000 * i + w) for i in top for w in range(8)])
            q = [sum(re[8 * j:8 * j + 8]) / n2 for j in range(5)]; k = int(np.argmax(q)); qq = q[k]
            nm = lambda i: f"{NAMES[PAIRS[i][0]]}↔{NAMES[PAIRS[i][1]]}"
            print(f"{name:7s}  {int((p > 0).sum()):7d}  {int((p > 1 / 64).sum()):10d}  {p[top[0]]:.4f} ({nm(top[0])})     "
                  f"{qq:.4f} ± {1.96 * np.sqrt(qq * (1 - qq) / n2):.4f} = 1/{1 / qq if qq else float('inf'):.1f} ({nm(top[k])})   "
                  + ", ".join(f"{nm(i)} {x:.4f}" for i, x in zip(top, q)), flush=True)
