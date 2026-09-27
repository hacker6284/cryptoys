"""Mechanism of the v9 swap distinguisher: per-layer survival of a card swap (analysis only).

For a transposition sigma = (x y) of card values and a state m entering a round:
  Compose     sigma commutes with every positional permutation: probability 1 (any key).
  lay/scoop, ShiftRows: positional, probability 1.
  SumRanks    rows rotate by (sum of ranks) mod 13, columns by (sum of rank+suit) mod 4.
              Commutes iff (x, y share a row  or  rank x = rank y) and
                           (x, y share a column after the row step  or  w4 x = w4 y),
              where w4 = (rank + suit) mod 4. Different ranks + equal w4 => exactly
              P(same row) = 12/51 for a uniformly placed state.
  GridCycle   commutes iff the two walks pick the same seat for the card after x and the
              card after y (then everything else is identical). Measured below.
Rounds: Compose with a round key re-randomises seats, so per-round survival multiplies:
  F_r (whitening, r-1 full rounds, final round) ~ P_S^r * P_G^(r-1);  E_r ~ (P_S * P_G)^r.

usage: python3 mechanism.py [N_DECKS] [SEED]      (log: mechanism.log)
"""
import sys, json, ctypes, subprocess, pathlib, time, numpy as np
from multiprocessing import Pool
HERE = pathlib.Path(__file__).resolve().parent
LIB = HERE / "build" / "liblayers.so"
if not LIB.exists() or LIB.stat().st_mtime < max((HERE / f).stat().st_mtime for f in ("layers.c", "dd9.c")):
    LIB.parent.mkdir(exist_ok=True)
    subprocess.check_call(["gcc", "-O2", "-shared", "-fPIC", "-o", str(LIB), str(HERE / "layers.c")])
_L = ctypes.CDLL(str(LIB))
_P = np.ctypeslib.ndpointer(dtype=np.int32, flags="C_CONTIGUOUS")
for f in ("layer_batch", "mix_batch", "stem_batch", "step_diag"):
    getattr(_L, f).argtypes = [ctypes.c_int, _P, ctypes.c_int, ctypes.c_int, _P]

AR = np.arange(52); RANK = AR % 13 + 1; SUIT = AR // 13; W4 = (RANK + SUIT) % 4
NAMES = [r + s for s in "♣♥♠♦" for r in "A23456789TJQK"]   # id = 13*suit + rank-1 (CHaSeD)
def nm(c): return NAMES[c]

def perms(rng, n): return np.ascontiguousarray(np.argsort(rng.random((n, 52)), axis=1).astype(np.int32))

def run(fn, width, x, y, n, seed):
    rng = np.random.default_rng(seed); d = perms(rng, n)
    o = np.zeros((n, width) if width > 1 else n, np.int32); getattr(_L, fn)(n, d, x, y, o)
    return d, o

def ps_analytic(x, y):
    if RANK[x] != RANK[y]: return 12 / 51 if W4[x] == W4[y] else 0.0
    return None   # same rank: needs a shared column after the row step (measured)

def pair_job(a):
    x, y, n, seed = a
    _, s = run("stem_batch", 1, x, y, n, seed)
    _, g = run("mix_batch", 1, x, y, n, seed + 1)
    return x, y, float(s.mean()), float(g.mean())

def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 400_000
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 7
    t0 = time.time(); out = {}
    print(f"# v9 swap mechanism, {n} random decks per measurement, seed {seed}")
    # 1. Per-layer, for the three pairs in results/kq_scaling.jsonl
    print("\n## 1. Per-layer survival for one round (state = uniform random deck)")
    print("pair      P_S meas  P_S theory  P_G|S meas  P_G (fresh deck)  round  1/round")
    per = {}
    for x, y in [(12, 24), (13, 25), (38, 50)]:
        _, o = run("layer_batch", 8, x, y, n, seed + 100 * x + y)
        S = o[:, 0] == 1; G = o[:, 1] == 1
        _, g = run("mix_batch", 1, x, y, n, seed + 7 + 100 * x + y)
        pS, pGS, pG = S.mean(), G[S].mean(), g.mean()
        per[(x, y)] = (pS, pG)
        print(f"{nm(x)}↔{nm(y)}  {pS:.4f}    {ps_analytic(x, y):.4f}      {pGS:.4f}      {pG:.4f}          "
              f"{(S & G).mean():.4f} {1 / (S & G).mean():6.1f}")
    # 2. Predicted vs measured F_r / E_r
    print("\n## 2. Prediction F_r = P_S^r P_G^(r-1), E_r = (P_S P_G)^r  vs  results/kq_scaling.jsonl + F6 run")
    meas = [json.loads(l) for l in open(HERE / "results/kq_scaling.jsonl")]
    f6 = json.load(open(HERE / "results/F6_KcQh_witnesses.json"))
    meas.append({"target": "F6", "swap": [12, 24], "n": f6["n"], "exact": f6["exact"]})
    print("target pair     measured (hits/n)            predicted   meas/pred")
    for r in meas:
        x, y = r["swap"]; pS, pG = per[(x, y)]; k = int(r["target"][1:])
        pred = pS ** k * pG ** (k - 1) if r["target"][0] == "F" else (pS * pG) ** k
        rate = r["exact"] / r["n"]
        print(f"{r['target']:5s}  {nm(x)}↔{nm(y)}  {rate:.3e} ({r['exact']}/{r['n']:.2g})  {pred:.3e}   {rate / pred:.2f}")
    # 3. GridCycle detail for K♣↔Q♥
    print("\n## 3. GridCycle detail for K♣↔Q♥ (step after the earlier of the two cards)")
    print("K♣ = (suit 0, rank 13): its step (Δrow 0, Δcol 13≡0) always targets its own seat -> always overflows")
    print("from column c. Q♥ = (1, 12): target (r+1, c-1); if blocked it scans row t from c-1.")
    print("Same seat iff (r+1, c-1) is occupied and (t, c-1) is occupied [one cell if t = r+1],")
    print("or the scan row is full except one cell (rare). Measured per position i of the card:")
    for x, y in [(12, 24), (24, 12)]:
        d, o = run("step_diag", 6, x, y, n // 4, seed + 11 + x)
        pos_y = np.argmax(d == y, axis=1); px = o[:, 0]; sel = px < pos_y; oo = o[sel]; nl = oo[:, 0] < 51
        other = 1 if x == 12 else 2
        q = (oo[nl, 3] == (oo[nl, 4] + 1) % 4).mean()
        print(f" step after {nm(x)}: ok={oo[:, 5].mean():.3f} (earlier card), Q♥-target blocked={(oo[nl, other] == 1).mean():.3f}, "
              f"P(t = row+1)={q:.3f}")
        out[f"q_{x}"] = float(q)
    d, o = run("step_diag", 6, 12, 24, n, seed + 13)
    # unconditional per-position (earlier/later mixed): use both cards, only steps where the other card is later
    pos_y = np.argmax(d == 24, axis=1); sel = o[:, 0] < pos_y; oo = o[sel]
    q = out["q_12"]
    print(" model f(i) = phi (q + (1-q) phi), phi = i/51 (fill), q = P(t=row+1); f(51) = 1")
    print(" pos   measured ok   model")
    for lo in range(0, 52, 6):
        s = (oo[:, 0] >= lo) & (oo[:, 0] < lo + 6)
        i = np.arange(lo, min(lo + 6, 52)); phi = i / 51; f = np.where(i == 51, 1.0, phi * (q + (1 - q) * phi))
        if s.sum(): print(f" {lo:2d}-{min(lo + 5, 51):2d}  {oo[s, 5].mean():.3f}         {f.mean():.3f}")
    i = np.arange(52); phi = i / 51; f = np.where(i == 51, 1.0, phi * (q + (1 - q) * phi))
    fbar = f.mean(); pairs = (np.outer(f, f).sum() - (f * f).sum()) / (52 * 51)
    print(f" model: mean f = {fbar:.3f}; P_G ≈ E[f(i) f(j)], i≠j = {pairs:.3f} (measured {per[(12, 24)][1]:.3f}); "
          f"per round ≈ 12/51 × {pairs:.3f} = 1/{1 / (12 / 51 * pairs):.1f}")
    # 4. The full class of vulnerable transpositions
    print("\n## 4. All 1326 transpositions: P_S, P_G, per-round survival, predicted F6")
    jobs = [(x, y, n // 4, seed * 1000 + 52 * x + y) for x in range(52) for y in range(x + 1, 52)
            if W4[x] == W4[y] or RANK[x] == RANK[y]]
    with Pool(8) as p: res = p.map(pair_job, jobs, chunksize=4)
    rows = []
    for x, y, pS, pG in res:
        th = ps_analytic(x, y)
        rows.append({"x": x, "y": y, "cls": "same-rank" if th is None else "equal-w4", "P_S": pS, "P_S_theory": th,
                     "P_G": pG, "round": pS * pG, "F6": pS ** 6 * pG ** 5})
    zero = 1326 - len(jobs)
    print(f"{zero} transpositions have different rank and different w4: SumRanks never commutes (P_S = 0 exactly).")
    for cls in ("equal-w4", "same-rank"):
        R = [r for r in rows if r["cls"] == cls]
        ps = np.array([r["P_S"] for r in R]); pg = np.array([r["P_G"] for r in R]); f6 = np.array([r["F6"] for r in R])
        print(f"{cls}: {len(R)} pairs; P_S mean {ps.mean():.4f} [{ps.min():.4f}, {ps.max():.4f}]; "
              f"P_G mean {pg.mean():.4f} [{pg.min():.4f}, {pg.max():.4f}]; predicted F6 median {np.median(f6):.1e}, max {f6.max():.1e}")
    rows.sort(key=lambda r: -r["F6"])
    print("\nTop 20 by predicted F6:")
    print("pair      class     Δ(suit,rank)  P_S     P_G     1/round  pred F6")
    for r in rows[:20]:
        x, y = r["x"], r["y"]
        dv = (int((SUIT[y] - SUIT[x]) % 4), int((RANK[y] - RANK[x]) % 13))
        print(f"{nm(x)}↔{nm(y)}  {r['cls']:9s} {str(dv):12s}  {r['P_S']:.4f}  {r['P_G']:.4f}  {1 / r['round']:6.1f}   {r['F6']:.1e}")
    kc = [r for r in rows if 12 in (r["x"], r["y"]) and r["cls"] == "equal-w4"]
    print(f"\nK♣ (self-blocking card) pairs: {len(kc)}; P_G mean {np.mean([r['P_G'] for r in kc]):.4f} vs "
          f"non-K♣ equal-w4 mean {np.mean([r['P_G'] for r in rows if 12 not in (r['x'], r['y']) and r['cls'] == 'equal-w4']):.4f}")
    json.dump(rows, open(HERE / "results/mechanism_pairs.json", "w"))
    print(f"\n(wrote results/mechanism_pairs.json; {time.time() - t0:.0f}s)")

if __name__ == "__main__":
    main()
