"""Which SumRanks column weight minimises the best swap's per-round survival?
P_G (GridCycle survival of a swap on a random deck) does not depend on SumRanks, so it is
measured once for all 1326 transpositions (v9 GridCycle); then for a column weight w the
different-rank pairs with w(x) = w(y) mod 4 pass SumRanks with probability 12/51 and the
same-rank pairs with probability ~3/51 (shared column), all others never.
Only weights where (rank mod 13, w mod 4) separates the 52 cards are allowed (T1: no
transposition commutes with SumRanks on all decks). usage: python3 weights.py [N]"""
import sys, pathlib, json, numpy as np
from multiprocessing import Pool
HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "attack"))
import mechanism as M
N = int(sys.argv[1]) if len(sys.argv) > 1 else 100_000
AR = np.arange(52); R = AR % 13 + 1; S = AR // 13
NAMES = M.NAMES

def pg(a):
    x, y = a; _, g = M.run("mix_batch", 1, x, y, N, 5000 + 52 * x + y); return float(g.mean())

WEIGHTS = {
    "rank+suit (v9)": R + S,
    "rank-suit": R - S,
    "rank+suit, K counts 14": np.where(R == 13, 14, R) + S,
    "rank-suit, K counts 14": np.where(R == 13, 14, R) - S,
    "rank+suit, K counts 15": np.where(R == 13, 15, R) + S,
}
if __name__ == "__main__":
    pairs = [(x, y) for x in range(52) for y in range(x + 1, 52)]
    with Pool(8) as p: P = np.array(p.map(pg, pairs, chunksize=16))
    json.dump({"N": N, "pairs": pairs, "P_G": P.tolist()}, open(HERE / "pg_all_pairs.json", "w"))
    print(f"P_G over all 1326 swaps (v9 GridCycle, {N} decks each): mean {P.mean():.4f}, max {P.max():.4f} "
          f"({NAMES[pairs[P.argmax()][0]]}↔{NAMES[pairs[P.argmax()][1]]})")
    for name, w in WEIGHTS.items():
        sep = len({(int(R[c]) % 13, int(w[c]) % 4) for c in AR}) == 52
        best = []
        for (x, y), g in zip(pairs, P):
            if R[x] == R[y]: ps = 3 / 51
            elif (w[x] - w[y]) % 4 == 0: ps = 12 / 51
            else: continue
            best.append((ps * g, ps, g, x, y))
        best.sort(reverse=True)
        top = best[0]
        f6 = top[1] ** 6 * top[2] ** 5
        print(f"{name:26s} separates cards: {sep}; best swap {NAMES[top[3]]}↔{NAMES[top[4]]}: "
              f"P_S {top[1]:.3f} × P_G {top[2]:.3f} = 1/{1 / top[0]:.0f} per round, F6 ≈ {f6:.1e}; "
              f"next: " + ", ".join(f"{NAMES[b[3]]}↔{NAMES[b[4]]} 1/{1 / b[0]:.0f}" for b in best[1:4]))
