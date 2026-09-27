"""Class breakdown of SumRanks-only survival (sronly2_<V>.npy): max and mean per pair class."""
import sys, numpy as np
# usage: python3 blindclass.py V1,V2,... [N1]   (N1 = stage-1 decks/pair used by sronly2.py; default 200000)
N1 = int(sys.argv[2]) if len(sys.argv) > 2 else 200000
PAIRS = [(x, y) for x in range(52) for y in range(x + 1, 52)]
rk = lambda c: c % 13; st = lambda c: c // 13
cls = np.array([0 if rk(x) == rk(y) else 1 if st(x) == st(y) else 2 for x, y in PAIRS])
print(f"SumRanks-only survival by pair class (stage-1 data, {N1} decks/pair); max / mean / #pairs>0")
print(f"{'variant':7} {'same rank (78)':>26} {'same suit (312)':>26} {'other (936)':>26}")
for v in sys.argv[1].split(","):
    p = np.load(f"sronly2_{v}.npy"); row = []
    for c in range(3):
        q = p[cls == c]; row.append(f"{q.max():.4f} / {q.mean():.4f} / {int((q > 0).sum()):4d}")
    print(f"{v:7} " + " ".join(f"{r:>26}" for r in row))
