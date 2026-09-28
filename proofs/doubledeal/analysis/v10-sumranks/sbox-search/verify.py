"""Verify sbox.c SumRanks against the frozen v10 spec: sum_ranks vectors, the 6 v10 encrypt vectors
(via ddport.encrypt with SumRanks swapped for the C S-box), and ddport on random grids."""
import sys, random
from pathlib import Path
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent.parent.parent / "security/checks"))
sys.path.insert(0, str(HERE))
sys.dont_write_bytecode = True
import ddport as P, sb
from dd_v8 import lay_cm, scoop_cm
def to52(g): return [g[r][c] for r in range(4) for c in range(13)]
def from52(x): return [list(x[13*r:13*r+13]) for r in range(4)]
vecs = P.vectors(10)  # frozen v10 (live vectors are v11)
nsr = 0
for v in vecs:
    if v["kind"] == "sum_ranks":
        assert scoop_cm(from52(sb.sr(to52(lay_cm(v["input"])))[0])) == v["output"], v["name"]; nsr += 1
orig = P.sum_ranks_v10
P.sum_ranks_v10 = lambda g: from52(sb.sr(to52(g))[0])
nenc = 0
for v in vecs:
    if v["kind"] == "encrypt":
        assert P.encrypt(v["message"], v["key"], 10) == v["cipher"], v["name"]; nenc += 1
P.sum_ranks_v10 = orig
rng = random.Random(5)
for _ in range(20000):
    m = list(range(52)); rng.shuffle(m); g = lay_cm(m)
    assert sb.sr(to52(g))[0] == to52(P.sum_ranks_v10(g)), f"C S-box != ddport.sum_ranks_v10 on deck {m}"
print(f"C S-box matches {nsr} v10 sum_ranks vectors, {nenc} v10 encrypt vectors (as the SumRanks inside ddport.encrypt), "
      f"and ddport.sum_ranks_v10 on 20000 random grids")
