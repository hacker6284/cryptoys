"""Context check (not SumRanks alone): for the worst SumRanks differences, how often does the same relabelling
also survive GridCycle (MixColumns) and a whole unkeyed round (SumRanks, ShiftRows, GridCycle)? Uses the repo's
cand.c (../cport.py, which builds ../build/libcand.so), variant W5c = v10. Relabellings commute with Compose (the keyed step), so the round
count is the per-round survival of a value difference. Usage: python3 round_check.py N"""
import sys, numpy as np
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent)); sys.dont_write_bytecode = True
import cport, sb
from sb import card as C, cyc
N = int(sys.argv[1]) if len(sys.argv) > 1 else 1_000_000
W5c = 131072
def vmap(f): return [13 * f(s, r)[0] + f(s, r)[1] for s in range(4) for r in range(13)]
LAB = [0, 2, 3, 1]; SOL = [0, 3, 1, 2]
cases = [
 ("rank+1 on every card (v10Sym)", vmap(lambda s, r: (s, (r + 1) % 13))),
 ("label^1 on every card (v10Sym)", vmap(lambda s, r: (SOL[LAB[s] ^ 1], r))),
 ("rank+5, label^2 (v10Sym)", vmap(lambda s, r: (SOL[LAB[s] ^ 2], (r + 5) % 13))),
 ("3-cycle AC->2C->3C", cyc([C('C', 'A'), C('C', '2'), C('C', '3')])),
 ("3-cycle AC->8C->JC", cyc([C('C', 'A'), C('C', '8'), C('C', 'J')])),
 ("3-cycle 5H->9H->KH", cyc([C('H', '5'), C('H', '9'), C('H', 'K')])),
 ("swap 2C<->7C", cyc([C('C', '2'), C('C', '7')])),
 ("swap KC<->KD (the v8 distinguisher pair)", cyc([C('C', 'K'), C('D', 'K')])),
]
rng = np.random.default_rng(11)
print(f"N = {N} random decks; columns: SumRanks+ShiftRows ('stem'), GridCycle alone (fresh deck), whole round")
for desc, sig in cases:
    ds = cport.rand_perms(rng, N)
    s, m, r = cport.layer_counts(ds, np.array(sig, np.int32), W5c)
    lo, hi = sb.wilson(int(r), N)
    print(f"  {desc:42s} stem {s:8d}  gridcycle {m:8d}  round {r:6d}  (round {r/N:.3g}, 95% CI [{lo:.2g},{hi:.2g}])")
