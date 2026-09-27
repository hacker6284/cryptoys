"""All 1326 transpositions: per-round survival P(stem and GridCycle commute) on uniform decks,
per variant; distribution summary and the product-formula F6 = P_S^6 (P_round/P_S)^5.
usage: python3 allpairs.py [N] > allpairs.log   (same seeds for every variant)"""
import sys, json, numpy as np, cport
from multiprocessing import Pool
from candidates import VARIANTS
from relations import transposition
N = int(sys.argv[1]) if len(sys.argv) > 1 else 20000
NAMES = [r + s for s in "♣♥♠♦" for r in "A23456789TJQK"]
PAIRS = [(x, y) for x in range(52) for y in range(x + 1, 52)]
def job(a):
    var, x, y = a
    rng = np.random.default_rng(7919 * 11 + 52 * x + y)
    return cport.layer_counts(cport.rand_perms(rng, N), transposition(x, y), var) / N
out = {}
print(f"n = {N} uniform decks per pair (resolution ~{1 / N:.0e}); P_round = P(SumRanks+ShiftRows and GridCycle both commute)")
print("variant  pairs P_S>0  pairs P_round>0  P_round>=1e-2  median P_round  max P_round (pair)      F6 formula max  sum over pairs F6 formula")
with Pool(8) as pool:
    import os
    for name in os.environ.get("VARS", "v9,R2,GR2,SP,PW,PW2,PW3").split(","):
        var = VARIANTS[name]
        R = np.array(pool.map(job, [(var, x, y) for x, y in PAIRS], chunksize=8))
        pS, pr = R[:, 0], R[:, 2]
        f6 = np.where(pS > 0, pS ** 6 * (pr / np.where(pS > 0, pS, 1)) ** 5, 0)
        i = int(np.argmax(pr)); j = int(np.argmax(f6))
        print(f"{name:7s}  {int((pS > 0).sum()):11d}  {int((pr > 0).sum()):15d}  {int((pr >= 1e-2).sum()):13d}  {np.median(pr):14.2e}  "
              f"{pr[i]:.2e} ({NAMES[PAIRS[i][0]]}↔{NAMES[PAIRS[i][1]]})    {f6[j]:.1e} ({NAMES[PAIRS[j][0]]}↔{NAMES[PAIRS[j][1]]})  {f6.sum():.1e}", flush=True)
        out[name] = {"P_S": pS.tolist(), "P_round": pr.tolist()}
json.dump(out, open(os.environ.get("OUT", "allpairs.json"), "w"))
