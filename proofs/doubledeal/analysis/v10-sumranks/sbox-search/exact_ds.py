"""Exact survival of every class of double swap of same-suit pairs (a a+d1)(b b+d2): for suit-preserving
differences only the rank gaps matter (see exact.py). d1, d2 in 1..6 (a gap d and 13-d are the same swap)."""
from multiprocessing import Pool
from exact import exact
from sb import card as C, cyc
def job(dd):
    d1, d2 = dd
    return d1, d2, exact(cyc([C('C', 0), C('C', d1)], [C('H', 0), C('H', d2)]))
if __name__ == "__main__":
    cls = [(a, b) for a in range(1, 7) for b in range(a, 7)]
    with Pool(8) as p: res = p.map(job, cls)
    res.sort(key=lambda r: -r[2])
    for d1, d2, pr in res: print(f"  gaps ({d1},{d2})  exact {pr} = {float(pr):.6g} = 1/{1/float(pr):.1f}  {'> 1/221' if pr > 1/221 else ''}")
