"""Exhaustive low-weight scans. Survival is invariant under composing with, or conjugating by, the
52 symmetries (51 non-identity) (v10Sym: rank shift + GF(4) label translation), which act transitively
on cards, so every value difference can be conjugated to move AC. Scans (value differences unless noted):
  c3  : all 3-cycles AC->b->c                         (2550)
  ds  : all double swaps (AC b)(c d)                   (62475)
  pt  : all position transpositions                    (1326)   [position mode, best output diff]
  pc3 : all position 3-cycles                          (44200 incl. orientation) [position mode]
Usage: python3 scan.py KIND N  -> prints the 25 best by same-diff survival (value) or best-out (position)."""
import sys, itertools, sb
from multiprocessing import Pool
from sb import cyc, name
KIND, N = sys.argv[1], int(sys.argv[2])
def cands():
    if KIND == "c3":
        for b in range(1, 52):
            for c in range(1, 52):
                if c != b: yield (f"3-cycle {name(0)}->{name(b)}->{name(c)}", cyc([0, b, c]))
    elif KIND == "ds":
        for b in range(1, 52):
            rest = [x for x in range(1, 52) if x != b]
            for c, d in itertools.combinations(rest, 2): yield (f"({name(0)} {name(b)})({name(c)} {name(d)})", cyc([0, b], [c, d]))
    elif KIND == "pt":
        for a, b in itertools.combinations(range(52), 2): yield (f"cells ({a//13},{a%13})<->({b//13},{b%13})", cyc([a, b]))
    elif KIND == "pc3":
        for a, b, c in itertools.combinations(range(52), 3):
            for o in ((a, b, c), (a, c, b)): yield ("cells " + "->".join(f"({x//13},{x%13})" for x in o), cyc(list(o)))
def work(item):
    desc, p = item
    if KIND in ("c3", "ds"): return (sb.same_only(p, N, 7), 0, desc)
    r = sb.survey(1, p, N, 7); return (r["top"], r["same"], desc)
if __name__ == "__main__":
    with Pool(8) as pool: res = pool.map(work, cands(), chunksize=64)
    res.sort(reverse=True)
    import collections
    print(f"{KIND}: {len(res)} differences, N = {N} decks each (seed 7). Top 25:")
    for r in res[:25]: print(f"  {r[2]:40s} {'same' if KIND in ('c3','ds') else 'best-out'} {r[0]:7d}/{N} = {r[0]/N:.4g}" + ("" if KIND in ("c3", "ds") else f"  same {r[1]}"))
    hist = collections.Counter(min(r[0] * 64 // N, 64) for r in res)
    print("  histogram of score in units of 1/64 (bucket: count):", dict(sorted(hist.items())))
    print("  number above 1/221:", sum(r[0] / N > 1/221 for r in res), " above 1/64:", sum(r[0] / N > 1/64 for r in res))
