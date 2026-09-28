"""Merge cand.c round outputs (a b srHits roundHits N) for one variant: python3 round2agg.py V files..."""
import sys, math
from collections import defaultdict
v = sys.argv[1]; S = 'CHSD'; R = 'A23456789TJQK'; nm = lambda c: R[c % 13] + S[c // 13]
HS = defaultdict(int); HR = defaultdict(int); N = defaultdict(int)
for f in sys.argv[2:]:
    for l in open(f):
        a, b, hs, hr, n = map(int, l.split()); HS[a, b] += hs; HR[a, b] += hr; N[a, b] += n
ks = sorted(HR, key=lambda k: -HR[k]); n = N[ks[0]]; h = HR[ks[0]]
p = h / n; z = 1.96; den = 1 + z * z / n; c = p + z * z / (2 * n); r = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n))
print(f"V{v} round: N={n}/same-suit pair; SR-stage mean {sum(HS.values())/len(HS)/n:.2e}; round mean {sum(HR.values())/len(HR)/n:.2e}; "
      f"GC|SR {sum(HR.values())/sum(HS.values()):.3f}; worst {nm(ks[0][0])}<->{nm(ks[0][1])} {h}/{n}={p:.2e} CI[{(c-r)/den:.1e},{(c+r)/den:.1e}]")
