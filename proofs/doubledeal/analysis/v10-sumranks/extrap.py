"""F6 extrapolation for CANDIDATES.md: least-squares fit of log(rate) on the round count r
over the non-zero F2-F4 exact rates in measure.json, evaluated at r = 6.
usage: python3 extrap.py > extrap.log"""
import json, pathlib, numpy as np
HERE = pathlib.Path(__file__).resolve().parent
import sys
d = {}
for f in (sys.argv[1:] or ["measure.json"]): d.update(json.load(open(HERE / f)))
print(f"{'row':22s} {'F2 hits/n':>16s} {'F3 hits/n':>16s} {'F4 hits/n':>16s}  {'per-round':>9s}  {'F6 extrap':>9s}  {'F6 formula':>10s}")
for key, v in d.items():
    row = {t: v[t] for t in ("F2", "F3", "F4") if t in v}
    if len(row) < 2:
        continue
    pts = [(int(t[1]), np.log(h / n)) for t, (h, n) in row.items() if h]
    if len(pts) > 1:
        slope, icpt = np.polyfit(*zip(*pts), 1)
        f6x = float(np.exp(np.polyval([slope, icpt], 6))); per = float(np.exp(slope))
    else:
        f6x = per = 0.0
    cells = " ".join(f"{h:>7d}/{n:<8.2g}" for (h, n) in row.values())
    note = "" if len(pts) == 3 else f"  ({len(pts)} non-zero points)"
    print(f"{key:22s} {cells}  {per:9.3g}  {f6x:9.2g}  {v.get('F6_formula', float('nan')):10.2g}{note}")
