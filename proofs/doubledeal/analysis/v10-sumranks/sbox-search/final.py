"""High-precision re-measurement of the worst differences found (20M decks each by default) -> markdown table.
Every row reports (a) same-difference survival and (b) the count of the most common output difference."""
import sys, sb
from sb import card as C, cyc
from fractions import Fraction as F
N = int(sys.argv[1]) if len(sys.argv) > 1 else 20_000_000
def cell(r, c): return 13 * r + c
rank1 = [13 * s + (r + 1) % 13 for s in range(4) for r in range(13)]
rows = [
 ("V", "rank+1 on every card (any of the 51 v10Sym elements)", "exact symmetry (proved, SumRanksV10Iff)", rank1, F(1)),
 ("V", "3-cycle of three same-suit cards, e.g. AC->2C->3C", "same-suit 3-cycle", cyc([C('C','A'), C('C','2'), C('C','3')]), F(9, 1105)),
 ("V", "4-cycle of same-suit cards AC->2C->3C->4C", "same-suit 4-cycle", cyc([C('C', r) for r in range(4)]), F(761, 270725)),
 ("V", "two swaps of same-suit pairs, unequal gaps, e.g. (AC 2C)(AH 3H)", "same-suit double swap", cyc([C('C','A'), C('C','2')], [C('H','A'), C('H','3')]), F(691, 270725)),
 ("V", "swap of two same-suit cards, e.g. 2C<->7C", "same-suit swap (old worst)", cyc([C('C','2'), C('C','7')]), F(1, 221)),
 ("V", "3-cycle of three same-rank cards, e.g. 2C->2H->2S", "same-rank 3-cycle", cyc([C('C','2'), C('H','2'), C('S','2')]), F(1, 850)),
 ("V", "GF(4) suit map on one rank, e.g. 2C<->2D, 2H<->2S", "subset relabelling", cyc([C('C','2'), C('D','2')], [C('H','2'), C('S','2')]), F(3, 20825)),
 ("P", "position swap cells (1,2)<->(3,6)", "best position swap (scan+hill-climb)", cyc([cell(1, 2), cell(3, 6)]), None),
 ("P", "position swap cells (0,0)<->(1,0) (weight-0 column)", "position swap", cyc([cell(0, 0), cell(1, 0)]), None),
 ("P", "rotate every row left by 1", "all-rows rotation", [cell(r, (c + 1) % 13) for r in range(4) for c in range(13)], None),
]
print("| # | kind | difference | class | (a) same-diff survival: hits/N, rate, 95% CI | exact | (b) best output diff: hits, rate | vs 1/64 | vs 1/221 |")
print("|---|---|---|---|---|---|---|---|---|")
for i, (m, d, cls, p, ex) in enumerate(rows):
    r = sb.survey(0 if m == "V" else 1, p, N, seed=77 + i)
    lo, hi = sb.wilson(r["same"], N); rate = r["same"] / N; top = r["top"] / N
    worst = max(rate, top)
    print(f"| {i+1} | {'value' if m == 'V' else 'position'} | {d} | {cls} | {r['same']}/{N} = {rate:.4g} (1/{1/rate if rate else float('inf'):.0f}) [{lo:.3g}, {hi:.3g}] | "
          f"{'' if ex is None else f'{ex} = 1/{1/float(ex):.1f}'} | {r['top']} = {top:.3g} ({'same as input' if r['top_is_same'] else 'a different output diff'}) | "
          f"{'ABOVE' if worst > 1/64 else 'below'} | {'ABOVE' if worst > 1/221 else 'below'} |", flush=True)
