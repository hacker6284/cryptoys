"""Analytic candidate differences for v10 SumRanks alone. mode V = value difference (card relabelling tau,
g' = tau o g, the kind that passes Compose unchanged), mode P = position difference (g'[cell] = g[pi[cell]]).
For each: (a) same-difference survival P[out diff == in diff], (b) best output difference = count of the most
common output difference over N random decks (a DP estimate). Usage: python3 battery.py [N]"""
import sys, sb
from sb import card as C, cyc, LAB, TW, SOL
N = int(sys.argv[1]) if len(sys.argv) > 1 else 2_000_000
def cell(r, c): return 13 * r + c
def ident(): return list(range(52))
def vmap(f):  # value map from a function on (suit, rank) -> (suit, rank)
    p = ident()
    for s in range(4):
        for r in range(13):
            s2, r2 = f(s, r); p[13*s + r] = 13*s2 + r2
    assert sorted(p) == ident(); return p
def labmap(x, ranks=range(13), mul=False):  # label -> label ^ x (or w*label if mul) on the given ranks
    return vmap(lambda s, r: (SOL[(TW[LAB[s]] if mul else LAB[s] ^ x)] if r in ranks else s, r))
def rankmap(f, suits=range(4)): return vmap(lambda s, r: (s, f(r) % 13 if s in suits else r))
def pmap(f):  # position map from function on (r, c) -> source (r, c)
    p = [0]*52
    for r in range(4):
        for c in range(13):
            r2, c2 = f(r, c); p[cell(r, c)] = cell(r2 % 4, c2 % 13)
    assert sorted(p) == ident(); return p
def pcyc(*cells_cycles): return cyc(*[[cell(*x) for x in cy] for cy in cells_cycles])
V = [  # (description, class, permutation)
 ("swap 2C<->7C", "swap, same suit (earlier worst class)", cyc([C('C','2'), C('C','7')])),
 ("swap 2C<->7H", "swap, different suit+rank", cyc([C('C','2'), C('H','7')])),
 ("swap 2C<->2H", "swap, same rank", cyc([C('C','2'), C('H','2')])),
 ("rank+1 on every card", "v10Sym (proved symmetry)", rankmap(lambda r: r + 1)),
 ("label^1 on every card (C<->D, H<->S)", "v10Sym (proved symmetry)", labmap(1)),
 ("rank+5 and label^2 on every card", "v10Sym (proved symmetry)", vmap(lambda s, r: (SOL[LAB[s] ^ 2], (r + 5) % 13))),
 ("3-cycle AC->2C->3C", "3-cycle, same suit, ranks in AP", cyc([C('C','A'), C('C','2'), C('C','3')])),
 ("3-cycle AC->5C->9C", "3-cycle, same suit, ranks in AP", cyc([C('C','A'), C('C','5'), C('C','9')])),
 ("3-cycle AC->2C->5C", "3-cycle, same suit", cyc([C('C','A'), C('C','2'), C('C','5')])),
 ("3-cycle 2C->2H->2S", "3-cycle, same rank", cyc([C('C','2'), C('H','2'), C('S','2')])),
 ("3-cycle 2C->2D->2H", "3-cycle, same rank", cyc([C('C','2'), C('D','2'), C('H','2')])),
 ("3-cycle 2C->7H->9S", "3-cycle, mixed", cyc([C('C','2'), C('H','7'), C('S','9')])),
 ("3-cycle 2C->2H->7C", "3-cycle, mixed rank/suit", cyc([C('C','2'), C('H','2'), C('C','7')])),
 ("(AC 2C)(5C 6C)", "double swap, same suit, equal rank gaps", cyc([C('C','A'), C('C','2')], [C('C','5'), C('C','6')])),
 ("(AC 2C)(AH 2H)", "double swap, same rank pair in two suits", cyc([C('C','A'), C('C','2')], [C('H','A'), C('H','2')])),
 ("(AC 2C)(3H 4H)", "double swap, equal gaps, two suits", cyc([C('C','A'), C('C','2')], [C('H','3'), C('H','4')])),
 ("(2C 2D)(5H 5S)", "double swap, same-rank pairs with equal GF(4) label change", cyc([C('C','2'), C('D','2')], [C('H','5'), C('S','5')])),
 ("(2C 7H)(7C 2H)", "double swap, cross", cyc([C('C','2'), C('H','7')], [C('C','7'), C('H','2')])),
 ("(2C 3C)(2D 3D)(2H 3H)(2S 3S)", "4 swaps: swap ranks 2,3 in every suit", rankmap(lambda r: {1: 2, 2: 1}.get(r, r))),
 ("label^1 on rank 2 (2C<->2D, 2H<->2S)", "GF(4) suit map on one rank", labmap(1, [1])),
 ("label^2 on rank 2 (2C<->2H, 2S<->2D)", "GF(4) suit map on one rank", labmap(2, [1])),
 ("label^1 on ranks 2,3", "GF(4) suit map on two ranks", labmap(1, [1, 2])),
 ("label^1 on ranks A..6 (half the deck)", "GF(4) suit map on 6 ranks", labmap(1, range(6))),
 ("label x w on rank 2 (D->H->S->D)", "GF(4)-linear (non-translation) suit map on one rank", labmap(0, [1], mul=True)),
 ("label x w on every card", "GF(4)-linear suit map, global", labmap(0, mul=True)),
 ("swap suits C<->D on every card", "suit swap, global (label 0<->1)", vmap(lambda s, r: ({0: 3, 3: 0}.get(s, s), r))),
 ("swap suits C<->H on every card", "suit swap, global (label 0<->2)", vmap(lambda s, r: ({0: 1, 1: 0}.get(s, s), r))),
 ("rank+1 within clubs only", "rank shift on one suit (13-cycle)", rankmap(lambda r: r + 1, [0])),
 ("rank+1 within clubs and diamonds", "rank shift on two suits", rankmap(lambda r: r + 1, [0, 3])),
 ("6-cycle AC->2C->..->6C", "rank cycle on 6 cards of a suit", cyc([C('C', r) for r in range(6)])),
 ("rank x2 on every card", "rank multiplication, global", rankmap(lambda r: 2 * (r + 1) - 1)),
 ("rank -> -rank on every card", "rank negation, global", rankmap(lambda r: -(r + 1) - 1)),
]
P = [
 ("swap cells (0,0)<->(1,0)", "position swap, column 0 (weight-0 cells)", pcyc([(0, 0), (1, 0)])),
 ("swap cells (0,3)<->(0,10)", "position swap in row 0", pcyc([(0, 3), (0, 10)])),
 ("swap cells (2,4)<->(3,4)", "position swap in a column", pcyc([(2, 4), (3, 4)])),
 ("3-cycle (0,1)(0,2)(0,3)", "position 3-cycle in a row", pcyc([(0, 1), (0, 2), (0, 3)])),
 ("3-cycle (2,1)(2,5)(2,9)", "position 3-cycle in a row", pcyc([(2, 1), (2, 5), (2, 9)])),
 ("3-cycle (0,5)(1,5)(2,5)", "position 3-cycle in a column", pcyc([(0, 5), (1, 5), (2, 5)])),
 ("3-cycle (0,1)(1,5)(2,9)", "position 3-cycle across rows/cols", pcyc([(0, 1), (1, 5), (2, 9)])),
 ("(0,1 0,12)(0,2 0,11)", "position double swap, row 0, mirrored", pcyc([(0, 1), (0, 12)], [(0, 2), (0, 11)])),
 ("(0,0 1,0)(2,0 3,0)", "position double swap, column 0", pcyc([(0, 0), (1, 0)], [(2, 0), (3, 0)])),
 ("rotate row 0 left by 1", "row rotation", pmap(lambda r, c: (r, c + 1) if r == 0 else (r, c))),
 ("rotate row 3 left by 1", "row rotation", pmap(lambda r, c: (r, c + 1) if r == 3 else (r, c))),
 ("rotate every row left by 1", "all rows rotated", pmap(lambda r, c: (r, c + 1))),
 ("rotate every row left by 6", "all rows rotated", pmap(lambda r, c: (r, c + 6))),
 ("rotate column 0 down by 1", "column rotation", pmap(lambda r, c: (r - 1, c) if c == 0 else (r, c))),
 ("rotate column 7 down by 2", "column rotation", pmap(lambda r, c: (r - 2, c) if c == 7 else (r, c))),
 ("rotate every column down by 1 (rows cycle)", "all columns rotated", pmap(lambda r, c: (r - 1, c))),
 ("swap rows 0 and 2", "row swap", pmap(lambda r, c: ({0: 2, 2: 0}.get(r, r), c))),
 ("swap columns 0 and 1", "column swap", pmap(lambda r, c: (r, {0: 1, 1: 0}.get(c, c)))),
 ("swap block rows0-1 x cols0-3 with cols6-9", "block move", pmap(lambda r, c: (r, (c + 6) % 13 if r < 2 and c < 4 else (c - 6 if r < 2 and 6 <= c <= 9 else c)))),
]
def run(mode, lst, n):
    out = []
    for i, (desc, cls, p) in enumerate(lst):
        r = sb.survey(0 if mode == "V" else 1, p, n, seed=1000 + i)
        lo, hi = sb.wilson(r["same"], n); tlo, thi = sb.wilson(r["top"], n)
        out.append((mode, desc, cls, r["same"], lo, hi, r["top"], tlo, thi, r["top_is_same"], r["distinct"]))
        print(f"{mode} | {desc:48s} | {cls:52s} | same {r['same']:8d}/{n} = {r['same']/n:.3g} [{lo:.3g},{hi:.3g}] | "
              f"best-out {r['top']:8d} = {r['top']/n:.3g} ({'=in' if r['top_is_same'] else 'other'}) | distinct {r['distinct']}", flush=True)
    return out
if __name__ == "__main__":
    print(f"N = {N} random decks per difference; 1/64 = {1/64:.4g}, 1/221 = {1/221:.4g}")
    run("V", V, N); run("P", P, N)
