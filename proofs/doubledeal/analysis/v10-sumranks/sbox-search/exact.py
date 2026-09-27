"""Exact survival probabilities (no sampling) for two families of value differences.
Fact used: if every turn amount is unchanged, the output difference equals the input difference, and when the
relabelling keeps every card's suit (resp. rank) the columns (resp. rows) see nothing at all. The grid each
stage reads from is a bijective image of the input grid, so it is uniformly random; the moved cards therefore sit
in uniformly random distinct cells and survival = fraction of placements where every read total is unchanged.
  suit-preserving tau: condition per row: sum over moved cards in the row of (13-k)*(rank change) = 0 mod 13
  rank-preserving tau: condition per column j: (GF(4) label change of col j-1, weighted by row 0,1,w,w^2)
                        XOR (XOR of label changes in col j) = 0, for all 13 columns cyclically."""
import itertools, sys
from fractions import Fraction
from sb import card as C, name
LAB = [0, 2, 3, 1]; TW = [0, 2, 3, 1]
def wmul(x, r):  # multiply label x by w^r for row weights 0,1,w,w^2 (row 0 weight 0)
    if r == 0: return 0
    for _ in range(r - 1): x = TW[x]
    return x
def exact(moves):  # moves: dict card -> image card
    cards = list(moves)
    suit_pres = all(c // 13 == moves[c] // 13 for c in cards)
    rank_pres = all(c % 13 == moves[c] % 13 for c in cards)
    assert suit_pres or rank_pres
    dr = [(moves[c] % 13 - c % 13) % 13 for c in cards]
    dl = [LAB[moves[c] // 13] ^ LAB[c // 13] for c in cards]
    good = tot = 0
    for cells in itertools.permutations(range(52), len(cards)):
        tot += 1
        if suit_pres:
            acc = [0] * 4
            for (cl, d) in zip(cells, dr): acc[cl // 13] += (13 - cl % 13) * d
            good += all(a % 13 == 0 for a in acc)
        else:
            S = [0] * 13; Vv = [0] * 13
            for (cl, d) in zip(cells, dl): r, c = divmod(cl, 13); S[c] ^= d; Vv[c] ^= wmul(d, r)
            good += all((Vv[(j - 1) % 13] ^ S[j]) == 0 for j in range(13))
    return Fraction(good, tot)
def cyc(*cs): 
    m = {}
    for c in cs:
        for i, x in enumerate(c): m[x] = c[(i + 1) % len(c)]
    return m
CASES = [
 ("swap 2C<->7C", cyc([C('C','2'), C('C','7')])),
 ("3-cycle AC->2C->3C", cyc([C('C','A'), C('C','2'), C('C','3')])),
 ("3-cycle AC->8C->JC", cyc([C('C','A'), C('C','8'), C('C','J')])),
 ("3-cycle 2C->2H->2S (same rank)", cyc([C('C','2'), C('H','2'), C('S','2')])),
 ("swap 2C<->2H (same rank)", cyc([C('C','2'), C('H','2')])),
]
if len(sys.argv) > 1:  # also the 4-card ones (slower)
    CASES += [("(AC 2C)(5C 6C)", cyc([C('C','A'), C('C','2')], [C('C','5'), C('C','6')])),
              ("(AC 2C)(AH 2H)", cyc([C('C','A'), C('C','2')], [C('H','A'), C('H','2')])),
              ("4-cycle AC->2C->3C->4C", cyc([C('C', r) for r in range(4)])),
              ("4-cycle AC->2C->4C->3C", cyc([C('C','A'), C('C','2'), C('C','4'), C('C','3')])),
              ("label^1 on rank 2 (2C<->2D)(2H<->2S)", cyc([C('C','2'), C('D','2')], [C('H','2'), C('S','2')]))]
if __name__ == "__main__":
  for d, m in CASES:
    p = exact(m); print(f"  {d:40s} exact {p} = {float(p):.6g} = 1/{1/float(p) if p else float('inf'):.1f}", flush=True)
