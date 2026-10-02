"""Which card -> piece namings cover all 50 pieces?  (Finite enumeration on the SPEC face
adjacency; m9_search tables.)  Face r's ring, clockwise from outside, starting at the edge
toward a START neighbour: E1 C1 E2 C2 ... E5 C5 (C_j = corner at the clockwise end of E_j).
(1) one piece per card: the 4 suits pick 4 fixed ring positions P (same rule on every face);
    best number of distinct pieces named by the 48 non-King cards, over all P and start rules.
(2) one edge + one corner per card: suit k names (E_k, C_k) for k = 1..4 or k = 2..5."""
import itertools
import mdfix_lib as L

NB = [list(r) for r in L.ref.NBRS]
STARTS = {'lowest': lambda r: min(NB[r]), 'highest': lambda r: max(NB[r]),
          'next id up (cyclic)': lambda r: min(NB[r], key=lambda n: (n - r) % 12),
          'next id down (cyclic)': lambda r: min(NB[r], key=lambda n: (r - n) % 12)}


def ring(r, start, d):
    nb = NB[r] if d == 1 else NB[r][::-1]
    i = nb.index(start)
    nb = nb[i:] + nb[:i]
    out = []
    for j in range(5):
        out.append(frozenset((r, nb[j])))
        out.append(frozenset((r, nb[j], nb[(j + 1) % 5])))
    return out


ALL = {frozenset((r, n)) for r in range(12) for n in NB[r]} | {frozenset(c) for c in L.ref.CORNER_FACES}
assert len(ALL) == 50
best = (0, None)
for sn, sf in STARTS.items():
    for d in (1, -1):
        rings = [ring(r, sf(r), d) for r in range(12)]
        for P in itertools.combinations(range(10), 4):
            u = {rings[r][p] for r in range(12) for p in P}
            if len(u) > best[0]:
                best = (len(u), (sn, 'cw' if d == 1 else 'ccw', P))
print(f'(1) one piece per card, same 4 ring positions on every face: at most {best[0]} of 50 pieces named '
      f'(best rule {best[1]}; enumerated over 4 start rules x 2 directions x 210 position sets). Counting argument: a uniform '
      f'rule picks e edges and 4-e corners per face, naming <= 12e edges and <= 12(4-e) corners; 12e >= 30 forces e >= 3, '
      f'then <= 12 < 20 corners, so no such rule covers all 50 pieces')
for sn, sf in STARTS.items():
    for d in (1, -1):
        rings = [ring(r, sf(r), d) for r in range(12)]
        for ks in ((0, 1, 2, 3), (1, 2, 3, 4)):
            u = set()
            for r in range(12):
                for k in ks:
                    u |= {rings[r][2 * k], rings[r][2 * k + 1]}
            miss = sorted(sorted(x) for x in ALL - u)
            print(f'(2) pair (E_k, C_k), start {sn:22s} {"cw " if d == 1 else "ccw"} k = {ks[0] + 1}..{ks[-1] + 1}: '
                  f'{len(u)} of 50 named; missing {miss}')
