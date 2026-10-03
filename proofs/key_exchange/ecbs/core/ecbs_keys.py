"""Key encodings for ECBS (modular: each encoding turns random physical choices into a walk).
Every encoding returns (walk, scalar_terms), where walk is the step list for Board.walk and
scalar_terms is a list of (digit, base_index, frob_count_after) so the scalar can be recomputed
independently: k = sum digit * mu[base_index] * lambda^frob_count_after  (mod l)."""
import random
SHIPS = (5, 4, 3, 3, 2)

def ship_positions(L):
    out = []
    for h in (True, False):
        for r in range(10 if h else 11 - L):
            for c in range(11 - L if h else 10):
                out.append(tuple((r * 10 + c + i) if h else ((r + i) * 10 + c) for i in range(L)))
    return out
POS = {L: ship_positions(L) for L in set(SHIPS)}

def dice_fleet(rnd):
    """The spec's dice procedure: coin for orientation, d10s for the top-left cell (re-rolling only a
       die that would put the ship off the grid), full restart on any overlap.  Returns the list of
       5 ships (tuples of cell numbers 0..99)."""
    while True:
        occ = set(); ships = []
        for L in SHIPS:
            h = rnd.random() < 0.5
            r = rnd.randrange(10) if h else rnd.randrange(11 - L)       # re-rolling off-grid values
            c = rnd.randrange(11 - L) if h else rnd.randrange(10)       # == uniform on the legal range
            cells = tuple((r * 10 + c + i) if h else ((r + i) * 10 + c) for i in range(L))
            if occ & set(cells): break
            occ |= set(cells); ships.append(cells)
        else:
            return ships

def three_state(rnd, G):
    """G fleets; a white/red sign peg (coin) in every ship cell. Returns grids as 100-char lists."""
    grids = []
    for _ in range(G):
        ships = dice_fleet(rnd); g = ['.'] * 100
        for s in ships:
            for c in s: g[c] = 'W' if rnd.random() < 0.5 else 'R'
        grids.append(g)
    return grids

def walk_three_state(grids, twisted=False):
    """one Frobenius per cell, then add +-P_g at a ship cell (P_g = P, or tau-bar^g P if twisted)."""
    walk = []; terms = []
    cells = [(g, c) for g, grid in enumerate(grids) for c in grid]
    M = len(cells)
    for j, (g, c) in enumerate(cells):
        walk.append('F')
        if c != '.':
            base = g if twisted else 0
            walk.append(('A', c, base)); terms.append((1 if c == 'W' else -1, base, M - 1 - j))
    return walk, terms

def pegs_only(rnd, m):
    """m cells, each an independent uniform trit (a blind draw from a bag of empty/white/red tokens)."""
    return [rnd.choice('.WR') for _ in range(m)]

def walk_pegs(cells):
    walk = []; terms = []; M = len(cells)
    for j, c in enumerate(cells):
        walk.append('F')
        if c != '.': walk.append(('A', c, 0)); terms.append((1 if c == 'W' else -1, 0, M - 1 - j))
    return walk, terms

def six_state(rnd, G):
    """G grids: a dice-placed fleet (ship yes/no) AND an independent uniform peg in every cell."""
    out = []
    for _ in range(G):
        ships = dice_fleet(rnd); occ = {c for s in ships for c in s}
        out.append([(rnd.choice('.WR'), c in occ) for c in range(100)])
    return out

def walk_six(grids):
    """per cell: Frobenius; add +-P for the peg; Frobenius; add P if the cell holds a ship."""
    cells = [x for g in grids for x in g]; M = len(cells); walk = []; terms = []
    for j, (peg, ship) in enumerate(cells):
        after_peg = 2 * (M - 1 - j) + 1; after_ship = 2 * (M - 1 - j)
        walk.append('F')
        if peg != '.': walk.append(('A', peg, 0)); terms.append((1 if peg == 'W' else -1, 0, after_peg))
        walk.append('F')
        if ship: walk.append(('A', 'W', 0)); terms.append((1, 0, after_ship))
    return walk, terms

def scalar(terms, lam, mus, l):
    return sum(d * mus[b] * pow(lam, e, l) for d, b, e in terms) % l
