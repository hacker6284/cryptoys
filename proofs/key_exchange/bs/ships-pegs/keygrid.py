"""Ships+pegs key grid: evidence harness, cross-checked against bs.sudo by check_oracle.py; not a
reference.  It simulates BS SPEC §4.2 BUILD (d12 hole die, d6 growth and Sub/Cruiser rolls, d10
row cup) and §4.3 READ (start marker, ship pass, peg pass).  The normative description is
primitives/key_exchange/bs/SPEC.md with bs.sudo beside it; this file follows the SPEC's wording
step by step.  read_ship_pass is written from the SPEC wording and cross-checked against
read_rule.encode on every call.  The dropped all-d6 layout is in ../key-selection/alld6.py.

Layout records use read_rule's convention: (kind, 'H'/'V', (row, col) of first hole, bow),
bow 0 = at the first hole, 1 = at the last hole.  Pegs: 0 none, 1 white, 2 red.
Keypad: SPEC §4.2 step 2 (face f: first hole (f-1)//3, second hole (f-1)%3)."""
import random
from read_rule import encode, KL

KIND = {2: "D", 4: "B", 5: "A"}


def build(rng, n=10, m=10, stats=None):
    """Evidence harness, cross-checked against bs.sudo by check_oracle.py; not a reference."""
    st = stats if stats is not None else {}
    def roll(kind, sides):
        st[kind] = st.get(kind, 0) + 1
        return rng.randint(1, sides)
    under = {}                       # hole -> ship index (the pieces on the board)
    ships, pegs = [], [0] * (n * m)
    free = lambda r, c: 0 <= r < n and 0 <= c < m and (r, c) not in under
    cup = []
    for h in range(n * m):          # the cursor
        r, c = divmod(h, m)
        if c == 0:                                 # step 0: the row cup
            cup = []
            for _ in range((m + 1) // 2):
                while True:
                    f = rng.randint(0, 9); st["d10"] = st.get("d10", 0) + 1
                    if f: break
                    st["d10_void"] = st.get("d10_void", 0) + 1
                cup.append(f)
        if (r, c) not in under:                     # step 1: grow until it bumps
            across, down = free(r, c + 1), free(r + 1, c)
            heading = bow = None
            if across or down:
                f = roll("hole_d12", 12)
                if across and down:
                    heading = None if f <= 4 else ("H" if f <= 8 else "V")
                else:
                    heading = None if f <= 6 else ("H" if across else "V")
                bow = 0 if f % 2 else 1              # odd: bow at this hole
            if heading:
                dr, dc = (0, 1) if heading == "H" else (1, 0)
                L = 2                                  # lay a Destroyer
                while L < 5 and free(r + dr * L, c + dc * L):   # room for one more hole
                    if roll("grow_d6", 6) >= (4 if L == 2 else 6): L += 1   # swap in the next piece
                    else: break
                K = KIND.get(L) or ("S" if roll("kind_d6", 6) <= 3 else "C")
                for t in range(L): under[(r + dr * t, c + dc * t)] = len(ships)
                ships.append((K, heading, (r, c), bow))
        f = cup[c // 2]                               # step 2: the peg
        pegs[h] = (f - 1) // 3 if c % 2 == 0 else (f - 1) % 3
    return ships, pegs


def read_ship_pass(ships, n=10, m=10):
    """The fleet walk, from the SPEC wording, without the start marker."""
    first, last, covered = {}, {}, set()
    for K, o, (r, c), bow in ships:
        L = KL[K]; cells = [(r, c + t) if o == "H" else (r + t, c) for t in range(L)]
        first[cells[0]] = 1 if o == "H" else 2          # white across, red down
        last[cells[-1]] = ([2 if bow == 1 else 1]       # white points back, red points on
                           + ([0 if K == "S" else 1] if L == 3 else []))   # Sub dives, Cruiser flag
        covered.update(cells)
    out = []
    for r in range(n):
        for c in range(m):
            h = (r, c)
            out += [first[h]] if h in first else (last[h] if h in last else [0])
    return out


def read(ships, pegs, n=10, m=10):
    """Cell string for one page: ship pass then peg pass (no marker)."""
    s = read_ship_pass(ships, n, m)
    assert s == encode(ships, n, m)
    return s + list(pegs)


def key_cells(pages, n=10, m=10):
    """The whole key as B7 walks it: the start marker, then every page ships-then-pegs."""
    return [1] + sum((read(s, p, n, m) for s, p in pages), [])


def board_string(rng):
    """One dice-built key grid as the walk string bspegs.walk takes: 'W' (start marker), then the
    ship pass and the peg pass, '.'/'W'/'R' = plain/white/red."""
    ships, pegs = build(rng)
    return "".join(".WR"[t] for t in key_cells([(ships, pegs)]))


def exponent(cells):
    e = 0
    for t in cells: e = 3 * e + t
    return e


if __name__ == "__main__":
    rng = random.Random(1)
    s, p = build(rng)
    t = key_cells([(s, p)])
    print(len(s), "ships;", len(t) - 1, "cells; e has", exponent(t).bit_length(), "bits")
