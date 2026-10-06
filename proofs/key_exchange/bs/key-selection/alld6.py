"""The all-d6 key-grid layout that BS SPEC §4.2 dropped (NOTES.md §5, "Dice layouts dropped from
the spec").  Analysis only: it is not a SPEC option.  Moved here from ../ships-pegs/keygrid.py,
where it was build(..., fallback="d6"); the dice it throws, and their order, are unchanged.

Step 1 (grow until it bumps) with a d6 hole die: both headings open, 1-2 sea, 3-4 across, 5-6
down; one heading open, 1-3 sea, 4-6 that heading; a separate d6 for the bow (1-3 at this hole).
Growth and Sub/Cruiser rolls as in the SPEC.  Step 2: one d6 per peg (1-2 none, 3-4 white,
5-6 red).  Layout records as in ../ships-pegs/keygrid.py."""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "ships-pegs"))
from keygrid import KIND


def build_all_d6(rng, n=10, m=10, stats=None):
    st = stats if stats is not None else {}
    def roll(kind, sides):
        st[kind] = st.get(kind, 0) + 1
        return rng.randint(1, sides)
    under = {}                       # hole -> ship index (the pieces on the board)
    ships, pegs = [], [0] * (n * m)
    free = lambda r, c: 0 <= r < n and 0 <= c < m and (r, c) not in under
    for h in range(n * m):          # the cursor
        r, c = divmod(h, m)
        if (r, c) not in under:                     # step 1: grow until it bumps
            across, down = free(r, c + 1), free(r + 1, c)
            heading = bow = None
            if across or down:
                f = roll("hole_d6", 6)
                if across and down:
                    heading = None if f <= 2 else ("H" if f <= 4 else "V")
                else:
                    heading = None if f <= 3 else ("H" if across else "V")
                if heading: bow = 0 if roll("bow_d6", 6) <= 3 else 1
            if heading:
                dr, dc = (0, 1) if heading == "H" else (1, 0)
                L = 2                                  # lay a Destroyer
                while L < 5 and free(r + dr * L, c + dc * L):   # room for one more hole
                    if roll("grow_d6", 6) >= (4 if L == 2 else 6): L += 1   # swap in the next piece
                    else: break
                K = KIND.get(L) or ("S" if roll("kind_d6", 6) <= 3 else "C")
                for t in range(L): under[(r + dr * t, c + dc * t)] = len(ships)
                ships.append((K, heading, (r, c), bow))
        pegs[h] = (roll("peg_d6", 6) - 1) // 2        # step 2: one d6 per peg
    return ships, pegs
