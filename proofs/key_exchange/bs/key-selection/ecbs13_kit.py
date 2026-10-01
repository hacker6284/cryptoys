"""Themed three-state fleet key (a candidate key that was not chosen; NOTES.md): the former BS §4.1 = ECBS §1.3 placement with the proposed dice: d20 = heading (low half across, high half down) +
across coordinate (last digit, 0 = 10); along die = smallest die whose top face keeps the ship on
the grid (Carrier d6, Battleship d8, 3-holers d8, Destroyer d10), re-rolled if off the grid;
full restart on overlap (unchanged); signs: one d8 per two ship cells (half, then odd/even)."""
import random, collections, json, itertools
from fractions import Fraction as F
from pathlib import Path
HERE = Path(__file__).resolve().parent            # every file path is anchored on this script's directory
FLEET = [5, 4, 3, 3, 2]; ALONG = {5: 6, 4: 8, 3: 8, 2: 10}
# exactness of the d20 split: (half, last digit as 1..10) uniform over 2 x 10
cnt = collections.Counter((f > 10, (f % 10) or 10) for f in range(1, 21))
assert len(cnt) == 20 and set(cnt.values()) == {1}
# exactness of sign d8: (half, parity) uniform 2x2
cnt = collections.Counter((f > 4, f % 2) for f in range(1, 9)); assert set(cnt.values()) == {2}
def place(rng, st):
    while True:
        st["attempts"] += 1; occ = set(); ok = True
        for L in FLEET:
            st["reads"] += 1; f = rng.randint(1, 20); o = f > 10; a = (f % 10) or 10
            while True:
                st["reads"] += 1; s = rng.randint(1, ALONG[L])
                if s <= 11 - L: break
                st["offgrid_rerolls"] += 1
            cells = {(a, s + t) if not o else (s + t, a) for t in range(L)}
            if cells & occ: ok = False; break
            occ |= cells
        if ok: break
        st["restarts"] += 1
    st["reads"] += 9; st["sign_reads"] += 9          # ceil(17/2) d8 for 17 sign cells
rng = random.Random(13); st = collections.Counter(); M = 200000
for _ in range(M): place(rng, st)
res = {k: v / M for k, v in st.items()}
print(json.dumps(res)); json.dump(res, open(HERE / "ecbs13_kit_results.json", "w"), indent=1)
