"""v9Sym is cyclic of order 52. Every nontrivial element has a power equal to
W1 = v9Sym 0 2 (the unique involution) or W2 = v9Sym 1 0 (order 13)."""
import sys, pathlib; sys.path.insert(0, str(pathlib.Path(__file__).parent))
from emp import v9sym
G = {(a, b): v9sym(a, b) for a in range(13) for b in range(4)}
I = list(range(52)); comp = lambda s, t: [s[t[c]] for c in range(52)]
assert all(comp(s, t) in G.values() for s in G.values() for t in G.values())
W1, W2 = G[(0, 2)], G[(1, 0)]
for ab, s in G.items():
    if ab == (0, 0): continue
    x = s
    while x not in (W1, W2):
        x = comp(s, x); assert x != I, ab
print("ok: all 51 nontrivial v9Sym reduce to W1 or W2")
