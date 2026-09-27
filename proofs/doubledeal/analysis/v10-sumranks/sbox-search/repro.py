"""Minimal reproducers, run on the repo's reference Python port (ddport.sum_ranks_v10, which matches the v10 vectors),
independent of sbox.c.
1. v10Sym (rank+1 on every card): SumRanks(sigma o deck) == sigma o SumRanks(deck) for every deck.
2. Same-suit 3-cycle tau = AC->2C->3C: whenever AC, 3C, 2C lie in row 0 at columns 1, 2, 3 (deck positions 4, 8, 12
   in column-major order) the difference passes SumRanks with certainty; over random decks it passes 9/1105."""
import sys, random
sys.dont_write_bytecode = True
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[3] / "security/checks"))
import ddport as P
from dd_v8 import lay_cm
AC, C2, C3 = 0, 1, 2
tau = list(range(52)); tau[AC], tau[C2], tau[C3] = C2, C3, AC           # card AC becomes 2C, 2C becomes 3C, 3C becomes AC
rank1 = [13 * (c // 13) + (c % 13 + 1) % 13 for c in range(52)]
def passes(sig, deck):
    g = lay_cm(deck); g2 = lay_cm([sig[c] for c in deck])
    return P.sum_ranks_v10(g2) == [[sig[c] for c in row] for row in P.sum_ranks_v10(g)]
rng = random.Random(2026)
n = 2000
print("1. rank+1 on every card passes on", sum(passes(rank1, rng.sample(range(52), 52)) for _ in range(n)), "/", n, "random decks")
hits = 0
for _ in range(n):
    rest = [c for c in range(52) if c not in (AC, C2, C3)]; rng.shuffle(rest)
    deck = rest[:4] + [AC] + rest[4:7] + [C3] + rest[7:10] + [C2] + rest[10:]
    assert deck[4] == AC and deck[8] == C3 and deck[12] == C2
    hits += passes(tau, deck)
print("2. AC->2C->3C with AC,3C,2C at row 0 columns 1,2,3 passes on", hits, "/", n, "random completions")
print("   why: row 1's turn reads row 0's total sum (13-k)*rank; the three changes are +1 at k=1, +1 at k=3, -2 at k=2,"
      " so the total moves by 12*1 + 10*1 + 11*(-2) = 0; no other row holds a moved card, and suits are unchanged,"
      " so no column total moves either")
r = sum(passes(tau, rng.sample(range(52), 52)) for _ in range(40000))
print(f"   over 40000 fully random decks: {r} passes ({r/40000:.4f}; exact 9/1105 = {9/1105:.4f})")
