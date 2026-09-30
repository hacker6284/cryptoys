"""Exact prefix-survival of card relabellings through v12 GridCycle (= the v11 walk).

MEASUREMENT / EXHAUSTIVE ENUMERATION, not a proof. Lean proves UPPER BOUNDS that
match some of these numbers (security/DoubleDealSecurity/GridCycleSurvival.lean):
A_2(s) <= #(fixed points of s, plus K-clubs/K-spades if s exchanges them)/52 for
every s; A_2 = 0 for every nontrivial v10Sym except v10Sym 0 3; and survival of
v10Sym 0 3 <= 1/4420 (the A_4 value below; heavy library, kernel decide! of the
first-three-seat check). The other printed values are not formalised.

For a relabelling s of card values (a permutation of 0..51) and a deck u (a
permutation of the 52 cards in walk order), GridCycle "commutes with s at u"
iff mix_columns(s.u) = s.mix_columns(u) iff the seat walks of s.u and u agree
at every step (Lean: mixColumns_rel_iff_walk). The seat of walk card n depends
only on the cards u[0..n-1], so

    A_k(s) = P_u[ seat_n(s.u) = seat_n(u) for every n < k ]      (u uniform)

is computed EXACTLY by enumerating the 52*51*...*(52-k+2) ordered prefixes of
length k-1, and A_52(s) >= A_k(s) >= ... is the survival probability. So every
A_k(s) printed here is an exact upper bound on the GridCycle survival of s
(exact rational numbers; the enumeration is exhaustive, not sampled).

Usage:
    python3 prefix_survival.py [--quick]   # the measurements (prefix_survival.log)
    python3 prefix_survival.py --lean      # write the Lean lists LKC / LKS
    python3 prefix_survival.py --check     # CI: fail if the committed Lean lists are stale

--lean / --check: the lists `LKC` / `LKS` of
security/DoubleDealSecurity/GridCycleSurvivalLists.lean (the second and third cards
(c1, c2) that keep the seats of walk cards 1..3 unchanged under v10Sym 0 3 when the
first card is K-clubs / K-spades) are generated here, by the same `seats_prefix`
that computes A_4, and `--check` compares them with the committed file (the
tools/gencheck.py convention, like security/checks/gen_v8_vectors.py). The kernel
checks the lists independently (`Check3 KC LKC`, `Check3 KS LKS`, heavy library),
so a wrong committed list fails the heavy build either way.
"""
import itertools
import sys
from fractions import Fraction
from math import perm
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
sys.path.insert(0, str(HERE.parents[1] / 'security' / 'checks'))
sys.path.insert(0, str(REPO / 'tools'))
import ddport as P  # noqa: E402
from gencheck import parser, emit  # noqa: E402

LEAN_OUT = HERE.parents[1] / 'security' / 'DoubleDealSecurity' / 'GridCycleSurvivalLists.lean'
KC, KS = 12, 38  # K-clubs, K-spades (DoubleDealSecurity/Decks.lean)

suit, rank = P.suit, P.rank


def seats_prefix(pre):
    """Seats of walk cards 0..len(pre) (len(pre)+1 seats) for a walk whose first
    cards are `pre`: the v11 rule, forward direction (ddport.walk_v11)."""
    occ = [[False] * 13 for _ in range(4)]
    grid = [[-1] * 13 for _ in range(4)]
    t = 0
    f = (2, 0)
    seats = []
    prev = None
    for i in range(len(pre) + 1):
        if i == 0:
            r, c = 2, 0
        else:
            tr, tc = P.step(prev, *f)
            if not occ[tr][tc]:
                r, c = tr, tc
                f = (tr, tc)
            else:
                b = grid[tr][tc]
                r, c = P.overflow_seat_v11(occ, (t + suit(b)) % 4, (tc + rank(b)) % 13)
                t = (t + 1) % 4
                f = P.step(b, tr, tc)
        occ[r][c] = True
        seats.append((r, c))
        if i < len(pre):
            prev = pre[i]
            grid[r][c] = prev
    return seats


def selfcheck(n=300, seed=1):
    import random
    rng = random.Random(seed)
    for _ in range(n):
        d = list(range(52))
        rng.shuffle(d)
        full = P.walk_v11(d)
        for k in (1, 2, 3, 5, 51):
            assert seats_prefix(d[:k]) == full[:k + 1], (d, k)


def A(s, k):
    """Exact A_k(s) as a Fraction (enumerates ordered prefixes of length k-1)."""
    if k <= 1:
        return Fraction(1)
    good = 0
    for pre in itertools.permutations(range(52), k - 1):
        spre = [s[c] for c in pre]
        if seats_prefix(list(pre)) == seats_prefix(spre):
            good += 1
    return Fraction(good, perm(52, k - 1))


def names():
    R = 'A23456789TJQK'
    S = 'CHSD'
    return [R[c % 13] + S[c // 13] for c in range(52)]


def seats3_pairs(s, c0):
    """The (c1, c2), c0/c1/c2 distinct, with seats of walk cards 1..3 of the prefix
    (c0, c1, c2) equal to those of (s c0, s c1, s c2). Lean: `check3 c0 L c1 c2` holds
    for every (c1, c2) iff this list is contained in L."""
    out = []
    for c1 in range(52):
        for c2 in range(52):
            if len({c0, c1, c2}) < 3:
                continue
            if seats_prefix([c0, c1, c2])[1:4] == seats_prefix([s[c0], s[c1], s[c2]])[1:4]:
                out.append((c1, c2))
    return out


def lean_text():
    s = P.v10sym(0, 3)
    # Only K-clubs / K-spades can start a surviving deck (Lean gcSurvives_first: the
    # first card must be a fixed point of s, or K-clubs/K-spades exchanged by s).
    starts = [c for c in range(52) if s[c] == c or {c, s[c]} == {KC, KS}]
    assert starts == [KC, KS], starts
    lkc, lks = seats3_pairs(s, KC), seats3_pairs(s, KS)
    # Consistency with the Lean statements (30 triples, 30 / (52 * 51 * 50) = 1/4420 = A_4).
    assert len(lkc) + len(lks) == 30, (len(lkc), len(lks))
    a4 = A(s, 4)
    assert a4 == Fraction(len(lkc) + len(lks), 52 * 51 * 50) == Fraction(1, 4420), a4

    def lst(name, c0, pairs, card):
        rows = []
        for i in range(0, len(pairs), 8):
            rows.append(', '.join(f'({a}, {b})' for a, b in pairs[i:i + 8]))
        body = ',\n    '.join(rows)
        return (f'/-- Second and third cards keeping seats 1..3 unchanged under `v10Sym 0 3`, '
                f'first card {card} (card {c0}). -/\n'
                f'def {name} : List (Fin 52 × Fin 52) :=\n  [{body}]\n')
    return f'''/-
  GENERATED by proofs/doubledeal/analysis/v12-diffusion/prefix_survival.py --lean;
  do not edit (CI: `prefix_survival.py --check`).

  For `v10Sym 0 3` (♣↔♠, ♥↔♦, same rank) and first card
  K♣ (`LKC`) or K♠ (`LKS`): the pairs `(c1, c2)` of second and third cards, with
  `c0, c1, c2` distinct, for which the seats of walk cards 1, 2, 3 are unchanged.
  {len(lkc)} + {len(lks)} = {len(lkc) + len(lks)} pairs; with the first card these are the
  {len(lkc) + len(lks)} first-card triples `T03` of `GridCycleSurvival.lean`
  ({len(lkc) + len(lks)} / (52 · 51 · 50) = 1/4420 = the exact `A_4` in
  `analysis/v12-diffusion/prefix_survival.log`). Only K♣ / K♠ can start a surviving
  deck (`gcSurvives_first`).

  These lists are data, not trusted: the kernel checks that they are complete
  (`Check3 KC LKC`, `Check3 KS LKS`, `decide!` in
  `DoubleDealSecurityHeavy/GridCycleSurvival.lean`), so a wrong list fails the heavy
  build. Card ids are `13 · suit + rank` (suits ♣ ♥ ♠ ♦, ranks A..K).
-/
namespace DoubleDeal.Security.GridCycleSurvival

{lst('LKC', KC, lkc, 'K♣')}
{lst('LKS', KS, lks, 'K♠')}
end DoubleDeal.Security.GridCycleSurvival
'''


def main():
    args = cli.parse_args()
    if args.lean or args.check:
        selfcheck()
        sys.exit(emit(LEAN_OUT, lean_text(), args.check,
                      fix='python3 proofs/doubledeal/analysis/v12-diffusion/prefix_survival.py --lean'))
    quick = args.quick
    selfcheck()
    print('selfcheck: seats_prefix == ddport.walk_v11 prefixes on 300 random decks: ok')
    N = names()
    # Family 1: the 51 nontrivial v10Sym (the symmetries of v10 SumRanks).
    print('\n== v10Sym a x (51 nontrivial): exact A_2, A_3 ==')
    kmax = 3 if not quick else 2
    rows = []
    for a in range(13):
        for x in range(4):
            if (a, x) == (0, 0):
                continue
            s = P.v10sym(a, x)
            vals = [A(s, k) for k in range(2, kmax + 1)]
            rows.append(((a, x), vals))
            print(f'v10Sym {a:2d} {x}: ' + '  '.join(f'A_{k}={v} ({float(v):.3e})'
                                                  for k, v in zip(range(2, kmax + 1), vals)))
    nz = [r for r in rows if r[1][0] != 0]
    print(f'nonzero A_2: {[r[0] for r in nz]}')
    if not quick:
        s = P.v10sym(0, 3)
        a4 = A(s, 4)
        print(f'v10Sym 0 3: A_4 = {a4} ({float(a4):.3e})')
    # Family 2: all 1326 transpositions (value swaps): exact A_2 and A_3.
    print('\n== transpositions (a b), all 1326: exact A_2, A_3 ==')
    best = []
    for a, b in itertools.combinations(range(52), 2):
        s = list(range(52))
        s[a], s[b] = b, a
        a2 = A(s, 2)
        a3 = A(s, 3) if not quick else None
        best.append((a3 if a3 is not None else a2, a2, a, b))
    best.sort(reverse=True)
    a2max = max(x[1] for x in best)
    print(f'max A_2 over transpositions = {a2max} ({float(a2max):.4f}); min = {min(x[1] for x in best)}')
    if not quick:
        print('top 10 by A_3:')
        for a3, a2, a, b in best[:10]:
            print(f'  ({N[a]} {N[b]}): A_2={a2} A_3={a3} ({float(a3):.4f})')
        print(f'min A_3 over transpositions = {min(x[0] for x in best)}')


cli = parser(__doc__)
cli.add_argument('--lean', action='store_true',
                 help='write the Lean lists LKC / LKS (' + str(LEAN_OUT.name) + ')')
cli.add_argument('--quick', action='store_true', help='A_2 only (measurement mode)')

if __name__ == '__main__':
    main()
