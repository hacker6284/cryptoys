"""Deck families (and their Lean boilerplate) for the rank-partition lemma: every relabelling
sigma with the seat-26 condition `Cell0Cov sigma tau` (some tau) maps cards of equal rank
to cards of equal rank (`RankPartition.cell0Cov_rank_of_checks`; unconditional in the
heavy library). One step toward `PrimeNonSwapCase`, not the conjecture.

For each D in {0, 1, 2} (y = 13, 26, 39: the three cards of rank A other than x = 0, the
A of clubs), three classes k and three members i (9 decks per D, 27 in all):
  * all 27 decks of one D agree outside row 3 (seats s with s % 4 = 3);
  * member (k, i) has stem cell 0 equal to the card at the row-0 seat (0, col[k]),
    with col[0], col[1], col[2] distinct;
  * member (k, 1) is member (k, 0) with the cards x and y exchanged (both are in row 3);
  * member (k, 2) agrees with member (k, 0) in row 3 only where member (k, 0) has x or y.
Each deck is emitted as a list of seat swaps (`swapsPerm`, product left to right, applied
to the identity deck). The search is deterministic (xorshift64, seed D + 1). Not a proof by
itself: the heavy Lean library checks the structure (`fam_struct_D`) and each stem cell 0
(`fam_c0_D_k_i`) by kernel `decide!`, so a wrong entry fails the heavy build.

Usage:
    python3 rank_family.py           # print the families
    python3 rank_family.py --lean    # write the Lean files and the log
    python3 rank_family.py --check   # CI: fail if a Lean file or the log is stale

--lean writes
  security/DoubleDealSecurity/RankPartitionLists.lean (famSwaps, famCol),
  security/DoubleDealSecurityHeavy/RankPartitionChecks.lean (fam_struct_D, fam_c0_D_k_i),
  rank_family.log (the printed output).
"""
import contextlib
import io
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
SEC = HERE.parents[1] / 'security'
sys.path.insert(0, str(HERE.parent / 'v12-covariant'))
sys.path.insert(0, str(REPO / 'tools'))
import cell0lib as C  # noqa: E402
from gencheck import parser, emit  # noqa: E402

LISTS_OUT = SEC / 'DoubleDealSecurity' / 'RankPartitionLists.lean'
CHECKS_OUT = SEC / 'DoubleDealSecurityHeavy' / 'RankPartitionChecks.lean'
LOG_OUT = HERE / 'rank_family.log'
FIX = 'python3 proofs/doubledeal/analysis/v12-primenonswap/rank_family.py --lean'

X = 0
YS = [13, 26, 39]
ROW3 = [4 * j + 3 for j in range(13)]


class Rng:
    def __init__(self, seed):
        self.s = (seed * 0x9E3779B97F4A7C15 + 1) & (2**64 - 1)

    def below(self, n):
        s = self.s
        s ^= (s << 13) & (2**64 - 1)
        s ^= s >> 7
        s ^= (s << 17) & (2**64 - 1)
        self.s = s
        return s % n

    def shuffle(self, xs):
        xs = list(xs)
        for i in range(len(xs) - 1, 0, -1):
            j = self.below(i + 1)
            xs[i], xs[j] = xs[j], xs[i]
        return xs


def seat_of_c0(m):
    return m.index(C.g(m))


def base_deck(y):
    """Identity deck with x = 0 and y moved into row 3 (seat 3 and, if needed, seat 7)."""
    m = list(range(52))
    m[0], m[3] = m[3], m[0]
    if y % 4 != 3:
        m[y], m[7] = m[7], m[y]
    assert X in [m[s] for s in ROW3] and y in [m[s] for s in ROW3]
    return m


def with_row3(base, row):
    m = list(base)
    for j, s in enumerate(ROW3):
        m[s] = row[j]
    return m


def family(D):
    y = YS[D]
    base = base_deck(y)
    r3 = [base[s] for s in ROW3]
    rng = Rng(D + 1)
    classes = []
    while len(classes) < 3:
        row = rng.shuffle(r3)
        m1 = with_row3(base, row)
        p = seat_of_c0(m1)
        if p % 4 != 0 or any(p // 4 == c for c, _ in classes):
            continue
        row2 = [y if v == X else X if v == y else v for v in row]
        m2 = with_row3(base, row2)
        if seat_of_c0(m2) != p:
            continue
        for _ in range(20000):
            row3 = rng.shuffle(r3)
            if any(row3[j] == row[j] and row[j] not in (X, y) for j in range(13)):
                continue
            m3 = with_row3(base, row3)
            if seat_of_c0(m3) == p:
                classes.append((p // 4, [m1, m2, m3]))
                break
    return classes


def swaps_of(m):
    """Seat swaps t_1 .. t_n with m = t_1 * ... * t_n as permutations (seat -> card),
    i.e. m[s] = t_1(t_2(...t_n(s))); Lean `swapsPerm` (foldr)."""
    cur = list(m)
    ts = []
    for i in range(52):
        if cur[i] != i:
            j = cur.index(i)
            cur[i], cur[j] = cur[j], cur[i]   # cur := cur * (i j)
            ts.append((i, j))
    ts.reverse()                              # now m * a_1 * ... * a_n = id (a_i appended in
                                              # order), so m = a_n * ... * a_1 = ts[0] * ts[1] * ...
    for s in range(52):                       # self-check against the Lean meaning
        v = s
        for a, b in reversed(ts):
            v = b if v == a else a if v == b else v
        assert v == m[s]
    return ts


def check_structure(fams):
    for D, cl in enumerate(fams):
        y = YS[D]
        cols = [c for c, _ in cl]
        assert len(set(cols)) == 3
        allm = [m for _, ms in cl for m in ms]
        for m in allm:
            assert sorted(m) == list(range(52))
            assert all(m[s] == allm[0][s] for s in range(52) if s % 4 != 3)
        for c, (m1, m2, m3) in cl:
            for mm in (m1, m2, m3):
                assert C.g(mm) == m1[4 * c]
            for s in ROW3:
                v = m1[s]
                assert m2[s] == (y if v == X else X if v == y else v)
                if m3[s] == v:
                    assert v in (X, y)


def report(fams):
    print(f'x = {X}; y = {YS} for D = 0, 1, 2 (the four cards of rank A: 0, 13, 26, 39)')
    for D, cl in enumerate(fams):
        print(f'D = {D} (y = {YS[D]}):')
        for k, (c, ms) in enumerate(cl):
            print(f'  class {k}: stem cell 0 = card {ms[0][4 * c]} at row-0 seat {4 * c} (column {c})')
            for i, m in enumerate(ms):
                print(f'    member {i}: row 3 = {[m[s] for s in ROW3]}; {len(swaps_of(m))} swaps')


def fmt_swaps(ts):
    return '[' + ', '.join(f'({a}, {b})' for a, b in ts) + ']'


def lists_text(fams):
    entries = []
    for D, cl in enumerate(fams):
        for k, (_, ms) in enumerate(cl):
            for i, m in enumerate(ms):
                entries.append(f'    -- D = {D}, class {k}, member {i}\n    {fmt_swaps(swaps_of(m))}')
    cols = [c for cl in fams for c, _ in cl]
    return f'''/-
  GENERATED by proofs/doubledeal/analysis/v12-primenonswap/rank_family.py --lean;
  do not edit (CI: `rank_family.py --check`).

  The 27 decks of the rank-partition families (`permDeck (RankPartition.famPerm D k i)`;
  `famPerm` is the product of entry `9 D + 3 k + i` of `famSwaps`, a list of seat swaps) and the
  row-0 column of stem cell 0 for each class (`famCol`, entry `3 D + k`). These lists are
  data, not trusted: the heavy library checks the structure and every stem cell 0 by
  kernel `decide!` (`fam_struct_D`, `fam_c0_D_k_i`), so a wrong entry fails the heavy build.
-/
namespace DoubleDeal.Security.RankPartition

/-- The seat swaps of the 27 family decks (entry `9 D + 3 k + i`). -/
def famSwaps : List (List (Fin 52 × Fin 52)) := [
{(",\n").join(entries)}]

/-- The row-0 column holding stem cell 0 for class `k` of family `D` (entry `3 D + k`). -/
def famCol : List (Fin 13) := {cols}

end DoubleDeal.Security.RankPartition
'''


def checks_text():
    parts = []
    for D in range(3):
        parts.append(f'/-- (PROVED, kernel `decide!`) The structure of family {D}. -/\n'
                     f'theorem fam_struct_{D} : FamStruct {D} := by decide!\n')
        for k in range(3):
            for i in range(3):
                parts.append(f'/-- (PROVED, kernel `decide!`) Stem cell 0 of deck ({D}, {k}, {i}). -/\n'
                             f'theorem fam_c0_{D}_{k}_{i} : famC0Check {D} {k} {i} := by decide!\n')
    c0cases = ''.join(f'  | ⟨{D}, _⟩, ⟨{k}, _⟩, ⟨{i}, _⟩ => fam_c0_{D}_{k}_{i}\n'
                      for D in range(3) for k in range(3) for i in range(3))
    return f'''/-
  GENERATED by proofs/doubledeal/analysis/v12-primenonswap/rank_family.py --lean;
  do not edit (CI: `rank_family.py --check`).

  HEAVY: the finite checks `RankChecks` of `DoubleDealSecurity/RankPartition.lean`, by
  kernel `decide!`: the structure of each family (`fam_struct_D`, no stem evaluation) and
  one stem evaluation per deck (`fam_c0_D_k_i`, 27). One theorem per deck because kernel
  memory is released between declarations but grows with the number of stem evaluations
  inside one `decide!`.
-/
import DoubleDealSecurity.RankPartition

namespace DoubleDeal.Security.RankPartition

{"".join(parts)}
/-- (PROVED) Every stem-cell-0 check. -/
theorem fam_c0_all : ∀ D k i : Fin 3, famC0Check D k i
{c0cases}
/-- (PROVED) The finite checks. -/
theorem rankChecks_ok : RankChecks := by
  refine ⟨fun D => ?_, fam_c0_all⟩
  match D with
  | ⟨0, _⟩ => exact fam_struct_0
  | ⟨1, _⟩ => exact fam_struct_1
  | ⟨2, _⟩ => exact fam_struct_2

end DoubleDeal.Security.RankPartition
'''


def main():
    args = cli.parse_args()
    fams = [family(D) for D in range(3)]
    check_structure(fams)
    if not (args.lean or args.check):
        report(fams)
        return 0
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        report(fams)
    rc = 0
    for path, text in ((LISTS_OUT, lists_text(fams)), (CHECKS_OUT, checks_text()),
                       (LOG_OUT, buf.getvalue())):
        rc |= emit(path, text, args.check, fix=FIX)
    return rc


cli = parser(__doc__)
cli.add_argument('--lean', action='store_true',
                 help='write the Lean files and the log (see the module docstring)')

if __name__ == '__main__':
    sys.exit(main())
