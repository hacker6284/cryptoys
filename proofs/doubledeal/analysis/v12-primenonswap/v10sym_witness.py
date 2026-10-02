"""Witness decks (and their Lean boilerplate) for steps 2-4 of the seat-26 argument: every
relabelling sigma with `Cell0Cov sigma tau` (some tau) is a `v10Sym a x` and tau = sigma
(`LabelStep.cell0Cov_mem_v10Sym_of_checks`; unconditional in the heavy library). Step 1
(the rank partition) is `rank_family.py`.

Three groups of decks (cards are seat contents of `permDeck`; rank index = card % 13):
  * aff (9 decks, classes k, members i; step 2, the rank map is affine): the four cards
    x = 0, y = 1, x2 = 2, y2 = 14 sit in row 3 of member (k, 0) at columns cx, cy, cx2, cy2
    with cx + cy2 = cy + cx2 (mod 13); member (k, 1) is member (k, 0) with x <-> y AND
    x2 <-> y2 exchanged; member (k, 2) agrees with member (k, 0) in row 3 only where member
    (k, 0) has one of the four cards; all 9 decks agree outside row 3; member (k, i) has stem
    cell 0 at the row-0 seat (0, col[k]) with the three col[k] distinct.
  * tau (2 decks; step 3, tau = sigma): both have stem cell 0 equal to card 0; for each
    l = 1..12 the candidate sets C_l(m) = { m(rowSeat(rowAmts(scaleP l m), rho)) : rho } (row
    amounts of the packet whose ranks are l * rank, mod 13) of the two decks meet only in
    card 0 when l = 1 and are disjoint otherwise.
  * lab (1 deck; step 4, label maps): after the row stage, every column is either a full
    rank class of a rank index != 0 or holds only rank indices 0 and 1; for e = 1, 2, 3 the
    per-rank label translation by e at rank index 0 (`tr (eVec e)`) moves the source row of
    stem cell 0 (`c0Row`).
Each deck is a list of seat swaps (`swapsPerm`, as in rank_family.py). The searches are
deterministic (xorshift64). Not a proof by itself: the heavy Lean library checks every
property by kernel `decide!`, one stem evaluation per theorem, so a wrong entry fails the
heavy build.

Usage:
    python3 v10sym_witness.py           # print the decks
    python3 v10sym_witness.py --lean    # write the Lean files and the log
    python3 v10sym_witness.py --check   # CI: fail if a Lean file or the log is stale

--lean writes
  security/DoubleDealSecurity/V10SymLists.lean (affSwaps, affCol, tauSwaps, labSwaps),
  security/DoubleDealSecurityHeavy/V10SymChecks.lean (the decide! theorems),
  v10sym_witness.log (the printed output).
"""
import contextlib
import io
import itertools
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
SEC = HERE.parents[1] / 'security'
sys.path.insert(0, str(HERE.parent / 'v12-covariant'))
sys.path.insert(0, str(REPO / 'tools'))
sys.path.insert(0, str(HERE))
import cell0lib as C  # noqa: E402
from gencheck import parser, emit  # noqa: E402
from rank_family import Rng, ROW3, with_row3, seat_of_c0, swaps_of, fmt_swaps  # noqa: E402

P = C.P
LISTS_OUT = SEC / 'DoubleDealSecurity' / 'V10SymLists.lean'
CHECKS_OUT = SEC / 'DoubleDealSecurityHeavy' / 'V10SymChecks.lean'
LOG_OUT = HERE / 'v10sym_witness.log'
FIX = 'python3 proofs/doubledeal/analysis/v12-primenonswap/v10sym_witness.py --lean'

# ---------------------------------------------------------------- the row stage, c0Row
def lay(m):
    return [[m[4 * c + r] for c in range(13)] for r in range(4)]


def row_turn_vals(row):
    """rowTurnV10 on a row of packet values: sum (13 - j) * rank, rank = v % 13 + 1."""
    return sum((13 - j) * (v % 13 + 1) for j, v in enumerate(row)) % 13


def row_stage(m):
    """(row amounts T, post-row grid) of the packet m: rows 1, 2, 3, 0, each turned by the
    amount read from the previous (already turned) row."""
    g = lay(m)
    T = [0] * 4
    for i in (1, 2, 3, 0):
        T[i] = row_turn_vals(g[(i + 3) % 4])
        g[i] = P.rotl(g[i], T[i])
    return T, g


def c0_row(m):
    """Row of the seat of m holding stem cell 0 (Lean `c0Row`)."""
    s = seat_of_c0(m)
    T, _ = row_stage(m)
    assert s == 4 * (T[s % 4] % 13) + s % 4     # stemPos_zero
    return s % 4


def scale(m, l):
    """Lean `scaleP l m`: packet values with rank = l * rank(m s) (mod 13)."""
    return [((l * (v % 13 + 1)) % 13 + 12) % 13 for v in m]


def cands(m, l):
    T, _ = row_stage(scale(m, l))
    return [m[4 * (T[r] % 13) + r] for r in range(4)]


SOL = P.SUIT_OF_LABEL
LAB = P.LABEL


def card(r, l):
    return 13 * SOL[l] + r


def tr(d):
    """Lean `tr d`: per-rank label translation (rank index r, label l -> l xor d r)."""
    return [card(c % 13, LAB[c // 13] ^ d[c % 13]) for c in range(52)]


def e_vec(e):
    return [e] + [0] * 12


def relabel(s, m):
    return [s[c] for c in m]


# ---------------------------------------------------------------- aff
FOUR = (0, 1, 2, 14)
AX, AY, AX2, AY2 = FOUR
ASW = {AX: AY, AY: AX, AX2: AY2, AY2: AX2}


def aff_base():
    m = list(range(52))
    for k, v in enumerate(FOUR):           # the four cards into row-3 seats 3, 7, 11, 15
        s = 4 * k + 3
        i = m.index(v)
        m[i], m[s] = m[s], m[i]
    return m


def aff_family():
    base = aff_base()
    r3 = [base[s] for s in ROW3]
    rng = Rng(1)
    classes = []
    while len(classes) < 3:
        row = rng.shuffle(r3)
        col = {v: j for j, v in enumerate(row)}
        if (col[AX] + col[AY2] - col[AY] - col[AX2]) % 13:
            continue
        m1 = with_row3(base, row)
        p = seat_of_c0(m1)
        if p % 4 or any(p // 4 == c for c, _ in classes):
            continue
        m2 = with_row3(base, [ASW.get(v, v) for v in row])
        if seat_of_c0(m2) != p:
            continue
        for _ in range(20000):
            row3 = rng.shuffle(r3)
            if any(row3[j] == row[j] and row[j] not in FOUR for j in range(13)):
                continue
            m3 = with_row3(base, row3)
            if seat_of_c0(m3) == p:
                classes.append((p // 4, [m1, m2, m3]))
                break
    return classes


def aff_check(cl):
    assert len({c for c, _ in cl}) == 3
    allm = [m for _, ms in cl for m in ms]
    for m in allm:
        assert sorted(m) == list(range(52))
        assert all(m[s] == allm[0][s] for s in range(52) if s % 4 != 3)
    for c, (m1, m2, m3) in cl:
        for mm in (m1, m2, m3):
            assert C.g(mm) == m1[4 * c]
        for s in ROW3:
            v = m1[s]
            assert m2[s] == ASW.get(v, v)
            if m3[s] == v:
                assert v in FOUR
        col = {m1[s]: j for j, s in enumerate(ROW3)}
        assert (col[AX] + col[AY2] - col[AY] - col[AX2]) % 13 == 0


# ---------------------------------------------------------------- tau
def tau_ok(m1, m2):
    for l in range(1, 13):
        a, b = set(cands(m1, l)), set(cands(m2, l))
        if a & b != ({0} if l == 1 else set()):
            return False
    return True


def tau_pair():
    rng = Rng(7)
    decks = []
    while True:
        m = rng.shuffle(range(52))
        if C.g(m) != 0:
            continue
        for m0 in decks:
            if tau_ok(m0, m):
                return [m0, m]
        decks.append(m)


def tau_check(pair):
    for m in pair:
        assert sorted(m) == list(range(52)) and C.g(m) == 0
    assert tau_ok(*pair)


# ---------------------------------------------------------------- lab
def deck_of_post(gp):
    """The deck whose post-row grid is gp (undo rows 0, 3, 2, 1)."""
    g = [r[:] for r in gp]
    for i in (0, 3, 2, 1):
        g[i] = P.rotl(g[i], -row_turn_vals(g[(i + 3) % 4]))
    m = [0] * 52
    for r in range(4):
        for c in range(13):
            m[4 * c + r] = g[r][c]
    assert row_stage(m)[1] == gp
    return m


def lab_make(rng, mixcol):
    l0 = rng.shuffle(range(4))
    l1 = rng.shuffle(range(4))
    cols = {0: [card(0, l0[0]), card(1, l1[0]), card(1, l1[1]), card(1, l1[2])]}
    cols[mixcol] = rng.shuffle([card(0, l0[1]), card(0, l0[2]), card(0, l0[3]), card(1, l1[3])])
    others = rng.shuffle(range(2, 13))
    k = 0
    for c in range(1, 13):
        if c != mixcol:
            cols[c] = [card(others[k], l) for l in rng.shuffle(range(4))]
            k += 1
    return deck_of_post([[cols[c][r] for c in range(13)] for r in range(4)])


def lab_kills(m, e):
    return c0_row(relabel(tr(e_vec(e)), m)) != c0_row(m)


def lab_deck():
    rng = Rng(3)
    while True:
        m = lab_make(rng, 1 + rng.below(12))
        if all(lab_kills(m, e) for e in (1, 2, 3)):
            return m


def lab_check(m):
    assert sorted(m) == list(range(52))
    _, g = row_stage(m)
    for c in range(13):
        rs = [g[r][c] % 13 for r in range(4)]
        assert (len(set(rs)) == 1 and rs[0] != 0) or set(rs) <= {0, 1}
    assert all(lab_kills(m, e) for e in (1, 2, 3))


# ---------------------------------------------------------------- output
def compute():
    aff = aff_family()
    aff_check(aff)
    tau = tau_pair()
    tau_check(tau)
    lab = lab_deck()
    lab_check(lab)
    return aff, tau, lab


def report(aff, tau, lab):
    print(f'aff: x, y, x2, y2 = {FOUR}')
    for k, (c, ms) in enumerate(aff):
        col = {ms[0][s]: j for j, s in enumerate(ROW3)}
        print(f'  class {k}: stem cell 0 = card {ms[0][4 * c]} at row-0 seat {4 * c} (column {c}); '
              f'row-3 columns of the four in member 0: {[col[v] for v in FOUR]}')
        for i, m in enumerate(ms):
            print(f'    member {i}: row 3 = {[m[s] for s in ROW3]}; {len(swaps_of(m))} swaps')
    print('tau: stem cell 0 = card 0 in both decks')
    for i, m in enumerate(tau):
        print(f'  deck {i}: {m}')
    for l in range(1, 13):
        print(f'  l = {l:2d}: C_l = {sorted(cands(tau[0], l))} / {sorted(cands(tau[1], l))}')
    print(f'lab: deck {lab}')
    _, g = row_stage(lab)
    print('  post-row rank indices by column:', [[g[r][c] % 13 for r in range(4)] for c in range(13)])
    print('  c0Row:', c0_row(lab), '; after tr (eVec e), e = 1, 2, 3:',
          [c0_row(relabel(tr(e_vec(e)), lab)) for e in (1, 2, 3)])


HEADER = '''/-
  GENERATED by proofs/doubledeal/analysis/v12-primenonswap/v10sym_witness.py --lean;
  do not edit (CI: `v10sym_witness.py --check`).
'''


def lists_text(aff, tau, lab):
    aent = []
    for k, (_, ms) in enumerate(aff):
        for i, m in enumerate(ms):
            aent.append(f'    -- class {k}, member {i}\n    {fmt_swaps(swaps_of(m))}')
    tent = [f'    -- deck {i}\n    {fmt_swaps(swaps_of(m))}' for i, m in enumerate(tau)]
    cols = [c for c, _ in aff]
    return HEADER + f'''
  The witness decks of steps 2-4 (`RankAffine`, `TauEq`, `LabelStep`), each a list of seat
  swaps (`swapsPerm`). These lists are data, not trusted: the heavy library checks every
  property by kernel `decide!` (`V10SymChecks.lean`), so a wrong entry fails the heavy build.
-/
namespace DoubleDeal.Security.RankAffine

/-- The seat swaps of the 9 decks of the affine family (entry `3 k + i`). -/
def affSwaps : List (List (Fin 52 × Fin 52)) := [
{(",\n").join(aent)}]

/-- The row-0 column holding stem cell 0 for class `k` (entry `k`). -/
def affCol : List (Fin 13) := {cols}

end DoubleDeal.Security.RankAffine

namespace DoubleDeal.Security.TauEq

/-- The seat swaps of the two decks of step 3 (entry `i`). -/
def tauSwaps : List (List (Fin 52 × Fin 52)) := [
{(",\n").join(tent)}]

end DoubleDeal.Security.TauEq

namespace DoubleDeal.Security.LabelStep

/-- The seat swaps of the deck of step 4. -/
def labSwaps : List (Fin 52 × Fin 52) :=
  {fmt_swaps(swaps_of(lab))}

end DoubleDeal.Security.LabelStep
'''


def checks_text():
    a = ['/-- (PROVED, kernel `decide!`) The structure of the affine family. -/\n'
         'theorem aff_struct : AffStruct := by decide!\n']
    for k in range(3):
        for i in range(3):
            a.append(f'/-- (PROVED, kernel `decide!`) Stem cell 0 of deck ({k}, {i}). -/\n'
                     f'theorem aff_c0_{k}_{i} : affC0Check {k} {i} := by decide!\n')
    acases = ''.join(f'  | ⟨{k}, _⟩, ⟨{i}, _⟩ => aff_c0_{k}_{i}\n' for k in range(3) for i in range(3))
    t = []
    for i in range(2):
        t.append(f'/-- (PROVED, kernel `decide!`) Stem cell 0 of deck {i} is card 0. -/\n'
                 f'theorem tau_g0_{i} : tauG0 {i} := by decide!\n')
    for l in range(1, 13):
        t.append(f'/-- (PROVED, kernel `decide!`) The candidate sets for l = {l}. -/\n'
                 f'theorem tau_cand_{l} : tauCand {l} := by decide!\n')
    lcases = ''.join(f'  | ⟨{l}, _⟩, _ => tau_cand_{l}\n' for l in range(1, 13))
    lb = ['/-- (PROVED, kernel `decide!`) The post-row structure of the deck. -/\n'
          'theorem lab_struct : LabStruct := by decide!\n']
    for e in range(1, 4):
        lb.append(f'/-- (PROVED, kernel `decide!`) `tr (eVec {e})` moves the source row of stem cell 0. -/\n'
                  f'theorem lab_kill_{e} : LabKill {e} := by decide!\n')
    ecases = ''.join(f'  | ⟨{e}, _⟩, _ => lab_kill_{e}\n' for e in range(1, 4))
    return HEADER + f'''
  HEAVY: the finite checks of steps 2-4 by kernel `decide!`: `AffRankChecks`
  (`RankAffine`), `TauChecks` (`TauEq`) and `LabelChecks` (`LabelStep`). One stem
  evaluation per theorem (kernel memory grows with the number of stem evaluations inside
  one `decide!`).
-/
import DoubleDealSecurity.LabelStep

namespace DoubleDeal.Security.RankAffine

{"".join(a)}
/-- (PROVED) Every stem-cell-0 check of the affine family. -/
theorem aff_c0_all : ∀ k i : Fin 3, affC0Check k i
{acases}
/-- (PROVED) The finite checks of step 2. -/
theorem affRankChecks_ok : AffRankChecks := ⟨aff_struct, aff_c0_all⟩

end DoubleDeal.Security.RankAffine

namespace DoubleDeal.Security.TauEq

{"".join(t)}
/-- (PROVED) Every candidate-set check. -/
theorem tau_cand_all : ∀ l : ZMod 13, l ≠ 0 → tauCand l
  | ⟨0, _⟩, h => absurd rfl h
{lcases}
/-- (PROVED) The finite checks of step 3. -/
theorem tauChecks_ok : TauChecks :=
  ⟨fun i => match i with
    | ⟨0, _⟩ => tau_g0_0
    | ⟨1, _⟩ => tau_g0_1, tau_cand_all⟩

end DoubleDeal.Security.TauEq

namespace DoubleDeal.Security.LabelStep

{"".join(lb)}
/-- (PROVED) Every kill check. -/
theorem lab_kill_all : ∀ e : Fin 4, e ≠ 0 → LabKill e
  | ⟨0, _⟩, h => absurd rfl h
{ecases}
/-- (PROVED) The finite checks of step 4. -/
theorem labelChecks_ok : LabelChecks := ⟨lab_struct, lab_kill_all⟩

end DoubleDeal.Security.LabelStep
'''


def main():
    args = cli.parse_args()
    data = compute()
    if not (args.lean or args.check):
        report(*data)
        return 0
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        report(*data)
    rc = 0
    for path, text in ((LISTS_OUT, lists_text(*data)), (CHECKS_OUT, checks_text()),
                       (LOG_OUT, buf.getvalue())):
        rc |= emit(path, text, args.check, fix=FIX)
    return rc


cli = parser(__doc__)
cli.add_argument('--lean', action='store_true',
                 help='write the Lean files and the log (see the module docstring)')

if __name__ == '__main__':
    sys.exit(main())
