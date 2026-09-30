"""Generate the M9 decoder certificate `../lean/MegaDreifach/M9Cert.lean`.

Stdlib only.  Reuses the Python E_m of `m9_search.py` (tables read from `Em.lean`).

At the canonical grip `gripId` (rotation 0), the first card `a` has net
`N0 a = net2 gripId a` and the second card `b` at intermediate grip `rotAt s1` has
net `conj s1 (N0 b)` (`G2CovRead.net2_cov`).  The 162,240 items `(a, s1, b)` have
products `P = compose (conj s1 (N0 b)) (N0 a)`.  The certificate is a decision tree
on the 50 slot codes of `P` (corner slot `t < 20`: `3 cp + co`; edge slot `t - 20`:
`60 + 2 ep + eo`, as `m9_search.code`) whose leaves name the first card `a`, or an
ambiguity group of items that share one product with different first cards.  Lean
re-checks every item against the tree (`M9Dec*.lean`, kernel `decide!`), so the tree
is untrusted data: a wrong tree fails the build, it cannot prove a false statement.

Each ambiguity-group entry also records the two `W`-slots the second card's read
sees (corner read for odd deal positions, edge read for even ones); Lean recomputes
them and checks that entries with different first cards read different slots.

  python3 m9_cert.py          # write M9Cert.lean
  python3 m9_cert.py --check  # fail if M9Cert.lean differs from a fresh generation
"""
import sys
from collections import defaultdict
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import m9_search as M  # noqa: E402

OUT = HERE.parent / "lean" / "MegaDreifach" / "M9Cert.lean"
DENSE = 60          # nodes with more kids than this are laid out densely
DENSE_SLOTS = 120   # entry slots of a dense node, indexed by slot-code value v < 120
CHUNK = 630         # words per Nat literal (keeps literals near 16k bits)
LOGBITS = 16

# Certificate layout.  Each constant has a twin, named in backquotes, in the
# "Certificate layout" section of `../lean/MegaDreifach/M9Canon.lean`; keep them in step.
WORD = 26           # bits per tree word (`wordBits`; mask `wordMask` = 2^26 - 1)
VAL_SHIFT = 19      # entry = v << VAL_SHIFT | leaf << LEAF_BIT | payload (`valShift`)
LEAF_BIT = 18       # leaf flag bit; payload < 2^LEAF_BIT (`leafBit`, `payMod`)
DENSE_TAG = 1000    # count word of a dense node (`denseTag`)
AMB_BASE = 100      # leaf labels >= AMB_BASE name ambiguity group label - AMB_BASE (`ambBase`)
FIELD = 100         # two-digit decimal fields of ambiguity entries (`fieldB`)
# Bits per packed identity-grip net entry (`cpBits` … `eoBits`; `G2Cov.posN` widths).
CP_BITS, CO_BITS, EP_BITS, EO_BITS = 5, 2, 5, 1


def ilog2_fix(n):
    """floor(2^LOGBITS * log2 n), exact integer arithmetic (no floats)."""
    big = n ** (1 << LOGBITS)
    return big.bit_length() - 1


LOG = [0] + [ilog2_fix(n) for n in range(1, 53)]


def items():
    R = M.ROTS
    nets = [[M.g2_step((M.ID, o), c, 1)[0] for c in range(52)] for o in R]
    byP = defaultdict(list)
    for a in range(52):
        A = nets[0][a]
        for s1 in range(60):
            for b in range(52):
                byP[M.code(M.compose(nets[s1][b], A))].append((a, s1, b))
    return nets, byP


def wslots(nets, a, s1, b):
    """(corner W-slot, edge W-slot) read by the second card (`g1` = held-turned N0 a)."""
    g1, _, phys, noon = M.held_turn(nets[0][a], M.ROTS[s1], b)
    _, sc = M.read_slot(phys, noon, 1)
    _, se = M.read_slot(phys, noon, 2)
    return g1[0][sc], g1[2][se]


def build_tree(byP):
    weight = defaultdict(int)
    for P, v in byP.items():
        for a, _, _ in v:
            weight[(a, P)] += 1
    dedup = sorted(weight)
    amb = []

    def build(S):
        labs = {a for a, _ in S}
        if len(labs) == 1:
            return ("L", S[0][0])
        Ps = {P for _, P in S}
        if len(Ps) == 1:
            (P,) = Ps
            amb.append(sorted(byP[P]))
            return ("L", AMB_BASE + len(amb) - 1)
        best = None
        for t in range(50):
            parts = defaultdict(lambda: [0, set()])
            for a, P in S:
                p = parts[P[t]]
                p[0] += weight[(a, P)]
                p[1].add(a)
            if len(parts) == 1:
                continue
            key = (sum(w * LOG[len(l)] for w, l in parts.values()), t)
            if best is None or key < best:
                best = key
        t = best[1]
        parts = defaultdict(list)
        for it in S:
            parts[it[1][t]].append(it)
        return ("N", t, [(v, build(parts[v])) for v in sorted(parts)])

    return build(dedup), amb


def layout(tree):
    words = []

    def lay(n):
        off = len(words)
        t, kids = n[1], n[2]
        dense = len(kids) > DENSE
        words.append(t)
        words.append(DENSE_TAG if dense else len(kids))
        base = len(words)
        words.extend([0] * (DENSE_SLOTS if dense else len(kids)))
        ents = []
        for v, c in kids:
            if c[0] == "L":
                assert 0 <= c[1] < (1 << LEAF_BIT)
                e = (v << VAL_SHIFT) | (1 << LEAF_BIT) | c[1]
            else:
                co = lay(c)
                assert 0 < co < (1 << LEAF_BIT)
                e = (v << VAL_SHIFT) | co
            ents.append((v, e))
        for j, (v, e) in enumerate(ents):
            words[base + (v if dense else j)] = e
        return off

    lay(tree)
    return words


def pack(ws, bits):
    n = 0
    for k, w in enumerate(ws):
        assert 0 <= w < (1 << bits)
        n |= w << (bits * k)
    return n


def generate():
    sys.set_int_max_str_digits(0)
    sys.setrecursionlimit(10000)
    nets, byP = items()
    tree, amb = build_tree(byP)
    words = layout(tree)
    N0 = nets[0]
    out = ["/-\n  GENERATED by `proofs/megadreifach/m9/m9_cert.py` -- do not edit.\n"
           "  Untrusted decoder data for the M9 canonical-grip check; see `M9Canon.lean`.\n"
           f"  {len(words)} tree words, {len(amb)} ambiguity groups "
           f"({sum(map(len, amb))} entries).\n-/",
           "namespace MegaDreifach.M9Cert"]
    rows = lambda i, bits: pack([v for n in N0 for v in n[i]], bits)
    out.append(f"def n0CpN : Nat := {rows(0, CP_BITS)}")
    out.append(f"def n0CoN : Nat := {rows(1, CO_BITS)}")
    out.append(f"def n0EpN : Nat := {rows(2, EP_BITS)}")
    out.append(f"def n0EoN : Nat := {rows(3, EO_BITS)}")
    chunks = [words[i:i + CHUNK] for i in range(0, len(words), CHUNK)]
    for i, ch in enumerate(chunks):
        out.append(f"def m9t{i} : Nat := {pack(ch, WORD)}")
    out.append("/-- All tree words, `WORD` bits each. -/\ndef m9big : Nat :=\n  " + " +\n  ".join(
        f"Nat.shiftLeft m9t{i} {WORD * CHUNK * i}" for i in range(len(chunks))))
    ents = []
    for g in amb:
        es = []
        for a, s1, b in g:
            w1, w0 = wslots(nets, a, s1, b)
            assert max(a, s1, b, w1, w0) < FIELD
            es.append(str((((a * FIELD + s1) * FIELD + b) * FIELD + w1) * FIELD + w0))
        ents.append("[" + ", ".join(es) + "]")
    out.append("/-- Ambiguity groups: entries "
               "`a·10⁸ + s1·10⁶ + b·10⁴ + w1·100 + w0`. -/\n"
               "def ambG : List (List Nat) := [\n  "
               + ",\n  ".join(ents) + "]")
    out.append("end MegaDreifach.M9Cert")
    pairs = sum(1 for g in amb for x in g for y in g if x[0] < y[0])
    stats = dict(items=sum(map(len, byP.values())), products=len(byP), words=len(words),
                 chunks=len(chunks), amb=len(amb), amb_entries=sum(map(len, amb)),
                 amb_pairs=pairs)
    # Identity-grip counts behind m9_search's 24,300 = 60 x 405 candidates (a < c).
    assert (stats["items"], stats["products"], stats["amb"], stats["amb_entries"], pairs) == (
        162240, 99720, 111, 384, 405), stats
    return "\n\n".join(out) + "\n", stats


def main():
    text, stats = generate()
    print("M9 certificate:", stats)
    if "--check" in sys.argv:
        ok = OUT.exists() and OUT.read_text() == text
        print("M9Cert.lean up to date:", ok)
        return 0 if ok else 1
    OUT.write_text(text)
    print("wrote", OUT)
    return 0


if __name__ == "__main__":
    sys.exit(main())
