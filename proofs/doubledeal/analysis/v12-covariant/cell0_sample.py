"""How far does the seat-26 argument reach beyond transpositions? MEASUREMENT.

Evidence (sampled, not a proof) for the hypothesis `hcell` of the Lean reduction
`CovariantNarrow.roundBody_covariant_iff_id_of_cell0_prime`: every σ of prime order
p <= 52 with `Cell0Cov σ τ` for some τ is a v10Sym. That hypothesis is a
SUFFICIENT condition for the conjecture, not known to be true or necessary.

For sampled relabellings s of prime order, searches for two decks m1, m2 with
g(m1) = g(m2) and g(s.m1) != g(s.m2), g(m) = stem(m)[0]; such a pair shows that
no τ satisfies `Cell0Cov s τ` (Lean `not_cell0Cov_of_witness`), hence (Lean
`cell0Cov_of_covPair`) that s is not covariant for F = GridCycle o stem. Random
decks, fixed seed, deterministic. A failure to find a witness would NOT show
covariance; a witness for a sampled s is a finite fact about that s only, not a
statement about its cycle type.

Usage:
    python3 cell0_sample.py            # print (defaults: 100 samples per type)
    python3 cell0_sample.py --log      # write cell0_sample.log (defaults only)
    python3 cell0_sample.py --check    # CI: fail if cell0_sample.log is stale
    python3 cell0_sample.py --samples N  # other sample sizes (print only)
"""
import contextlib
import io
import random
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
sys.path.insert(0, str(HERE.parents[1] / 'security' / 'checks'))
sys.path.insert(0, str(REPO / 'tools'))
import ddport as P  # noqa: E402
from gencheck import parser, emit  # noqa: E402

SAMPLES = 100   # default samples per cycle type (the committed log uses the defaults)
TRIES = 4000    # random decks per sampled relabelling
SEED = 20260929
LOG_OUT = HERE / 'cell0_sample.log'

V = 12


def g(m):
    return P.stem(m, V)[0]


def perm_of_type(rng, p, k):
    """k disjoint p-cycles on random cards."""
    cards = rng.sample(range(52), p * k)
    s = list(range(52))
    for c in range(k):
        cyc = cards[c * p:(c + 1) * p]
        for i in range(p):
            s[cyc[i]] = cyc[(i + 1) % p]
    return s


def witness(s, rng, tries=TRIES):
    by = {}
    for _ in range(tries):
        d = list(range(52))
        rng.shuffle(d)
        key = g(d)
        img = g([s[x] for x in d])
        if key in by and by[key] != img:
            return True
        by.setdefault(key, img)
    return False


def report(n):
    rng = random.Random(SEED)
    types = [(2, k) for k in (1, 2, 3, 6, 13, 26)] + [(3, 1), (3, 5), (3, 17), (5, 1), (5, 10),
                                                        (7, 7), (13, 1), (13, 4), (17, 3),
                                                        (47, 1)]
    print(f'invocation: python3 cell0_sample.py --samples {n} '
          f'(default {SAMPLES}); {TRIES} random decks per sigma; seed {SEED}; MEASURED')
    total = found_all = 0
    for p, k in types:
        found = sum(witness(perm_of_type(rng, p, k), rng) for _ in range(n))
        total += n
        found_all += found
        print(f'  {k} disjoint {p}-cycles: seat-26 witness found for {found}/{n}')
    print(f'  all sampled prime-order sigma: {found_all}/{total}')
    vs = sum(witness(P.v10sym(a, x), rng) for a in range(13) for x in range(4) if (a, x) != (0, 0))
    print(f'  control, the 51 nontrivial v10Sym (g commutes with them, so no witness can exist): {vs}/51')


def main():
    args = cli.parse_args()
    if args.log or args.check:
        if args.samples != SAMPLES:
            raise SystemExit('--log / --check use the defaults only')
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf):
            report(SAMPLES)
        return emit(LOG_OUT, buf.getvalue(), args.check,
                    fix='python3 proofs/doubledeal/analysis/v12-covariant/cell0_sample.py --log')
    report(args.samples)
    return 0


cli = parser(__doc__)
cli.add_argument('--log', action='store_true', help='write cell0_sample.log (defaults only)')
cli.add_argument('--samples', type=int, default=SAMPLES, help='samples per cycle type')

if __name__ == '__main__':
    sys.exit(main())
