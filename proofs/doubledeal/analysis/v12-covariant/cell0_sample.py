"""How far does the seat-26 argument reach beyond transpositions? MEASUREMENT.

For sampled relabellings s of prime order (the conjecture reduces to prime order
p <= 52: Lean roundBody_covariant_iff_id_of_prime), searches for two decks m1, m2
with g(m1) = g(m2) and g(s.m1) != g(s.m2), g(m) = stem(m)[0]; such a pair rules
out covariance of F = GridCycle o stem for every output relabelling tau (Lean
not_cell0Cov_of_witness + cell0Cov_of_covPair). Random decks, fixed seed. A
failure to find a witness would NOT show covariance; finding one for a sampled s
is a finite fact about that s only, not a statement about its cycle type.

Usage: python3 cell0_sample.py [samples_per_type]   (default 200)
"""
import random
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[1] / 'security' / 'checks'))
import ddport as P  # noqa: E402

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


def witness(s, rng, tries=4000):
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


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 200
    rng = random.Random(20260929)
    types = [(2, k) for k in (1, 2, 3, 6, 13, 26)] + [(3, 1), (3, 5), (3, 17), (5, 1), (5, 10),
                                                        (7, 7), (13, 1), (13, 4), (17, 3),
                                                        (47, 1)]
    print(f'samples per cycle type: {n}; seed 20260929; MEASURED')
    for p, k in types:
        found = sum(witness(perm_of_type(rng, p, k), rng) for _ in range(n))
        print(f'  {k} disjoint {p}-cycles: seat-26 witness found for {found}/{n}')
    vs = sum(witness(P.v10sym(a, x), rng) for a in range(13) for x in range(4) if (a, x) != (0, 0))
    print(f'  control, the 51 nontrivial v10Sym (g commutes with them, so no witness can exist): {vs}/51')


if __name__ == '__main__':
    main()
