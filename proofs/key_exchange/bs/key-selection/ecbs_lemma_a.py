"""Why the fleet-based keys were not carried over to ECBS (key-selection NOTES §4).

ECBS Lemma A with digit differences D = 2 on positions 0..npos-1: B = sum 2*3^(p/2); the key map
is certified injective mod l when B^2 < l.  A free-fleet page needs up to 134 positions (133 cells +
marker); a ships+pegs page up to 234.  The curve orders l and field degrees n are copied from the
ECBS SPEC tier table (primitives/key_exchange/ecbs/SPEC.md §1); this script does not read ECBS files."""
ECBS = {  # tier: (n, l)
    "Serious": (179, 5078489869724426155952648514707704116694985077007329814177591439556413097455105423907),
    "Hobby": (59, 2826077218347794449447657747),
}

def lemma_a_ok(npos, ell):
    """ECBS Lemma A with D=2 on positions 0..npos-1: B = sum 2*3^(p/2); need B^2 < ell.
    Exact: B = A + C*sqrt3, B^2 = A^2 + 3C^2 + 2AC sqrt3 < ell."""
    A = sum(2 * 3 ** (p // 2) for p in range(0, npos, 2))
    C = sum(2 * 3 ** (p // 2) for p in range(1, npos, 2))
    # (A^2+3C^2 - ell) + 2AC*sqrt3 < 0
    X = A * A + 3 * C * C - ell; Y = 2 * A * C
    return X < 0 and X * X > 3 * Y * Y

if __name__ == "__main__":
    for tier, (nn, ell) in ECBS.items():
        best = max(k for k in range(1, 300) if lemma_a_ok(k, ell))
        for key, need in (("free-fleet page", 134), ("ships+pegs page", 234)):
            ok = need <= min(best, nn)
            print(f"== ECBS {tier}: n={nn}, Lemma A (D=2) holds for up to {best} positions; "
                  f"a {key} needs up to {need}: {'OK, injective mod l' if ok else 'NOT certified'}")
