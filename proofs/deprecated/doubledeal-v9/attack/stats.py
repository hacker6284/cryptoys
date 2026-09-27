"""Pair statistics on delta = C' o C^-1 (card -> card), and ideal references.

For m' = sigma o m under one key, delta(c) = C'[pos_C(c)] does not depend on the
last round key (a positional Compose), and the whitening Compose makes the
positions of the input pair uniformly random. Ideal cipher: delta is a uniform
non-identity permutation (the identity has probability 1/(52!-1), negligible).
"""
import math, numpy as np
from scipy import stats as SS

AR = np.arange(52)
RANK = AR % 13; SUIT = AR // 13

def delta(C, C2):
    pos = np.argsort(C, axis=1)
    return np.take_along_axis(C2, pos, axis=1)

def pair_stats(D, sigma):
    """per-pair scalars; each has the same ideal law as the one named in REF_OF."""
    s = np.asarray(sigma)
    return {
        "F": (D == AR).sum(1),                       # fixed points (52 - #differing positions)
        "A": (D == s).sum(1),                        # sigma-agreement: E(sm)[o] == s(E(m)[o])
        "RF": (RANK[D] == RANK).sum(1),              # rank kept
        "RA": (RANK[D] == RANK[s]).sum(1),           # rank agrees with sigma
        "SF": (SUIT[D] == SUIT).sum(1),              # suit kept
        "SA": (SUIT[D] == SUIT[s]).sum(1),           # suit agrees with sigma
        "R13": ((RANK[D] - RANK) % 13 == 0).sum(1),  # = RF, kept for (e) naming
    }
REF_OF = {"F": "F", "A": "F", "RF": "RF", "RA": "RF", "SF": "SF", "SA": "SF", "R13": "RF"}

def exact_fixed_point_pmf(n=52, kmax=52):
    return np.array([sum((-1) ** j / math.factorial(j) for j in range(n - k + 1)) / math.factorial(k)
                     for k in range(kmax + 1)])

_REF = {}
def reference(nsim=4_000_000, seed=12345):
    """pmfs of F (exact), RF, SF (simulated) for a uniform random permutation."""
    if _REF: return _REF
    rng = np.random.default_rng(seed)
    h = {"RF": np.zeros(53), "SF": np.zeros(53)}
    for _ in range(nsim // 500_000):
        D = np.argsort(rng.random((500_000, 52)), axis=1)
        h["RF"] += np.bincount((RANK[D] == RANK).sum(1), minlength=53)
        h["SF"] += np.bincount((SUIT[D] == SUIT).sum(1), minlength=53)
    _REF.update({"F": exact_fixed_point_pmf(), "RF": h["RF"] / h["RF"].sum(), "SF": h["SF"] / h["SF"].sum()})
    return _REF

def test_scalar(x, pmf):
    """(p_mean, p_chi2, effect): z-test of the mean and binned chi-square vs the ideal pmf."""
    n = len(x); k = np.arange(len(pmf))
    mu = (k * pmf).sum(); var = ((k - mu) ** 2 * pmf).sum()
    z = (x.mean() - mu) / math.sqrt(var / n)
    p_mean = 2 * SS.norm.sf(abs(z))
    obs = np.bincount(x, minlength=len(pmf))[:len(pmf)]
    exp = pmf * n
    # merge tails until every expected count >= 5
    keep = exp >= 5
    lo, hi = np.argmax(keep), len(keep) - np.argmax(keep[::-1]) - 1
    o = np.concatenate([[obs[:lo + 1].sum()], obs[lo + 1:hi], [obs[hi:].sum()]])
    e = np.concatenate([[exp[:lo + 1].sum()], exp[lo + 1:hi], [exp[hi:].sum()]])
    chi = ((o - e) ** 2 / e).sum(); p_chi = SS.chi2.sf(chi, len(o) - 1)
    return p_mean, p_chi, (x.mean() - mu) / math.sqrt(var)

def joint_chi2(D):
    """chi-square on the 52x52 table (c, delta(c)); rows are multinomial(n, 1/52)."""
    n = len(D)
    t = np.bincount((AR * 52 + D).ravel(), minlength=52 * 52).reshape(52, 52)
    e = n / 52
    chi = ((t - e) ** 2 / e).sum()
    return SS.chi2.sf(chi, 52 * 51), chi

def card_position_chi2(C):
    """single ciphertexts: 52x52 (card, position) table vs uniform."""
    n = len(C)
    t = np.bincount((C * 52 + AR).ravel(), minlength=2704).reshape(52, 52)
    e = n / 52
    chi = ((t - e) ** 2 / e).sum()
    return SS.chi2.sf(chi, 52 * 51), chi
