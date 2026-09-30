"""Chosen relations sigma (card relabellings; a positional swap of two cards is a transposition)."""
import sys
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[3] / 'doubledeal/security/checks'))
import ddport as P
AR = np.arange(52); RANK = AR % 13; SUIT = AR // 13

def v9sym(a, b): return np.array(P.v9sym(a, b))

def transposition(x, y):
    s = AR.copy(); s[x], s[y] = y, x; return s

def relations(seed=2026):
    rng = np.random.default_rng(seed)
    R = {}
    for a in range(13):
        for b in range(4):
            if (a, b) != (0, 0): R[f"v9Sym({a},{b})"] = v9sym(a, b)
    # rank-preserving: permute suits within each rank (the v8 break was rank-preserving)
    R["rankpres:swap C<->H"] = np.array([13 * [1, 0, 2, 3][c // 13] + c % 13 for c in AR])
    for i in range(3):
        s = AR.copy()
        for r in range(13): s[[13 * q + r for q in range(4)]] = [13 * q + r for q in rng.permutation(4)]
        R[f"rankpres:random{i}"] = s
    # suit-preserving: permute ranks within each suit
    R["suitpres:rank+1"] = np.array([13 * (c // 13) + (c % 13 + 1) % 13 for c in AR])
    for i in range(3):
        s = AR.copy()
        for q in range(4): s[13 * q:13 * q + 13] = 13 * q + rng.permutation(13)
        R[f"suitpres:random{i}"] = s
    R["swap A♣A♥ (same rank)"] = transposition(0, 13)
    R["swap A♣2♣ (same suit, adjacent)"] = transposition(0, 1)
    R["swap A♣9♠"] = transposition(0, 34)
    R["swap K♣K♦"] = transposition(12, 51)
    return R
