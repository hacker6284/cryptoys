"""Chosen relations sigma (card relabellings; a positional swap of two cards is a transposition)."""
import numpy as np
AR = np.arange(52); RANK = AR % 13; SUIT = AR // 13

def v9sym(a, b):
    r0, su = AR % 13, AR // 13
    wrap = np.where(r0 + a < 13, 0, 13)
    return 13 * ((su + b + 16 - a + wrap) % 4) + (r0 + a) % 13

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
