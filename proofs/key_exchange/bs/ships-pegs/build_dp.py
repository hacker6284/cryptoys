"""Exact entropy of local sequential BUILD rules for a free fleet on an n x m grid.

A BUILD rule: walk holes in reading order; at every hole not already covered by a
ship, draw an option from a fixed distribution q over
   water | (length L, kind, across/down, bow end)
and re-draw until the option fits (ship inside grid, not overlapping).  So
P(option | hole) = q(option) / q(fitting options).  What fits depends only on
  rl = rows left (including this one)  and  r = free run to the right (incl. this hole).
Computes exactly (float64): Shannon H, collision H2, min-entropy Hmin, E[#3-hole ships],
E[#ships], and the expected dice per hole via a caller-supplied cost function.
"""
import math, numpy as np, itertools, sys

KIND_LEN = {"D": 2, "S": 3, "C": 3, "B": 4, "A": 5}

class Rule:
    """q: dict with keys 'water' and kinds; each kind's mass is split evenly over
    2 orientations x 2 bows unless orient_split given."""
    def __init__(self, name, qwater, qkind, dice_cost=None, p_across=0.5, misfit="reroll"):
        self.name, self.qw, self.qk = name, qwater, dict(qkind)
        self.misfit = misfit            # "reroll": roll again for this hole; "water": leave it water
        self.pa = p_across
        self.dice_cost = dice_cost      # function(fitinfo) -> expected dice per decision, optional

    def local(self, r, rl):
        """Return list of (prob, kind, orient) for fitting options (bow split handled
        as 1 extra bit of entropy, bows always both fit)."""
        opts = [(self.qw, None, None)]
        for K, L in KIND_LEN.items():
            qk = self.qk.get(K, 0.0)
            if qk == 0: continue
            if L <= r:  opts.append((qk * self.pa, K, "H"))
            if L <= rl: opts.append((qk * (1 - self.pa), K, "V"))
        Z = sum(o[0] for o in opts)
        if self.misfit == "water":
            T = self.qw + 4 * sum(self.qk.values()) / 4          # total mass of all options
            ship = [(p / T, K, o) for p, K, o in opts[1:]]
            return [(1 - sum(p for p, _, _ in ship), None, None)] + ship, 1.0
        return [(p / Z, K, o) for p, K, o in opts], Z

def analyse(rule, n=10, m=10, want=("H", "H2", "Hmin", "n3", "ships")):
    base = 5
    size = base ** m
    digits = np.array(list(itertools.product(range(base), repeat=m)), dtype=np.int8) if m <= 6 else None
    # compute digit arrays lazily without the full product for m=10
    idx = np.arange(size, dtype=np.int64)
    dig = []
    for k in range(m):
        dig.append(((idx // base ** (m - 1 - k)) % base).astype(np.int8))
    del idx
    # free run length r(s, j): consecutive zero digits starting at j (cap 5)
    run = [None] * m
    nxt = np.zeros(size, dtype=np.int8)
    for j in range(m - 1, -1, -1):
        cur = np.where(dig[j] == 0, np.minimum(nxt + 1, 5), 0).astype(np.int8)
        run[j] = cur; nxt = cur
    # tables per (rl, r): probabilities per option class
    mass = np.zeros(size); mass[0] = 1.0
    sq = np.zeros(size); sq[0] = 1.0            # sum of P^2 (collision)
    lg = np.full(size, -np.inf); lg[0] = 0.0      # max log2 P
    H = 0.0; n3 = 0.0; ships = 0.0; dice = 0.0
    for i in range(n):
        rl = n - i
        pend = {0: (mass, sq, lg)}
        def get(k):
            if k not in pend:
                pend[k] = (np.zeros(size), np.zeros(size), np.full(size, -np.inf))
            return pend[k]
        for j in range(m):
            M, Q, G = pend.pop(j)
            Mn, Qn, Gn = get(j + 1)
            d = dig[j]
            # covered from above: deterministic
            cov = d > 0
            if cov.any():
                src = np.nonzero(cov)[0]
                dst = src - base ** (m - 1 - j)
                Mn[dst] += M[src]; Qn[dst] += Q[src]; Gn[dst] = np.maximum(Gn[dst], G[src])
            free = np.nonzero((d == 0) & ((M > 0) | (G > -np.inf)))[0]
            if len(free) == 0: continue
            rr = run[j][free]
            for r in range(1, 6):
                sel = free[rr == r]
                if len(sel) == 0: continue
                opts, Z = rule.local(min(r, m - j), rl)
                Ms, Qs, Gs = M[sel], Q[sel], G[sel]
                # local entropy: options + bow bit for ships
                h = 0.0
                for p, K, o in opts:
                    if p > 0:
                        h += -p * math.log2(p) + (p if K else 0.0)   # bow: 1 bit
                H += h * Ms.sum()
                if rule.dice_cost: dice += rule.dice_cost(opts, Z) * Ms.sum()
                for p, K, o in opts:
                    if p == 0: continue
                    if K is None:
                        tgtM, tgtQ, tgtG = Mn, Qn, Gn; dst = sel; pb = p
                    else:
                        L = KIND_LEN[K]; pb = p / 2    # each bow
                        ships += p * Ms.sum()
                        if L == 3: n3 += p * Ms.sum()
                        if o == "V":
                            tgtM, tgtQ, tgtG = Mn, Qn, Gn
                            dst = sel + (L - 1) * base ** (m - 1 - j)
                        else:
                            tgtM, tgtQ, tgtG = get(j + L); dst = sel
                    # two bows: each prob pb; mass gets p total, sq gets 2*pb^2, max gets pb
                    tgtM[dst] += Ms * p
                    tgtQ[dst] += Qs * (p * p if K is None else 2 * pb * pb)
                    tgtG[dst] = np.maximum(tgtG[dst], Gs + math.log2(pb))
        mass, sq, lg = pend.pop(m)
    assert abs(mass[0] - 1) < 1e-9 and abs(mass.sum() - 1) < 1e-9, (mass[0], mass.sum())
    return {"rule": rule.name, "H": H, "H2": -math.log2(sq[0]), "Hmin": -lg[0],
            "n3": n3, "ships": ships, "cells": m * n + n3, "dice": dice}

if __name__ == "__main__":
    r = Rule("test", 1, {"D": 1, "S": 1, "C": 1, "B": 1, "A": 1})
    for g in [(2, 2), (2, 3), (3, 3)]:
        print(g, analyse(r, *g))
