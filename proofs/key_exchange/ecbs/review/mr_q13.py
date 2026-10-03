#!/usr/bin/env python3
"""mr_q13.py -- Q13: register bands for the projective mixed addition (X:Y:Z) + (x2, y2).

A tiny register machine with the spec's operation model (R4, ecbs_physical.PB):
  mac(d, a, b)      d (+)= +-a*b on the WORKBENCH; b is consumed (its band empties) unless keep_b,
                    in which case b's pegs jump into a fresh TWIN band during the op;
  copy(d, s)        new register (a band);   add(d, s) d += +-s in place (s kept);   free(r).
Bands at an instant = live registers not on the workbench; the workbench holds the destination of the
op in progress, or the latest result until the next op (swap move allowed).
Calibration: the spec's schedule (ecbs_physical.PB.madd) must give 9.  Values are carried as real
GF(3^179) elements and the result is compared with an independent affine addition.
Run: python mr_q13.py"""
import random
from mr_ec import field, Curve

class M:
    def __init__(self, F): self.F = F; self.r = {}; self.wb = None; self.peak = 0; self.muls = 0; self.trace = []
    def _bands(self, extra=0):
        live = [k for k in self.r]
        return len(live) - (1 if self.wb in self.r else 0) + extra
    def _note(self, extra=0, what=""):
        b = self._bands(extra); self.peak = max(self.peak, b); self.trace.append((what, b))
    def load(self, name, val): self.r[name] = val
    def copy(self, d, s, neg=False):
        self.r[d] = -self.r[s] if neg else self.r[s]; self._note(0, f"copy {d}<-{s}")
    def add(self, d, s, neg=False):
        self.r[d] = self.r[d] - self.r[s] if neg else self.r[d] + self.r[s]; self._note(0, f"add {d}+={s}")
    def negate(self, d): self.r[d] = -self.r[d]
    def free(self, d): del self.r[d]; self._note(0, f"free {d}")
    def mac(self, d, a, b, neg=False, keep_b=False):
        """d = new or existing; during the op: d on workbench, b (and its twin) in bands"""
        self.muls += 1
        prod = self.r[a] * self.r[b]
        if d not in self.r: self.r[d] = self.F(0)
        self.wb = d
        self._note(1 if keep_b else 0, f"mac {d} += {a}*{b}{' (twin)' if keep_b else ''}")
        self.r[d] = self.r[d] - prod if neg else self.r[d] + prod
        if not keep_b: del self.r[b]

def spec_schedule(m):
    """transcription of ecbs_physical.PB.madd (same order, same keep/consume choices)"""
    m.copy('v', 'X', neg=True); m.mac('v', 'x2', 'Z', keep_b=True)
    m.copy('u', 'Y', neg=True); m.mac('u', 'y2', 'Z', keep_b=True)
    m.copy('uc', 'u'); m.mac('A0', 'u', 'uc')                 # A = u^2
    m.mac('A', 'Z', 'A0')                                        # A = u^2 Z (u^2 consumed)
    m.copy('vc', 'v'); m.mac('vv', 'v', 'vc')                    # vv = v^2
    m.copy('w', 'v'); m.add('w', 'X', neg=True); m.add('w', 'Z', neg=True)
    m.mac('A', 'vv', 'w', neg=True)                              # A -= vv w
    m.copy('s', 'A', neg=True); m.mac('s', 'vv', 'X')            # s = vv X - A (X consumed)
    m.mac('X3', 'v', 'A')                                        # X3 = v A (A consumed)
    m.mac('vvv', 'vv', 'v'); m.free('vv')                        # v^3 (v consumed)
    m.mac('Y3', 's', 'u'); m.free('s')                           # Y3 = u s (u consumed)
    m.mac('Y3', 'vvv', 'Y', neg=True)                            # Y3 -= v^3 Y
    m.mac('Z3', 'vvv', 'Z'); m.free('vvv')                       # Z3 = v^3 Z
    return ('X3', 'Y3', 'Z3')

def new_schedule(m):
    """F-form (char 3, a2 = -1):  v = x2 Z - X,  u = y2 Z - Y,
       F = u^2 Z + v^2 (v + Z),  Z3 = v^3 Z,  X3 = v F + x2 Z3,  Y3 = -(u F + y2 Z3).
       Same 12 multiplies; X and Y are overwritten in place by v and u."""
    m.negate('X'); m.mac('X', 'x2', 'Z', keep_b=True)                 # X -> v  (Z kept by twin)
    m.negate('Y'); m.mac('Y', 'y2', 'Z', keep_b=True)                 # Y -> u
    v, u = 'X', 'Y'
    m.copy('uc', u); m.mac('G', u, 'uc')                              # G = u^2
    m.mac('P', 'Z', 'G')                                              # P = u^2 Z  (G consumed, Z kept as 'a')
    m.copy('vc', v); m.mac('t', v, 'vc')                              # t = v^2
    m.mac('W', 't', 'Z')                                              # W = v^2 Z  (Z consumed: last use)
    m.mac('P', v, 't')                                                # P += v^3   (t consumed)
    m.add('P', 'W')                                                   # P = F
    m.mac('Z3', v, 'W')                                               # Z3 = v W = v^3 Z (W consumed)
    m.mac('X3', 'P', v)                                               # X3 = F v   (v consumed)
    m.mac('X3', 'x2', 'Z3', keep_b=True)                              # X3 += x2 Z3
    m.mac('Y3', u, 'P', neg=True); m.free(u)                          # Y3 = -u F
    m.mac('Y3', 'y2', 'Z3', neg=True, keep_b=True)                    # Y3 -= y2 Z3
    return ('X3', 'Y3', 'Z3')

def main():
    rnd = random.Random(13); n = 179
    F = field(n, 59); C = Curve(F, 2, 1); q = 3 ** n
    def rand_el(): return F([rnd.randrange(3) for _ in range(n)]) if False else sum((rnd.randrange(3) * F.gen() ** i for i in range(n)), F(0))
    def rand_pt():
        while True:
            x = rand_el(); r = C.rhs(x); y = r ** ((q + 1) // 4)
            if y * y == r: return (x, y)
    for name, sched in (("spec (ecbs_physical.PB.madd)", spec_schedule), ("F-form (this review)", new_schedule)):
        ok = 0; peak = 0; muls = 0
        for trial in range(20):
            P1 = rand_pt(); P2 = rand_pt(); Zr = rand_el()
            m = M(F)
            for k, val in (('x2', P2[0]), ('y2', P2[1]), ('X', P1[0] * Zr), ('Y', P1[1] * Zr), ('Z', Zr)): m.load(k, val)
            X3, Y3, Z3 = sched(m)
            S = C.add(P1, P2)
            live = sorted(m.r)
            ok += (m.r[X3] / m.r[Z3] == S[0] and m.r[Y3] / m.r[Z3] == S[1] and set(live) == {'x2', 'y2', X3, Y3, Z3})
            peak = max(peak, m.peak); muls = m.muls
        print(f"{name:32s}: correct {ok}/20 vs affine chord rule; multiplies {muls}; PEAK BANDS (outside workbench) = {peak}")
        print("    trace (op: bands):", "; ".join(f"{w}: {b}" for w, b in m.trace))

if __name__ == "__main__": main()
