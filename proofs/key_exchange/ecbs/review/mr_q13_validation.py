#!/usr/bin/env python3
"""mr_q13_validation.py -- Q13 for the receiver's trace check (spec 5.2 step 2.2; ecbs_physical.PB.trace_check).
Same register machine as mr_q13.py plus cube(d, s) (comb cube: new result on the workbench, input consumed).
(a) transcription of the spec schedule (calibration: must give 8);
(b) a reordered schedule: in every chord-rule addition the second point's y (a Frobenius copy, or B's y)
    is formed only AFTER the inversion of the run, so it is not live during Itoh-Tsujii.
Both are run on honest points (must accept) and on B + T5 (must reject), n = 179, real field values.
Run: python mr_q13_validation.py"""
import random
from mr_ec import field, Curve
from mr_q13 import M

class MV(M):
    def cube(self, d, s):
        self.muls += 0
        v = self.r[s] ** 3
        self.r[d] = self.F(0); self.wb = d; self._note(0, f"cube {d}<-{s}")
        self.r[d] = v; del self.r[s]
    def cube_times(self, d, s, m):          # d = s^(3^m), s kept (copy, then m cubes)
        self.copy(d + "_c0", s); cur = d + "_c0"
        for i in range(m):
            nxt = d if i == m - 1 else f"{d}_c{i+1}"
            self.cube(nxt, cur); cur = nxt
        if m == 0: self.r[d] = self.r.pop(cur)
    def one(self, d): self.r[d] = self.r[d] + 1

def inv(m, d, x, n):
    """spec R6 (Itoh-Tsujii with the halving ladder); x kept; result in d."""
    m.copy('e', x); k = 1
    for b in bin(n - 1)[3:]:
        m.cube_times('t', 'e', k); m.mac('ne', 'e', 't'); m.free('e'); m.r['e'] = m.r.pop('ne'); m.wb = 'e'; k *= 2
        if b == '1':
            m.cube('t', 'e'); m.mac('e', x, 't'); k += 1
    m.cube(d, 'e')
    m.copy('c', x); m.mac('nrm', d, 'c'); assert m.r['nrm'] == 1 or m.r['nrm'] == -1
    if m.r['nrm'] == -1: m.negate(d)
    m.free('nrm')

def aadd_spec(m, x1, y1, x2, y2, out, n):
    """(x1,y1) kept, (x2,y2) consumed (ecbs_physical.PB.aadd)"""
    m.add(x2, x1, neg=True); dx = x2
    if m.r[dx] == 0: raise ArithmeticError
    inv(m, 'di', dx, n)
    m.add(y2, y1, neg=True); dy = y2
    m.mac('lam', 'di', dy); m.free('di')
    m.copy('lc', 'lam'); m.mac(out[0], 'lam', 'lc'); m.one(out[0]); m.add(out[0], x1); m.add(out[0], dx, neg=True); m.free(dx)
    m.copy('tt', x1); m.add('tt', out[0], neg=True); m.mac(out[1], 'lam', 'tt'); m.free('lam'); m.add(out[1], y1, neg=True)

def trace_spec(m, n):
    m.copy('Sx', 'bx'); m.copy('Sy', 'by'); k = 1
    for b in bin(n)[3:]:
        m.cube_times('tx', 'Sx', k); m.cube_times('ty', 'Sy', k)
        aadd_spec(m, 'Sx', 'Sy', 'tx', 'ty', ('nx', 'ny'), n)
        m.free('Sx'); m.free('Sy'); m.r['Sx'] = m.r.pop('nx'); m.r['Sy'] = m.r.pop('ny'); k *= 2
        if b == '1':
            m.copy('a0', 'Sx'); m.cube('tx', 'a0'); m.copy('a1', 'Sy'); m.cube('ty', 'a1')
            if k + 1 == n:
                ok = m.r['tx'] == m.r['bx'] and m.r['ty'] == -m.r['by']
                for r in ('tx', 'ty', 'Sx', 'Sy'): m.free(r)
                return ok
            m.free('Sx'); m.free('Sy')
            m.copy('x2c', 'bx'); m.copy('y2c', 'by')
            aadd_spec(m, 'tx', 'ty', 'x2c', 'y2c', ('nx', 'ny'), n)
            m.free('tx'); m.free('ty'); m.r['Sx'] = m.r.pop('nx'); m.r['Sy'] = m.r.pop('ny'); k += 1

def aadd_lazy(m, x1, y1, x2, make_y2, out, n):
    """(x1,y1) kept; x2 consumed; y2 is MADE after the inversion by make_y2(name)."""
    m.add(x2, x1, neg=True); dx = x2
    if m.r[dx] == 0: raise ArithmeticError
    inv(m, 'di', dx, n)
    make_y2('dy'); m.add('dy', y1, neg=True)
    m.mac('lam', 'di', 'dy'); m.free('di')
    m.copy('lc', 'lam'); m.mac(out[0], 'lam', 'lc'); m.one(out[0]); m.add(out[0], x1); m.add(out[0], dx, neg=True); m.free(dx)
    m.copy('tt', x1); m.add('tt', out[0], neg=True); m.mac(out[1], 'lam', 'tt'); m.free('lam'); m.add(out[1], y1, neg=True)

def trace_lazy(m, n):
    m.copy('Sx', 'bx'); m.copy('Sy', 'by'); k = 1
    for b in bin(n)[3:]:
        m.cube_times('tx', 'Sx', k)
        kk = k
        aadd_lazy(m, 'Sx', 'Sy', 'tx', lambda d, kk=kk: m.cube_times(d, 'Sy', kk), ('nx', 'ny'), n)
        m.free('Sx'); m.free('Sy'); m.r['Sx'] = m.r.pop('nx'); m.r['Sy'] = m.r.pop('ny'); k *= 2
        if b == '1':
            m.copy('a0', 'Sx'); m.cube('tx', 'a0')
            if k + 1 == n:
                m.copy('a1', 'Sy'); m.cube('ty', 'a1')
                ok = m.r['tx'] == m.r['bx'] and m.r['ty'] == -m.r['by']
                for r in ('tx', 'ty', 'Sx', 'Sy'): m.free(r)
                return ok
            m.free('Sx')
            m.copy('x2c', 'bx')
            # first point is tau(S) = (tx, ty); ty is made now from Sy (Sy still live), second point is B
            m.copy('a1', 'Sy'); m.cube('ty', 'a1'); m.free('Sy')
            aadd_lazy(m, 'tx', 'ty', 'x2c', lambda d: m.copy(d, 'by'), ('nx', 'ny'), n)
            m.free('tx'); m.free('ty'); m.r['Sx'] = m.r.pop('nx'); m.r['Sy'] = m.r.pop('ny'); k += 1

def trace_lazy2(m, n):
    """as trace_lazy, but in the +1 step keep Sy (not ty) through the inversion: ty = tau(Sy) is made
       after the inversion as well (the first point's y is needed only after the inversion too)."""
    m.copy('Sx', 'bx'); m.copy('Sy', 'by'); k = 1
    for b in bin(n)[3:]:
        m.cube_times('tx', 'Sx', k)
        kk = k
        aadd_lazy(m, 'Sx', 'Sy', 'tx', lambda d, kk=kk: m.cube_times(d, 'Sy', kk), ('nx', 'ny'), n)
        m.free('Sx'); m.free('Sy'); m.r['Sx'] = m.r.pop('nx'); m.r['Sy'] = m.r.pop('ny'); k *= 2
        if b == '1':
            m.copy('a0', 'Sx'); m.cube('tx', 'a0')
            if k + 1 == n:
                m.copy('a1', 'Sy'); m.cube('ty', 'a1')
                ok = m.r['tx'] == m.r['bx'] and m.r['ty'] == -m.r['by']
                for r in ('tx', 'ty', 'Sx', 'Sy'): m.free(r)
                return ok
            m.free('Sx')
            # B's x minus tx, in a fresh copy of bx
            m.copy('dx', 'bx'); m.add('dx', 'tx', neg=True)
            if m.r['dx'] == 0: raise ArithmeticError
            inv(m, 'di', 'dx', n)
            m.cube('ty', 'Sy')                                    # ty = tau(Sy), Sy consumed (last use)
            m.copy('dy', 'by'); m.add('dy', 'ty', neg=True)
            m.mac('lam', 'di', 'dy'); m.free('di')
            m.copy('lc', 'lam'); m.mac('nx', 'lam', 'lc'); m.one('nx'); m.add('nx', 'tx'); m.add('nx', 'dx', neg=True); m.free('dx')
            m.copy('tt', 'tx'); m.add('tt', 'nx', neg=True); m.mac('ny', 'lam', 'tt'); m.free('lam'); m.add('ny', 'ty', neg=True)
            m.free('tx'); m.free('ty'); m.r['Sx'] = m.r.pop('nx'); m.r['Sy'] = m.r.pop('ny'); k += 1

def main():
    rnd = random.Random(7)
    for n, k in ((23, 15), (59, 39), (179, 59)):
        F = field(n, k); C = Curve(F, 2, 1); q = 3 ** n
        V = lambda n_: None
        # honest point: random point times 5; bad: honest + (1,1) (a rational 5-torsion point)
        def rand_pt():
            while True:
                x = sum((rnd.randrange(3) * F.gen() ** i for i in range(n)), F(0)); r = C.rhs(x); y = r ** ((q + 1) // 4)
                if y * y == r: return (x, y)
        T5 = (F(1), F(1)); assert C.on(T5)
        for name, sched in (("spec", trace_spec), ("lazy-y", trace_lazy), ("lazy-y, both points", trace_lazy2)):
            res = []; peak = 0
            for kind in ("honest", "honest", "B+T5"):
                B = C.mul(5, rand_pt())
                if kind == "B+T5": B = C.add(B, T5)
                m = MV(F); m.load('bx', B[0]); m.load('by', B[1])
                try: ok = sched(m, n)
                except ArithmeticError: ok = False
                res.append(ok); peak = max(peak, m.peak)
                assert set(m.r) == {'bx', 'by'}, sorted(m.r)
            print(f"n = {n:3d} {name:22s}: accept(honest, honest, B+T5) = {res}; PEAK BANDS = {peak}", flush=True)

if __name__ == "__main__": main()
