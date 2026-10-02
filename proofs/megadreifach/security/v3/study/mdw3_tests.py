"""Tests for the single-pass rules of mdw3_lib (scratch only).  Reuses the work functions of mdw_tests
(D2, D3, merge) and mdw_d1big (D1 + D1', same samples) with the dm of mdw3_lib patched in.

Parts:
  bound                       element-level support of the last-two-swap quotient of the bare single pass
  d2scan N KIND:M ...         D2 (secret uniform h, cards 51,52 swapped), N pairs each
  d2 KIND M N SEED0           D2
  d3 KIND M N SEED0           telescoping at 51/52, 4 pair classes x IV/uniform, N each
  merge KIND M N SEED0        adjacent swaps at mdw_tests.POS x IV/uniform, N each
  big KIND M N SEED0          D1 left + D1' right on the same samples (mdw_d1big statistics)
  diag KIND M N SEED0         D1 left: coincidence of the pieces named by the last two steps
"""
import math
import random
import sys
import time
from multiprocessing import Pool

import mdfix_lib as L
import mdfix_dist as M
import mdw_lib as W
import mdw_tests as TT
import mdw_d1big as B
import mdw3_lib as T

comp, inv = L.compose_st, L.inv_st
_em0, _mk0, _mkB = W.em, TT.mk, B.mk


def em_any(kind, t, h, deal, rec=None, stop=52, rounds=True):
    if kind.startswith('S'):
        return T.em3(kind, t, h, deal, rec=rec, stop=stop, rounds=rounds)
    return _em0(kind, t, h, deal, rec, stop, rounds)


def mk_any(kind, t):
    return T.make_dm(kind, t) if kind.startswith('S') else _mk0(kind, t)


W.em = em_any
TT.mk = mk_any
B.mk = mk_any
TT.cards_only = lambda kind, h, d: em_any(kind, 0, h, d, rounds=False)


def bound():
    G = L.eng.GROUP_ORDER
    print(f'|G| = {G} = 2^{math.log2(G):.2f}')
    print('Bare single pass, cards 51 and 52 swapped: steps 1..50 are identical, so W = T.P and W\'\' = T\'\'.P with the same')
    print('prefix P, and Q = W^-1 W\'\' = P^-1 (T^-1 T\'\') P is a conjugate of T^-1 T\'\', a word of at most 4s face turns (s = turns')
    print('per step; 48 generators).  Element-level support (NOT a bound on conjugacy-invariant statistics, which see only the')
    print('class; the D2 failure itself is measured by d2scan):')
    for var, s in sorted(T.TURNS.items()):
        Lw = 4 * s
        ball = sum(48 ** i for i in range(Lw + 1))
        print(f'  VAR {var}: s = {s}: words of length <= {Lw}: <= 2^{math.log2(ball):.1f} elements, a fraction <= 2^{math.log2(ball) - math.log2(G):.1f} of G')
    sys.stdout.flush()


def diag_work(a):
    kind, m, n, seed = a
    rng = random.Random(seed)
    r = dict(n=n, chk=0, ffc=0, ffe=0, c1=0, c2=0, e1=0, e2=0, c2d=0, e2d=0, req=0, c1req=0, ffc_req=0)
    for _ in range(n):
        K = list(range(52))
        rng.shuffle(K)
        h = L.uniform_st(rng)
        e1, e2 = rng.sample(range(30), 2)
        h2 = comp(B.gflip(e1, e2), h)
        rec, r1, r2 = [], [], []
        X = T.em3(kind, m, h, K, rec=rec, regout=r1)
        X2 = T.em3(kind, m, h2, K, regout=r2)
        hi, h2i = inv(h), inv(h2)
        Q = comp(inv(comp(hi, comp(comp(h, X), hi))), comp(h2i, comp(comp(h2, X2), h2i)))
        samec = [W.find_c(X, c) == W.find_c(X2, c) for c in range(20)]
        samee = [W.find_e(X, e) == W.find_e(X2, e) for e in range(30)]
        fq = sum(Q[s] == 3 * s for s in range(20))
        r['chk'] += fq == sum(samec)
        r['ffc'] += fq
        r['ffe'] += sum(samee)
        cl, el = rec[-1][1], rec[-2][1]                 # last step: ('e', e), ('c', c)
        cl1, el1 = rec[-3][1], rec[-4][1]
        r['c1'] += samec[cl]
        r['e1'] += samee[el]
        r['c2'] += samec[cl1] if cl1 != cl else 0
        r['e2'] += samee[el1] if el1 != el else 0
        r['c2d'] += cl1 != cl
        r['e2d'] += el1 != el
        eq = r1[0] == r2[0]
        r['req'] += eq
        if eq:
            r['c1req'] += samec[cl]
            r['ffc_req'] += sum(samec)
    return r


def pc(k, m, P):
    lo, hi = L.wilson(k, m)
    return f'{k / m:.5f} [{lo:.5f},{hi:.5f}] (ideal {P:.5f}, excess {k / m - P:+.5f})'


def main():
    args = sys.argv[1:]
    part = args[0]
    out = W.selftest(kinds=(('NRk', 52),))
    print(out[-2] if len(out) > 1 else '')
    print('\n'.join(T.selftest([('SAF', 0), ('SAF', 26), ('SAR', 26), ('SBF', 26), ('SBR', 26), ('SCF', 26), ('SCR', 26),
                                ('SDF', 26), ('SDR', 26)])))
    T0 = time.time()
    if part == 'bound':
        bound()
        return
    with Pool(4) as p:
        if part == 'd2scan':
            N = int(args[1])
            import os
            base = int(os.environ.get('MDW_D2BASE', '40000000'))
            print(f'D2 scan, {N} pairs each; seeds {base} + 1000*j + chunk (j = item index)')
            for j, km in enumerate(args[2:]):
                kind, m = km.split(':')
                m = int(m)
                R, dt = TT.run(p, TT.d2_work, (kind, m), N, base + 1000 * j)
                M.show_d2(f'{kind}{m}', R, dt)
                print(f'     cost {T.cost(kind, m)}')
                sys.stdout.flush()
        elif part in ('d2', 'd3', 'merge', 'big', 'diag'):
            kind, m, N, seed0 = args[1], int(args[2]), int(args[3]), int(args[4])
            print(f'{part} {kind}{m}: N={N}, seeds {seed0}+...; cost {T.cost(kind, m)}')
            if part == 'd2':
                nch = max(1, N // 100000)
                R = M.merge(p.map(TT.d2_work, [(kind, m, N // nch, seed0 + c) for c in range(nch)]))
                M.show_d2(f'{kind}{m}', R, time.time() - T0)
            elif part == 'd3':
                for si, start in enumerate(('IV', 'rand')):
                    for ci, cls in enumerate(('same', 'opp', 'KA', 'rand')):
                        R, dt = TT.run(p, TT.d3_work, (kind, m, start, cls), N, seed0 + 100 * (4 * si + ci))
                        ub = 1 - 0.05 ** (1 / R['n'])
                        print(f"D3 {kind}{m} start {start:4s} pair {cls:4s} n={R['n']}: card-phase positions equal {R['poseq']}, "
                              f"output collisions {R['coll']} (0-hit 95% bound {ub:.1e}) ex {R['ex'][:2]}  [{dt:.0f}s]")
                        sys.stdout.flush()
            elif part == 'merge':
                law = L.moved_law()
                bins = [(0, 40), (41, 44), (45, 46), (47, 47), (48, 48), (49, 49), (50, 50)]
                tot, hits, peq = 0, [], 0
                H = {'IV': [0] * 51, 'rand': [0] * 51}
                for si, start in enumerate(('IV', 'rand')):
                    for i in TT.POS:
                        R, dt = TT.run(p, TT.merge_work, (kind, m, start, i), N, seed0 + 10000 * si + 100 * i)
                        H[start] = [x + y for x, y in zip(H[start], R['hist'])]
                        hits += R['hits']
                        peq += R['peq']
                        tot += sum(R['hist'])
                        mean_i = sum(k * c for k, c in enumerate(R['hist'])) / sum(R['hist'])
                        print(f"  merge {kind}{m} {start:4s} swap at {i:2d}: mean differing slots {mean_i:.4f}, "
                              f"P(<=46) {sum(R['hist'][:47]) / sum(R['hist']):.5f} (ideal {float(sum(law[:47])):.5f}), "
                              f"state equal right after the pair {R['peq']}, collisions {len(R['hits'])}  [{dt:.0f}s]")
                        sys.stdout.flush()
                print(f'merge {kind}{m}: {tot} adjacent-swap pairs ({len(TT.POS)} positions {TT.POS} x IV/uniform x {N}); '
                      f'state equal right after the swapped pair {peq}; output collisions {len(hits)}; 0-hit 95% bound per pair '
                      f'{1 - 0.05 ** (1 / tot):.2e}; hits {hits[:5]}')
                for start in H:
                    n = sum(H[start])
                    mean = sum(k * c for k, c in enumerate(H[start])) / n
                    print(f'  {start:4s} differing output slots: mean {mean:.4f} (ideal {M.MMEAN:.4f}); '
                          + '; '.join(f'[{a}-{b}] {sum(H[start][a:b + 1]) / n:.5f} (ideal {float(sum(law[a:b + 1])):.5f})' for a, b in bins))
            elif part == 'big':
                nch = N // B.CHN
                parts, q = [], max(1, nch // 4)
                for i, r in enumerate(p.imap(B.big_work, [(kind, m, B.CHN, seed0 + c) for c in range(nch)])):
                    parts.append(r)
                    if (i + 1) % q == 0 or i + 1 == nch:
                        B.report(B.merge_all(parts), time.time() - T0, f'{i + 1}/{nch} chunks')
            else:
                nch = N // B.CHN
                R = M.merge(p.map(diag_work, [(kind, m, B.CHN, seed0 + c) for c in range(nch)]))
                n = R['n']
                print(f"  check: #coinciding corners == #fully fixed corners of Q in {R['chk']}/{n}")
                print(f"  fully fixed corners of Q: mean {R['ffc'] / n:.5f} (ideal 0.33333, excess {R['ffc'] / n - 1 / 3:+.5f} +- "
                      f"{1.96 * math.sqrt((1 / 3) / n):.5f}); edges {R['ffe'] / n:.5f} (ideal 0.50000, excess {R['ffe'] / n - 0.5:+.5f} +- "
                      f"{1.96 * math.sqrt(0.5 / n):.5f})  [approx. null sd: sqrt(mean)]")
                print(f"  last step's corner coincides:   {pc(R['c1'], n, 1 / 60)}")
                print(f"  last step's edge coincides:     {pc(R['e1'], n, 1 / 60)}")
                print(f"  second-to-last step's corner (if a different piece; P(different) {R['c2d'] / n:.5f}): {pc(R['c2'], n, R['c2d'] / n / 60)}")
                print(f"  second-to-last step's edge   (if a different piece; P(different) {R['e2d'] / n:.5f}): {pc(R['e2'], n, R['e2d'] / n / 60)}")
                print(f"  final registers equal: {pc(R['req'], n, 1 / 12)}; given equal: last corner coincides "
                      f"{R['c1req'] / max(1, R['req']):.5f}, mean coinciding corners {R['ffc_req'] / max(1, R['req']):.5f}")
    print(f'wall time {time.time() - T0:.0f} s, workers 4')


if __name__ == '__main__':
    main()
