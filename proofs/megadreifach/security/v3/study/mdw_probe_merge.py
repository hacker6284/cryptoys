"""Why a register is needed: card-phase merges of the last two cards (swap of positions 51, 52),
uniform start, for four variants of the named-pair card step (no blank rounds / no replay).
  NP     no register: card turn on face r (King: face 0, -k)
  NPch   NP, and every card after the first starts by turning the face carrying the THIRD
         sticker of the previous card's named corner (+1): a junction turn, still no register
  NS     deck-only register: card turn on face (r - r_prev) mod 12 (r_prev = previous card's face rank)
  NR     state register (rule NRr of mdw_lib): card turn on face (r + R) mod 12, R = face turned last
Counts: card-phase positions equal; of those, register (NR: R; others: none) equal; class of the
swapped pair (same rank or not).  Seeds 36_000_000 + 1000*variant + chunk, 8 chunks of 25,000.
Also prints 4 example merges of NP (turn blocks in both orders)."""
import random
import sys
import time
from collections import Counter
from multiprocessing import Pool

import mdfix_lib as L
import mdw_lib as W

apply, F1, FOP = W.apply, W.F1, W.FOP
THIRD = [3 - W.CARD[c][5] - W.CARD[c][6] for c in range(52)]
NAMES = lambda c: 'A23456789TJQK'[c // 4] + 'CHSD'[c % 4]   # noqa: E731


def blk(st, card, face, amt, tr=None):
    _, e, ir, inn, c, jr, jn, _, _ = W.CARD[card]
    if amt % 5:
        apply(st, FOP[face][amt % 5])
        if tr is not None:
            tr.append((face, amt % 5))
    for find, tab, piece, idx in ((W.find_e, W.EFACE, e, ir), (W.find_e, W.EFACE, e, inn),
                                  (W.find_c, W.CFACE, c, jr), (W.find_c, W.CFACE, c, jn)):
        s, v = find(st, piece)
        x = tab[s][v][idx]
        apply(st, F1[x])
        if tr is not None:
            tr.append((x, 1))
    return x


def em(kind, h, deal, tr=None):
    st = list(h)
    R, prev, pc = 0, 0, None
    for card in deal:
        r, k = card // 4, card % 4 + 1
        rr, a = (r, k) if r < 12 else (0, 5 - k)
        if kind == 'NR':
            face = (rr + R) % 12 if r < 12 else R
        elif kind == 'NS':
            face = (rr - prev) % 12
        else:
            face = rr
        if kind == 'NPch' and pc is not None:
            s, v = W.find_c(st, W.CARD[pc][4])
            apply(st, F1[W.CFACE[s][v][THIRD[pc]]])
        R = blk(st, card, face, a, tr)
        prev, pc = rr, card
    return st, R


def work(a):
    kind, n, seed = a
    rng = random.Random(seed)
    pe = co = 0
    cls = Counter()
    for _ in range(n):
        h = L.uniform_st(rng)
        d = list(range(52))
        rng.shuffle(d)
        d2 = list(d)
        d2[50], d2[51] = d2[51], d2[50]
        x1, r1 = em(kind, h, d)
        x2, r2 = em(kind, h, d2)
        if x1 == x2:
            pe += 1
            co += r1 == r2
            cls['same rank' if d[50] // 4 == d[51] // 4 else 'different rank'] += 1
    return dict(n=n, pe=pe, co=co, cls=cls)


def main():
    print('\n'.join(W.selftest()))
    T0 = time.time()
    with Pool(4) as p:
        for vi, kind in enumerate(('NP', 'NPch', 'NS', 'NR')):
            t0 = time.time()
            rs = p.map(work, [(kind, 25000, 36_000_000 + 1000 * vi + c) for c in range(8)])
            n = sum(r['n'] for r in rs)
            pe = sum(r['pe'] for r in rs)
            co = sum(r['co'] for r in rs)
            cls = sum((r['cls'] for r in rs), Counter())
            lo, hi = L.wilson(pe, n)
            print(f'{kind:5s} n={n}: card-phase positions equal after swapping cards 51,52: {pe} ({pe / n:.2e}, 95% CI [{lo:.1e},{hi:.1e}]); '
                  f'register also equal {co}; by pair class {dict(cls)}; {n * 3 / 51:.0f} of the pairs are expected to be same-rank  [{time.time() - t0:.0f}s]')
            sys.stdout.flush()
    rng = random.Random(36_999_000)
    found = 0
    while found < 4:
        h = L.uniform_st(rng)
        d = list(range(52))
        rng.shuffle(d)
        st, _ = em('NP', h, d[:50])
        a, b = d[50], d[51]
        s1, s2 = list(st), list(st)
        t1, t2 = [], []
        blk(s1, a, *W.card_face_amt(a)[:2], t1)
        blk(s1, b, *W.card_face_amt(b)[:2], t1)
        blk(s2, b, *W.card_face_amt(b)[:2], t2)
        blk(s2, a, *W.card_face_amt(a)[:2], t2)
        if s1 == s2:
            found += 1
            print(f'  NP merge example {found}: cards {NAMES(a)}, {NAMES(b)}; turns (face, clicks) in order ab: {t1}; order ba: {t2}')
    print(f'wall time {time.time() - T0:.0f} s, workers 4')


if __name__ == '__main__':
    main()
