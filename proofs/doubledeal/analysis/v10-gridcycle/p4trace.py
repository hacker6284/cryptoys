"""Independent Python implementation of the Phase 4 "C sends itself" variants (analysis only).
Card c: suit c//13 (clubs 0, hearts 1, spades 2, diamonds 3), rank c%13+1; seats (row, col), first card at (2, 0).
Next target from finger f by the card just placed x: (f.row + suit(x), f.col + rank(x)) mod (4, 13).
50: finger stays on the target T (ghost finger). Blocked: row marker + suit(C), start column T.col + rank(C),
    first free seat to the right, drop a row if full; marker +1.   51: as 50, finger moves to where C landed.
52: row by suit(C), column by rank(blocker).   53: row by suit(blocker), column by rank(C).
usage: python3 p4trace.py   (re-checks every witness stored in p4/collide_*.log, then traces two of them)"""
import re, glob
R = 'A23456789TJQK'; S = 'CHSD'
nm = lambda c: R[c % 13] + S[c // 13]

def scan(g, row, c0):
    for a in range(4):
        for q in range(13):
            s = ((row + a) % 4, (c0 + q) % 13)
            if s not in g: return s
    raise AssertionError

def mix(V, d, log=None):
    g = {(2, 0): d[0]}; t = 0; f = (2, 0)
    for i in range(1, 52):
        p, x = d[i - 1], d[i]
        T = ((f[0] + p // 13) % 4, (f[1] + p % 13 + 1) % 13)
        if T not in g:
            s = T; why = 'free'
        else:
            o = g[T]
            rs = o // 13 if V == 53 else x // 13
            cr = o % 13 + 1 if V == 52 else x % 13 + 1
            s = scan(g, (t + rs) % 4, (T[1] + cr) % 13)
            why = f'blocked by {nm(o)}; scan row {(t + rs) % 4} from col {(T[1] + cr) % 13} -> {s}; marker {t}->{(t + 1) % 4}'
            t = (t + 1) % 4
        g[s] = x
        if log is not None: log.append(f'{i:2d} {nm(x)} target {T} {why}')
        f = s if V == 51 else T
    return [g[(r, c)] for r in range(4) for c in range(13)]

n = 0
for fn in sorted(glob.glob('p4/collide_*.log')):
    for line in open(fn):
        m = re.match(r'collision V(\d+): swap walk positions (\d+),(\d+) \(cards \d+,\d+\) deck: (.*)', line)
        if not m: continue
        V, i, j = int(m[1]), int(m[2]), int(m[3]); d = list(map(int, m[4].split()))
        e = d[:]; e[i], e[j] = e[j], e[i]
        same = mix(V, d) == mix(V, e); n += 1
        print(f'V{V}: decks differ at walk positions {i},{j} ({nm(d[i])} <-> {nm(d[j])}); tables equal: {same}')
        assert same and d != e and sorted(d) == list(range(52))
print(f'{n} witnesses independently confirmed')

def trace(V, i, j, d, lo, hi):
    e = d[:]; e[i], e[j] = e[j], e[i]
    for name, deck in (('deck A', d), ('deck B', e)):
        log = []; mix(V, deck, log)
        print(f'--- V{V} {name}, steps {lo}..{hi}:'); print('\n'.join(log[lo - 1:hi]))
for fn, V in (('p4/collide_50.log', 50),):
    ws = [l for l in open(fn) if l.startswith('collision')]
    for l in ws[:2]:
        m = re.match(r'collision V(\d+): swap walk positions (\d+),(\d+) \(cards \d+,\d+\) deck: (.*)', l)
        i, j = int(m[2]), int(m[3]); d = list(map(int, m[4].split()))
        trace(V, i, j, d, i, min(51, j + 1))
