"""Independent Python implementation of the bump variants (analysis only) and a traced collision.
Card c: suit c//13 (clubs 0, hearts 1, spades 2, diamonds 3), rank c%13+1; seats (row, col), start (2, 0).
usage: python3 p3trace.py   (verifies the stored witnesses and prints a trace of the first one)"""
R = 'A23456789TJQK'; S = 'CHSD'
nm = lambda c: R[c % 13] + S[c // 13]

def scan(occ, row, c0, t, mark):
    for a in range(4):
        rr = (row + a) % 4
        for q in range(13):
            cc = (c0 + q) % 13
            if (rr, cc) not in occ:
                return (rr, cc), ((t + a + 1) % 4 if mark else t)
    raise AssertionError

def bump(V, d, log=None):
    g = {(2, 0): d[0]}; t = 0; f = (2, 0); drv = d[0]
    for i in range(1, 52):
        x = d[i]; T = ((f[0] + drv // 13) % 4, (f[1] + drv % 13 + 1) % 13)
        if T not in g:
            g[T] = x; f = T; drv = x
            if log is not None: log.append(f'{i:2d} {nm(x)} -> {T} free')
            continue
        o = g[T]
        if V in (40, 42): s, t = scan(g, t, T[1], t, True)
        else:
            t0 = t; s, _ = scan(g, (t0 + o // 13) % 4, (T[1] + o % 13 + 1) % 13, t, False); t = (t0 + 1) % 4
        g[s] = o; g[T] = x
        if log is not None: log.append(f'{i:2d} {nm(x)} -> {T} bumps {nm(o)} to {s}; marker {t}')
        if V in (40, 41): f = T; drv = x
        else: f = s; drv = o
    return [g[(r, c)] for r in range(4) for c in range(13)]

W = [(40, 21, 22, [17,30,9,26,0,13,34,50,19,45,6,8,38,37,43,28,1,18,39,14,33,12,36,11,42,10,32,27,51,46,15,2,44,48,29,3,4,31,41,5,40,24,25,22,49,21,16,23,7,35,47,20]),
     (41, 14, 15, [26,44,37,17,33,34,9,5,21,7,16,0,29,31,12,13,4,45,14,22,42,32,43,36,48,18,35,47,19,24,1,40,20,51,46,6,8,27,30,25,49,41,23,15,3,50,2,28,10,11,38,39]),
     (42, 3, 4, [39,21,23,13,25,14,9,50,11,29,2,7,34,6,24,10,8,45,40,49,1,46,41,48,47,5,28,0,35,18,4,36,15,26,38,20,42,19,44,3,30,17,22,43,33,51,37,32,16,31,12,27]),
     (43, 10, 11, [35,27,40,11,26,49,19,46,47,41,25,51,31,20,36,42,2,48,8,32,1,24,23,3,6,10,9,5,0,16,39,4,15,13,45,30,21,50,29,12,18,22,14,33,38,17,34,28,7,37,43,44])]
for V, i, j, d in W:
    e = d[:]; e[i], e[j] = e[j], e[i]
    same = bump(V, d) == bump(V, e)
    print(f'V{V}: decks differ at walk positions {i},{j} ({nm(d[i])}, {nm(d[j])}); outputs equal: {same}')
    assert same and d != e
V, i, j, d = W[0]; e = d[:]; e[i], e[j] = e[j], e[i]
for name, deck in (('deck A', d), ('deck B', e)):
    log = []; bump(V, deck, log)
    print(f'--- {name}, steps {i-1}..{j+3}:'); print('\n'.join(log[i-2:j+3]))
