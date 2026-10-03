"""PLAYER_CARD_v3, followed literally: full exchanges at Toy / Hobby / Serious against PARI.
Both players on their own HB3 board in lockstep.  Checks: base point by rule = P; sent C = [a]P;
sent A = pi(C) - C = [(lambda-1)a]P; each receiver's rebuilt A equals the sender's A; shared keys agree
and equal [(lambda-1)ab]P.  Also records the band peak, control-row use, and moves per phase.
Variant 'store_P': P kept all game in two extra bands (question ii)."""
import sys, os, json, random, time
sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import homes as H, homes_v3 as V
os.chdir(H.ECBS)
import ecbs_exchange as X, ecbs_keys as K
os.chdir(HERE)
CELLS = {'Toy': 16, 'Hobby': 51, 'Serious': 162}
FOLD = {'Toy': ('C', 'A', 'AB'), 'Hobby': ('C', 'A', 'AB'), 'Serious': ('FGHI', 'ABCD', 'ABCDE')}

def fold_key(hb, T):
    """'Fold the across: Serious drops rows F to I onto rows A to D, and Toy and Hobby drop row C onto
    row A. The key is rows A to E (Serious) or A to B.'"""
    w = hb.w; x = hb.value('across'); src, dst, keep = FOLD[T.name]
    rows = lambda s: [ord(c) - 65 for c in s]
    out = x[:]
    for r_s, r_d in zip(rows(src), rows(dst)):
        for c in range(w):
            i, j = r_s * w + c, r_d * w + c
            if i < hb.n and x[i] != '.':
                hb._drop(out, j, x[i])                  # drop it onto the same column
    return out[:len(keep) * w]

def ref_fold(T, x, w):
    """spec 6: z_j = sum of x_i over i = j (mod m), m = kept rows x lane width (independent of the card)."""
    m = len(FOLD[T.name][2]) * w; v = {'.': 0, 'W': 1, 'R': 2}
    z = [0] * m
    for i, c in enumerate(x): z[i % m] = (z[i % m] + v[c]) % 3
    return ''.join('.WR'[t] for t in z)

def exchange(T, rnd, store_P=False):
    R = T.R; l = T.l; M = CELLS[T.name]; st = {'tier': T.name, 'store_P': store_P}
    lam1 = (T.lam - 1) % l
    while True:
        ca, cb = K.pegs_only(rnd, M), K.pegs_only(rnd, M)
        if any(c != '.' for c in ca) and any(c != '.' for c in cb): break
    ka = K.scalar(K.walk_pegs(ca)[1], T.lam, T.mus, l); kb = K.scalar(K.walk_pegs(cb)[1], T.lam, T.mus, l)
    extra = ('P across', 'P up') if store_P else ()
    B = {w: V.HB3(T.name, T.n, T.k, extra_homes=extra) for w in 'AB'}
    cells = {'A': ca, 'B': cb}; m = {w: {} for w in 'AB'}
    def phase(w, name, fn):
        hb = B[w]; hb.phase = name; m0 = hb.moves; pk = hb.peak; hb.peak = 0
        r = fn(hb); m[w][name] = m[w].get(name, 0) + hb.moves - m0
        ph = st.setdefault('peak_by_phase', {}); ph[name] = max(ph.get(name, 0), hb.peak); hb.peak = max(pk, hb.peak); return r
    # --- base point, roll, own walk, finish
    for w in 'AB':
        j = phase(w, 'base point', V.base_point3); st['base_hole'] = j
        hb = B[w]
        st.setdefault('P_ok', []).append((hb.value('base across'), hb.value('base up')) == (list(T.P[0]), list(T.P[1])))
        if store_P:                                         # keep P for the next game in two extra bands
            phase(w, 'store P', lambda hb: (hb.copy('P across', 'base across'), hb.copy('P up', 'base up')))
        hb.key_grid_moves += sum(c != '.' for c in cells[w])  # roll the key into the key grid
        phase(w, 'own walk', lambda hb: V.walk3(hb, cells[w]))
        def fin(hb): H.finish(hb); hb.clear('base across'); hb.clear('base up')
        phase(w, 'own walk', fin)
    C = {w: (B[w].value('across'), B[w].value('up')) for w in 'AB'}
    st['C_ok'] = [R.pt(C['A']) == R.mul(ka, T.Pref), R.pt(C['B']) == R.mul(kb, T.Pref)]
    other = {'A': 'B', 'B': 'A'}
    # --- swap C by calls, curve test
    for w in 'AB':
        o = other[w]
        phase(w, 'swap', lambda hb: V.call_session(hb, B[o], rnd))
    for w in 'AB':
        st.setdefault('on_curve', []).append(phase(w, 'curve test', H.on_curve))
    # --- make own certificate; drop a white peg in the phase hole
    for w in 'AB':
        phase(w, 'make certificate', lambda hb: V.certificate(hb, 'across', 'up')); B[w].cr.phase_drop()
    A = {w: (B[w].value('across'), B[w].value('up')) for w in 'AB'}
    st['A_ok'] = [R.pt(A['A']) == R.mul(ka * lam1 % l, T.Pref), R.pt(A['B']) == R.mul(kb * lam1 % l, T.Pref),
                  R.pt(A['A']) == R.add(R.frob(R.pt(C['A'])), R.neg(R.pt(C['A'])))]
    # --- rebuild theirs in the base bands; phase peg red; compare by calls
    for w in 'AB':
        phase(w, 'rebuild theirs', lambda hb: V.certificate(hb, 'base across', 'base up')); B[w].cr.phase_drop()
    for w in 'AB':                                          # second calls: their A into the bottom and gap
        o = other[w]
        phase(w, 'swap', lambda hb: V.call_session(hb, B[o], rnd))
    for w in 'AB':
        ok = V.receive_certificate(B[w]); st.setdefault('match', []).append(ok)
        phase(w, 'rebuild theirs', lambda hb: (hb.clear('bottom'), hb.clear('gap')))
    for w in 'AB':                                          # once both have called: clear the across and up
        phase(w, 'rebuild theirs', lambda hb: (hb.clear('across'), hb.clear('up')))
    # --- shared walk
    out = {}
    for w in 'AB':
        phase(w, 'shared walk', lambda hb: V.walk3(hb, cells[w]))
        def fin2(hb): H.finish(hb); hb.clear('base across'); hb.clear('base up')
        phase(w, 'shared walk', fin2)
        hb = B[w]; out[w] = (hb.value('across'), hb.value('up'))
        m0 = hb.moves; kf = fold_key(hb, T); m[w]['fold'] = hb.moves - m0
        st.setdefault('fold_key', []).append(''.join(kf))
        st.setdefault('fold_ref_ok', []).append(''.join(kf) == ref_fold(T, R.unpt(R.mul(ka * kb * lam1 % l, T.Pref))[0], hb.w))
        if store_P:                                         # P is still in its two bands at the end
            assert (hb.value('P across'), hb.value('P up')) == (list(T.P[0]), list(T.P[1]))
    Kref = R.mul(ka * kb * lam1 % l, T.Pref)
    st['agree'] = out['A'] == out['B']; st['shared_ok'] = R.pt(out['A']) == Kref
    st['fold_agree'] = st['fold_key'][0] == st['fold_key'][1]; del st['fold_key']
    st['peak'] = [B[w].peak for w in 'AB']; st['peak_strict'] = [B[w].peak_strict for w in 'AB']
    st['peak_where'] = [B[w].peak_where[0] for w in 'AB']
    st['max_bench_hole'] = max(B[w].max_index for w in 'AB'); st['benchlen'] = B['A'].benchlen
    cr = B['A'].cr
    st['control'] = dict(row_holes=cr.length, ladder=''.join(cr.row[cr.ladder0:cr.ladder0 + cr.nrungs]),
                         park_hole=cr.park_hole, tally_first=cr.tally0,
                         tally_max=max(B[w].cr.tally_max for w in 'AB'),
                         highest_hole_used=max(B[w].cr.max_hole for w in 'AB'),
                         script_marker_max=max(B[w].cr.marker_max for w in 'AB') + 1,
                         phase_end=[B[w].cr.row[B[w].cr.phase] for w in 'AB'])
    st['moves'] = {w: sum(m[w].values()) for w in 'AB'}; st['moves_by_phase'] = m
    st['ctrl'] = {w: B[w].ctrl for w in 'AB'}; st['key_grid'] = {w: B[w].key_grid_moves for w in 'AB'}
    st['calls'] = {w: B[w].calls for w in 'AB'}; st['ladder_build_once'] = B['A'].ladder_moves
    st['ops'] = B['A'].ops
    inv = V.coord_inverse(T.name); calls_ok = True
    for w in 'AB':
        log = B[w].call_log; seen = set()
        for dst, src, i, g, cell in log:
            calls_ok &= inv[(g, cell)] == (src, i) and (g, cell, dst) not in seen; seen.add((g, cell, dst))
        idx = [i for _, _, i, _, _ in log]
        calls_ok &= idx == list(range(T.n)) * 4                       # number order, every hole, 4 bands
    st['calls_ok'] = calls_ok; st['call_example'] = [f"grid {g}, {c}" for _, _, _, g, c in B['A'].call_log[:2]]
    st['cursor_steps'] = {w: B[w].cursor_steps for w in 'AB'}; st['stale_cleared'] = {w: B[w].stale_cleared for w in 'AB'}
    st['control']['calling_hole'] = cr.calling
    return st

if __name__ == '__main__':
    tiers = sys.argv[1].split(',') if len(sys.argv) > 1 else ['Toy', 'Hobby', 'Serious']
    reps = int(sys.argv[2]) if len(sys.argv) > 2 else 2
    store = len(sys.argv) > 3 and sys.argv[3] == 'store_P'
    res = {}
    for name in tiers:
        T = X.Tier(name); rnd = random.Random(20261001 + len(name) + (7 if store else 0))
        print(name, 'n', T.n, 'k', T.k, flush=True)
        runs = []
        for r in range(reps):
            t0 = time.time(); st = exchange(T, rnd, store_P=store); st['secs'] = round(time.time() - t0, 1)
            print(' ', json.dumps({k: v for k, v in st.items() if k != 'moves_by_phase'}), flush=True)
            print('   by phase', json.dumps(st['moves_by_phase']), flush=True)
            runs.append(st)
        res[name] = runs
    json.dump(res, open(os.path.join(HERE, f'card_sim_v3_{"_".join(tiers)}{"_storeP" if store else ""}.json'), 'w'), indent=1, default=str)
