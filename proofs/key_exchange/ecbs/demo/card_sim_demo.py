"""CARD.md at Demo (n = 7, 1/2 set, chord walk), followed literally: full exchanges against PARI for
EVERY pair of non-empty 2-cell keys (8 x 8 = 64 exchanges, 128 people).  Same checks as
../card/card_sim_v3.py: base point by rule = P; sent C = [a]P; sent A = pi(C) - C = [(lambda-1)a]P; each
receiver's rebuilt A equals the sender's A; curve test passed; shared points agree and equal
[(lambda-1)ab]P; folded key = spec s6 reference fold.  Also: band peak, control row (need / holes,
highest hole, tally, script marker), calls, moves per phase.
Fold at Demo: 'drop rows C and D onto rows A and B; the key is rows A-B' (m = 4; ../core/ecbs_extractor).
Usage: python card_sim_demo.py   (writes card_sim_demo.json; prints card_sim_demo.txt's content)"""
import sys, os, json, random, time, itertools
sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import homes_demo as D
H, V = D.H, D.V
os.chdir(H.ECBS)
import ecbs_exchange as X, ecbs_keys as K
os.chdir(HERE)
M = 2
KEEP = 4                                   # rows A-B of a 2-wide lane

def fold_key(hb):
    """'Drop rows C and D onto rows A and B, same column.  The key is rows A and B.'"""
    x = hb.value('across'); out = x[:KEEP]
    for i in range(KEEP, hb.n):
        if x[i] != '.': hb._drop(out, i - KEEP, x[i])
    return out

def ref_fold(x):
    v = {'.': 0, 'W': 1, 'R': 2}; z = [0] * KEEP
    for i, c in enumerate(x): z[i % KEEP] = (z[i % KEEP] + v[c]) % 3
    return ''.join('.WR'[t] for t in z)

def exchange(T, ca, cb, rnd):
    R = T.R; l = T.l; st = {'keys': [''.join(ca), ''.join(cb)]}
    lam1 = (T.lam - 1) % l
    ka = K.scalar(K.walk_pegs(ca)[1], T.lam, T.mus, l); kb = K.scalar(K.walk_pegs(cb)[1], T.lam, T.mus, l)
    B = {w: D.HBDemo() for w in 'AB'}
    cells = {'A': ca, 'B': cb}; m = {w: {} for w in 'AB'}
    def phase(w, name, fn):
        hb = B[w]; hb.phase = name; m0 = hb.moves; pk = hb.peak; hb.peak = 0
        r = fn(hb); m[w][name] = m[w].get(name, 0) + hb.moves - m0
        ph = st.setdefault('peak_by_phase', {}); ph[name] = max(ph.get(name, 0), hb.peak); hb.peak = max(pk, hb.peak); return r
    for w in 'AB':
        j = phase(w, 'base point', D.base_point_demo); st['base_hole'] = j
        hb = B[w]
        st.setdefault('P_ok', []).append((hb.value('base across'), hb.value('base up')) == (list(T.P[0]), list(T.P[1])))
        hb.key_grid_moves += sum(c != '.' for c in cells[w])
        phase(w, 'own walk', lambda hb: D.walk_demo(hb, cells[w]))
        phase(w, 'own walk', lambda hb: (hb.clear('base across'), hb.clear('base up')))
    C = {w: (B[w].value('across'), B[w].value('up')) for w in 'AB'}
    st['C_ok'] = [R.pt(C['A']) == R.mul(ka, T.Pref), R.pt(C['B']) == R.mul(kb, T.Pref)]
    other = {'A': 'B', 'B': 'A'}
    for w in 'AB':
        phase(w, 'swap', lambda hb: V.call_session(hb, B[other[w]], rnd))
    for w in 'AB':
        st.setdefault('on_curve', []).append(phase(w, 'curve test', H.on_curve))
    for w in 'AB':
        phase(w, 'make certificate', lambda hb: V.certificate(hb, 'across', 'up')); B[w].cr.phase_drop()
    A = {w: (B[w].value('across'), B[w].value('up')) for w in 'AB'}
    st['A_ok'] = [R.pt(A['A']) == R.mul(ka * lam1 % l, T.Pref), R.pt(A['B']) == R.mul(kb * lam1 % l, T.Pref),
                  R.pt(A['A']) == R.add(R.frob(R.pt(C['A'])), R.neg(R.pt(C['A']))),
                  R.pt(A['B']) == R.add(R.frob(R.pt(C['B'])), R.neg(R.pt(C['B'])))]
    for w in 'AB':
        phase(w, 'rebuild theirs', lambda hb: V.certificate(hb, 'base across', 'base up')); B[w].cr.phase_drop()
    for w in 'AB':
        phase(w, 'swap', lambda hb: V.call_session(hb, B[other[w]], rnd))
    for w in 'AB':
        st.setdefault('match', []).append(V.receive_certificate(B[w]))
        phase(w, 'rebuild theirs', lambda hb: (hb.clear('bottom'), hb.clear('gap')))
    for w in 'AB':
        phase(w, 'rebuild theirs', lambda hb: (hb.clear('across'), hb.clear('up')))
    out = {}
    Kref = R.mul(ka * kb * lam1 % l, T.Pref)
    for w in 'AB':
        phase(w, 'shared walk', lambda hb: D.walk_demo(hb, cells[w]))
        phase(w, 'shared walk', lambda hb: (hb.clear('base across'), hb.clear('base up')))
        hb = B[w]; out[w] = (hb.value('across'), hb.value('up'))
        m0 = hb.moves; kf = fold_key(hb); m[w]['fold'] = hb.moves - m0
        st.setdefault('fold_key', []).append(''.join(kf))
        st.setdefault('fold_ref_ok', []).append(''.join(kf) == ref_fold(R.unpt(Kref)[0]))
    st['agree'] = out['A'] == out['B']; st['shared_ok'] = R.pt(out['A']) == Kref
    st['fold_agree'] = st['fold_key'][0] == st['fold_key'][1]
    st['peak'] = [B[w].peak for w in 'AB']
    st['max_bench_hole'] = max(B[w].max_index for w in 'AB'); st['benchlen'] = B['A'].benchlen
    cr = B['A'].cr
    st['control'] = dict(row_holes=cr.length, script_holes=cr.script, ladder=''.join(cr.row[cr.ladder0:cr.ladder0 + cr.nrungs]),
                         park_hole=cr.park_hole, tally_first=cr.tally0,
                         tally_max=max(B[w].cr.tally_max for w in 'AB'),
                         highest_hole_used=max(B[w].cr.max_hole for w in 'AB'),
                         script_marker_max=max(B[w].cr.marker_max for w in 'AB') + 1,
                         phase_end=[B[w].cr.row[B[w].cr.phase] for w in 'AB'], calling_hole=cr.calling)
    st['moves'] = {w: sum(m[w].values()) for w in 'AB'}; st['moves_by_phase'] = m
    st['ctrl'] = {w: B[w].ctrl for w in 'AB'}; st['calls'] = {w: B[w].calls for w in 'AB'}
    st['cursor_steps'] = {w: B[w].cursor_steps for w in 'AB'}; st['stale_cleared'] = {w: B[w].stale_cleared for w in 'AB'}
    st['ladder_build_once'] = B['A'].ladder_moves; st['ops'] = B['A'].ops
    inv = V.coord_inverse('Demo'); calls_ok = True
    for w in 'AB':
        log = B[w].call_log; seen = set()
        for dst, src, i, g, cell in log:
            calls_ok &= inv[(g, cell)] == (src, i) and (g, cell, dst) not in seen; seen.add((g, cell, dst))
        calls_ok &= [i for _, _, i, _, _ in log] == list(range(T.n)) * 4
    st['calls_ok'] = calls_ok; st['call_example'] = [f"grid {g}, {c}" for _, _, _, g, c in B['A'].call_log[:3]]
    return st

def main():
    T = X.Tier('Demo'); rnd = random.Random(20261003)
    keys = [list(k) for k in itertools.product('.WR', repeat=M) if any(c != '.' for c in k)]
    runs = []; t0 = time.time()
    for ca, cb in itertools.product(keys, keys):
        runs.append(exchange(T, ca, cb, rnd))
    people = [(r, w) for r in runs for w in 'AB']
    def allok(key): return all(all(v) if isinstance(v, list) else v for v in (r[key] for r in runs))
    tot = [r['moves'][w] for r, w in people]
    ph = {}
    for r, w in people:
        for k, v in r['moves_by_phase'][w].items(): ph.setdefault(k, []).append(v)
    mean = lambda v: sum(v) / len(v)
    check = sum(sum(ph[k]) for k in ('curve test', 'make certificate', 'rebuild theirs')) / sum(tot)
    c0 = runs[0]['control']
    need_measured = c0['script_marker_max'] + V.PHASE + V.CALLING + len(c0['ladder']) + 1 + max(r['control']['tally_max'] for r in runs)
    need_15 = 15 + V.PHASE + V.CALLING + len(c0['ladder']) + 1 + max(r['control']['tally_max'] for r in runs)
    summ = dict(
        exchanges=len(runs), people=len(people), key_pairs='all 8 x 8 non-empty 2-cell keys',
        base_point_is_P=sum(sum(r['P_ok']) for r in runs), sent_C_ok=sum(sum(r['C_ok']) for r in runs),
        sent_A_ok=sum(sum(r['A_ok'][:2]) for r in runs), A_is_piC_minus_C=sum(sum(r['A_ok'][2:]) for r in runs),
        curve_test_passed=sum(sum(r['on_curve']) for r in runs), rebuilt_A_matches=sum(sum(r['match']) for r in runs),
        shared_agree=sum(r['agree'] for r in runs), shared_is_lam1abP=sum(r['shared_ok'] for r in runs),
        fold_ref_ok=sum(sum(r['fold_ref_ok']) for r in runs), fold_agree=sum(r['fold_agree'] for r in runs),
        calls_ok=sum(r['calls_ok'] for r in runs), call_example=runs[0]['call_example'],
        calls_per_receiver=sorted({r['calls'][w] for r, w in people}),
        cursor_steps_per_receiver=sorted({r['cursor_steps'][w] for r, w in people}),
        stale_cleared=sum(r['stale_cleared'][w] for r, w in people),
        band_peak=max(max(r['peak']) for r in runs),
        peak_by_phase={k: max(r['peak_by_phase'][k] for r in runs) for k in runs[0]['peak_by_phase']},
        highest_bench_hole=max(r['max_bench_hole'] for r in runs), benchlen=runs[0]['benchlen'],
        moves_per_person_mean=round(mean(tot)), moves_min=min(tot), moves_max=max(tot),
        moves_by_phase_mean={k: round(mean(v)) for k, v in ph.items()},
        check_share=round(check, 4), base_point_share=round(sum(ph['base point']) / sum(tot), 4),
        control_moves_mean=round(mean([r['ctrl'][w] for r, w in people])),
        ladder_build_once=runs[0]['ladder_build_once'],
        control=dict(holes=c0['row_holes'], script_holes=c0['script_holes'], ladder=c0['ladder'],
                     layout=f"script 0-{c0['script_holes'] - 1}, phase {c0['script_holes']}, calling {c0['calling_hole']}, "
                            f"ladder {c0['calling_hole'] + 1}-{c0['calling_hole'] + len(c0['ladder'])}, parking {c0['park_hole']}, "
                            f"tally {c0['tally_first']}-{c0['tally_first'] + max(r['control']['tally_max'] for r in runs) - 1}",
                     tally_max=max(r['control']['tally_max'] for r in runs),
                     script_marker_peak=max(r['control']['script_marker_max'] for r in runs),
                     highest_hole_used=max(r['control']['highest_hole_used'] for r in runs),
                     need_with_measured_script=need_measured, need_with_15_hole_script=need_15,
                     phase_end=sorted({p for r in runs for p in r['control']['phase_end']})),
        secs=round(time.time() - t0, 1))
    json.dump(dict(summary=summ, runs=runs), open(os.path.join(HERE, 'card_sim_demo.json'), 'w'), indent=1, default=str)
    print(json.dumps(summ, indent=1))

def overrun_15():
    """the other tiers' 15-hole script row at Demo: lay out the control row and run one exchange."""
    try:
        hb = D.HBDemo(script=15); D.base_point_demo(hb)
    except (AssertionError, IndexError) as e:
        return f"overrun while laying the ladder: script 0-14, phase 15, calling 16, ladder from 17 in a 16-hole row ({type(e).__name__})"
    return "no overrun"

if __name__ == '__main__':
    main()
    print("15-hole script row at Demo:", overrun_15())
