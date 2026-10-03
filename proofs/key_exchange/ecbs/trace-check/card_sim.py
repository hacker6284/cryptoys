"""Run the fixed-home card literally, full exchanges at Toy / Hobby / Serious, vs PARI."""
import sys, os, json, random, time, hashlib
sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..', 'card'))   # homes.py lives with the card harness
import homes as H
os.chdir(H.ECBS)
import ecbs_exchange as X, ecbs_keys as K
os.chdir(HERE)
CELLS = {'Toy': 16, 'Hobby': 51, 'Serious': 162}

def person_walk(hb, cells):
    hb.phase = 'walk'; live = H.walk(hb, cells); assert live
    hb.phase = 'finish'; H.finish(hb)
    A = (hb.value('across'), hb.value('up')); hb.clear('across'); hb.clear('up'); return A

def exchange(T, rnd, derive_P=True, check='trace'):
    R = T.R; l = T.l; M = CELLS[T.name]; st = {}
    for attempt in range(50):
        ca, cb = K.pegs_only(rnd, M), K.pegs_only(rnd, M)
        if all(c == '.' for c in ca) or all(c == '.' for c in cb): continue
        ka = K.scalar(K.walk_pegs(ca)[1], T.lam, T.mus, l); kb = K.scalar(K.walk_pegs(cb)[1], T.lam, T.mus, l)
        try:
            boards = {}
            pubs = {}
            for who, cells in (('A', ca), ('B', cb)):
                hb = H.HB(T.name, T.n, T.k); boards[who] = hb
                m0 = hb.moves
                if derive_P:
                    hb.phase = 'base point'; j = H.base_point(hb); st['base_hole'] = j
                else:
                    hb.put('base across', T.P[0]); hb.put('base up', T.P[1])
                st.setdefault('P_ok', []).append((hb.value('base across'), hb.value('base up')) == (list(T.P[0]), list(T.P[1])))
                st.setdefault('m_P', []).append(hb.moves - m0); m0 = hb.moves
                if check == 'trace':
                    pubs[who] = person_walk(hb, cells)
                    st.setdefault('m_pub', []).append(hb.moves - m0)
                    hb.clear('base across'); hb.clear('base up')           # clear P before receiving
                else:                                                    # option D: send A = tau C - C and C
                    hb.phase = 'walk'; H.walk(hb, cells); hb.phase = 'finish'; H.finish(hb)
                    hb.clear('base across'); hb.clear('base up')
                    st.setdefault('m_pub', []).append(hb.moves - m0); m0 = hb.moves
                    hb.phase = 'certificate'; H.make_certificate(hb)
                    st.setdefault('m_make', []).append(hb.moves - m0)
                    pubs[who] = ((hb.value('across'), hb.value('up')), (hb.value('base across'), hb.value('base up')))
                    for h in ('across', 'up', 'base across', 'base up'): hb.clear(h)
            out = {}
            for who, cells, other in (('A', ca, 'B'), ('B', cb, 'A')):
                hb = boards[who]
                if check == 'trace':
                    Bp = pubs[other]
                    hb.put('base across', Bp[0]); hb.put('base up', Bp[1])
                    m0 = hb.moves; hb.phase = 'on curve'; on = H.on_curve(hb)
                    m1 = hb.moves; hb.phase = 'trace'; tr = H.trace_check(hb)
                else:
                    Bp, Cp = pubs[other]
                    hb.put('base across', Cp[0]); hb.put('base up', Cp[1])
                    m0 = hb.moves; hb.phase = 'on curve'; on = True
                    m1 = hb.moves; hb.phase = 'certificate'; tr = H.check_certificate(hb, Bp)   # includes C's curve test
                    hb.clear('base across'); hb.clear('base up'); hb.put('base across', Bp[0]); hb.put('base up', Bp[1])
                m2 = hb.moves; st.setdefault('m_on', []).append(m1 - m0); st.setdefault('m_tr', []).append(m2 - m1)
                st.setdefault('valid', []).append((on, tr))
                out[who] = person_walk(hb, cells); st.setdefault('m_shared', []).append(hb.moves - m2)
            f = 1 if check == 'trace' else (T.lam - 1) % l
            pa = pubs['A'] if check == 'trace' else pubs['A'][0]; pb = pubs['B'] if check == 'trace' else pubs['B'][0]
            st['pub_ok'] = [R.pt(pa) == R.mul(ka * f % l, T.Pref), R.pt(pb) == R.mul(kb * f % l, T.Pref)]
            st['agree'] = out['A'] == out['B']; st['matches_ref'] = R.pt(out['A']) == R.mul(ka * kb * f % l, T.Pref)
            st['tally_holes_peak'] = max(boards[w].tally_holes_peak for w in 'AB')
            st['peak'] = [boards[w].peak for w in 'AB']; st['peak_strict'] = [boards[w].peak_strict for w in 'AB']
            st['peak_where'] = boards['A'].peak_where
            st['max_bench_hole'] = max(boards[w].max_index for w in 'AB'); st['benchlen'] = boards['A'].benchlen
            st['tally_max'] = {'inv': max(boards[w].inv_tally.max for w in 'AB'), 'trace': max(boards[w].trace_tally.max for w in 'AB')}
            st['moves'] = [boards[w].moves for w in 'AB']; st['ctrl'] = [boards[w].ctrl for w in 'AB']
            st['ops'] = boards['A'].ops
            st['rerolls'] = attempt
            return st
        except H.Exceptional as e:
            st = {}; continue
    raise RuntimeError('too many exceptional keys')

def script_row(T, rnd):
    """per-line multiply/cube counts of one F-form add + Frobenius, from the literal walk."""
    hb = H.HB(T.name, T.n, T.k); hb.put('base across', T.P[0]); hb.put('base up', T.P[1])
    H.start_walk(hb, False); hb.line_log.clear()
    H.frobenius_point(hb); H.fform_add(hb, True)
    from collections import Counter
    return Counter(f"{a}:{b}" for a, b in hb.line_log)

if __name__ == '__main__':
    tiers = sys.argv[1].split(',') if len(sys.argv) > 1 else ['Toy', 'Hobby', 'Serious']
    reps = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    res = {}
    for name in tiers:
        T = X.Tier(name); rnd = random.Random(20260930 + len(name))
        print(name, 'n', T.n, 'k', T.k, 'base hole', T.base_hole, flush=True)
        print(' script row', dict(script_row(T, rnd)), flush=True)
        runs = []
        for check in ('trace', 'cert'):
          for r in range(reps):
            t0 = time.time(); st = exchange(T, rnd, derive_P=(r == 0), check=check); st['secs'] = round(time.time() - t0, 1); st['check'] = check
            print(' ', {k: v for k, v in st.items() if not k.startswith('m_')}, flush=True)
            print('   moves: P', st['m_P'], 'pub', st['m_pub'], 'make', st.get('m_make'), 'on', st['m_on'], 'check', st['m_tr'], 'shared', st['m_shared'], flush=True)
            runs.append(st)
        res[name] = runs
    json.dump(res, open(os.path.join(HERE, 'card_sim_' + '_'.join(tiers) + '.json'), 'w'), indent=1, default=str)
