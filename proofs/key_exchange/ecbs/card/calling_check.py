"""Calling-rule checks for v3 (BS s3.1 as revised after DHH's #152 review), per tier:
 (a) resume: let go at EVERY hole of a 4-band calling session and resume from the board alone;
 (b) stale pegs: a receiving home holding old pegs.  Without 'clear it first' a misfire leaves the stale
     peg (copy wrong); with the rule the copy is exact;
 (c) coordinates: every call names a hole of the sender's published band, never row J (control row),
     never a key grid, in number order; the four bands' coordinate ranges."""
import sys, os, random, json
sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import homes as H, homes_v3 as V
os.chdir(H.ECBS)
import ecbs_exchange as X
os.chdir(HERE)
out = {}
for name in ('Toy', 'Hobby', 'Serious'):
    T = X.Tier(name); n = T.n; rnd = random.Random(5 + n); R = T.R
    def pair():
        snd = V.HB3(name, n, T.k); rec = V.HB3(name, n, T.k)
        for h in ('across', 'up'): snd.put(h, R.rand_el(rnd))
        for h in ('across', 'up'): rec.put(h, R.rand_el(rnd))        # receiver's own point stays put
        return snd, rec
    # (a) let go before every single call of a session (C plan), resume from the board
    snd, rec = pair(); rec.put('base up', R.rand_el(rnd))          # a stale peg band in a receiving home
    V.start_calling(rec); k = 0
    while rec.cr.row[rec.cr.calling] == 'W':
        dst, i = rec.cursor; src = dict(V.plan_for(rec))[dst]       # everything read off the board
        if rec.home[dst] is not None:
            assert rec.home[dst][:i] == snd.home[src][:i] and all(c == '.' for c in rec.home[dst][i:])
        V.call_step(rec, snd); k += 1
    ok_a = k == 2 * n and rec.home['base across'] == snd.home['across'] and rec.home['base up'] == snd.home['up']
    # (b) stale pegs in the receiving homes
    trials = 200; wrong_noclear = wrong_rule = 0
    for _ in range(trials):
        snd, rec = pair()
        stale = (R.rand_el(rnd), R.rand_el(rnd))
        # without the rule: answers laid over old pegs (a misfire lays nothing, so the old peg stays)
        lay = lambda old, band: [b if b != '.' else o for o, b in zip(old, band)]
        wrong_noclear += lay(stale[0], snd.home['across']) != snd.home['across'] or lay(stale[1], snd.home['up']) != snd.home['up']
        rec.put('base across', list(stale[0])); rec.put('base up', list(stale[1]))
        V.call_session(rec, snd, rnd)
        wrong_rule += rec.home['base across'] != snd.home['across'] or rec.home['base up'] != snd.home['up']
    # (c) coordinates
    inv = V.coord_inverse(name); cells = {}
    for home in H.HOMES:
        cs = [V.coord(name, home, i) for i in range(n)]
        assert all(c[1][0] != 'J' for c in cs) and len(set(cs)) == n
        cells[home] = f"grid {cs[0][0]}, {cs[0][1]} .. grid {cs[-1][0]}, {cs[-1][1]}"
    allc = [V.coord(name, h, i) for h in H.HOMES for i in range(n)]
    out[name] = dict(resume_every_hole=ok_a, calls_in_session=k,
                     stale_trials=trials, stale_copy_wrong_without_clearing=wrong_noclear, stale_copy_wrong_with_rule=wrong_rule,
                     homes_disjoint=len(set(allc)) == len(allc), never_row_J=True,
                     published_bands=dict(across=cells['across'], up=cells['up']),
                     key_grids=V.GEOM[name]['key'], workspace_grids=V.GEOM[name]['work'])
    print(name, json.dumps(out[name]), flush=True)
json.dump(out, open(os.path.join(HERE, 'calling_check.json'), 'w'), indent=1)
