#!/usr/bin/env python3
"""Hand-work (peg moves) per person for each ECBS key encoding, measured with the peg recipes.
Each run is a full exchange checked against PARI (see ecbs_exchange.full_exchange).  The
constant-work (dummy addition) variants are a MODEL: measured mean in-walk addition cost times the
number of dummy additions.  Time at an ASSUMED 1 move per second, like the draft."""
import sys, random, json, statistics as st
from ecbs_pegs import Board
import ecbs_exchange as X
import ecbs_keys as K

class MeteredBoard(Board):
    """Board that also meters moves spent inside mixed additions and Frobenius steps."""
    def __init__(self, n, k):
        super().__init__(n, k); self.add_moves = 0; self.frob_moves = 0; self.depth = 0
    def mixed_add(self, *a, **kw):
        m0 = self.moves; r = super().mixed_add(*a, **kw); self.add_moves += self.moves - m0; return r
    def frobenius(self, Q):
        m0 = self.moves; r = super().frobenius(Q); self.frob_moves += self.moves - m0; return r

def main(name, reps):
    T = X.Tier(name); rnd = random.Random(777 + T.n)
    T.board = lambda: MeteredBoard(T.n, T.k)
    encs = {"Toy": [('three', 1), ('pegs', 19)], "Hobby": [('three', 2), ('twisted', 2), ('pegs', 55)],
            "Serious": [('three', 6), ('three', 7), ('twisted', 6), ('pegs', 162), ('pegs', 173), ('pegs', 175),
                        ('pegs', 200), ('six', 2)]}[name]
    cells = lambda e, p: {'three': 100 * p, 'twisted': 100 * p, 'pegs': p, 'six': 100 * p}[e]
    out = {}
    # mean in-walk addition cost: meter a few public walks directly
    B = T.board(); w, _ = K.walk_three_state(K.three_state(rnd, T.G))
    X.run_walk(T, w, [T.P])
    Bm = T.board(); steps = [d if d == 'F' else ('A', d[1], T.P) for d in w]; Q = Bm.walk(steps, *T.P)
    per_add = Bm.add_moves / Bm.ops['ptadd']; per_F = Bm.frob_moves / max(1, Bm.ops.get('cube', 0) / 3)
    print(f"{name}: mean in-walk mixed addition = {per_add:,.0f} moves; Frobenius step = {per_F:,.0f} moves")
    for enc, p in encs:
        runs = [X.full_exchange(T, rnd, enc, p) for _ in range(reps)]
        assert all(r['agree'] and r['matches_ref'] and all(r['trace_ok']) and all(r['on_curve']) for r in runs)
        pp = [r['moves']['per_person'] for r in runs]; adds = [r['adds_A'] for r in runs]
        walks = [r['moves']['pub'] + r['moves']['shared'] for r in runs]
        dummies = {'three': cells(enc, p) - 1, 'twisted': cells(enc, p) - 1, 'pegs': p - 1, 'six': 2 * cells(enc, p) - 1}[enc]
        cw = st.mean(pp) + 2 * (dummies - st.mean(adds)) * per_add
        out[f"{enc}{p}"] = dict(per_person_mean=st.mean(pp), per_person_runs=pp, adds_runs=adds,
                                 validation=st.mean(r['moves']['on_curve'] + r['moves']['trace'] for r in runs),
                                 tau_bar=st.mean(r['moves']['tau_bar'] for r in runs), constant_work=cw)
        print(f"  {enc:8s} {p:4d}: additions/walk {adds}; per person {st.mean(pp)/1e6:6.2f} M moves "
              f"(runs {[round(x/1e6, 2) for x in pp]}) of which validation {out[f'{enc}{p}']['validation']/1e6:.2f} M, "
              f"tau-bar {out[f'{enc}{p}']['tau_bar']/1e6:.2f} M;  = {st.mean(pp)/3600:,.0f} h @ 1 move/s;"
              f"  constant-work model {cw/1e6:.1f} M", flush=True)
    json.dump(dict(per_add=per_add, per_F=per_F, runs=out), open(f"ecbs_costs_{name}.json", "w"), indent=1)

if __name__ == "__main__":
    for name in sys.argv[1:] or ["Toy", "Hobby", "Serious"]:
        main(name, 3)
