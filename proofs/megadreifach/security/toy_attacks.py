"""End-to-end attacks on a scaled-down MegaDreifach-shaped hash (findings F3/F4).

Toy model with exactly the proved structure of the real compression function
(CornerDriven.emBlock_word / dmStep_word):
    state  (c, e),   c in Z_{2^k}  (stands for the corner part),
                     e in H_n = {even perms of n edges} x {flip vectors, even sum}
    dm((c, e), m) = ( F(c, m),  e * X(c, m) * e )
F and X are pseudo-random (SHA-256), i.e. we even *idealise* the corner part;
only the "edges driven by corners, updated by e X e" structure is kept.
Log2 of state space = k + log2|H_n|.

  collision : Joux multicollision on corners, then first merge in the edge tree.
  preimage  : corner multicollision + one corner-matching last block, then an
              edge meet-in-the-middle using square roots backward.
All found collisions/preimages are re-verified by hashing the full messages.
"""
import hashlib, itertools, math, random, sys
from collections import defaultdict

def mkgroup(n):
    def comp(a, b):   # apply b first then a (any fixed convention works)
        ap, af = a; bp, bf = b
        return (tuple(bp[ap[i]] for i in range(n)), tuple((bf[ap[i]] + af[i]) & 1 for i in range(n)))
    def inv(a):
        ap, af = a; ip = [0]*n
        for i in range(n): ip[ap[i]] = i
        return (tuple(ip), tuple(af[ip[i]] for i in range(n)))
    return comp, inv

def parity(p):
    return sum(p[i] > p[j] for i in range(len(p)) for j in range(i+1, len(p))) & 1

class Toy:
    def __init__(self, k, n, seed=0):
        self.k, self.n, self.seed = k, n, seed
        self.comp, self.inv = mkgroup(n)
        self.logH = math.log2(math.factorial(n)//2 * 2**(n-1))
        self.ncomp = 0
    def _h(self, *a):
        return hashlib.sha256(repr((self.seed,) + a).encode()).digest()
    def F(self, c, m):
        self.ncomp += 1
        return int.from_bytes(self._h('F', c, m)[:8], 'big') % (1 << self.k)
    def X(self, c, m):
        d = self._h('X', c, m); rng = random.Random(d)
        p = list(range(self.n)); rng.shuffle(p)
        if parity(p): p[0], p[1] = p[1], p[0]
        f = [rng.randrange(2) for _ in range(self.n - 1)]; f.append(sum(f) & 1)
        return (tuple(p), tuple(f))
    def estep(self, e, X):
        return self.comp(self.comp(e, X), e)
    def hash(self, msg, iv):
        c, e = iv
        for m in msg:
            X = self.X(c, m); c2 = int.from_bytes(self._h('F', c, m)[:8], 'big') % (1 << self.k)
            c, e = c2, self.estep(e, X)
        return c, e

def corner_collision(T, c, ctr):
    seen = {}
    while True:
        m = next(ctr); v = T.F(c, m)
        if v in seen: return seen[v], m, v
        seen[v] = m

def attack_collision(T, iv):
    """Joux on corners, one stage at a time, extending the edge tree until two
    different prefixes give the same edge state (same corner by construction)."""
    ctr = itertools.count(); c, _ = iv
    level = {iv[1]: []}                      # edge state -> one message prefix
    edge_ops = 0
    while True:
        m0, m1, c2 = corner_collision(T, c, ctr)
        X0, X1 = T.X(c, m0), T.X(c, m1)
        nxt = {}
        for e, pre in level.items():
            for m, X in ((m0, X0), (m1, X1)):
                e2 = T.estep(e, X); edge_ops += 1
                if e2 in nxt:
                    return nxt[e2], pre + [m], edge_ops
                nxt[e2] = pre + [m]
        level, c = nxt, c2

def all_elements(T):
    n = T.n
    for p in itertools.permutations(range(n)):
        if parity(p): continue
        for f in itertools.product((0, 1), repeat=n-1):
            yield (p, tuple(f) + (sum(f) & 1,))

def attack_preimage(T, iv, target, roots, max_last=64):
    ctr = itertools.count(); c, e0 = iv
    L = math.ceil(T.logH) + 1                 # stages with 2 choices each
    t1 = L // 2; t2 = L - t1
    stages = []
    for _ in range(L):
        m0, m1, c2 = corner_collision(T, c, ctr)
        stages.append((c, (m0, m1)))
        c = c2
    # forward edge tree over the first t1 stages
    fwd = {e0: []}
    for (cs, ms) in stages[:t1]:
        nf = {}
        for e, pre in fwd.items():
            for mm in ms:
                nf.setdefault(T.estep(e, T.X(cs, mm)), pre + [mm])
        fwd = nf
    def back(e_next, X):
        # e X e = e_next  <=>  (e X)^2 = e_next X  <=>  e = r X^{-1}, r^2 = e_next X
        Xi = T.inv(X)
        return [T.comp(r, Xi) for r in roots.get(T.comp(e_next, X), [])]
    # last block: match the target corner (2^k work each, the dominant cost).
    # The backward square-root tree can die out (e*X_last need not be a square),
    # so retry with a fresh corner-matching last block until the MitM succeeds.
    tries = 0
    while tries < max_last:
        while True:
            m = next(ctr)
            if T.F(c, m) == target[0]: break
        tries += 1
        last = (c, m)
        bwd = {e: [] for e in back(target[1], T.X(*last))}
        for (cs, ms) in reversed(stages[t1:]):
            nb = {}
            for e, suf in bwd.items():
                for mm in ms:
                    for e2 in back(e, T.X(cs, mm)):
                        nb.setdefault(e2, [mm] + suf)
            bwd = nb
        for e, pre in fwd.items():
            if e in bwd:
                return pre + bwd[e] + [last[1]], len(fwd), len(bwd), tries
    return None, len(fwd), 0, tries

if __name__ == '__main__':
    mode = sys.argv[1] if len(sys.argv) > 1 else 'both'
    if mode in ('coll', 'both'):
        print("== collision attack (toy): generic birthday = 2^((k+logH)/2) compressions")
        for (k, n) in [(20, 6), (24, 7), (28, 8), (32, 8)]:
            costs = []; eops = []
            for s in range(5):
                T = Toy(k, n, seed=s)
                iv = (0, (tuple(range(n)), (0,)*n))
                a, b, eo = attack_collision(T, iv)
                assert a != b and T.hash(a, iv) == T.hash(b, iv)
                costs.append(T.ncomp); eops.append(eo)
            gen = (k + T.logH) / 2
            print(f"k={k} n={n} log|state|={k+T.logH:.1f}: attack avg 2^{math.log2(sum(costs)/5):.1f} "
                  f"compressions + 2^{math.log2(sum(eops)/5):.1f} edge ops (5/5 verified) vs generic 2^{gen:.1f}")
    if mode in ('pre', 'both'):
        print("== preimage attack (toy): generic = 2^(k+logH) compressions")
        for (k, n) in [(16, 6), (16, 7), (20, 7)]:
            T0 = Toy(k, n)
            roots = defaultdict(list)
            for g in all_elements(T0):
                roots[T0.comp(g, g)].append(g)
            ok = 0; costs = []; tr = []
            for s in range(8):
                T = Toy(k, n, seed=100 + s)
                iv = (0, (tuple(range(n)), (0,)*n))
                rng = random.Random(s)
                tgt = T.hash([rng.randrange(1 << 40) for _ in range(3)], iv)   # a reachable target
                msg, nf, nb, tries = attack_preimage(T, iv, tgt, roots); tr.append(tries)
                if msg is not None and T.hash(msg, iv) == tgt:
                    ok += 1
                costs.append(T.ncomp)
            print(f"k={k} n={n} log|state|={k+T.logH:.1f}: {ok}/8 preimages found+verified, "
                  f"avg 2^{math.log2(sum(costs)/8):.1f} compressions, avg {sum(tr)/8:.1f} corner-matching last blocks "
                  f"(fwd/bwd lists ~2^{math.log2(max(nf,1)):.1f}/2^{math.log2(max(nb,1)):.1f}) "
                  f"vs generic 2^{k+T.logH:.1f}")
