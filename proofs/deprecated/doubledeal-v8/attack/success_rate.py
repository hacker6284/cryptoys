"""Success rate of the same-rank relabel distinguisher on the real DoubleDeal v8 encrypt
(frozen, deprecated; Nr=6, PassKey schedule), random keys, fixed query budget; plus a control
(different-rank swap) and a CTR variant (chosen distinct nonces N, tau.N; keystream recovered
from known plaintext).

Seeds are deterministic per (mode, key index).
Usage: python3 success_rate.py [pairs_per_key] [n_keys]
"""
import random
import sys
from multiprocessing import Pool
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import dd_v8 as dd  # noqa: E402

MODES = ('attack', 'control', 'ctr')


def tau_swap(x, y):
    t = list(range(52))
    t[x], t[y] = y, x
    return t


def app(t, deck):
    return [t[c] for c in deck]


def ks(msg, cipher):
    """Keystream deck S from a known (M, C = Compose(M, S)): pos_S(j) = M.index(C[j])."""
    s = [0]*52
    for j in range(52):
        s[msg.index(cipher[j])] = j
    return s


def one_pair(mode, R, keys):
    if mode == 'ctr':
        nonce = list(range(39))
        R.shuffle(nonce)
        r = R.randrange(13)
        s1, s2 = R.sample(range(3), 2)   # swap within C/H/S only (the nonce has no diamonds)
        t = tau_swap(13*s1 + r, 13*s2 + r)
        nonce2 = app(t, nonce)
        i = R.randrange(10**6)
        msg = list(range(52))
        R.shuffle(msg)                   # known plaintext block
        c1 = dd.compose(msg, dd.encrypt_keys(dd.counter_deck(nonce, i), keys))
        c2 = dd.compose(msg, dd.encrypt_keys(dd.counter_deck(nonce2, i), keys))
        return ks(msg, c2) == app(t, ks(msg, c1)), None
    msg = list(range(52))
    R.shuffle(msg)
    if mode == 'attack':
        r = R.randrange(13)
        s1, s2 = R.sample(range(4), 2)
        t = tau_swap(13*s1 + r, 13*s2 + r)
    else:  # control: two cards of different rank
        while True:
            x, y = R.sample(range(52), 2)
            if dd.rank(x) != dd.rank(y):
                break
        t = tau_swap(x, y)
    c1 = dd.encrypt_keys(msg, keys)
    c2 = dd.encrypt_keys(app(t, msg), keys)
    return c2 == app(t, c1), msg


def run_key(args):
    k, npairs, mode = args
    R = random.Random(777 + 31*k + 1000*MODES.index(mode))
    K = list(range(52))
    R.shuffle(K)
    keys = dd.expand_keys(K)
    hits = 0
    first = None
    last_msg = None
    for q in range(npairs):
        hit, last_msg = one_pair(mode, R, keys)
        if hit:
            hits += 1
            if first is None:
                first = q + 1
    if last_msg is not None:  # sanity: encrypt_keys == public encrypt
        assert dd.encrypt_keys(last_msg, keys) == dd.encrypt(last_msg, K)
    return k, hits, first


def main():
    npairs = int(sys.argv[1]) if len(sys.argv) > 1 else 1 << 14
    nkeys = int(sys.argv[2]) if len(sys.argv) > 2 else 24
    with Pool(8) as pool:
        for mode in MODES:
            res = pool.map(run_key, [(k, npairs, mode) for k in range(nkeys)])
            succ = sum(1 for _, h, _ in res if h > 0)
            tot = sum(h for _, h, _ in res)
            firsts = sorted(f for _, _, f in res if f)
            median = firsts[len(firsts)//2] if firsts else None
            print(f'[{mode}] keys={nkeys} pairs/key={npairs} queries/key={2*npairs}: '
                  f'success={succ}/{nkeys} total_hits={tot} rate/pair={tot/(nkeys*npairs):.2e} '
                  f'median first-hit pair#={median}', flush=True)


if __name__ == '__main__':
    main()
