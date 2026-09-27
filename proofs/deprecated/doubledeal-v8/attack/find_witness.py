"""Search for a v8 witness: key K, message M with E_K(tau M) = tau E_K(M), tau = KC(12) <-> KD(51).

Writes ../witness_v8.json. Deterministic (seed 20260926); the committed witness took 739 trials.
"""
import json
import random
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import dd_v8 as dd  # noqa: E402
from relabel import app, swap  # noqa: E402

OUT = HERE.parent / "witness_v8.json"


def main():
    tau = swap(12, 51)
    rng = random.Random(20260926)
    key = list(range(52))
    rng.shuffle(key)
    keys = dd.expand_keys(key)
    for trial in range(1, 200000):
        msg = list(range(52))
        rng.shuffle(msg)
        c1 = dd.encrypt_keys(msg, keys)
        c2 = dd.encrypt_keys(app(tau, msg), keys)
        if c2 == app(tau, c1) and c1 != c2:
            assert dd.encrypt(msg, key) == c1
            assert dd.encrypt(app(tau, msg), key) == c2
            w = dict(tau=[12, 51], key=key, message=msg, cipher=c1,
                     message_tau=app(tau, msg), cipher_tau=c2, trials=trial)
            with OUT.open('w') as f:
                json.dump(w, f, indent=1)
            print('found after', trial, 'trials')
            print(json.dumps(w))
            return


if __name__ == '__main__':
    main()
