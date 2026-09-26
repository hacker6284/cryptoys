"""Search for a v8 witness: key K, message M with E_K(tau M) = tau E_K(M), tau = KC(12) <-> KD(51)."""
import random, sys, json; sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__))); import dd_v8 as dd
tau = list(range(52)); tau[12], tau[51] = 51, 12
app = lambda t, D: [t[c] for c in D]
R = random.Random(20260926)
K = list(range(52)); R.shuffle(K); keys = dd.expand_keys(K)
for trial in range(1, 200000):
    M = list(range(52)); R.shuffle(M)
    C = dd.encrypt_keys(M, keys); C2 = dd.encrypt_keys(app(tau, M), keys)
    if C2 == app(tau, C) and C != C2:
        assert dd.encrypt(M, K) == C and dd.encrypt(app(tau, M), K) == C2
        w = dict(tau=[12, 51], key=K, message=M, cipher=C, message_tau=app(tau, M), cipher_tau=C2, trials=trial)
        json.dump(w, open(__import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)), '..', 'witness_v8.json'), 'w'), indent=1); print('found after', trial, 'trials'); print(json.dumps(w)); break
