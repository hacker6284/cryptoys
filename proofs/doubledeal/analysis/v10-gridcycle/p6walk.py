"""Table walkthrough of Phase 6 variant B (62): ghost finger, blocker sends you, blocker nudges the finger.
Prints the encryption steps (with blocked placements spelled out) and the decryption of the same table.
usage: python3 p6walk.py [seed] [steps]"""
import random, sys
R = 'A23456789TJQK'; S = 'CHSD'; nm = lambda c: R[c % 13] + S[c // 13]
seat = lambda s: f'r{s[0]}c{s[1]:<2d}'
seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1; STEPS = int(sys.argv[2]) if len(sys.argv) > 2 else 20
rng = random.Random(seed); d = rng.sample(range(52), 52)

def scan(taken, row, c0):
    for a in range(4):
        for q in range(13):
            s = ((row + a) % 4, (c0 + q) % 13)
            if s not in taken: return s, a * 13 + q + 1

print(f'deck (first {STEPS}): ' + ' '.join(nm(c) for c in d[:STEPS]))
print('ENCRYPT  (finger f, marker t; step of a card = +suit rows (C0 H1 S2 D3), +rank columns, mod 4 / mod 13)')
g = {(2, 0): d[0]}; f = (2, 0); t = 0; logE = [f' 0 {nm(d[0])} -> {seat((2,0))} (start seat)']
for i in range(1, 52):
    p = d[i - 1]; T = ((f[0] + p // 13) % 4, (f[1] + p % 13 + 1) % 13)
    if T not in g:
        g[T] = d[i]; line = f'{i:2d} {nm(d[i])}: f {seat(f)} + {nm(p)} -> target {seat(T)} free -> sits there; finger {seat(T)}'; f = T
    else:
        B = g[T]; row = (t + B // 13) % 4; c0 = (T[1] + B % 13 + 1) % 13; s, k = scan(g, row, c0)
        nf = ((T[0] + B // 13) % 4, c0)
        line = (f'{i:2d} {nm(d[i])}: f {seat(f)} + {nm(p)} -> target {seat(T)} TAKEN by {nm(B)}; scan row t{t}+{S[B//13]}={row} from col '
                f'{T[1]}+{B%13+1}={c0} -> {seat(s)} ({k} seat{"s" if k>1 else ""} checked); marker {t}->{(t+1)%4}; '
                f'NUDGE: finger = target + {nm(B)} = {seat(nf)}')
        g[s] = d[i]; t = (t + 1) % 4; f = nf
    logE.append(line)
print('\n'.join(logE[:STEPS]))
out = [g[(k // 13, k % 13)] for k in range(52)]
print('table (rows 0..3):'); [print('  r%d ' % r + ' '.join(f'{nm(out[r*13+c]):>3}' for c in range(13))) for r in range(4)]
print('DECRYPT  (reads the table; ticks off seats as it goes; the same finger/marker bookkeeping)')
G = {(k // 13, k % 13): out[k] for k in range(52)}; seen = {(2, 0)}; hand = [G[(2, 0)]]; f = (2, 0); t = 0
logD = [f' 0 start seat {seat((2,0))} holds {nm(hand[0])}']
for i in range(1, 52):
    p = hand[-1]; T = ((f[0] + p // 13) % 4, (f[1] + p % 13 + 1) % 13)
    if T not in seen:
        s = T; line = f'{i:2d} f {seat(f)} + {nm(p)} -> {seat(T)} not ticked -> card {nm(G[s])}; finger {seat(T)}'; f = T
    else:
        B = G[T]; row = (t + B // 13) % 4; c0 = (T[1] + B % 13 + 1) % 13; s, k = scan(seen, row, c0)
        nf = ((T[0] + B // 13) % 4, c0)
        line = (f'{i:2d} f {seat(f)} + {nm(p)} -> {seat(T)} already ticked (blocker {nm(B)}): scan row {row} from col {c0} over UNticked seats '
                f'-> {seat(s)} = {nm(G[s])}; marker {t}->{(t+1)%4}; finger {seat(nf)}')
        t = (t + 1) % 4; f = nf
    seen.add(s); hand.append(G[s]); logD.append(line)
print('\n'.join(logD[:STEPS]))
print('decrypted deck equals the original:', hand == d)
assert hand == d
