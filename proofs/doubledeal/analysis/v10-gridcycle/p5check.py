"""Independent Python re-implementation (analysis only) of GridCycle v10, rule 1 (id 33) and rule 2 (id 30),
written from the rule text, and an exact comparison of all 1326 swap spreads per deck against p5sim.
Card c: suit c//13, rank c%13+1. Seats row*13+col, output index == seat. First card at (2,0).
v10:    finger moves to where the card landed; blocked: marker row t, first free seat right of the target
        column (wrapping), marker +1 after use; a full row advances the marker and the next row is tried.
rule 1: ghost finger (next step from the target); blocked by B: row t+suit(B), first free seat scanning right
        from column T.col+rank(B), next rows if full; marker +1.
rule 2: as rule 1 but the scan starts at the target column.
usage: python3 p5check.py [decks]"""
import random, subprocess, sys

def mix(rule, d):
    g = {}; t = 0; f = (2, 0); g[f] = d[0]; seat = f
    for i in range(1, 52):
        p = d[i - 1]
        T = ((f[0] + p // 13) % 4, (f[1] + p % 13 + 1) % 13)
        if T not in g:
            s = T
        elif rule == 0:
            s = None
            while s is None:
                for q in range(13):
                    c = ((T[1] + q) % 13)
                    if (t, c) not in g: s = (t, c); break
                t = (t + 1) % 4
        else:
            B = g[T]; row = (t + B // 13) % 4; c0 = (T[1] + (B % 13 + 1 if rule == 33 else 0)) % 13
            s = next(((row + a) % 4, (c0 + q) % 13) for a in range(4) for q in range(13) if ((row + a) % 4, (c0 + q) % 13) not in g)
            t = (t + 1) % 4
        g[s] = d[i]
        f = s if rule == 0 else T
    return [g[(k // 13, k % 13)] for k in range(52)]

def spreads(rule, d):
    o0 = mix(rule, d); out = []
    for i in range(52):
        for j in range(i + 1, 52):
            e = d[:]; e[i], e[j] = e[j], e[i]; o1 = mix(rule, e)
            out.append(sum(a != b for a, b in zip(o0, o1)))
    return out

n = int(sys.argv[1]) if len(sys.argv) > 1 else 20
rng = random.Random(5)
decks = [rng.sample(range(52), 52) for _ in range(n)]
for rule in (0, 33, 30):
    res = subprocess.run(['./p5sim', 'x', str(rule)], input='\n'.join(' '.join(map(str, d)) for d in decks) + '\n',
                         capture_output=True, text=True, check=True).stdout.split('\n')
    bad = sum(list(map(int, res[k].split())) != spreads(rule, d) for k, d in enumerate(decks))
    print(f'rule {rule}: {n} decks x 1326 swaps, spreads identical to p5sim: {bad == 0} ({bad} decks differ)')
    assert bad == 0
