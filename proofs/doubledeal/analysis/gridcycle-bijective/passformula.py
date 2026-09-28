"""Closed-form swap survival of the PassMix family, and PassMix-F hand cost.
Survival of tau = (a b) is AT LEAST  e(e-1)/(52*51),  e = #{steps k : act_k(a) == act_k(b)}  (proved on paper,
README section 4: equal actions at both steps where a and b are controllers => the swap survives, and the controller
order of a uniform deck is a uniform ordering). It would EQUAL that value if Lemma M (survive => equal actions)
held; Lemma M is false in general (lemmaM_small.py) and passmech.c finds rare exceptions at 52 cards, so the
measured survival is the formula plus a small reconvergence term. Step k: hand size n = 51-k after the pop, key size m = k.
usage: python3 passformula.py"""
import random
suit = lambda c: c // 13; rank = lambda c: c % 13 + 1
NAME = lambda c: 'A23456789TJQK'[c % 13] + 'CHSD'[c // 13]
def act_f2(c, k):
    n, m, r, s = 51 - k, k, rank(c), suit(c)
    if r < n: return (r % n, s % m if m else 0)
    return (s % n if n else 0, r % m if m else 0)
def act_m(c, k):
    n, m = 51 - k, k
    return (rank(c) % n if n else 0, suit(c) % m if m else 0)
def table(act, label):
    rows = []
    for a in range(52):
        for b in range(a + 1, 52):
            steps = [k for k in range(52) if act(a, k) == act(b, k)]
            e = len(steps); rows.append((e * (e - 1), a, b, steps))
    rows.sort(reverse=True)
    top = rows[0][0]
    worst = [r for r in rows if r[0] == top]
    hist = {}
    for r in rows: hist[r[0]] = hist.get(r[0], 0) + 1
    mean = sum(r[0] for r in rows) / 1326 / 2652
    print(f'{label}: worst closed-form survival {top}/2652 = 1/{2652/top:.1f} ({len(worst)} pairs, e.g. '
          f'{NAME(worst[0][1])}<->{NAME(worst[0][2])}, equal-action steps {worst[0][3]}); mean over pairs {mean:.3g} (1/{1/mean:.0f})')
    print('   pairs by e(e-1):', ', '.join(f'{k}/2652: {v}' for k, v in sorted(hist.items(), reverse=True)))
    for cls, f in (('same rank', lambda a, b: a % 13 == b % 13), ('same suit', lambda a, b: a // 13 == b // 13),
                   ('other', lambda a, b: a % 13 != b % 13 and a // 13 != b // 13)):
        sel = [r[0] for r in rows if f(r[1], r[2])]
        print(f'   {cls}: max {max(sel)}/2652, mean {sum(sel)/len(sel)/2652:.3g}')
def act_f3(c, k):
    n, m, r, s = 51 - k, k, rank(c), suit(c)
    if r < n: h, g = (r, s) if m >= 4 else (r + 13 * s, 0)
    else: h, g = (s, r) if n >= 4 else (0, r + 13 * s)
    return (h % n if n else 0, g % m if m else 0)
table(act_f2, 'PASSF2 (PassMix-F)')
table(act_f3, 'PASSF3 (PassMix-F + edge rule)')
table(act_m, 'PASSM (no fallback)')
# hand cost of one PassMix-F pass: cards counted off in cuts, and cuts that wrap (amount >= pile size)
rng = random.Random(1); tot = wraps = fall = 0; T = 20000
for _ in range(T):
    d = list(range(52)); rng.shuffle(d)
    for k, c in enumerate(d):          # controller order is a uniform ordering, so a shuffled deck is one
        n, m, r, s = 51 - k, k, rank(c), suit(c)
        if r < n: amt = [(r, n), (s, m)]
        else: amt = [(r, m), (s, n)]; fall += 1
        for x, size in amt:
            if size: tot += x % size; wraps += x >= size and x > 0
cost3 = 0
for _ in range(T):
    d = list(range(52)); rng.shuffle(d)
    for k, c in enumerate(d):
        h, g = act_f3(c, k); cost3 += h + g
print(f'PassMix-F + edge rule: {cost3/T:.0f} cards counted off per pass')
print(f'PassMix-F hand cost per pass (T={T} decks): {tot/T:.0f} cards counted off in cuts ({tot/T/52:.1f} per controller), '
      f'{fall/T:.1f} fallback steps, {wraps/T:.1f} cuts per pass that wrap (count round a pile smaller than the amount)')
