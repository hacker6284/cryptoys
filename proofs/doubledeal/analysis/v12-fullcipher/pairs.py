"""EMPIRICAL / ENUMERATION ONLY (no theorem uses it; see NOTES.md, section 5).
L(m) = max over nonzero D_1..D_m mod 13 and tau of #{eps in {0,1}^m : sum eps_i D_i = tau (mod 13)}.
Exact enumeration (WLOG D_1 = 1 by scaling; checked without WLOG for m <= 4)."""
import itertools
def L(m, wlog=True):
    best = 0
    Ds = itertools.product(range(1, 13), repeat=m-1) if wlog else itertools.product(range(1, 13), repeat=m)
    for D in Ds:
        D = (1,) + D if wlog else D
        cnt = [0]*13
        for e in itertools.product((0, 1), repeat=m):
            cnt[sum(a*b for a, b in zip(e, D)) % 13] += 1
        best = max(best, max(cnt))
    return best
for m in range(1, 7):
    l = L(m); extra = "" if m > 4 else f" (no-WLOG check: {L(m, False)})"
    print(f"m={m}: L={l}/{2**m} = {l/2**m:.4f}; four rows: {(l/2**m)**4:.5f}; two rows: {(l/2**m)**2:.4f}{extra}")
