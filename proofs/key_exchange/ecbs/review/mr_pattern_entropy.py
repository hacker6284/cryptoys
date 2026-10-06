#!/usr/bin/env python3
"""mr_pattern_entropy.py -- exact pattern statistics for C9 from mr_fleets2_results.txt.
'S h w N1 SM SinvM SlogM' lines: over labelled fleets whose union's bounding box is h x w and anchored at (0,0):
N1 = count, SM = sum M, SinvM = sum 1/M, SlogM = sum log2 M.  Each anchored pattern has (11-h)(11-w) translates.
#patterns = sum_hw tr * SinvM;  over ALL labelled fleets F: E[log2 M(T(F))] = sum_hw tr * SlogM / NLAB,
Shannon entropy of the pattern T = log2 NLAB - E[log2 M].  Run: python mr_pattern_entropy.py"""
import math
N = None; npat = 0.0; slog = 0.0; nl = 0
for l in open('mr_fleets2_results.txt'):
    t = l.split()
    if t and t[0] == 'NLAB': N = int(t[1])
    if t and t[0] == 'S':
        h, w, n1 = int(t[1]), int(t[2]), int(t[3]); tr = (11 - h) * (11 - w)
        npat += tr * float(t[5]); slog += tr * float(t[6]); nl += tr * n1
assert nl == N, (nl, N)
print(f"NLAB = {N} (translate-weighted anchored count reproduces NLAB: {nl == N})")
print(f"distinct covered patterns = {npat:.6e} = 2^{math.log2(npat):.4f}   (spec C9 [MC]: ~1.366e10 = 2^33.67)")
print(f"Shannon entropy of the pattern = {math.log2(N) - slog / N:.4f} bits   (spec C9 [MC, 1e5 samples]: ~33.605)")
