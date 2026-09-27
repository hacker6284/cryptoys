"""Shared harness for the branch-number measurements (analysis only).

Layers are deck -> deck functions on the v8/v9 ports in ../ddport.py:
  GC  = GridCycle (mix_columns) alone
  SR  = SumRanks alone, lay_cm -> sum_ranks -> scoop_cm (positions = column-major seats)
  SRGC= GridCycle o ShiftRows o SumRanks  (the unkeyed full round; ShiftRows is a fixed
        seat permutation so it does not change weights, but it does change which seats meet)
  SRGC_noSh = GridCycle o SumRanks (literally "SumRanks followed by GridCycle", no ShiftRows)
  RK  = full round with a fixed key = Compose(GC(ShiftRows(SR(m))), K)
Weight of a difference between two decks = number of positions where they differ.
"""
import sys, random
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import ddport as P          # ddport puts the frozen v8 attack dir (dd_v8) on sys.path
from dd_v8 import lay_cm, scoop_cm

FIXED_KEY_SEED = 20260927
_kr = random.Random(FIXED_KEY_SEED)
FIXED_KEY = list(range(52)); _kr.shuffle(FIXED_KEY)

def GC(v): return lambda d: P.mix_columns(d, v)
def SR(v): return lambda d: scoop_cm(P.sum_ranks(lay_cm(d), v))
def SRGC(v): return lambda d: P.mix_columns(P.stem(d, v), v)
def SRGC_noSh(v): return lambda d: P.mix_columns(scoop_cm(P.sum_ranks(lay_cm(d), v)), v)
def RK(v, k=FIXED_KEY): return lambda d: P.full_round(d, k, v)

LAYERS = {'GC': GC, 'SR': SR, 'SRGC': SRGC, 'SRGC_noSh': SRGC_noSh, 'RK': RK}

def wt(a, b): return sum(x != y for x, y in zip(a, b))
def swap(d, i, j):
    e = list(d); e[i], e[j] = e[j], e[i]; return e
def rdeck(rng):
    d = list(range(52)); rng.shuffle(d); return d
NAMES = [r + s for s in 'CHSD' for r in 'A23456789TJQK']
def show(d): return ' '.join(NAMES[c] for c in d)
