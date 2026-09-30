#!/bin/sh
# Reproduce every number in README.md. Not part of CI (about 20-30 CPU-minutes on 8 cores).
set -e
cd "$(dirname "$0")"
./build.sh
python3 xcheck.py                      # C model == repo Python port (ddport, checked in CI against vectors)
python3 candcheck.py > candcheck.log   # cand.c stem/GC, variants.c walkv(V=0) (used by round.c) and gc_mix == ddport
mkdir -p runs
for s in 1 2 3 4; do ./survival value 50000 $s > runs/value_$s.txt & ./survival pos 50000 $((s+100)) > runs/pos_$s.txt & done; wait
python3 agg.py value 10 > survival_value.log; python3 agg.py pos 20 > survival_pos.log
./structure 200000 3 > structure.log
./mechanism 1000000 9 > mechanism.log
./cycles3 400 5 100000 > cycles3.log
for v in 1 2 3 5 6 9 10 11; do ./variants $v value 20000 11 > runs/var$v.txt & done; wait
./variants 7 value 20000 11 > runs/var7.txt & ./variants 8 value 20000 11 > runs/var8.txt &
for s in 31 32 33; do ./variants 7 value 20000 $s > runs/var7_$s.txt & ./variants 8 value 20000 $s > runs/var8_$s.txt & done; wait
{ for v in 1 2 3 5 6 9 10 11; do python3 aggm.py V$v runs/var$v.txt; done
  python3 aggm.py V7 runs/var7.txt runs/var7_*.txt; python3 aggm.py V8 runs/var8.txt runs/var8_*.txt
  python3 aggm.py V0=v10 runs/value_*.txt; } > variants_value.log
for v in 0 2 5 7 8 11; do ./round $v 400000 21 > runs/round_v$v.txt & done; wait
python3 aggr.py runs/round_v*.txt > round.log
for v in 0 1 2 3 5 6 7 8 9 10 11; do ./variants $v stats 100000 7; done > variants_cost.log
