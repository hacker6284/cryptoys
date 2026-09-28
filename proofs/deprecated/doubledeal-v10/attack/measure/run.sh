#!/bin/sh
# Reproduce survival_value.log and mechanism.log (copied from the GridCycle analysis,
# branch doubledeal-gridcycle-analysis, proofs/doubledeal/analysis/v10-gridcycle/).
# Not part of CI: the full survival run is ~10-20 CPU-minutes. xcheck.py is cheap.
set -e
cd "$(dirname "$0")"
CC=${CC:-cc}
for p in survival mechanism; do $CC -O2 -Wall -o $p $p.c; done
python3 xcheck.py                 # C model == ddport v10 mix_columns on 2000 random decks
mkdir -p runs
for s in 1 2 3 4; do ./survival value 50000 $s > runs/value_$s.txt & done; wait
python3 agg.py value 10 > survival_value.log
./mechanism 1000000 9 > mechanism.log
