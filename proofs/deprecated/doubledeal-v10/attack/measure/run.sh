#!/bin/sh
# The v10 measurements cited by ../../README.md (survival_value.log, mechanism.log) live with their
# C sources in proofs/doubledeal/analysis/v10-gridcycle/. This script checks the C model against
# ddport here, then reproduces those two logs in that folder (same commands as its run_all.sh).
# Not part of CI: the full survival run is ~10-20 CPU-minutes. xcheck.py is cheap (and is in CI).
set -e
cd "$(dirname "$0")"
python3 xcheck.py
cd ../../../../doubledeal/analysis/v10-gridcycle
./build.sh
mkdir -p runs
for s in 1 2 3 4; do ./survival value 50000 $s > runs/value_$s.txt & done; wait
python3 agg.py value 10 > survival_value.log
./mechanism 1000000 9 > mechanism.log
