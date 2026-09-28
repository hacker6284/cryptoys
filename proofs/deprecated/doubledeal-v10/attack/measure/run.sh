#!/bin/sh
# The v10 measurements cited by ../../README.md (survival_value.log, mechanism.log) live with their
# C sources in proofs/doubledeal/analysis/v10-gridcycle/. This script runs that folder's xcheck.py
# (C model == ddport v10 on 2000 decks; cheap, and in CI), then reproduces those two logs there
# (same commands as its run_all.sh). Not part of CI: the full survival run is ~10-20 CPU-minutes.
set -e
cd "$(dirname "$0")/../../../../doubledeal/analysis/v10-gridcycle"
python3 xcheck.py
./build.sh
mkdir -p runs
for s in 1 2 3 4; do ./survival value 50000 $s > runs/value_$s.txt & done; wait
python3 agg.py value 10 > survival_value.log
./mechanism 1000000 9 > mechanism.log
