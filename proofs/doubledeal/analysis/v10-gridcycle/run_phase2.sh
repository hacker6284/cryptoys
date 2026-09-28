#!/bin/sh
# Reproduce PHASE2.md. Not part of CI (roughly 1 CPU-hour on 8 cores).
set -e
cd "$(dirname "$0")"
./build.sh
python3 candcheck.py
mkdir -p p2
for v in 0 20 21 22 23 24 25 26 27 28 29 30 31 33 35; do ./cand $v value 3000 1 > p2/scr_$v.txt & done; wait
for f in p2/scr_*.txt; do v=${f#p2/scr_}; v=${v%.txt}; python3 aggm.py V$v $f | head -1; done > p2/screen_summary.log
for v in 30 31 33; do for s in 1 2 3 4 5 6 7 8; do ./cand $v value 25000 $((s+1000)) > p2/full_${v}_$s.txt & done; wait; done
for v in 30 31 33; do python3 aggm.py V$v p2/full_${v}_*.txt; done > p2/full_summary.log
for v in 30 31 33; do ./cand $v cyc3 400 5 100000 > p2/cyc3_$v.log & done; wait
for v in 30 33; do ./cand $v cyc3 4000 9 200000 > p2/cyc3b_$v.log & done; wait
for v in 30 31 33; do for s in 1 2; do ./cand $v round 200000 $((s+50)) > p2/round_${v}_$s.txt & done; done; wait
for v in 30 31 33; do python3 round2agg.py $v p2/round_${v}_*.txt; done > p2/round_summary.log
for v in 0 7 20 22 23 26 28 30 31 33 35; do ./cand $v stats 100000 7; done > p2/cost.log
./cand 33 gap 3000 3 > p2/gap_33.log; ./cand 0 gap 1000 3 > p2/gap_0.log
