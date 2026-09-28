#!/bin/sh
# Reproduce PHASE6.md (anti-resync tweaks to rule 1: variants 60-64). Not part of CI; about 45 minutes on 8 cores.
# Baseline survival numbers for v10 / rule 1 / rule 2 are the Phase 2 logs (same cand.c code path, unchanged).
set -e
cd "$(dirname "$0")"
mkdir -p p6
DDPORT_DIR=${DDPORT_DIR:-../../security/checks} python3 candcheck.py > p6/candcheck.log
cc -O2 -Wall -Wextra -o cand cand.c
cc -O2 -Wall -Wextra -o p3small p3small.c
cc -O2 -Wall -Wextra -o p5sim p5.c
# 1. invertibility: small grids (exhaustive), 100k round trip (cand stats), independent Python enc/dec
for rc in "2 3" "3 2" "2 4" "4 2" "3 3"; do for v in 0 33 60 61 62 63 64; do ./p3small $rc $v; done; done > p6/small_injectivity.log
for v in 0 30 33 60 61 62 63 64; do ./cand $v stats 100000 7; done > p6/cost.log
python3 p6check.py 2000 > p6/check.log
python3 p6walk.py 1 16 > p6/walkthrough.log
# 2. survival (as PHASE2)
for v in 60 61 62 63 64; do ./cand $v value 3000 1 > p6/scr_$v.txt & done; wait
for v in 60 61 62 63 64; do for s in 1 2 3 4 5 6 7 8; do ./cand $v value 25000 $((s+1000)) > p6/full_${v}_$s.txt & done; wait; done
for v in 60 61 62 63 64; do python3 aggm.py V$v p6/full_${v}_*.txt; done > p6/full_summary.log
for v in 60 61 62 63 64; do ./cand $v cyc3 4000 9 200000 > p6/cyc3_$v.log & done
for v in 60 61 62 63 64; do for s in 1 2; do ./cand $v round 200000 $((s+50)) > p6/round_${v}_$s.txt & done; done; wait
for v in 60 61 62 63 64; do python3 round2agg.py $v p6/round_${v}_*.txt; done > p6/round_summary.log
for f in p2/cyc3b_33.log p2/cyc3b_30.log p6/cyc3_6*.log; do printf "%s: " $f; sed -n 2,11p $f |
  awk '{split($7,a,"/"); if(a[1]+0>m){m=a[1]+0; c=$1" "$2" "$3}} END{printf "refined max %d/200000=%.1e %s\n", m, m/200000, c}'; done > p6/cyc3_summary.log
# 3. spread (as PHASE5), baselines rerun with the same binary
for v in 0 33 30 60 61 62 63 64; do ./p5sim dist $v 20000 11 > p6/dist_$v.log & done; wait
for v in 0 33 30 60 61 62 63 64; do ./p5sim cyc3 $v 2000000 12 > p6/spcyc3_$v.log & done; wait
for v in 0 33 30 60 61 62 63 64; do ./p5sim climb $v 20 20000 8 31 17 > p6/climbfar_$v.log & done; wait
for v in 0 33 30 60 61 62 63 64; do ./p5sim merge $v 2000 14 > p6/merge_$v.log & done; wait
grep -h RESULT p6/climbfar_*.log > p6/climbsummary.log
