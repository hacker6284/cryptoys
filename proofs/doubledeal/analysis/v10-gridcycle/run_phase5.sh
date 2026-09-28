#!/bin/sh
# Reproduce PHASE5.md (swap spread / diffusion of GridCycle alone). Not part of CI; about 5 minutes on 12 cores.
set -e
cd "$(dirname "$0")"
mkdir -p p5
./build.sh
python3 p5check.py 20 > p5/check.log
for v in 0 33 30; do (./p5sim dist $v 20000 11 > p5/dist_$v.log; ./p5sim cyc3 $v 2000000 12 > p5/cyc3_$v.log) & done
for v in 0 33 30; do for k in 1 3 5 10; do ./p5sim climb $v $k 20000 8 2$k > p5/climb_${v}_k$k.log & done; done
./p5sim ideal 2000000 13 > p5/ideal.log
wait
for v in 0 33 30; do ./p5sim merge $v 2000 14; done > p5/merge.log
for v in 0 33 30; do ./p5sim climb $v 20 20000 8 31 17 > p5/climbfar_$v.log & done; wait
grep -h RESULT p5/climb_*.log p5/climbfar_*.log > p5/climbsummary.log
