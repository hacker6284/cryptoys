#!/bin/sh
# B1 measurements for the v10Sym rows and columns of the one-round (mix round) difference table.
# EMPIRICAL ONLY; no theorem uses them. Not run by CI. Uses ../v12-differential/diff1.c (modes
# r, k, c); builds into $BUILD (default /tmp/v12-dp1).
# Usage: sh run.sh [N] [JOBS]   (defaults N = 20000000 samples per run, JOBS = 6 parallel runs)
set -e
cd "$(dirname "$0")"
B=${BUILD:-/tmp/v12-dp1}; mkdir -p "$B" logs
N=${1:-20000000}; J=${2:-6}
cc -O2 -o "$B/diff1" ../v12-differential/diff1.c
: > "$B/jobs.txt"
for a in 0 1 2 3 4 5 6 7 8 9 10 11 12; do for x in 0 1 2 3; do
  [ "$a$x" = "00" ] && continue
  echo "v10:$a,$x $N $((1000 + 4 * a + x)) r row_${a}_${x}" >> "$B/jobs.txt"
  echo "v10:$a,$x $N $((2000 + 4 * a + x)) c col_${a}_${x}" >> "$B/jobs.txt"
done; done
echo "v10:0,3 $((N / 10)) 3003 k kcks_0_3" >> "$B/jobs.txt"
xargs -P "$J" -L 1 sh -c '"$0" "$1" "$2" "$3" - "$4" > "$0.$5.log"' "$B/diff1" < "$B/jobs.txt"
cat "$B"/diff1.row_*.log > logs/rows.log; cat "$B"/diff1.col_*.log > logs/cols.log
cp "$B/diff1.kcks_0_3.log" logs/kcks_0_3.log
( "$B/diff1" 0,1 $((N / 10)) 7 - r; "$B/diff1" 0,1 $((N / 10)) 8 - c ) > logs/control_swap01.log   # positive control
