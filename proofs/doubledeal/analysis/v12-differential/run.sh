#!/bin/sh
# M6 measurements (EMPIRICAL ONLY; no theorem uses them). Not run by CI.
# Builds into $BUILD (default /tmp/v12-differential); sample files (*.bin, 80 MB each)
# go there too and are not part of the repository. Logs are written to ./logs.
# Timed on the dev box: selftest 2 s, toy 4 min (one core), scan 4 min (4 cores); one, back
# and mitm not timed. Usage: sh run.sh [selftest|toy|one|back|scan|mitm|all]
set -e
cd "$(dirname "$0")"
B=${BUILD:-/tmp/v12-differential}; mkdir -p "$B" logs
for p in selftest diff1 mitm gcval scan1 relkey; do cc -O2 -o "$B/$p" "$p.c"; done
what=${1:-all}
if [ "$what" = selftest ] || [ "$what" = all ]; then "$B/selftest" > logs/selftest.log; fi
if [ "$what" = toy ] || [ "$what" = all ]; then   # MITM estimator check: GridCycle, key, GridCycle
  "$B/gcval" d 0,1 0,1 20000000 1 > logs/gcval_direct_s01.log
  "$B/gcval" d 0,1 0,2 20000000 2 > logs/gcval_direct_s01_s02.log
  "$B/gcval" f 0,1 0,1 10000000 3 "$B/gf.bin"; "$B/gcval" b 0,1 0,1 10000000 4 "$B/gb.bin"
  "$B/mitm" "$B/gf.bin" "$B/gb.bin" "$("$B/relkey" 0,1)" 0 > logs/gcval_mitm_s01.log
fi
run() { "$B/diff1" "$1" 10000000 "$2" "$B/f_$3.bin" > "logs/f_$3.log"; }
runb() { "$B/diff1" "$1" 10000000 "$2" "$B/b_$3.bin" b > "logs/b_$3.log"; }
if [ "$what" = one ] || [ "$what" = all ] || [ "$what" = mitm ]; then
  run 0,1 1 s01 & run 43,46 2 s4346 & run 12,51 3 s1251 & run 0,14 4 s014 & wait
  run 0,1,2 5 c012 & run "0,1;2,3" 6 d0123 & run v10:0,3 7 v03 & run v10:1,0 8 v10 & wait
fi
if [ "$what" = back ] || [ "$what" = all ] || [ "$what" = mitm ]; then
  runb 0,1 101 s01 & runb 43,46 102 s4346 & runb 0,2 103 s02 & runb 13,14 104 s1314 & wait
  runb 1,2 105 s12 & runb 0,1,2 106 c012 & runb "0,1;2,3" 107 d0123 & wait
fi
if [ "$what" = scan ] || [ "$what" = all ]; then
  for p in 0 1 2 3; do "$B/scan1" $p 4 1000000 42 > "$B/scan1_$p.log" & done; wait
  sort -n -k1,1 -k2,2 "$B"/scan1_?.log > logs/scan1.log
fi
if [ "$what" = mitm ] || [ "$what" = all ]; then
  k() { "$B/relkey" "$1"; }
  : > logs/mitm.log
  m() { echo "== $1 -> $2" >> logs/mitm.log; "$B/mitm" "$B/f_$3.bin" "$B/b_$4.bin" "$(k "$1")" "$(k "$2")" >> logs/mitm.log; }
  m 0,1 0,1 s01 s01; m 0,1 0,2 s01 s02; m 0,1 1,2 s01 s12; m 0,1 13,14 s01 s1314
  m 43,46 43,46 s4346 s4346; m 0,1,2 0,1,2 c012 c012; m 0,1,2 0,1 c012 s01
  m 0,1 0,1,2 s01 c012; m "0,1;2,3" "0,1;2,3" d0123 d0123; m 0,1 "0,1;2,3" s01 d0123
fi
