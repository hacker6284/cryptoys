#!/bin/sh
# M7 measurements (EMPIRICAL ONLY; no theorem uses them). Not run by CI.
# Builds into $BUILD (default /tmp/v12-fullcipher); no binaries in the repository.
# Logs are written to ./logs. Timed on the dev box: final 1 min, mixfinal ~11 min and
# scoping ~4 min (4 and 8 cores), coupling ~13 min (one core; section 5 of NOTES.md).
# Usage: sh run.sh [final|mixfinal|scoping|coupling|all]
set -e
cd "$(dirname "$0")"
B=${BUILD:-/tmp/v12-fullcipher}; mkdir -p "$B" logs
for p in final1 mixfinal rowmax; do cc -O2 -Wall -Wextra -o "$B/$p" "$p.c"; done
what=${1:-all}
if [ "$what" = final ] || [ "$what" = all ]; then   # final no-mix round alone, 10^6 decks
  : > logs/final1.log
  for s in 0,1 43,46 12,51 0,14 0,1,2 "0,1;2,3" v10:1,0 v10:0,1; do
    "$B/final1" "$s" 1000000 1 >> logs/final1.log
  done
fi
mf() { for i in $2; do printf 'seed %s: ' "$i"; "$B/mixfinal" "$1" 25000000 "$i"; done > "$B/mf_$3.log"; }
if [ "$what" = mixfinal ] || [ "$what" = all ]; then   # one mix round + final round
  mf 0,1 "101 102 103 104" a & mf 0,1 "105 106 107 108" b &
  mf 43,46 "111 112 113 114" c & mf 43,46 "115 116 117 118" d & wait
  cat "$B"/mf_a.log "$B"/mf_b.log "$B"/mf_c.log "$B"/mf_d.log > logs/mixfinal.log
fi
if [ "$what" = scoping ] || [ "$what" = all ]; then   # the M7 scoping run of 5♦↔8♦
  for i in 101 102 103 104 105 106 107 108; do
    ( printf 'seed %s: ' "$i"; "$B/mixfinal" 43,46 25000000 "$i" ) > "$B/sc_$i.log" &
  done; wait
  for i in 101 102 103 104 105 106 107 108; do cat "$B/sc_$i.log"; done > logs/mixfinal_scoping.log
fi
if [ "$what" = coupling ] || [ "$what" = all ]; then   # section 5: coupling constants
  "$B/rowmax" > logs/rowmax.log
  python3 pairs.py > logs/pairs.log
  python3 qtype.py > logs/qtype.log
  python3 pairs5.py > logs/pairs5.log
  python3 union_crude.py > logs/union_crude.log
fi
