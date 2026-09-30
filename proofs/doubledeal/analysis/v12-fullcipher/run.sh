#!/bin/sh
# M7 measurements (EMPIRICAL ONLY; no theorem uses them). Not run by CI.
# Builds into $BUILD (default /tmp/v12-fullcipher); no binaries in the repository.
# Logs are written to ./logs. Timed on the dev box: final 1 min, mixfinal ~8 min (4 cores).
# Usage: sh run.sh [final|mixfinal|all]
set -e
cd "$(dirname "$0")"
B=${BUILD:-/tmp/v12-fullcipher}; mkdir -p "$B" logs
for p in final1 mixfinal; do cc -O2 -Wall -Wextra -o "$B/$p" "$p.c"; done
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
