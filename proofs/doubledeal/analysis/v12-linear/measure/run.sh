#!/bin/sh
# M8b measurements for the note (../NOTES.md, "M8b measurements"). EMPIRICAL (sampled) or
# SCRIPT-COMPUTED; NONE of these is a proof, and no theorem uses them. Not run by CI
# (checks/selftest.py reruns only stem_sign_dp.py --small, byte-compared with its log).
# Builds into $BUILD (default /tmp/v12-linear-measure); logs go to ./logs.
# Timed on the dev box (one core each; about 12 min in all): first_order ~1m40s per seed
# (seeds 1, 2, 3), sign_layers ~4m, stem_sign_check ~5 s, stem_turn_dump +
# stem_turn_model_check ~5 s (the dump, ~26 MB, stays in $BUILD), stem_sign_dp ~2m20s
# (its --small check ~2 s), stem_turn_dp_check ~5 s.
# Usage: sh run.sh [first|sign|stem|all]
set -e
cd "$(dirname "$0")"
B=${BUILD:-/tmp/v12-linear-measure}; mkdir -p "$B" logs
for p in first_order sign_layers stem_sign_check stem_turn_dump; do
  cc -O2 -o "$B/$p" "$p.c" -lm
done
what=${1:-all}
if [ "$what" = first ] || [ "$what" = all ]; then
  "$B/first_order" 50000000 1 > logs/first_order.log
  "$B/first_order" 50000000 2 > logs/first_order_seed2.log
  "$B/first_order" 50000000 3 > logs/first_order_seed3.log
fi
if [ "$what" = sign ] || [ "$what" = all ]; then
  "$B/sign_layers" 100000000 2 > logs/sign_layers.log
fi
if [ "$what" = stem ] || [ "$what" = all ]; then
  "$B/stem_sign_check" 4000000 > logs/stem_sign_check.log
  "$B/stem_turn_dump" 200000 > "$B/stem_turns.txt"
  python3 stem_turn_model_check.py "$B/stem_turns.txt" > logs/stem_turn_model_check.log
  python3 stem_turn_dp_check.py > logs/stem_turn_dp_check.log
  python3 stem_sign_dp.py --small > logs/stem_sign_dp_small.log
  python3 stem_sign_dp.py > logs/stem_sign_dp.log
fi
