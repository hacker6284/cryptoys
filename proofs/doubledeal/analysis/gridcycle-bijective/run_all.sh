#!/bin/sh
# Reproduces every log in logs/ (about 60-70 minutes wall clock on 8 cores; the pass layers dominate).
# All runs are seeded, so output does not depend on thread count. Needs a checkout of the doubledeal-v11 port
# for xcheck.py:
#   mkdir -p /tmp/v11tree && git archive origin/doubledeal-v11 proofs/doubledeal/security/checks \
#       proofs/deprecated/doubledeal-v8/attack | tar -x -C /tmp/v11tree
set -e
cd "$(dirname "$0")"
CC="gcc -O2 -fopenmp -Wall -Wextra"
$CC -o measure measure.c -lm; $CC -o passmech passmech.c -lm; $CC -o stemvec stemvec.c
V11TREE=${V11TREE:-/tmp/v11tree}
run() { log=$1; shift; { echo "\$ $*"; "$@"; } > "logs/$log.log" 2>&1; }
runa() { log=$1; shift; { echo "\$ $*"; "$@"; } >> "logs/$log.log" 2>&1; }
ALL="0 1 2 3 4 5 6 7 8 9 10 11 12 13"
run xcheck python3 xcheck.py "$V11TREE" 1000
: > logs/check.log;  for L in $ALL; do runa check ./measure check $L 100000 1; done
: > logs/sym.log;    for L in $ALL; do runa sym ./measure sym $L 20 1; done
: > logs/spread.log; for L in 0 1 2 3 5 6 9 10 11 12 13; do runa spread ./measure spread $L 20000 2; done
: > logs/surv.log;   for L in 0 1 2 3 11 5 6 9 10 12 13; do runa surv ./measure surv $L 50000 3; done
: > logs/surv_extra.log; for L in 4 7 8; do runa surv_extra ./measure surv $L 5000 3; done
: > logs/round.log;  for L in 0 11 10 12 13; do runa round ./measure round $L 50000 4; done
: > logs/passmech.log; for V in 10 6 13; do runa passmech ./passmech $V 50000 5; done
# one-round refinements: the SumRanks-worst same-suit pair AS<->JS and v11's sampled one-round top pair 5H<->KH
: > logs/round_pairs.log
for L in 0 10 13; do runa round_pairs ./measure pair $L 2000000 6 26 36 1; runa round_pairs ./measure pair $L 2000000 6 17 25 1; done
# layer-alone refinements of sampled worst pairs (max-of-1326 estimates are inflated by noise)
: > logs/surv_pairs.log
runa surv_pairs ./measure pair 0 1000000 7 5 12 0
runa surv_pairs ./measure pair 10 1000000 7 5 44 0
runa surv_pairs ./measure pair 11 1000000 7 31 44 0
runa surv_pairs ./measure pair 12 1000000 7 9 35 0
run lemmaM_small python3 lemmaM_small.py 7 30 1
run passwalk python3 passwalk.py 1
run passformula python3 passformula.py
