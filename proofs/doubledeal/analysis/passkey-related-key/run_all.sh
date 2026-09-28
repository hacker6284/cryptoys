#!/usr/bin/env bash
# Reproduces every log in logs/ (each log starts with its producing command). ~20 min on 8 cores.
set -euo pipefail
cd "$(dirname "$0")"
gcc -O2 -Wall -Wextra -o vec vec.c
gcc -O2 -fopenmp -Wall -Wextra -o keysched keysched.c -lm
gcc -O2 -fopenmp -Wall -Wextra -o rk rk.c -lm
run() { local log=$1; shift; { echo "$ $*"; "$@"; } > "logs/$log" 2>&1; echo "wrote logs/$log"; }
COLL="1,13 14,26 27,39 2,14 2,26 15,27 15,39 28,40 3,15 3,27 3,39 16,28 16,40 29,41 4,16 4,28 4,40 17,29 17,41 30,42 5,17 5,29 5,41 18,30 18,42 31,43 6,18 6,30 6,42 19,31 19,43 32,44 7,19 7,31 7,43 20,32 20,44 33,45 8,20 8,32 8,44 21,33 21,45 34,46 9,21 9,33 9,45 22,34 22,46 35,47 10,22 10,34 10,46 23,35 23,47 36,48 11,23 11,35 11,47 24,36 24,48 37,49 12,24 12,36 12,48 25,37 25,49 38,50"
run xcheck.log python3 xcheck.py 300
run colliders.log python3 colliders.py
run pass.log ./keysched pass 50000 11
run sched_top.log ./keysched sched 5000000 12 14,26 1,13 27,39 2,14 38,50
run sched_all68.log ./keysched sched 500000 13 $COLL
run rk_main.log ./rk 10000000 14 14,26
run rk_more.log ./rk 2000000 15 1,13 27,39 12,24 38,50 50,51 38,51 0,51
gcc -O2 -fopenmp -Wall -Wextra -o readings readings.c -lm
run readings.log ./readings 20000 21
run readings_exact.log python3 readings_exact.py
