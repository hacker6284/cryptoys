#!/bin/sh
# Reproduce PHASE3.md (bump variants). Not part of CI; about a minute.
set -e
cd "$(dirname "$0")"
mkdir -p p3
for p in p3small p3collide p3roundtrip; do cc -O2 -Wall -Wextra -o $p $p.c; done
for rc in "2 3" "3 2" "2 4" "4 2" "3 3"; do for v in 0 33 40 41 42 43 45 46 47 48; do ./p3small $rc $v; done; done > p3/small_injectivity.log
for v in 40 41 42 43; do ./p3collide $v 2000 51 7 > p3/collide_$v.log & done; wait
python3 p3trace.py > p3/trace.log
for v in 40 41 42 43; do ./p3roundtrip $v 100000 5; done > p3/roundtrip.log
