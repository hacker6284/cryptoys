#!/bin/sh
# Reproduce PHASE4.md ("C sends itself" variants 50-53). Not part of CI; about a minute.
set -e
cd "$(dirname "$0")"
mkdir -p p4
./build.sh
for rc in "2 3" "3 2" "2 4" "4 2" "3 3"; do for v in 0 33 50 51 52 53; do ./p3small $rc $v; done; done > p4/small_injectivity.log
for v in 50 51 52 53; do ./p4sim $v collide 2000 7 > p4/collide_$v.log & done; wait
python3 p4trace.py > p4/trace.log
for v in 50 51 52 53; do ./p4sim $v decrypt 100000 5; done > p4/decrypt.log
for v in 50 51 52 53; do ./p4sim $v decrypt 10000 9 100000000 > p4/count$v.log; done
for v in 50 51 52 53; do printf "V%s " $v; grep '^deck' p4/count$v.log | awk '{print $4}' | sort -n |
  awk '{a[NR]=$1; s+=log($1)} END{print "decks="NR, "min="a[1], "median="a[int(NR/2)+1], "p90="a[int(NR*0.9)], "max="a[NR], "geomean=" exp(s/NR)}'; done > p4/count_summary.log
