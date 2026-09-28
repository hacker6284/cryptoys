#!/bin/sh
# Build every C tool of this folder (needs a C compiler only; CC=... to choose it).
# Called by run_all.sh and by each run_phase*.sh.
set -e
cd "$(dirname "$0")"
CC=${CC:-cc}
# binary:source
for t in survival:survival.c variants:variants.c structure:structure.c cycles3:cycles3.c \
         mechanism:mechanism.c round:round.c cand:cand.c p3small:p3small.c \
         p3collide:p3collide.c p3roundtrip:p3roundtrip.c p4sim:p4.c p5sim:p5.c; do
  $CC -O2 -Wall -Wextra -o "${t%%:*}" "${t#*:}"
done
