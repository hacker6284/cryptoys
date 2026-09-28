#!/bin/sh
# Build the C tools (needs a C compiler only).
set -e
cd "$(dirname "$0")"
CC=${CC:-cc}
for p in survival variants structure cycles3 mechanism round; do $CC -O2 -Wall -Wextra -o $p $p.c; done
