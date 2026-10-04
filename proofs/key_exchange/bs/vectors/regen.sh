#!/usr/bin/env bash
# Rebuild (or --check) the BS known-answer vectors: a wrapper for
# proofs/key_exchange/vectors_regen.sh bs (see there).
#   proofs/key_exchange/bs/vectors/regen.sh [--check]
exec "$(dirname "$0")/../../vectors_regen.sh" bs "$@"
