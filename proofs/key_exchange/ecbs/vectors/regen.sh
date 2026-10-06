#!/usr/bin/env bash
# Rebuild (or --check) the ECBS known-answer vectors: a wrapper for
# proofs/key_exchange/vectors_regen.sh ecbs (see there).
#   proofs/key_exchange/ecbs/vectors/regen.sh [--check]
exec "$(dirname "$0")/../../vectors_regen.sh" ecbs "$@"
