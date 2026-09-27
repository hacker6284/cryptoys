#!/usr/bin/env bash
# FROZEN DoubleDeal v9 (deprecated): rebuild doubledeal_v9_vectors.json from
# primitives/cipher/doubledeal/v9/doubledeal_v9.sudo via the sudoc JS target at
# the same pin as proofs/doubledeal/vectors/regen.sh. With --check, regenerate to
# a temp file and fail unless it is byte-identical to the committed JSON.
#
# Usage: proofs/deprecated/doubledeal-v9/vectors/regen_v9.sh [--check]
#   SUDOC=/path/to/sudoc   (optional; otherwise $SUDOCODE_DIR/sudoc/target/release/sudoc)
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../../../.." && pwd)"
VEC="$ROOT/proofs/deprecated/doubledeal-v9/vectors"
SUDO="$ROOT/primitives/cipher/doubledeal/v9/doubledeal_v9.sudo"
SUDOCODE_COMMIT="${SUDOCODE_COMMIT:-606f06f4d852aac7f37bccd4823775d00d2ba5a6}"
SUDOCODE_DIR="${SUDOCODE_DIR:-/tmp/sudocode}"
SUDOC_BIN="${SUDOC:-$SUDOCODE_DIR/sudoc/target/release/sudoc}"

check=0
[[ "${1:-}" == "--check" ]] && check=1

DOUBLEDEAL_SUDO_SHA256="$(sha256sum "$SUDO" | awk '{print $1}')"
DOUBLEDEAL_SUDO="$SUDO"
export DOUBLEDEAL_SUDO DOUBLEDEAL_SUDO_SHA256 SUDOCODE_COMMIT

OUT="$(mktemp -d)"
trap 'rm -rf "$OUT"' EXIT
"$SUDOC_BIN" build --target js --tests -o "$OUT/js" "$SUDO" >/dev/null
node "$VEC/collect_vectors_v9.mjs" "$OUT/js" > "$OUT/v.json"

if [[ "$check" -eq 1 ]]; then
  if cmp -s "$OUT/v.json" "$VEC/doubledeal_v9_vectors.json"; then
    echo "OK doubledeal_v9_vectors.json matches $SUDO"
  else
    diff -u "$VEC/doubledeal_v9_vectors.json" "$OUT/v.json" | head -40 >&2
    echo "FAIL doubledeal_v9_vectors.json differs from a fresh v9 build" >&2
    exit 1
  fi
else
  cp "$OUT/v.json" "$VEC/doubledeal_v9_vectors.json"
  echo "wrote $VEC/doubledeal_v9_vectors.json"
fi
