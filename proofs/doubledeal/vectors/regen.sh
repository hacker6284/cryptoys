#!/usr/bin/env bash
# Rebuild (or --check) the DoubleDeal known-answer vectors from the .sudo sources
# via the sudoc JS target at the sudocode pin (proofs/SUDOCODE_PIN, read by
# proofs/sudocode.sh). The pin is recorded in each JSON as sudocode_commit.
#
# Usage (from anywhere):
#   proofs/doubledeal/vectors/regen.sh [current|v8|v9|v10] [--check]
#     current (default)  doubledeal.sudo -> doubledeal_vectors.json and DoubleDeal/Vectors.lean
#     v8, v9, v10        frozen, deprecated versions -> their doubledeal_vN_vectors.json
#   --check              build to a temp dir; fail unless byte-identical to the committed files
#
# Optional: SUDOC=/path/to/sudoc, SUDOCODE_DIR=/path/to/sudocode (see proofs/sudocode.sh).
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../../.." && pwd)"
usage() { echo "usage: $0 [current|v8|v9|v10] [--check]" >&2; exit 2; }

version=current
check=0
for arg in "$@"; do
  case "$arg" in
    current|v8|v9|v10) version="$arg" ;;
    --check) check=1 ;;
    *) usage ;;
  esac
done

# version | .sudo source | collector | committed JSON
case "$version" in
  current) sudo=primitives/cipher/doubledeal/doubledeal.sudo
           collect=proofs/doubledeal/vectors/collect_vectors.mjs
           json=proofs/doubledeal/vectors/doubledeal_vectors.json ;;
  v8)      sudo=primitives/cipher/doubledeal/v8/doubledeal_v8.sudo
           collect=proofs/deprecated/doubledeal-v8/vectors/collect_vectors_v8.mjs
           json=proofs/deprecated/doubledeal-v8/vectors/doubledeal_v8_vectors.json ;;
  v9)      sudo=primitives/cipher/doubledeal/v9/doubledeal_v9.sudo
           collect=proofs/deprecated/doubledeal-v9/vectors/collect_vectors_v9.mjs
           json=proofs/deprecated/doubledeal-v9/vectors/doubledeal_v9_vectors.json ;;
  v10)     sudo=primitives/cipher/doubledeal/v10/doubledeal_v10.sudo
           collect=proofs/deprecated/doubledeal-v10/vectors/collect_vectors_v10.mjs
           json=proofs/deprecated/doubledeal-v10/vectors/doubledeal_v10_vectors.json ;;
esac
# current only: the Lean mirror of the JSON
lean=proofs/doubledeal/lean/DoubleDeal/Vectors.lean

source "$ROOT/proofs/sudocode.sh"

DOUBLEDEAL_SUDO="$ROOT/$sudo"
DOUBLEDEAL_SUDO_SHA256="$(sha256sum "$DOUBLEDEAL_SUDO" | awk '{print $1}')"
export DOUBLEDEAL_SUDO DOUBLEDEAL_SUDO_SHA256

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
"$SUDOC" build --target js --tests -o "$tmp/js" "$DOUBLEDEAL_SUDO" >/dev/null
node "$ROOT/$collect" "$tmp/js" > "$tmp/vectors.json"

if [[ "$check" -eq 1 ]]; then
  if ! cmp -s "$tmp/vectors.json" "$ROOT/$json"; then
    diff -u "$ROOT/$json" "$tmp/vectors.json" | head -40 >&2 || true
    echo "STALE $json differs from a fresh build of $sudo (fix: $0 $version)" >&2
    exit 1
  fi
  echo "OK $json matches $sudo (sudocode $SUDOCODE_COMMIT)"
  if [[ "$version" == current ]]; then
    python3 "$ROOT/proofs/doubledeal/vectors/json_to_lean.py" --check \
      --json "$ROOT/$json" --lean "$ROOT/$lean"
  fi
else
  cp "$tmp/vectors.json" "$ROOT/$json"
  echo "wrote $json (sudo_sha256=$DOUBLEDEAL_SUDO_SHA256, sudocode_commit=$SUDOCODE_COMMIT)"
  if [[ "$version" == current ]]; then
    python3 "$ROOT/proofs/doubledeal/vectors/json_to_lean.py" \
      --json "$ROOT/$json" --lean "$ROOT/$lean"
  fi
fi
