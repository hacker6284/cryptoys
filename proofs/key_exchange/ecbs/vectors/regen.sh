#!/usr/bin/env bash
# Rebuild (or --check) the ECBS known-answer vectors from primitives/key_exchange/ecbs/ecbs.sudo
# via the sudoc JS target at the sudocode pin (proofs/SUDOCODE_PIN, read by
# proofs/sudocode.sh). The pin and the .sudo hash are recorded in the JSON.
#
# Usage (from anywhere):
#   proofs/key_exchange/ecbs/vectors/regen.sh [--check]
#     (default)  inputs.json + ecbs.sudo -> ecbs_vectors.json
#     --check    build to a temp dir; fail unless byte-identical to the committed file
# Takes about 20 s (most of it the one Serious exchange, in the generated JS).
#
# Optional: SUDOC=/path/to/sudoc, SUDOCODE_DIR=/path/to/sudocode (see proofs/sudocode.sh).
# The oracle cross-check is separate: python3 proofs/key_exchange/ecbs/vectors/check_oracle.py (needs cypari2)
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../../../.." && pwd)"
check=0
for arg in "$@"; do
  case "$arg" in
    --check) check=1 ;;
    *) echo "usage: $0 [--check]" >&2; exit 2 ;;
  esac
done

sudo=primitives/key_exchange/ecbs/ecbs.sudo
dir=proofs/key_exchange/ecbs/vectors
json=$dir/ecbs_vectors.json

source "$ROOT/proofs/sudocode.sh"

ECBS_SUDO_SHA256="$(sha256sum "$ROOT/$sudo" | awk '{print $1}')"
export ECBS_SUDO_SHA256

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
"$SUDOC" build --target js --tests -o "$tmp/js" "$ROOT/$sudo" >/dev/null
node "$tmp/js/_ecbs_impl.mjs" >"$tmp/tap.txt" || { cat "$tmp/tap.txt" >&2; exit 1; }
node "$ROOT/$dir/collect_vectors.mjs" "$tmp/js" > "$tmp/vectors.json"

if [[ "$check" -eq 1 ]]; then
  if ! cmp -s "$tmp/vectors.json" "$ROOT/$json"; then
    diff -u "$ROOT/$json" "$tmp/vectors.json" | head -40 >&2 || true
    echo "STALE $json differs from a fresh build of $sudo (fix: $0)" >&2
    exit 1
  fi
  echo "OK $json matches $sudo (sudocode $SUDOCODE_COMMIT)"
else
  cp "$tmp/vectors.json" "$ROOT/$json"
  echo "wrote $json (sudo_sha256=$ECBS_SUDO_SHA256, sudocode_commit=$SUDOCODE_COMMIT)"
fi
