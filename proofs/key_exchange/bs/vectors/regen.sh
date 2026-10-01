#!/usr/bin/env bash
# Rebuild (or --check) the BS known-answer vectors from primitives/key_exchange/bs/bs.sudo
# via the sudoc JS target at the sudocode pin (proofs/SUDOCODE_PIN, read by
# proofs/sudocode.sh). The pin and the .sudo hash are recorded in the JSON.
#
# Usage (from anywhere):
#   proofs/key_exchange/bs/vectors/regen.sh [--check]
#     (default)  inputs.json + bs.sudo -> bs_vectors.json
#     --check    build to a temp dir; fail unless byte-identical to the committed file
#
# Optional: SUDOC=/path/to/sudoc, SUDOCODE_DIR=/path/to/sudocode (see proofs/sudocode.sh).
# The oracle cross-check is separate: python3 proofs/key_exchange/bs/vectors/check_oracle.py
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../../../.." && pwd)"
check=0
for arg in "$@"; do
  case "$arg" in
    --check) check=1 ;;
    *) echo "usage: $0 [--check]" >&2; exit 2 ;;
  esac
done

sudo=primitives/key_exchange/bs/bs.sudo
dir=proofs/key_exchange/bs/vectors
json=$dir/bs_vectors.json

source "$ROOT/proofs/sudocode.sh"

BS_SUDO_SHA256="$(sha256sum "$ROOT/$sudo" | awk '{print $1}')"
export BS_SUDO_SHA256

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
"$SUDOC" build --target js --tests -o "$tmp/js" "$ROOT/$sudo" >/dev/null
node "$tmp/js/_bs_impl.mjs" >"$tmp/tap.txt" || { cat "$tmp/tap.txt" >&2; exit 1; }
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
  echo "wrote $json (sudo_sha256=$BS_SUDO_SHA256, sudocode_commit=$SUDOCODE_COMMIT)"
fi
