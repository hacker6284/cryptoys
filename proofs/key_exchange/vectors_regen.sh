#!/usr/bin/env bash
# Rebuild (or --check) the known-answer vectors of a key-exchange design from
# primitives/key_exchange/<name>/<name>.sudo via the sudoc JS target at the sudocode pin
# (proofs/SUDOCODE_PIN, read by proofs/sudocode.sh). The pin and the .sudo hash are
# recorded in the JSON. One script for every design; <name>/vectors/regen.sh is a
# wrapper kept for CI, the docs and the JSON's generated_by field.
#
# Usage (from anywhere):
#   proofs/key_exchange/vectors_regen.sh <name> [--check]     # name: bs or ecbs
#     (default)  <name>/vectors/inputs.json + <name>.sudo -> <name>/vectors/<name>_vectors.json
#     --check    build to a temp dir; fail unless byte-identical to the committed file
# The sudo tests run first (TAP); any failure stops the script. ECBS takes about 20 s
# (most of it the one Serious exchange, in the generated JS).
#
# Optional: SUDOC=/path/to/sudoc, SUDOCODE_DIR=/path/to/sudocode (see proofs/sudocode.sh).
# The oracle cross-check is separate: python3 proofs/key_exchange/<name>/vectors/check_oracle.py
# (ECBS needs cypari2).
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
usage() { echo "usage: $0 <bs|ecbs> [--check]" >&2; exit 2; }
[[ $# -ge 1 ]] || usage
name="$1"; shift
case "$name" in bs|ecbs) ;; *) usage ;; esac
check=0
for arg in "$@"; do
  case "$arg" in
    --check) check=1 ;;
    *) usage ;;
  esac
done

sudo=primitives/key_exchange/$name/$name.sudo
dir=proofs/key_exchange/$name/vectors
json=$dir/${name}_vectors.json

source "$ROOT/proofs/sudocode.sh"

sha_var="${name^^}_SUDO_SHA256"
export "$sha_var=$(sha256sum "$ROOT/$sudo" | awk '{print $1}')"

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
"$SUDOC" build --target js --tests -o "$tmp/js" "$ROOT/$sudo" >/dev/null
node "$tmp/js/_${name}_impl.mjs" >"$tmp/tap.txt" || { cat "$tmp/tap.txt" >&2; exit 1; }
node "$ROOT/$dir/collect_vectors.mjs" "$tmp/js" > "$tmp/vectors.json"

if [[ "$check" -eq 1 ]]; then
  if ! cmp -s "$tmp/vectors.json" "$ROOT/$json"; then
    diff -u "$ROOT/$json" "$tmp/vectors.json" | head -40 >&2 || true
    echo "STALE $json differs from a fresh build of $sudo (fix: proofs/key_exchange/vectors_regen.sh $name)" >&2
    exit 1
  fi
  echo "OK $json matches $sudo (sudocode $SUDOCODE_COMMIT)"
else
  cp "$tmp/vectors.json" "$ROOT/$json"
  echo "wrote $json (${sha_var,,}=${!sha_var}, sudocode_commit=$SUDOCODE_COMMIT)"
fi
