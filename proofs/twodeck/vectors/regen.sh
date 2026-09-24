#!/usr/bin/env bash
# Regenerate twodeck_vectors.json and TwoDeck/Vectors.lean from twodeck.sudo
# via the sudoc JS target. Same compiler path as .github/workflows/pages.yml.
#
# Usage (from the repo root or this directory):
#   proofs/twodeck/vectors/regen.sh
#
# Optional:
#   SUDOC=/path/to/sudoc SUDOCODE_DIR=/path/to/sudocode proofs/twodeck/vectors/regen.sh
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../../.." && pwd)"
VEC="$ROOT/proofs/twodeck/vectors"
SUDO="$ROOT/primitives/cipher/twodeck/twodeck.sudo"

SUDOCODE_DIR="${SUDOCODE_DIR:-/tmp/sudocode}"
if [[ -n "${SUDOC:-}" ]]; then
  SUDOC_BIN="$SUDOC"
else
  SUDOC_BIN="$SUDOCODE_DIR/sudoc/target/release/sudoc"
fi

if [[ ! -x "$SUDOC_BIN" ]]; then
  if [[ ! -d "$SUDOCODE_DIR/.git" ]]; then
    git clone --depth 1 https://github.com/hacker6284/sudocode.git "$SUDOCODE_DIR"
  fi
  cargo build --release --manifest-path "$SUDOCODE_DIR/sudoc/Cargo.toml"
  SUDOC_BIN="$SUDOCODE_DIR/sudoc/target/release/sudoc"
fi

OUT="${TMPDIR:-/tmp}/twodeck-vector-js"
rm -rf "$OUT"
mkdir -p "$OUT"
"$SUDOC_BIN" build --target js --tests -o "$OUT" "$SUDO"

node "$VEC/collect_vectors.mjs" "$OUT" > "$VEC/twodeck_vectors.json"
python3 "$VEC/json_to_lean.py" --json "$VEC/twodeck_vectors.json" --lean "$ROOT/proofs/twodeck/lean/TwoDeck/Vectors.lean"

echo "regenerated $VEC/twodeck_vectors.json and proofs/twodeck/lean/TwoDeck/Vectors.lean"
