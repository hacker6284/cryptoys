#!/usr/bin/env bash
# Regenerate doubledeal_vectors.json and DoubleDeal/Vectors.lean from doubledeal.sudo
# via the sudoc JS target. Same compiler path as .github/workflows/pages.yml,
# but pinned to SUDOCODE_COMMIT (not sudocode tip).
#
# Usage (from the repo root or this directory):
#   proofs/doubledeal/vectors/regen.sh
#
# Optional:
#   SUDOC=/path/to/sudoc SUDOCODE_DIR=/path/to/sudocode proofs/doubledeal/vectors/regen.sh
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../../.." && pwd)"
VEC="$ROOT/proofs/doubledeal/vectors"
SUDO="$ROOT/primitives/cipher/doubledeal/doubledeal.sudo"

# Pin the sudocode tree used to emit JS. Bump this only when you intend to
# change the compiler, then re-run this script.
SUDOCODE_COMMIT="${SUDOCODE_COMMIT:-606f06f4d852aac7f37bccd4823775d00d2ba5a6}"

SUDOCODE_DIR="${SUDOCODE_DIR:-/tmp/sudocode}"
if [[ -n "${SUDOC:-}" ]]; then
  SUDOC_BIN="$SUDOC"
else
  SUDOC_BIN="$SUDOCODE_DIR/sudoc/target/release/sudoc"
fi

if [[ ! -x "$SUDOC_BIN" ]]; then
  if [[ ! -d "$SUDOCODE_DIR/.git" ]]; then
    git clone https://github.com/hacker6284/sudocode.git "$SUDOCODE_DIR"
  fi
  git -C "$SUDOCODE_DIR" fetch --depth 1 origin "$SUDOCODE_COMMIT"
  git -C "$SUDOCODE_DIR" checkout --detach "$SUDOCODE_COMMIT"
  cargo build --release --manifest-path "$SUDOCODE_DIR/sudoc/Cargo.toml"
  SUDOC_BIN="$SUDOCODE_DIR/sudoc/target/release/sudoc"
fi

DOUBLEDEAL_SUDO_SHA256="$(sha256sum "$SUDO" | awk '{print $1}')"
export DOUBLEDEAL_SUDO_SHA256 SUDOCODE_COMMIT

OUT="${TMPDIR:-/tmp}/doubledeal-vector-js"
rm -rf "$OUT"
mkdir -p "$OUT"
"$SUDOC_BIN" build --target js --tests -o "$OUT" "$SUDO"

node "$VEC/collect_vectors.mjs" "$OUT" > "$VEC/doubledeal_vectors.json"
python3 "$VEC/json_to_lean.py" --json "$VEC/doubledeal_vectors.json" --lean "$ROOT/proofs/doubledeal/lean/DoubleDeal/Vectors.lean"

echo "regenerated $VEC/doubledeal_vectors.json and proofs/doubledeal/lean/DoubleDeal/Vectors.lean"
echo "  sudo_sha256=$DOUBLEDEAL_SUDO_SHA256"
echo "  sudocode_commit=$SUDOCODE_COMMIT"
