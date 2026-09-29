#!/usr/bin/env bash
# Regenerate (or --check) emitted Lean from normative .sudo files via the
# sudocode protocol-4 Lean backend.
#
# Pin: proofs/SUDOCODE_PIN (hacker6284/sudocode main), read by proofs/sudocode.sh.
#
# Terminates gate ON: sudoc emit-ir --require terminates.
# Production paths are bounded `for` in DoubleDeal (current, and frozen v8, v9, v10, v11),
# MegaDreifach, Scramble, and DoubleDeal-CBC-HMAC. DoubleDeal's test-only
# kind-scan whiles are stripped under the gate. CBC-HMAC imports
# MegaDreifach via an extra -I.
#
# Usage (from anywhere):
#   proofs/emit_lean.sh [--check] [TARGET ...]   # no TARGET: all of them (table below)
#     --check   CI: fail if committed Generated/ is stale (writes nothing)
#   Write mode also stamps Generated/EMITTED_FROM.json (tools/emit_lean.py --install).
#   doubledeal-cbc-hmac is accepted as an alias of cbc-hmac.
#
# Optional:
#   SUDOC=/path/to/sudoc
#   SUDOCODE_DIR=/path/to/sudocode   # must contain backends/lean/ at the pin (default: proofs/sudocode.sh)
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

# The targets, spelled once: name | .sudo | Generated/ | extra -I directories.
# doubledeal-v8, -v9, -v10 are frozen, deprecated (vulnerability-proof / write-up
# targets); doubledeal-v11 is frozen, superseded (not attacked). Do not change their .sudo.
# megadreifach is PINNED TO THE FROZEN, DEPRECATED v1 (v1/megadreifach.sudo): the Lean proof
# package proofs/megadreifach/ models v1 and has not been ported to v2, so its Generated/ is
# emitted from v1. The file keeps the name megadreifach.sudo so the emitted module stays
# `Megadreifach` (the entry is the file stem). The current v2 sudo is not emitted to Lean
# on its own; it only reaches Lean through cbc-hmac's -I import (emitted code, no proofs).
TARGET_TABLE="
doubledeal      primitives/cipher/doubledeal/doubledeal.sudo              proofs/doubledeal/lean/Generated
doubledeal-v8   primitives/cipher/doubledeal/v8/doubledeal_v8.sudo        proofs/deprecated/doubledeal-v8/lean/Generated
doubledeal-v9   primitives/cipher/doubledeal/v9/doubledeal_v9.sudo        proofs/deprecated/doubledeal-v9/lean/Generated
doubledeal-v10  primitives/cipher/doubledeal/v10/doubledeal_v10.sudo      proofs/deprecated/doubledeal-v10/lean/Generated
doubledeal-v11  primitives/cipher/doubledeal/v11/doubledeal_v11.sudo      proofs/deprecated/doubledeal-v11/lean/Generated
megadreifach    primitives/hash/megadreifach/v1/megadreifach.sudo         proofs/megadreifach/lean/Generated
scramble        primitives/hash/scramble/scramble.sudo                    proofs/scramble/lean/Generated
cbc-hmac        primitives/aead/doubledeal-cbc-hmac/doubledeal_cbc_hmac.sudo proofs/doubledeal-cbc-hmac/lean/Generated primitives/hash/megadreifach
"
# Parsed once: the names in order, and each target's .sudo, Generated/ and -I dirs.
ALL_TARGETS=()
declare -A T_SUDO T_GEN T_INC
while read -r name sudo_path generated includes; do
  [[ -n "$name" ]] || continue
  ALL_TARGETS+=("$name")
  T_SUDO[$name]="$sudo_path"
  T_GEN[$name]="$generated"
  T_INC[$name]="$includes"
done <<< "$TARGET_TABLE"

usage() {
  local IFS='|'
  echo "usage: $0 [--check] [${ALL_TARGETS[*]} ...]" >&2
  echo "  cbc-hmac is also accepted as doubledeal-cbc-hmac" >&2
  exit 2
}

CHECK=0
TARGETS=()
for arg in "$@"; do
  case "$arg" in
    --check) CHECK=1 ;;
    doubledeal-cbc-hmac) TARGETS+=(cbc-hmac) ;;
    *)
      if [[ -n "${T_SUDO[$arg]:-}" ]]; then TARGETS+=("$arg"); else usage; fi ;;
  esac
done
if [[ ${#TARGETS[@]} -eq 0 ]]; then
  TARGETS=("${ALL_TARGETS[@]}")
fi

# Pin, SUDOCODE_DIR default and sudoc build: proofs/sudocode.sh (shared with vectors/regen.sh).
source "$ROOT/proofs/sudocode.sh"

SCRATCH="$(mktemp -d)"
trap 'rm -rf "$SCRATCH"' EXIT

emit_one() {
  local name="$1" sudo_path="$2" generated="$3"
  shift 3
  local args=("$ROOT/$sudo_path" --out "$SCRATCH/$name")
  if [[ "$CHECK" -eq 1 ]]; then
    args+=(--check "$ROOT/$generated")
  else
    args+=(--install "$ROOT/$generated")
  fi
  local inc
  for inc in "$@"; do
    args+=(-I "$ROOT/$inc")
  done
  python3 "$ROOT/tools/emit_lean.py" "${args[@]}"
}

for t in "${TARGETS[@]}"; do
  # shellcheck disable=SC2086  # T_INC: zero or more space-separated directories
  emit_one "$t" "${T_SUDO[$t]}" "${T_GEN[$t]}" ${T_INC[$t]}
done

echo "sudocode_lean_commit=$SUDOCODE_COMMIT ref=$SUDOCODE_REF"
if [[ "$CHECK" -eq 1 ]]; then
  echo "Generated Lean matches emit from current .sudo"
else
  echo "wrote Generated/ — do not hand-edit those files"
fi
