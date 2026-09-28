#!/usr/bin/env bash
# Regenerate (or --check) emitted Lean from normative .sudo files via the
# sudocode protocol-4 Lean backend.
#
# Pin: proofs/SUDOCODE_PIN (hacker6284/sudocode main), read by proofs/sudocode.sh.
#
# Terminates gate ON: sudoc emit-ir --require terminates.
# Production paths are bounded `for` in DoubleDeal (current, and frozen v8, v9, v10),
# MegaDreifach, Scramble, and DoubleDeal-CBC-HMAC. DoubleDeal's test-only
# kind-scan whiles are stripped under the gate. CBC-HMAC imports
# MegaDreifach via an extra -I.
#
# Usage (from repo root):
#   proofs/emit_lean.sh              # write Generated/ (all seven targets)
#   proofs/emit_lean.sh --check      # CI: fail if committed Generated/ is stale
#   proofs/emit_lean.sh doubledeal   # one algorithm
#   proofs/emit_lean.sh doubledeal-v8  # frozen deprecated v8
#   proofs/emit_lean.sh doubledeal-v9  # frozen deprecated v9
#   proofs/emit_lean.sh doubledeal-v10 # frozen deprecated v10
#   proofs/emit_lean.sh megadreifach
#   proofs/emit_lean.sh scramble
#   proofs/emit_lean.sh cbc-hmac     # alias: doubledeal-cbc-hmac
#
# Optional:
#   SUDOC=/path/to/sudoc
#   SUDOCODE_DIR=/path/to/sudocode   # must contain backends/lean/ at the pin (default: proofs/sudocode.sh)
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

CHECK=0
TARGETS=()
for arg in "$@"; do
  case "$arg" in
    --check) CHECK=1 ;;
    doubledeal|doubledeal-v8|doubledeal-v9|doubledeal-v10|megadreifach|scramble|cbc-hmac) TARGETS+=("$arg") ;;
    doubledeal-cbc-hmac) TARGETS+=("cbc-hmac") ;;
    *)
      echo "usage: $0 [--check] [doubledeal|doubledeal-v8|doubledeal-v9|doubledeal-v10|megadreifach|scramble|cbc-hmac ...]" >&2
      echo "  cbc-hmac is also accepted as doubledeal-cbc-hmac" >&2
      exit 2
      ;;
  esac
done
if [[ ${#TARGETS[@]} -eq 0 ]]; then
  TARGETS=(doubledeal doubledeal-v8 doubledeal-v9 doubledeal-v10 megadreifach scramble cbc-hmac)
fi

# Pin, SUDOCODE_DIR default and sudoc build: proofs/sudocode.sh (shared with vectors/regen.sh).
source "$ROOT/proofs/sudocode.sh"

emit_one() {
  local name="$1"
  local sudo_path="$2"
  local generated="$3"
  shift 3
  local includes=("$@")
  local scratch="${TMPDIR:-/tmp}/cryptoys-emit-${name}"
  rm -rf "$scratch"
  mkdir -p "$scratch"
  local extra=()
  if [[ "$CHECK" -eq 1 ]]; then
    extra+=(--check "$generated")
  else
    extra+=(--install "$generated")
  fi
  local inc_args=()
  local inc
  for inc in "${includes[@]}"; do
    inc_args+=(-I "$inc")
  done
  python3 "$ROOT/tools/emit_lean.py" "$sudo_path" --out "$scratch" "${extra[@]}" "${inc_args[@]}"
  if [[ "$CHECK" -eq 0 ]]; then
    python3 - <<PY
import hashlib, json, pathlib
root = pathlib.Path("$ROOT")
sudo = pathlib.Path("$sudo_path")
includes = [pathlib.Path(p) for p in """$(printf '%s\n' "${includes[@]}")""".splitlines() if p]
imported = []
for inc in includes:
    for child in sorted(inc.glob("*.sudo")):
        imported.append({
            "sudo_file": str(child.relative_to(root)),
            "sudo_sha256": hashlib.sha256(child.read_bytes()).hexdigest(),
        })
stamp = {
    "sudo_file": str(sudo.relative_to(root)),
    "sudo_sha256": hashlib.sha256(sudo.read_bytes()).hexdigest(),
    "sudocode_lean_commit": "$SUDOCODE_COMMIT",
    "sudocode_lean_ref": "$SUDOCODE_REF",
    "terminates_gate": True,
    "with_tests": True,
}
if includes:
    stamp["include_paths"] = [str(p.relative_to(root)) for p in includes]
if imported:
    stamp["imported_sudo"] = imported
pathlib.Path("$generated/EMITTED_FROM.json").write_text(json.dumps(stamp, indent=2) + "\n")
print("wrote $generated/EMITTED_FROM.json")
PY
  fi
}

for t in "${TARGETS[@]}"; do
  case "$t" in
    doubledeal)
      emit_one doubledeal \
        "$ROOT/primitives/cipher/doubledeal/doubledeal.sudo" \
        "$ROOT/proofs/doubledeal/lean/Generated"
      ;;
    doubledeal-v8)
      # Frozen, deprecated v8 (vulnerability-proof target). Do not change.
      emit_one doubledeal-v8 \
        "$ROOT/primitives/cipher/doubledeal/v8/doubledeal_v8.sudo" \
        "$ROOT/proofs/deprecated/doubledeal-v8/lean/Generated"
      ;;
    doubledeal-v9)
      # Frozen, deprecated v9 (vulnerability-proof target). Do not change.
      emit_one doubledeal-v9 \
        "$ROOT/primitives/cipher/doubledeal/v9/doubledeal_v9.sudo" \
        "$ROOT/proofs/deprecated/doubledeal-v9/lean/Generated"
      ;;
    doubledeal-v10)
      # Frozen, deprecated v10 (GridCycle parity write-up target). Do not change.
      emit_one doubledeal-v10 \
        "$ROOT/primitives/cipher/doubledeal/v10/doubledeal_v10.sudo" \
        "$ROOT/proofs/deprecated/doubledeal-v10/lean/Generated"
      ;;
    megadreifach)
      emit_one megadreifach \
        "$ROOT/primitives/hash/megadreifach/megadreifach.sudo" \
        "$ROOT/proofs/megadreifach/lean/Generated"
      ;;
    scramble)
      emit_one scramble \
        "$ROOT/primitives/hash/scramble/scramble.sudo" \
        "$ROOT/proofs/scramble/lean/Generated"
      ;;
    cbc-hmac)
      emit_one cbc-hmac \
        "$ROOT/primitives/aead/doubledeal-cbc-hmac/doubledeal_cbc_hmac.sudo" \
        "$ROOT/proofs/doubledeal-cbc-hmac/lean/Generated" \
        "$ROOT/primitives/hash/megadreifach"
      ;;
  esac
done

echo "sudocode_lean_commit=$SUDOCODE_COMMIT ref=$SUDOCODE_REF"
if [[ "$CHECK" -eq 1 ]]; then
  echo "Generated Lean matches emit from current .sudo"
else
  echo "wrote Generated/ — do not hand-edit those files"
fi
