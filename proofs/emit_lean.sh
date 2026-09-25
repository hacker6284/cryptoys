#!/usr/bin/env bash
# Regenerate (or --check) emitted Lean from normative .sudo files via the
# sudocode protocol-4 Lean backend.
#
# Pin: hacker6284/sudocode main @ SUDOCODE_LEAN_COMMIT
#   (PR #8 squash merge; Lean is in ALL_BACKENDS).
#
# Terminates gate ON: sudoc emit-ir --require terminates.
# DoubleDeal, MegaDreifach, Scramble, and DoubleDeal-CBC-HMAC production
# paths are bounded `for`. DoubleDeal test-only kind-scan whiles are
# stripped under the gate. CBC-HMAC imports MegaDreifach via extra -I.
#
# Usage (from repo root):
#   proofs/emit_lean.sh              # write Generated/ (all four)
#   proofs/emit_lean.sh --check      # CI: fail if committed Generated/ is stale
#   proofs/emit_lean.sh doubledeal   # one algorithm
#   proofs/emit_lean.sh megadreifach
#   proofs/emit_lean.sh scramble
#   proofs/emit_lean.sh cbc-hmac     # alias: doubledeal-cbc-hmac
#
# Optional:
#   SUDOC=/path/to/sudoc
#   SUDOCODE_DIR=/path/to/sudocode   # must contain backends/lean/ at the pin
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

# sudocode main at the PR #8 squash merge (Lean lockstep peer).
# Bump proofs/SUDOCODE_LEAN_PIN only when you intend to change the emitter.
SUDOCODE_LEAN_REPO="${SUDOCODE_LEAN_REPO:-https://github.com/hacker6284/sudocode.git}"
SUDOCODE_LEAN_REF="${SUDOCODE_LEAN_REF:-main}"
PIN_FILE="$ROOT/proofs/SUDOCODE_LEAN_PIN"
if [[ -z "${SUDOCODE_LEAN_COMMIT:-}" ]]; then
  SUDOCODE_LEAN_COMMIT="$(grep -E '^[0-9a-f]{40}$' "$PIN_FILE")"
fi
if [[ -z "$SUDOCODE_LEAN_COMMIT" ]]; then
  echo "could not read a 40-char SHA from $PIN_FILE" >&2
  exit 1
fi

SUDOCODE_DIR="${SUDOCODE_DIR:-/tmp/sudocode}"
CHECK=0
TARGETS=()
for arg in "$@"; do
  case "$arg" in
    --check) CHECK=1 ;;
    doubledeal|megadreifach|scramble|cbc-hmac) TARGETS+=("$arg") ;;
    doubledeal-cbc-hmac) TARGETS+=("cbc-hmac") ;;
    *)
      echo "usage: $0 [--check] [doubledeal|megadreifach|scramble|cbc-hmac ...]" >&2
      echo "  cbc-hmac is also accepted as doubledeal-cbc-hmac" >&2
      exit 2
      ;;
  esac
done
if [[ ${#TARGETS[@]} -eq 0 ]]; then
  TARGETS=(doubledeal megadreifach scramble cbc-hmac)
fi

if [[ -n "${SUDOC:-}" ]]; then
  SUDOC_BIN="$SUDOC"
else
  SUDOC_BIN="$SUDOCODE_DIR/sudoc/target/release/sudoc"
fi

need_fetch=0
if [[ ! -x "$SUDOC_BIN" ]]; then
  need_fetch=1
fi
if [[ ! -f "$SUDOCODE_DIR/backends/lean/emit.py" ]]; then
  need_fetch=1
fi
if [[ -d "$SUDOCODE_DIR/.git" ]]; then
  have="$(git -C "$SUDOCODE_DIR" rev-parse HEAD 2>/dev/null || true)"
  if [[ "$have" != "$SUDOCODE_LEAN_COMMIT" ]]; then
    need_fetch=1
  fi
fi

if [[ "$need_fetch" -eq 1 && -z "${SUDOC:-}" ]]; then
  if [[ ! -d "$SUDOCODE_DIR/.git" ]]; then
    git clone --filter=blob:none --branch "$SUDOCODE_LEAN_REF" \
      "$SUDOCODE_LEAN_REPO" "$SUDOCODE_DIR"
  fi
  git -C "$SUDOCODE_DIR" fetch --depth 1 origin "$SUDOCODE_LEAN_COMMIT"
  git -C "$SUDOCODE_DIR" checkout --detach "$SUDOCODE_LEAN_COMMIT"
  if [[ ! -f "$SUDOCODE_DIR/backends/lean/emit.py" ]]; then
    echo "blocker: $SUDOCODE_LEAN_COMMIT has no backends/lean/emit.py" >&2
    echo "expected sudocode main at/after the PR #8 merge (ff63b629)." >&2
    exit 1
  fi
  cargo build --release --manifest-path "$SUDOCODE_DIR/sudoc/Cargo.toml"
  SUDOC_BIN="$SUDOCODE_DIR/sudoc/target/release/sudoc"
fi

export SUDOC="$SUDOC_BIN"
export SUDOCODE_DIR

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
    "sudocode_lean_commit": "$SUDOCODE_LEAN_COMMIT",
    "sudocode_lean_ref": "$SUDOCODE_LEAN_REF",
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

echo "sudocode_lean_commit=$SUDOCODE_LEAN_COMMIT ref=$SUDOCODE_LEAN_REF"
if [[ "$CHECK" -eq 1 ]]; then
  echo "Generated Lean matches emit from current .sudo"
else
  echo "wrote Generated/ — do not hand-edit those files"
fi
