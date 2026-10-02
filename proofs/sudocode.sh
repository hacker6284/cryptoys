# Sourced (not run) by proofs/emit_lean.sh and proofs/doubledeal/vectors/regen.sh, and
# (through bash) by proofs/sudo_py.py.
# Reads the sudocode pin (proofs/SUDOCODE_PIN, via proofs/sudocode_pin.sh) and sets
# the SUDOCODE_DIR default. Needs ROOT (repo root). Sets and exports:
#   SUDOCODE_COMMIT  the pinned sudocode commit
#   SUDOCODE_REF     the branch it is on (main)
#   SUDOCODE_DIR     sudocode checkout (default /tmp/sudocode)
#   SUDOC            sudoc binary ($SUDOC if set, else built in $SUDOCODE_DIR at the pin)
SUDOCODE_REPO=https://github.com/hacker6284/sudocode.git
SUDOCODE_REF=main
SUDOCODE_COMMIT="$(sh "$ROOT/proofs/sudocode_pin.sh" || true)"
if [[ -z "$SUDOCODE_COMMIT" ]]; then
  echo "could not read a 40-char SHA from $ROOT/proofs/SUDOCODE_PIN" >&2
  exit 1
fi
SUDOCODE_DIR="${SUDOCODE_DIR:-/tmp/sudocode}"

if [[ -z "${SUDOC:-}" ]]; then
  SUDOC="$SUDOCODE_DIR/sudoc/target/release/sudoc"
  have="$(git -C "$SUDOCODE_DIR" rev-parse HEAD 2>/dev/null || true)"
  if [[ ! -x "$SUDOC" || ! -f "$SUDOCODE_DIR/backends/lean/emit.py" || "$have" != "$SUDOCODE_COMMIT" ]]; then
    if [[ ! -d "$SUDOCODE_DIR/.git" ]]; then
      git clone --filter=blob:none --branch "$SUDOCODE_REF" "$SUDOCODE_REPO" "$SUDOCODE_DIR"
    fi
    git -C "$SUDOCODE_DIR" fetch --depth 1 origin "$SUDOCODE_COMMIT"
    git -C "$SUDOCODE_DIR" checkout --detach "$SUDOCODE_COMMIT"
    if [[ ! -f "$SUDOCODE_DIR/backends/lean/emit.py" ]]; then
      echo "blocker: $SUDOCODE_COMMIT has no backends/lean/emit.py" >&2
      exit 1
    fi
    cargo build --release --manifest-path "$SUDOCODE_DIR/sudoc/Cargo.toml"
  fi
fi
export SUDOCODE_COMMIT SUDOCODE_REF SUDOCODE_DIR SUDOC
