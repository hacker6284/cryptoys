#!/bin/sh
# Render static-site build: same generate path as GitHub Pages.
# Fetch sudocode at proofs/SUDOCODE_PIN and build sudoc, then
# tools/generate-demos.sh (tests + tools/build.sh).
# Publish directory must be demos/. See .github/RENDER.md.
set -eu
root=$(CDPATH= cd -- "$(dirname "$0")/.." && pwd)
cd "$root"

ensure_cargo() {
    if command -v cargo >/dev/null 2>&1; then
        return 0
    fi
    for envfile in \
        "${CARGO_HOME:+$CARGO_HOME/env}" \
        "$HOME/.cargo/env" \
        /opt/render/project/.cargo/env
    do
        [ -n "$envfile" ] && [ -f "$envfile" ] || continue
        # shellcheck disable=SC1090
        . "$envfile"
        if command -v cargo >/dev/null 2>&1; then
            return 0
        fi
    done
    echo "Installing stable rustup (sudoc is a Rust crate; Pages uses dtolnay/rust-toolchain@stable)"
    export CARGO_HOME="${CARGO_HOME:-$HOME/.cargo}"
    export RUSTUP_HOME="${RUSTUP_HOME:-$HOME/.rustup}"
    # Write the installer first so a failed curl cannot become `sh` on empty stdin
    # (POSIX sh has no pipefail).
    init=$(mktemp)
    curl --proto '=https' --tlsv1.2 -fsSf https://sh.rustup.rs -o "$init"
    sh "$init" -y --profile minimal --default-toolchain stable
    rm -f "$init"
    # shellcheck disable=SC1091
    . "$CARGO_HOME/env"
    if ! command -v cargo >/dev/null 2>&1; then
        echo "error: rustup finished but cargo is not on PATH" >&2
        exit 1
    fi
}

ensure_cargo

# Always refresh: Render's build cache can keep a stale .sudocode. Build the
# commit in proofs/SUDOCODE_PIN, same as Pages generate-demos and CI.
pin=$(grep -E '^[0-9a-f]{40}$' proofs/SUDOCODE_PIN)
rm -rf .sudocode
git init -q .sudocode
git -C .sudocode fetch -q --depth 1 https://github.com/hacker6284/sudocode.git "$pin"
git -C .sudocode checkout -q --detach FETCH_HEAD
cargo build --release --manifest-path .sudocode/sudoc/Cargo.toml

export SUDOC="$root/.sudocode/sudoc/target/release/sudoc"
sh tools/generate-demos.sh
