#!/bin/sh
# Render static-site build: same generate path as GitHub Pages.
# Clone + build sudoc, then tools/generate-demos.sh (tests + tools/build.sh).
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
    curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs \
        | sh -s -- -y --profile minimal --default-toolchain stable
    # shellcheck disable=SC1091
    . "$CARGO_HOME/env"
    command -v cargo >/dev/null 2>&1
}

ensure_cargo

# Always refresh. Render's build cache can leave a stale sudocode tip if
# we skip the clone when .sudocode/.git already exists.
rm -rf .sudocode
git clone --depth 1 https://github.com/hacker6284/sudocode.git .sudocode
cargo build --release --manifest-path .sudocode/sudoc/Cargo.toml

export SUDOC="$root/.sudocode/sudoc/target/release/sudoc"
sh tools/generate-demos.sh
