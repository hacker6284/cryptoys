#!/bin/sh
# Shared generate path for GitHub Pages and Render.
# Assumes sudoc is already built. Matches .github/actions/generate-demos
# after the cargo build step: primitive JS tests, tools/build.sh, extra
# checks, then require the two demo modules Pages/Render must serve.
set -eu
root=$(CDPATH= cd -- "$(dirname "$0")/.." && pwd)
cd "$root"
sudoc=${SUDOC:-"$root/.sudocode/sudoc/target/release/sudoc"}
if [ ! -x "$sudoc" ]; then
    echo "sudoc not found or not executable: $sudoc" >&2
    echo "Build it first: cargo build --release --manifest-path .sudocode/sudoc/Cargo.toml" >&2
    exit 1
fi

"$sudoc" build --target js --tests -o /tmp/scramble-test primitives/hash/scramble/scramble.sudo
node /tmp/scramble-test/_scramble_impl.mjs
"$sudoc" build --target js --tests -o /tmp/megadreifach-test primitives/hash/megadreifach/megadreifach.sudo
node /tmp/megadreifach-test/_megadreifach_impl.mjs
"$sudoc" build --target js --tests -o /tmp/doubledeal-test primitives/cipher/doubledeal/doubledeal.sudo
node /tmp/doubledeal-test/_doubledeal_impl.mjs
"$sudoc" emit-ir --require terminates -I primitives/hash/megadreifach \
    primitives/aead/doubledeal-cbc-hmac/doubledeal_cbc_hmac.sudo > /dev/null
"$sudoc" build --target js --tests -o /tmp/ddch-test \
    -I primitives/hash/megadreifach \
    primitives/aead/doubledeal-cbc-hmac/doubledeal_cbc_hmac.sudo
node /tmp/ddch-test/_doubledeal_cbc_hmac_impl.mjs

SUDOC="$sudoc" sh tools/build.sh
node primitives/cipher/doubledeal/encoding.test.mjs
AEAD_OUT=/tmp/ddch-test node primitives/aead/doubledeal-cbc-hmac/aead.test.mjs
python3 primitives/aead/doubledeal-cbc-hmac/kats/check.py
test -f demos/scramble/generated/scramble.mjs
test -f demos/doubledeal/generated/doubledeal.mjs
test -f demos/scramble/SPEC.md
test -f demos/doubledeal/SPEC.md
touch demos/.nojekyll
