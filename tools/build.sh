#!/bin/sh
# Generate each demo's JavaScript and copy its spec beside the page.
set -eu
root=$(CDPATH= cd -- "$(dirname "$0")/.." && pwd)
sudoc=${SUDOC:-"$HOME/Documents/Projects/sudocode/sudoc/target/debug/sudoc"}
build_one() {
    name=$1
    src=$2
    out="$root/demos/$name/generated"
    mkdir -p "$out"
    "$sudoc" build --target js -o "$out" "$src"
    cp "$(dirname "$src")/SPEC.md" "$root/demos/$name/SPEC.md"
}

build_one scramble "$root/primitives/hash/scramble/scramble.sudo"
build_one doubledeal "$root/primitives/cipher/doubledeal/doubledeal.sudo"
