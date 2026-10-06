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
# MegaDreifach v3 (current); build_one copies v3/SPEC.md beside the page.
build_one megadreifach "$root/primitives/hash/megadreifach/v3/megadreifach.sudo"
# The KAT button checks the live digest against the v3 known-answer file.
cp "$root/primitives/hash/megadreifach/kats/megaminx_hash_kats_v3.json" "$root/demos/megadreifach/generated/kats.json"
