#!/bin/sh
# Generate the JavaScript the Scramble demo imports, and copy the spec beside it.
set -eu
root=$(CDPATH= cd -- "$(dirname "$0")/.." && pwd)
sudoc=${SUDOC:-"$HOME/Documents/Projects/sudocode/sudoc/target/debug/sudoc"}
out="$root/demos/scramble/generated"
mkdir -p "$out"
"$sudoc" build --target js -o "$out" "$root/primitives/hash/scramble/scramble.sudo"
cp "$root/primitives/hash/scramble/SPEC.md" "$root/demos/scramble/SPEC.md"
