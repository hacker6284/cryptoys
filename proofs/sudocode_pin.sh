#!/bin/sh
# The one reader of proofs/SUDOCODE_PIN: prints the pinned sudocode commit and
# fails if the file has no 40-char SHA line. Run it: sh proofs/sudocode_pin.sh
grep -E '^[0-9a-f]{40}$' "$(dirname "$0")/SUDOCODE_PIN"
