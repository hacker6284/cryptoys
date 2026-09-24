# MegaDreifach known-answer metadata

`megaminx_hash_kats.json` is a copy of the published KAT file at `primitives/hash/megadreifach/kats/`.

This drop checks **metadata** only (pad lengths, block counts, digest width, `|G|`, IV-COOK12 hex) from Lean (`lake exe megadreifach`). Sudo tests in `megadreifach.sudo` lock the same pad / φ / IV facts.

Full Hash digest equality (stone M13) is **OPEN**. Research hexes in the JSON are not sudo-asserted. Hand-written Lean is not a proof that the sudo text equals the Lean model.
