# MegaDreifach known-answer metadata

`megaminx_hash_kats.json` is a copy of the published KAT file at `primitives/hash/megadreifach/kats/`.

This drop checks **metadata** only (pad lengths, block counts, digest width, `|G|`, IV-COOK12 hex) from Lean (`lake exe megadreifach`). Sudo tests in `megadreifach.sudo` lock the same pad / φ / IV facts.

Full Hash digest equality in the proof package (stone M13) is **OPEN**. Research hexes were refreshed 2026-09-24 to current `megadreifach.sudo` (Python and emitted Lean agree). Algorithm Hash is `lean/Generated/` (`v_Hash`), not a handwritten body. See [`../ANTI_DRIFT.md`](../ANTI_DRIFT.md).
