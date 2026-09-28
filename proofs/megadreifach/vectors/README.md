# MegaDreifach known-answer metadata

`megaminx_hash_kats.json` is a byte-identical copy of the published KAT file at `primitives/hash/megadreifach/kats/`. `json_to_lean.py` generates `../lean/MegaDreifach/Vectors.lean` (message hex, lengths, digest hex) from the published file; `json_to_lean.py --check` (CI) fails if Vectors.lean is stale, the copy differs, or `MegaDreifachHeavy/Kat.lean` does not state every KAT on those strings.

`lake exe megadreifach` checks **metadata** (pad lengths, block counts, digest width, message byte counts, `|G|`, IV-COOK12 hex) in compiled Lean. Sudo tests in `megadreifach.sudo` lock the same pad / φ / IV facts.

Full Hash digest equality (stone M13) is proved for all 8 vectors as theorems about `Generated.v_Hash` in the non-default library `MegaDreifachHeavy` (`lean/MegaDreifachHeavy/Kat.lean`, `lake build MegaDreifachHeavy`, about 8 min of kernel time; CI job `megadreifach-heavy`). Research hexes were refreshed 2026-09-24 to current `megadreifach.sudo` (Python and emitted Lean agree). Algorithm Hash is `lean/Generated/` (`v_Hash`), not a handwritten body. See [`../ANTI_DRIFT.md`](../ANTI_DRIFT.md).
