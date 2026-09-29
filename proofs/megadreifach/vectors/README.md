<!-- Owns: how the MegaDreifach KAT copy is turned into Lean and checked. Maintenance rules: ../../../DOCS.md. -->
# MegaDreifach known-answer metadata

`megaminx_hash_kats_v1.json` is a byte-identical copy of the v1 KAT file [`primitives/hash/megadreifach/kats/megaminx_hash_kats_v1.json`](../../../primitives/hash/megadreifach/kats/megaminx_hash_kats_v1.json). This package is pinned to v1 ([why](../README.md)); the v2 KATs are not used here.

`json_to_lean.py` generates `../lean/MegaDreifach/Vectors.lean` (message hex, lengths, digest hex) from the v1 file; `json_to_lean.py --check` (CI) fails if Vectors.lean is stale, the copy differs, or `MegaDreifachHeavy/Kat.lean` does not state every KAT on those strings (a text lint).

It also generates `../lean/KatSpecCheck.lean`, a program run after the heavy build (`lake env lean --run KatSpecCheck.lean`, CI job `megadreifach-heavy`). It loads both package roots with `importModules` (no initializers run) and fails if any package module has a constant with `[init]` / `[builtin_init]`, or if some `kat_<name>` is not a theorem whose type is exactly the `Expr` `v_Hash (embed (hexBytes vec_<name>.msgHex)) = .ok (embed (hexBytes vec_<name>.digestHex))` built from constant names (no Kat-side syntax takes part). The heavy job deletes all cached package build outputs before `lake build MegaDreifach MegaDreifachHeavy`, so an `[init]` hook that exits 0 while Kat.lean is compiled cannot leave a stale Kat.olean behind.

`katspec_negatives.py` (CI job `megadreifach-lean`) plants shadows (`def Vectors.vec_empty`, `hexBytes`, `Megadreifach.v_Hash`, a class / inductive `Vectors`, `run_cmd`, a `macro_rules` hijack, an `axiom kat_empty`) and `[init]` hooks (`@[init]` that exits 0 when the command line mentions Kat, with a wrong digest and a warm cache; `@[init f]`, `attribute [init]`, `@[builtin_init]`, `initialize`) in a stubbed temporary copy and requires KatSpecCheck to catch each for the stated reason.
