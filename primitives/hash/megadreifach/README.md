# MegaDreifach

Toy three-megaminx Merkle–Damgård hash. Not for real use. The product name **MegaDreifach** is locked; the puzzle/group stays **megaminx**.

This directory is the published primitive:

| File | Role |
| --- | --- |
| `SPEC.md` | Normative specification, **v2 (current)** (`Hash` / `HashDeck` / `HashDeckBody`, plus `MegaDreifach*` aliases; `*BodyFrom` is the free-start analysis surface) |
| `megadreifach.sudo` | Conformance implementation (v2) |
| `kats/megaminx_hash_kats_v2.json` | v2 KAT file (same inputs and layout as v1) |
| `v1/SPEC.md`, `v1/megadreifach.sudo` | Frozen v1 (**deprecated**, broken; see the banner and PR #119). The sudo keeps the v1 file name so the Lean emitted from it stays the module `Megadreifach` |
| `kats/megaminx_hash_kats.json` | v1 KAT file (pad / IV / `|G|` metadata; v1 Hash hexes), unchanged. The Lean package, `proofs/megadreifach/vectors/` and `proofs/megadreifach/security/md.py` pin it |

Length extension on bare `Hash` is accepted by design. HMAC-MegaDreifach (the keyed construction) is specified with DoubleDeal-CBC-HMAC under `primitives/aead/doubledeal-cbc-hmac/`. **The Lean proof package under `proofs/megadreifach/` is pinned to v1** (its `Generated/` is emitted from `v1/megadreifach.sudo`, its vectors are the v1 KATs), so its proofs cover v1, not v2, until they are ported. A green Lean build is not a security claim. Hand-written Lean is not a proof that this sudo text equals the Lean model.

```sh
sudoc build --target js --tests -o /tmp/megadreifach primitives/hash/megadreifach/megadreifach.sudo
node /tmp/megadreifach/_megadreifach_impl.mjs
```

The frozen v1 file builds the same way (`v1/megadreifach.sudo`; use a different `-o` directory).
