# DoubleDeal-CBC-HMAC proofs

Sudo is normative. Emitted Lean under `lean/Generated/` is the
HMAC / KDF / pad / MAC-input algorithm from
`primitives/aead/doubledeal-cbc-hmac/doubledeal_cbc_hmac.sudo`.
See [`../ANTI_DRIFT.md`](../ANTI_DRIFT.md).

This does **not** claim sudo↔Lean semantic equivalence (Link 2).
It is **not** an AEAD security theorem. Byte-domain CBC that ranks
a deck stays in JS (`aead.mjs`) because `52!` is not a sudo `int`.
SCM / SMAC stay later.

The emit terminates gate is on. Production loops are bounded `for`.
CBC-HMAC imports MegaDreifach; emit-ir is given
`-I primitives/hash/megadreifach` so `Hash` is that module, not a
second handwritten hash.

## Generated Lean

Do not edit `lean/Generated/` by hand. From the repo root:

```sh
proofs/emit_lean.sh cbc-hmac
cd proofs/doubledeal-cbc-hmac/lean/Generated && lake build && ./.lake/build/bin/doubledeal_cbc_hmac_test
```

Expected TAP: **11/11**. Pin and regenerating: [`../ANTI_DRIFT.md`](../ANTI_DRIFT.md).
There is no algebraic proof package next door (no Link-2 refinement).
