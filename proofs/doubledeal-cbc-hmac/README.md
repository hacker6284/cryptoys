<!-- Owns: what this tree claims and does not claim for DoubleDeal-CBC-HMAC, its Link 2 theorems, and how to rebuild its Generated Lean. Maintenance rules: ../../DOCS.md. `check_axioms.py --selftest` requires the backticked theorem names here to equal CBC_HMAC_LINK2. -->
# DoubleDeal-CBC-HMAC proofs

Sudo is normative. Emitted Lean under `lean/Generated/` is the
HMAC / KDF / pad / MAC-input algorithm from
[`primitives/aead/doubledeal-cbc-hmac/doubledeal_cbc_hmac.sudo`](../../primitives/aead/doubledeal-cbc-hmac/doubledeal_cbc_hmac.sudo).
See [`../ANTI_DRIFT.md`](../ANTI_DRIFT.md).

Link 2 (below) proves the emitted Lean equal to a hand-written model on byte
inputs. That is not Link 1 (emitter faithfulness: the emitted Lean is still
trusted to mean the sudo). It is **not** an AEAD security theorem. Byte-domain CBC that ranks
a deck stays in JS ([`aead.mjs`](../../primitives/aead/doubledeal-cbc-hmac/aead.mjs)) because `52!` is not a sudo `int`.
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

## Link 2

Package `lean/` (root `DoubleDealCbcHmac`, core Lean only).

- `DoubleDealCbcHmac/Spec.lean`: the hand-written model from
  [SPEC](../../primitives/aead/doubledeal-cbc-hmac/SPEC.md) §3.1, §3.3, §4, §5, §6.1 and §6.3,
  on `List Nat` byte strings, no traps. The hash is a parameter `H`.
- `DoubleDealCbcHmac/Link2/`: one theorem per exported sudo function, stating that
  the emitted function returns `.ok (embed model)`. `H` is instantiated with
  MegaDreifach's algebraic hash `vhashAlg`, which `v_Hash_refines`
  (`proofs/megadreifach/lean/MegaDreifach/Link2/VHash.lean`) proves equal to the
  emitted `Megadreifach.v_Hash`.

| Emitted function | Theorem | Domain |
| --- | --- | --- |
| `xor_bytes` | `xor_bytes_refines` | equal lengths, bytes, length fits i64 |
| `hmac_normalize_key` | `hmac_normalize_key_refines` | bytes, `8·len` fits i64 |
| `HMAC` / `HMAC_MegaDreifach` | `v_HMAC_refines`, `v_HMAC_MegaDreifach_refines` | bytes, `8·len(key)` and `8·(28 + len(msg))` fit i64 |
| `pad_iso7816` | `pad_iso7816_refines` | bytes, length fits i64 |
| `unpad_iso7816` | `unpad_iso7816_char`, `unpad_iso7816_refines`, `unpad_iso7816_rejects` | bytes, length fits i64; traps exactly where the model rejects |
| `mac_input` | `mac_input_refines` | bytes, lengths fit i64 |
| `derive_keys` | `derive_keys_refines`, `derive_keys_empty` | nonempty bytes, `8·(36 + len)` fits i64; empty master traps |
| `cbc_chain_from_cipher_block` | `cbc_chain_from_cipher_block_refines` | 29 bytes |
| `tags_equal` | `tags_equal_refines` | length of the first fits i64 |

Hypotheses are domain conditions only: every input element is a byte and the
lengths fit the i64 bounds the emitted runtime checks. Outside them nothing is
claimed (the emitted code traps or overflows there; the model has no traps).

`unpad` follows SPEC §3.1 literally: the stream is nonempty and a multiple of 28
bytes, and ends in `0x80` followed only by `0x00`. It does not bound the number of
trailing zeros, so a `0x80` followed by a whole block of zeros or more is accepted
(neither the sudo nor SPEC rejects it); `pad` never produces such a stream.

The package re-elaborates the MegaDreifach Link 2 sources (lake library
`MegaDreifachLink`, `srcDir = "../../megadreifach/lean"`) against this package's
own emitted `Generated/Megadreifach.lean`, so `v_Hash_refines` is checked for the
copy CBC-HMAC calls, not assumed from the MegaDreifach package.

Not covered: the byte-domain CBC encrypt / decrypt and the AEAD API (JS, ranks a
deck); Link 1; any MAC, PRF or AEAD security claim.

```sh
cd proofs/doubledeal-cbc-hmac/lean
lake build
python3 ../../doubledeal/security/checks/scan_sorry.py --root . --exclude Generated
python3 ../../doubledeal/check_axioms.py cbc-hmac
```

CI: job `cbc-hmac-lean` in [`.github/workflows/proofs.yml`](../../.github/workflows/proofs.yml).
