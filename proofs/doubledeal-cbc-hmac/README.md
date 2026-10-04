<!-- Owns: what this tree claims and does not claim for DoubleDeal-CBC-Sandwich v2, and how to rebuild its Generated Lean. Maintenance rules: ../../DOCS.md. -->
# DoubleDeal-CBC-Sandwich v2 proofs

The directory keeps v1's name `doubledeal-cbc-hmac`; a separate pure `git mv` pull request renames it after #182 and #151 land. The frozen v1 Link 2 package is [`../deprecated/doubledeal-cbc-hmac-v1/`](../deprecated/doubledeal-cbc-hmac-v1/README.md).

Sudo is normative. Emitted Lean under `lean/Generated/` is the whole v2 algorithm from
[`primitives/aead/doubledeal-cbc-hmac/doubledeal_cbc_hmac.sudo`](../../primitives/aead/doubledeal-cbc-hmac/doubledeal_cbc_hmac.sudo),
with MegaDreifach and DoubleDeal imported (`-I primitives/hash/megadreifach/v3 -I primitives/cipher/doubledeal`).
See [`../ANTI_DRIFT.md`](../ANTI_DRIFT.md). The emit terminates gate is on; production loops are bounded `for`.

**The Lean lags v2.** There is no Link 2 for v2 yet: nothing here proves the emitted functions equal a hand-written model, and nothing here is an AEAD, MAC or PRF security theorem. The MAC uses MegaDreifach v3, which has no Lean model: the emitted `Megadreifach` module here is v3's emitted code, exercised by the TAP tests only. The security argument for v2 (relative to unproven heuristic assumptions on MegaDreifach v3) is summarised in the SPEC's §8 and given in full in [`security/ARGUMENT.md`](security/ARGUMENT.md); its evidence, the Sandwich tests on v3 with a v2 positive control, is in [`security/`](security/README.md).

## Generated Lean

Do not edit `lean/Generated/` by hand. From the repo root:

```sh
proofs/emit_lean.sh cbc-hmac
cd proofs/doubledeal-cbc-hmac/lean/Generated && lake build && ./.lake/build/bin/doubledeal_cbc_hmac_test
```

Expected TAP: **16/16**. Pin and regenerating: [`../ANTI_DRIFT.md`](../ANTI_DRIFT.md).

CI: matrix entry `cbc-hmac-generated` in [`.github/workflows/proofs.yml`](../../.github/workflows/proofs.yml).
