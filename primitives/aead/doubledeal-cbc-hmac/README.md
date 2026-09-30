<!-- Owns: the file map of this directory and the commands that build and check it. Maintenance rules: ../../../DOCS.md. -->
# DoubleDeal-CBC-Sandwich v2

Toy Encrypt-then-MAC on decks: **deck-CBC** (each plaintext deck Composed with the previous ciphertext deck, then [DoubleDeal](../../cipher/doubledeal/SPEC.md)), then a **Sandwich MAC** on one [MegaDreifach](../../hash/megadreifach/SPEC.md) chain (the key deck, the message decks, the key deck turned over). Two user-supplied key decks; a fresh truly shuffled IV deck per message. No XOR. Not for real use. Scope, rules and security honesty: [`SPEC.md`](SPEC.md).

The directory and file names keep v1's `doubledeal-cbc-hmac` (renaming is left to review; see the SPEC). Frozen v1 (DoubleDeal-CBC-HMAC): [`v1/`](v1/SPEC.md).

| File | Role |
| --- | --- |
| [`SPEC.md`](SPEC.md) | Normative specification (v2) |
| [`doubledeal_cbc_hmac.sudo`](doubledeal_cbc_hmac.sudo) | The whole construction: deck-CBC, Sandwich MAC, optional KDF, byte ⇄ deck edge, `aead_seal` / `aead_open` |
| [`aead.mjs`](aead.mjs) | Host wrapper: `randomDeck()` (CSPRNG, rejection), `encrypt` with a fresh IV deck, `decrypt`, `deriveKeyDecks` |
| [`aead_harness.mjs`](aead_harness.mjs) | Shared wiring for the test and the regenerator (`AEAD_OUT` = the sudoc JS build directory) |
| [`aead.test.mjs`](aead.test.mjs) | KATs, round trips with random keys and IVs, and rejects (tag, ciphertext, IV, AAD, truncation, swapped or wrong keys, non-deck numbers) |
| [`kats/doubledeal_cbc_hmac_kats.json`](kats/doubledeal_cbc_hmac_kats.json) | Published v2 vectors |
| [`kats/regen.mjs`](kats/regen.mjs) | Regenerates the KAT outputs from the sudo; `--check` (run by `tools/generate-demos.sh`) fails if a fresh run would change the JSON |
| [`kats/check.py`](kats/check.py) | Structural KAT checks (does not reimplement anything); run by `tools/generate-demos.sh` |
| [`v1/`](v1/SPEC.md) | Frozen DoubleDeal-CBC-HMAC v1: SPEC and sudo |

Run from the repo root (`-I` makes `megadreifach` and `doubledeal` importable):

```sh
sudoc emit-ir --require terminates -I primitives/hash/megadreifach -I primitives/cipher/doubledeal \
    primitives/aead/doubledeal-cbc-hmac/doubledeal_cbc_hmac.sudo > /dev/null
sudoc build --target js --tests -o /tmp/ddch -I primitives/hash/megadreifach -I primitives/cipher/doubledeal \
    primitives/aead/doubledeal-cbc-hmac/doubledeal_cbc_hmac.sudo
node /tmp/ddch/_doubledeal_cbc_hmac_impl.mjs
AEAD_OUT=/tmp/ddch node primitives/aead/doubledeal-cbc-hmac/aead.test.mjs
AEAD_OUT=/tmp/ddch node primitives/aead/doubledeal-cbc-hmac/kats/regen.mjs --check
python3 primitives/aead/doubledeal-cbc-hmac/kats/check.py
```

Generated Lean (v2, TAP only): [`proofs/doubledeal-cbc-hmac/`](../../../proofs/doubledeal-cbc-hmac/README.md). Frozen v1 Link 2: [`proofs/deprecated/doubledeal-cbc-hmac-v1/`](../../../proofs/deprecated/doubledeal-cbc-hmac-v1/README.md).
