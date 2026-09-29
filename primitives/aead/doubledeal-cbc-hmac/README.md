<!-- Owns: the file map of this directory and the commands that build and check it. Maintenance rules: ../../../DOCS.md. -->
# DoubleDeal-CBC-HMAC

Toy Encrypt-then-MAC: DoubleDeal in **CBC** on the 28-byte [§5.3](../../cipher/doubledeal/SPEC.md#53-bytes--deck) encoding, then **HMAC-MegaDreifach**. Not for real use. Scope and non-goals: [`SPEC.md`](SPEC.md).

| File | Role |
| --- | --- |
| [`SPEC.md`](SPEC.md) | Normative specification |
| [`doubledeal_cbc_hmac.sudo`](doubledeal_cbc_hmac.sudo) | HMAC, key schedule, pad, MAC input, CBC byte helpers |
| [`aead.mjs`](aead.mjs) | Byte-domain seal / open over §5.3 ranks |
| [`aead.test.mjs`](aead.test.mjs) | Round-trips and tag-tamper KATs |
| [`kats/doubledeal_cbc_hmac_kats.json`](kats/doubledeal_cbc_hmac_kats.json) | Published vectors |
| [`aead_harness.mjs`](aead_harness.mjs) | Shared aead.mjs wiring for the test and the regenerator (`AEAD_OUT`, `DD_MJS`) |
| [`kats/regen.mjs`](kats/regen.mjs) | Rewrites the KAT blobs after a DoubleDeal change; `--check` (run by `tools/generate-demos.sh`) fails if a fresh run would change the JSON; `aead.test.mjs` also checks them |
| [`kats/check.py`](kats/check.py) | Structural KAT checks (does not reimplement Hash); run by `tools/generate-demos.sh` |

Run from the repo root. The sudo conformance tests (`-I` makes `Hash` the MegaDreifach module):

```sh
sudoc emit-ir --require terminates -I primitives/hash/megadreifach \
    primitives/aead/doubledeal-cbc-hmac/doubledeal_cbc_hmac.sudo > /dev/null
sudoc build --target js --tests -o /tmp/ddch \
    -I primitives/hash/megadreifach \
    primitives/aead/doubledeal-cbc-hmac/doubledeal_cbc_hmac.sudo
node /tmp/ddch/_doubledeal_cbc_hmac_impl.mjs
```

The byte-domain AEAD and its KATs, which also need the DoubleDeal module from `tools/build.sh`:

```sh
export SUDOC=/path/to/sudoc
sh tools/build.sh
AEAD_OUT=/tmp/ddch node primitives/aead/doubledeal-cbc-hmac/aead.test.mjs
AEAD_OUT=/tmp/ddch node primitives/aead/doubledeal-cbc-hmac/kats/regen.mjs --check
python3 primitives/aead/doubledeal-cbc-hmac/kats/check.py
```

Generated Lean: [`proofs/doubledeal-cbc-hmac/`](../../../proofs/doubledeal-cbc-hmac/README.md).
