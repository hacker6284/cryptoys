# DoubleDeal-CBC-HMAC

Toy Encrypt-then-MAC: DoubleDeal in **CBC** on the 28-byte §5.3 encoding, then **HMAC-MegaDreifach**. The product name is locked. DoubleDeal-SCM / SMAC are not this primitive.

Not for real use. No AES-class claim. MegaDreifach is a toy hash, so the MAC inherits that. HMAC is still wired as HMAC.

| File | Role |
| --- | --- |
| `SPEC.md` | Normative specification |
| `doubledeal_cbc_hmac.sudo` | HMAC, key schedule, pad, MAC input, CBC byte helpers |
| `aead.mjs` | Byte-domain seal / open over §5.3 ranks |
| `aead.test.mjs` | Round-trips and tag-tamper KATs |
| `kats/doubledeal_cbc_hmac_kats.json` | Published vectors |

```sh
sudoc emit-ir --require terminates -I primitives/hash/megadreifach \
    primitives/aead/doubledeal-cbc-hmac/doubledeal_cbc_hmac.sudo > /dev/null

sudoc build --target js --tests -o /tmp/ddch \
    -I primitives/hash/megadreifach \
    primitives/aead/doubledeal-cbc-hmac/doubledeal_cbc_hmac.sudo
node /tmp/ddch/_doubledeal_cbc_hmac_impl.mjs

export SUDOC=/path/to/sudoc
sh tools/build.sh
AEAD_OUT=/tmp/ddch node primitives/aead/doubledeal-cbc-hmac/aead.test.mjs
```
