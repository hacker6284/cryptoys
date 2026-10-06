<!-- Owns: the repository map (one-line purpose per primitive, where each area is documented) and the sudo conformance test commands. Maintenance rules: DOCS.md. -->
# cryptoys

Toy cryptography, in both senses. The algorithms are experiments, and they are built out of actual toys. Not for real use; a green Lean build is not a security claim (see [proofs/README.md](proofs/README.md)).

Each primitive is a directory holding a normative specification and one [sudocode](https://github.com/hacker6284/sudocode) implementation. Demos are rendered with Three.js, and published from this repository with GitHub Pages and on Render as [cryptoygraphy.com](https://cryptoygraphy.com/).

## Primitives

| Primitive | Purpose | Specification | Proofs |
| --- | --- | --- | --- |
| Scramble | Toy hash. A message walks a solved cube; the digest is the seated pose. **Broken; do not use** ([Security](primitives/hash/scramble/SPEC.md#security)). | [SPEC.md](primitives/hash/scramble/SPEC.md) | [proofs/scramble/](proofs/scramble/) |
| MegaDreifach | Toy three-megaminx Merkle–Damgård hash. Current: [v3](primitives/hash/megadreifach/v3/SPEC.md) (colour-named card phase ZP26); v2 is [deprecated](primitives/hash/megadreifach/SPEC.md) (the frozen DoubleDeal-CBC-HMAC v1 still uses it; DoubleDeal-CBC-Sandwich v2 uses v3); v1 is [deprecated](primitives/hash/megadreifach/v1/SPEC.md). | [v3 SPEC.md](primitives/hash/megadreifach/v3/SPEC.md), [README](primitives/hash/megadreifach/README.md), [v2 SPEC.md](primitives/hash/megadreifach/SPEC.md) | [proofs/megadreifach/](proofs/megadreifach/) (v2); v3 evidence: [proofs/megadreifach/security/v3/](proofs/megadreifach/security/v3/README.md); frozen v1: [proofs/deprecated/megadreifach-v1/](proofs/deprecated/megadreifach-v1/README.md) |
| DoubleDeal | Toy block cipher on a 52-card deck. | [SPEC.md](primitives/cipher/doubledeal/SPEC.md) (version history: [§7a](primitives/cipher/doubledeal/SPEC.md#7a-version-history)) | [proofs/doubledeal/](proofs/doubledeal/); frozen versions: [proofs/deprecated/](proofs/deprecated/README.md) |
| DoubleDeal-CBC-Sandwich v2 | Toy Encrypt-then-MAC on decks: DoubleDeal in deck-CBC (Compose with the previous ciphertext deck), then a Sandwich MAC on MegaDreifach (key deck, message decks, key deck turned over). Two user-supplied key decks, a fresh shuffled IV deck. Replaces DoubleDeal-CBC-HMAC v1 (frozen). Not DoubleDeal-SCM. | [SPEC.md](primitives/aead/doubledeal-cbc-hmac/SPEC.md), [README](primitives/aead/doubledeal-cbc-hmac/README.md) | [proofs/doubledeal-cbc-hmac/](proofs/doubledeal-cbc-hmac/) |
| BS | Toy finite-field Diffie–Hellman worked by hand on Battleship pegboards; the key is one dice-built ships+pegs grid. Vectors: [proofs/key_exchange/bs/vectors/](proofs/key_exchange/bs/vectors/README.md). | [SPEC.md](primitives/key_exchange/bs/SPEC.md) | [proofs/key_exchange/bs/](proofs/key_exchange/bs/README.md) |
| ECBS | Toy elliptic-curve Diffie–Hellman over GF(3^n) worked by hand on Battleship pegboards; the received point is checked with a sender-made certificate. Player's card: [CARD.md](primitives/key_exchange/ecbs/CARD.md). Runnable spec: [ecbs.sudo](primitives/key_exchange/ecbs/ecbs.sudo). | [SPEC.md](primitives/key_exchange/ecbs/SPEC.md) | [proofs/key_exchange/ecbs/](proofs/key_exchange/ecbs/README.md) |

## Layout

| Path | Contents |
| --- | --- |
| [primitives/](primitives/) | Specifications and `.sudo` implementations, by kind (`hash/`, `cipher/`, `aead/`, `key_exchange/`) |
| [demos/](demos/README.md) | Playroom hub and the Scramble and DoubleDeal demos (GitHub Pages root) |
| [proofs/](proofs/README.md) | Proof ledger: what is machine-checked, what is evidence, what is not claimed |
| [tools/](tools/) | Demo generation (`build.sh`, `generate-demos.sh`, `render-build.sh`) and the Lean emit and generation-check helpers (`emit_lean.py`, `gencheck.py`) |
| [.github/](.github/) | CI workflows and actions, and the Render deploy notes ([RENDER.md](.github/RENDER.md)) |

Maintenance rules for these READMEs: [DOCS.md](DOCS.md).

## Build and test

The conformance tests are inside each `.sudo` file. With `sudoc` on the path:

```sh
sudoc build --target js --tests -o /tmp/scramble primitives/hash/scramble/scramble.sudo
node /tmp/scramble/_scramble_impl.mjs
sudoc build --target js --tests -o /tmp/megadreifach primitives/hash/megadreifach/megadreifach.sudo
node /tmp/megadreifach/_megadreifach_impl.mjs
sudoc build --target js --tests -o /tmp/megadreifach-v3-test primitives/hash/megadreifach/v3/megadreifach.sudo
node /tmp/megadreifach-v3-test/_megadreifach_impl.mjs
sudoc build --target js --tests -o /tmp/doubledeal primitives/cipher/doubledeal/doubledeal.sudo
node /tmp/doubledeal/_doubledeal_impl.mjs
sudoc build --target js --tests -o /tmp/bs primitives/key_exchange/bs/bs.sudo
node /tmp/bs/_bs_impl.mjs
sudoc build --target js --tests -o /tmp/ecbs primitives/key_exchange/ecbs/ecbs.sudo
node /tmp/ecbs/_ecbs_impl.mjs
```

DoubleDeal-CBC-Sandwich needs `-I primitives/hash/megadreifach/v3 -I primitives/cipher/doubledeal` and a JavaScript step; its commands are in [its README](primitives/aead/doubledeal-cbc-hmac/README.md). Building and serving the demos: [demos/README.md](demos/README.md#local).

`tools/generate-demos.sh` runs all of the above, the extra JavaScript and KAT checks, and `tools/build.sh`. It is what CI runs after building `sudoc` ([`.github/actions/generate-demos/`](.github/actions/generate-demos/action.yml)). It uses `SUDOC`, or `.sudocode/sudoc/target/release/sudoc` when `SUDOC` is unset.

Lean: [proofs/README.md](proofs/README.md) and [proofs/ANTI_DRIFT.md](proofs/ANTI_DRIFT.md).
