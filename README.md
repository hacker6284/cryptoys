# cryptoys

Toy cryptography, in both senses. The algorithms are experiments, and they are built out of actual toys.

Each primitive is a directory holding a normative specification and one [sudocode](https://github.com/hacker6284/sudocode) implementation. Demos are rendered with Three.js, and published from this repository with GitHub Pages. Demos-touching PRs also get a playroom preview at `https://hacker6284.github.io/cryptoys/pr/<N>/` — see `demos/README.md`.

```text
primitives/hash/scramble/SPEC.md
primitives/hash/scramble/scramble.sudo
demos/                    # GitHub Pages root — playroom hub
demos/playroom/           # mounted three.js room, poses, overlays
demos/scramble/
primitives/hash/megadreifach/SPEC.md
primitives/hash/megadreifach/megadreifach.sudo
primitives/cipher/doubledeal/SPEC.md
primitives/cipher/doubledeal/doubledeal.sudo
demos/doubledeal/
proofs/
```

## Scramble

Scramble is a hash. A message walks a solved cube. The digest is the seated pose, encoded as the cube-group index in 9 bytes. `scramble_v1` is superseded. `scramble_v2` is current.

The specification is `primitives/hash/scramble/SPEC.md`.

## MegaDreifach

MegaDreifach is a toy three-megaminx Merkle–Damgård hash. The product name is locked; the puzzle/group library stays megaminx. Digest is 29 bytes. Length extension on bare Hash is accepted by design. The published definition is `primitives/hash/megadreifach/SPEC.md` plus `megadreifach.sudo`. Lean *algorithm* defs under `proofs/megadreifach/lean/Generated/` are emitted from that sudo. Proof-only stones sit next door. This is not a sudo↔Lean equivalence theorem. A green Lean build is not a security claim. See `proofs/ANTI_DRIFT.md`.

## DoubleDeal

DoubleDeal (formerly TwoDeck) is a toy block cipher on a 52-card deck. A block is one deck. ECB encrypts each block on its own. CTR encrypts a counter deck and composes that keystream with the message. Diamonds carry the counter. The other three suits are the nonce. SumRanks, ShiftRows, and GridCycle are the unkeyed layers. Compose is the keyed layer. PassKey expands the master deck into the round keys. Section 5.3 encodes a byte string as decks, outside `encrypt` and `decrypt`: 28-byte blocks unrank into decks, and ciphertext is 29 bytes per deck because 52! does not fit in 28 bytes. A demo box is that text as UTF-8, unless it starts with `0x`, in which case the rest is hex.

The specification is `primitives/cipher/doubledeal/SPEC.md`. Emitted Lean for `encrypt` lives under `proofs/doubledeal/lean/Generated/`. PassKey stones are proof-only. See `proofs/ANTI_DRIFT.md`.

Build the demo's JavaScript with a local `sudoc`:

```sh
export SUDOC=/path/to/sudoc
sh tools/build.sh
```

`tools/build.sh` looks for `sudoc` at `~/Documents/Projects/sudocode/sudoc/target/debug/sudoc` when `SUDOC` is unset. Then serve `demos/` for the playroom hub. Scramble runs in the room (`?algo=scramble`); DoubleDeal is still its own teaching page.

The conformance tests are inside each `.sudo` file. With `sudoc` on the path:

```sh
sudoc build --target js --tests -o /tmp/scramble primitives/hash/scramble/scramble.sudo
node /tmp/scramble/_scramble_impl.mjs
sudoc build --target js --tests -o /tmp/megadreifach primitives/hash/megadreifach/megadreifach.sudo
node /tmp/megadreifach/_megadreifach_impl.mjs
```

GitHub Actions builds `sudoc` from [hacker6284/sudocode](https://github.com/hacker6284/sudocode), runs those tests, and publishes `demos/`.

## Proofs

What this library will and will not claim is in `proofs/README.md`. Anti-drift (sudo normative, Lean algorithms generated) is `proofs/ANTI_DRIFT.md`. DoubleDeal stones are under `proofs/doubledeal/`. MegaDreifach stones are under `proofs/megadreifach/`.
