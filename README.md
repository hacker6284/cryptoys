# cryptoys

Toy cryptography, in both senses. The algorithms are experiments, and they are built out of actual toys. Nothing in this repository is for real use.

Each primitive is a directory holding a normative specification and one [sudocode](https://github.com/hacker6284/sudocode) implementation. Demos are rendered with Three.js, and published from this repository with GitHub Pages.

```text
primitives/hash/scramble/SPEC.md
primitives/hash/scramble/scramble.sudo
demos/scramble/
```

## Scramble

Scramble is a hash. A message walks a solved cube. The digest is the seated pose, encoded as the cube-group index in 9 bytes. `scramble_v1` is superseded. `scramble_v2` is current.

The specification is `primitives/hash/scramble/SPEC.md`.

Build the demo's JavaScript with a local `sudoc`:

```sh
export SUDOC=/path/to/sudoc
sh tools/build.sh
```

`tools/build.sh` looks for `sudoc` at `~/Documents/Projects/sudocode/sudoc/target/debug/sudoc` when `SUDOC` is unset. Then serve `demos/` and open `scramble/`.

The conformance tests are inside `scramble.sudo`. With `sudoc` on the path:

```sh
sudoc build --target js --tests -o /tmp/scramble primitives/hash/scramble/scramble.sudo
node /tmp/scramble/_scramble_impl.mjs
```

GitHub Actions builds `sudoc` from [hacker6284/sudocode](https://github.com/hacker6284/sudocode), runs those tests, and publishes `demos/`.
