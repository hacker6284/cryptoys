# Scramble

Scramble is a toy hash. A message is a walk on a solved cube. The digest is the seated pose at the end of that walk. 

The prose in this file is normative. `scramble.sudo` is the conformance implementation. Its tests assert the vectors below. A mismatch is a bug in the implementation. Changing the behavior of a frozen version means publishing a new version.

`scramble_v1` is superseded. `scramble_v2` is current. Names stay frozen. The demo's default pointer is v2.

## Prior art

These are other walks that land in the cube group, or the Cayley-hash idea underneath them.

- Chris Brown, ["Cryptographic Hashing & Passwords"](https://www.usna.edu/Users/cs/wcbrown/courses/si110AY13S/lec/l25/lec.html), USNA SI110, 2013. A classroom hash: each character is two clockwise face turns. Version 2.0 runs the string forward and then backward. The lecture points out that a double comma cancels.
- [unixpickle/rubik-hash](https://github.com/unixpickle/rubik-hash). Two fixed move tapes. Each input bit picks which tape supplies the turn, and each bit is reused. The digest is the resulting group element.
- Augustin J. Farrugia, Benoit Chevallier-Mames, and Mathieu Ciet, [US20110040977A1](https://patents.google.com/patent/US20110040977A1/en), "Sponge and hash functions using a rubik's cube puzzle process", filed 2009, abandoned.
- Gilles Zémor, "Hash functions and graphs with large girths", EUROCRYPT 1991, and Jean-Pierre Tillich and Gilles Zémor, "Hashing with SL2", CRYPTO 1994. Hashing by a walk on a Cayley graph.
- Daniel J. Bernstein, CubeHash, a SHA-3 candidate. A different function that shares only the name "cube".

## The cube

Twenty-six cubies sit on the integer lattice. Coordinates are `x, y, z`, each in `{-1, 0, 1}`, excluding the core `(0, 0, 0)`.

`+Y` is up, `+Z` is front, `+X` is right. Solved colors:

| Axis | Face | Color | Letter |
| --- | --- | --- | --- |
| `+Y` | U | white | `W` |
| `-Y` | D | yellow | `Y` |
| `+X` | R | red | `R` |
| `-X` | L | orange | `O` |
| `+Z` | F | green | `G` |
| `-Z` | B | blue | `B` |

A facelet string is 54 letters, faces in the order U, R, F, D, L, B. Each face is nine stickers, row by row. The sticker read at each spot is the one facing that face's axis. The spots, left to right and top to bottom, are:

```text
U  (+Y): (-1, 1,-1) ( 0, 1,-1) ( 1, 1,-1)
         (-1, 1, 0) ( 0, 1, 0) ( 1, 1, 0)
         (-1, 1, 1) ( 0, 1, 1) ( 1, 1, 1)
R  (+X): ( 1, 1, 1) ( 1, 1, 0) ( 1, 1,-1)
         ( 1, 0, 1) ( 1, 0, 0) ( 1, 0,-1)
         ( 1,-1, 1) ( 1,-1, 0) ( 1,-1,-1)
F  (+Z): (-1, 1, 1) ( 0, 1, 1) ( 1, 1, 1)
         (-1, 0, 1) ( 0, 0, 1) ( 1, 0, 1)
         (-1,-1, 1) ( 0,-1, 1) ( 1,-1, 1)
D  (-Y): (-1,-1, 1) ( 0,-1, 1) ( 1,-1, 1)
         (-1,-1, 0) ( 0,-1, 0) ( 1,-1, 0)
         (-1,-1,-1) ( 0,-1,-1) ( 1,-1,-1)
L  (-X): (-1, 1,-1) (-1, 1, 0) (-1, 1, 1)
         (-1, 0,-1) (-1, 0, 0) (-1, 0, 1)
         (-1,-1,-1) (-1,-1, 0) (-1,-1, 1)
B  (-Z): ( 1, 1,-1) ( 0, 1,-1) (-1, 1,-1)
         ( 1, 0,-1) ( 0, 0,-1) (-1, 0,-1)
         ( 1,-1,-1) ( 0,-1,-1) (-1,-1,-1)
```

The solved facelet string is

```text
WWWWWWWWWRRRRRRRRRGGGGGGGGGYYYYYYYYYOOOOOOOOOBBBBBBBBB
```

## Moves

A quarter turn is one application of the map below, to every cubie on that face, including the center. The cubie's position moves, and each of its stickers moves with the same map. A half turn is two applications. A prime is three.

| Move | Cubies | Map `(x, y, z)` |
| --- | --- | --- |
| `U` or `D` | `y = 1` or `y = -1` | `(z, y, -x)` |
| `R` | `x = 1` | `(x, z, -y)` |
| `L` | `x = -1` | `(x, -z, y)` |
| `F` | `z = 1` | `(y, -x, z)` |
| `B` | `z = -1` | `(-y, x, z)` |

`U` and `D` use the same map. One `D` is that map once, restricted to the down layer.

## Rule B

Let `C` be the cubie in the up-front-right slot `(1, 1, 1)`. Let `up` be the color on `C` facing `+Y`, and let `front` be the color on `C` facing `+Z`.

Rotate the whole cube so the center of `up` goes to `+Y` and the center of `front` goes to `+Z`. Face centers stay on their axes during face turns, so each center is an axis-aligned unit vector. Those two vectors are perpendicular. Their cross product is the third axis.

Write `e` for the up center, `t` for the front center, and `n = e × t`. The rotation matrix, acting on column vectors, is

```text
[ n.x  n.y  n.z ]
[ e.x  e.y  e.z ]
[ t.x  t.y  t.z ]
```

Apply it to every cubie position and to every sticker direction. If `e` is already `+Y` and `t` is already `+Z`, the cube does not move. The trace still records the step.

## Closer and seat

After the padded tape:

1. `F2`
2. `B2`
3. The same whole-cube rotation as Rule B, with `up = W` and `front = G`. This is the seat. The seated pose is the digest.

## Digest

Number the seated cube as follows. Corner slots, in order, with sticker axes in orientation order:

```text
( 1, 1, 1)  +Y, +X, +Z
(-1, 1, 1)  +Y, +Z, -X
(-1, 1,-1)  +Y, -X, -Z
( 1, 1,-1)  +Y, -Z, +X
( 1,-1, 1)  -Y, +Z, +X
(-1,-1, 1)  -Y, -X, +Z
(-1,-1,-1)  -Y, -Z, -X
( 1,-1,-1)  -Y, +X, -Z
```

Corner piece ids, by the three colors on the piece:

| Id | Colors | Id | Colors |
| --- | --- | --- | --- |
| 0 | W, G, R | 4 | Y, G, R |
| 1 | W, G, O | 5 | Y, G, O |
| 2 | W, B, O | 6 | Y, B, O |
| 3 | W, B, R | 7 | Y, B, R |

The orientation of a corner is which of its three axes, in the order above, carries `W` or `Y`: `0`, `1`, or `2`.

Edge slots, in order. Orientation reads the first axis.

```text
( 1, 1, 0) +Y,+X    ( 0, 1, 1) +Y,+Z    (-1, 1, 0) +Y,-X    ( 0, 1,-1) +Y,-Z
( 1,-1, 0) -Y,+X    ( 0,-1, 1) -Y,+Z    (-1,-1, 0) -Y,-X    ( 0,-1,-1) -Y,-Z
( 1, 0, 1) +Z,+X    (-1, 0, 1) +Z,-X    (-1, 0,-1) -Z,-X    ( 1, 0,-1) -Z,+X
```

Edge piece ids, by the two colors: `RW GW OW BW RY GY OY BY GR GO BO BR` are `0` through `11`. The orientation bit is `0` when the first-axis sticker is `W`, `Y`, `R`, or `O`, and `1` otherwise.

Permutation rank is the factorial number system. For a list `p`,

```text
rank(p) = Σ inv(n) · (len(p) - 1 - n)!
```

where `inv(n)` counts entries after index `n` that are smaller than `p[n]`.

Let `cp` be the eight corner ids, `co` the first seven corner orientations, `ep` the twelve edge ids, and `eo` the first eleven edge orientation bits packed little-endian (`eo = Σ b[i] · 2^i` for `i` from 0 through 10). Then

```text
s = rank(cp)
s = s · 2187 + co          # 2187 = 3^7
s = s · 239500800 + ⌊rank(ep) / 2⌋
s = s · 2048 + eo          # 2048 = 2^11
```

`⌊rank(ep) / 2⌋` is truncating division of the rank, which is what the shipped engine does. The canonical digest is `s` as a 9-byte big-endian integer. The display form is the uppercase hexadecimal of `s`, zero-padded to 17 digits.

## Trace

`evaluate` returns the digest and the trace. The trace is every step, in order, including steps already taken during `update`. Each step records the facelet string after that step.

| Kind | When | Fields |
| --- | --- | --- |
| `move` | one face turn | `move` is the Singmaster token. `nybble` is one uppercase hex digit. `block` is the block index. `index` is the position of this turn inside the block. |
| `ruleB` | after a block | `up` and `front` are the color letters read from `(1, 1, 1)` before the rotation. `block` is that block. |
| `closer` | `F2`, then `B2` | `move` is `F2` or `B2`. |
| `canonicalize` | the seat | no move |

`block` and `index` are `0`, and the text fields are empty, when a kind does not use them. Timing, camera, and colors are not part of the trace.

## API

```text
s = scramble_v1()     # or scramble_v2()
s.update(bytes)       # any number of times
result = s.evaluate() # once
```

In sudo the state is an explicit parameter: `update(s, bytes)` and `evaluate(s)`. `result.digest` is the 9 bytes. `result.trace` is the step list.

`update(a)` then `update(b)` is the same message as `update(a || b)`. Each byte is two nybbles, high nybble first. `update` appends those bytes and applies every complete symbol immediately.

- v2's symbol is one nybble: its two quarter turns, then Rule B. Every message nybble is complete as soon as its byte has arrived.
- v1's symbol is a block of 8 nybbles: eight moves, then Rule B. A trailing partial block stays buffered, so a short `update` may not turn the cube.

`evaluate` runs once. It appends the padding, walks every symbol that `update` has not already walked, plays the closer, seats the cube, and returns. `update` after `evaluate`, a second `evaluate`, or a byte outside `0 .. 255` is an error. In the sudo implementation that error is the `AssertFailed` trap. No `update` calls, then `evaluate`, is the empty message.

Text and hexadecimal parsing belong to the demo. Text is UTF-8. Hex ignores a leading `0x`, spaces, and underscores, and a leading zero is added when the remaining length is odd. An empty hex field is the empty message. Any other character is an error.

## scramble_v1

Superseded by v2.

Each nybble is one move:

| Nybble | Move | Nybble | Move | Nybble | Move | Nybble | Move |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `0` | `U` | `4` | `L` | `8` | `F` | `C` | `U2` |
| `1` | `U'` | `5` | `L'` | `9` | `F'` | `D` | `D2` |
| `2` | `D` | `6` | `R` | `A` | `B` | `E` | `L2` |
| `3` | `D'` | `7` | `R'` | `B` | `B'` | `F` | `R2` |

A block is 8 nybbles, then Rule B.

Padding. Append the marker nybble `8`. Let `n = (8 - (length mod 8)) mod 8`, and append the first `n` nybbles of `6 0 7 1 8 2 9 3`. While the tape is shorter than 24 nybbles, append `6 0 7 1 8 2 9 3` again. The tape is then at least three blocks.

| Message | Steps | Digest hex | Final facelets |
| --- | --- | --- | --- |
| empty | 30 | `09A5C17D19DDDBEB4` | `YYGGWWWWWOOOGRYOYBRBBGGOBYGRBWRYGBBRGWGOORYWWYORRBBYRO` |
| `a` | 30 | `08BA8C16E8074354D` | `WBBBWGRWGORORRRYOBBOWYGBYGOGOBGYYYYWRWYYORGWRWOGWBBRGO` |
| byte `A7` | 30 | `12326FE0A08A76C41` | `WWBWWGYRWBWYORGYRGRWROGYOGGBYOBYYRRWROBOOGGYWOBGRBBOBY` |
| `hello` | 30 | `0DF7902ED206DF88C` | `BBWBWWRRBWBGGRRWGGBWOWGYYYRORBOYWYGWOOYOOORGGRYYBBYORG` |
| `cube` | 30 | `01F2D89DA1132D945` | `YRRBWGWRWRWGYRBWRYBBGWGGWOBGYOGYYYWORWRBOOGOOYGBYBOBRO` |

## scramble_v2

Current. The design notes record a collision attack around `2^32.6`, and a meet-in-the-middle second-preimage attack around `2^33`. The digest is about 65.2 bits wide because that is the order of the cube group. Those facts are why this version is still a toy. It stays callable so the demo and these vectors keep working.

Each nybble is two clockwise quarter turns, then Rule B. The block index is the nybble's index in the padded tape, and `index` is `0` for the first turn and `1` for the second.

| Nybble | Turns | Nybble | Turns | Nybble | Turns | Nybble | Turns |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `0` | `U R` | `4` | `D R` | `8` | `F U` | `C` | `L U` |
| `1` | `U F` | `5` | `D F` | `9` | `F D` | `D` | `F L` |
| `2` | `U L` | `6` | `R U` | `A` | `B U` | `E` | `R F` |
| `3` | `U B` | `7` | `R D` | `B` | `F R` | `F` | `R B` |

Padding. Append the marker nybble `8`. While the tape is shorter than 12 nybbles, append the cycle `6 0 7 1`.

| Message | Steps | Digest hex | Final facelets |
| --- | --- | --- | --- |
| empty | 39 | `06024E9B61052F461` | `RRORWBOYOWRBGRWROOBGGWGRYYWGBGGYWWOYBWWOOGRORYYYBBBGYB` |
| `a` | 39 | `1588A6469CFE7B286` | `RRYBWYGGGROBGRYBWWYWYGGOGBOOOWRYRBBRGROWOYYGWRYWBBOBWO` |
| byte `A7` | 39 | `1552B6EF7DA10C2E8` | `OGBYWYBWRYORWROGWRRGGBGROROWGYBYOBBWYRWBOWOOGYYBGBRGYW` |
| `hello` | 39 | `052A3C7D12291D140` | `ORWWWWWYWGRRORWGBOROORGBOBYBRRGYYYWYYOGGOGBYWBYBBBOGGR` |
| `cube` | 39 | `132FDCE0BF26E5898` | `OGBYWWWYYGBRBRWGRORGROGOBRWOYORYGRBWGOGWOWBBYYOYGBRBYW` |
