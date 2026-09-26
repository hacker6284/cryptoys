# MegaDreifach proofs

Normative product name: **MegaDreifach**. The puzzle/group library stays **megaminx**.

The published definition is [`primitives/hash/megadreifach/SPEC.md`](../../primitives/hash/megadreifach/SPEC.md) plus [`megadreifach.sudo`](../../primitives/hash/megadreifach/megadreifach.sudo). Sudo is normative. Emitted Lean under `lean/Generated/` is the algorithm (`v_Hash`). `lean/MegaDreifach/` is the obligation ledger for algebraic stones sudo does not express. It is not a second `Hash`. See [`../ANTI_DRIFT.md`](../ANTI_DRIFT.md). This does **not** claim sudo↔Lean semantic-equivalence theorems. The emit terminates gate is on. MegaDreifach sudo is terminates-ready: bigint trim/peel/carry, φ / even-perm search, and the Hash MD walk are bounded `for`.

MegaDreifach is a toy Merkle–Damgård hash on the megaminx group. The Lean package below proves **correctness / algebraic** facts (position legality, group law, encodings, pad injectivity, DM algebra). It does **not** prove collision resistance, ideal-cipher-on-G, or AES-class security. A green `lake build` is not a security claim.

Length extension on bare `Hash` is **accepted by design** (SHA-2-shaped). Do not read the pad theorems as “LE is gone.”

## Three layers (be honest)

| Layer | What it is | Trust base |
| --- | --- | --- |
| **(a) Theorems about the proof-only model** | Position legality, compose/inverse, rank packing, φ injectivity, pad injectivity, DM / 3-solve algebra, `require_permutation`, G2 one-card *reduction*. | Lean kernel. `lake build` of the proof package. **Not** Hash. |
| **(b) Generated TAP** | `proofs/emit_lean.sh` → `lake` → `megadreifach_test` (11/11). | Compiled emitted Lean. **Not** a sudo=Lean theorem. |
| **(c) KAT metadata** | Pad lengths, block counts, digest width, `\|G\|` in `vectors/` via `lake exe megadreifach`. Full Hash digest equality in *this* package is OPEN (M13). Research hexes were refreshed to current sudo (Python = emitted Lean). | Compiled Lean evaluation. |
| **(d) Equivalence** | sudo text = generated Lean, or `hashBlocks` = `Generated.v_Hash`. | OPEN. |

## What is proved

Sorry-free Lean 4.14 theorems. Details and file tags are in [`STONES.md`](STONES.md).

| Stone | Claim | Status |
| --- | --- | --- |
| M1 | Position model + legality predicates | Proved |
| M2 | Compose associative; inverse round-trip (hypothesized perm inverses) | Proved |
| M3 | Digest rank packing: mixed-radix components, even last-pair, 29-byte inj, `listOf` inj | Proved at the packing layer; even-perm Lehmer-prefix glue still open |
| M4 | Factoradic φ injective for `n < 2^{224}` | Proved |
| M5 | Pad B=28 injective; length field recovers bit length | Proved |
| M6 | DM `h' = compose h e`; 3-solve restores `(h', h'⁻¹, id)` | Proved |
| M7 | `HashDeckBody` rejects non-permutations | Proved |
| M8 | One-card G2 injectivity | Reduction proved; 60×52 net distinctness OPEN |
| M10 | F3 t=12 is a well-defined iterate | Proved (algebraic) |
| M11 | IV-COOK12 arrays satisfy legality predicates | Proved (kernel `decide` on the lists) |
| M12 | MD chain is the fold of DM; digest of the final `h` | Proved (algebraic) |
| Link 2 | `pad_message` ≃ algebraic `pad` on `PadWf` (bytes `≤ 255`, `8 * length` fits in an i64) | Proved (`pad_message_refines`, `pad_message_refines_array`, `pad_z_refines`). Not collision resistance. Not `v_Hash`. |
| Link 2 | `compose` ≃ algebraic `compose` on `PosWf` (lengths 20/20/30/30, in-range indices, orientations `< 3` / `< 2`) | Proved (`compose_refines`, `compose_refines_array`). Trap-free i64 indices. Not `v_Hash`. |
| Link 2 | `require_permutation` ≃ algebraic `requirePermutation` on `DealWf` (length 52, nonnegative ids `< 52`, no duplicates) | Proved (`require_permutation_refines`, `require_permutation_refines_array`). Trap-free i64 indices. Not `v_Hash`. |
| Link 2 | `pack_ori2` ≃ algebraic `packOri2` on `Ori2Wf` (length 30, entries `< 2`) | Proved (`pack_ori2_refines`, `pack_ori2_refines_array`). Value `< 2^29`, one limb. Not `v_Hash`. |
| Link 2 | `pack_ori3` ≃ algebraic `packOri3` on `Ori3Wf` (length 20, entries `< 3`) | Proved (`pack_ori3_refines`, `pack_ori3_refines_array`). Value `< 3^19`, at most two limbs. Not `v_Hash`. |
| Link 2 | `even_perm_rank_big` ≃ algebraic `evenRank` on `Rank20Wf` (length 20, permutation of `0..19`, rank `< 2·10^9`) | Proved (`even_perm_rank_big_refines`, `even_perm_rank_big_refines_array`). One-limb multiply, two-limb sum. Not every corner rank. Not length 30. Not M3 injectivity. Not `v_Hash`. |
| Link 2 | `position_to_bytes` ≃ algebraic `positionToBytes` on `PosBytesWf` (corner rank 0, corner-ori pack 0, edge prefix `0..27`, any `Ori2Wf` edge ori) | Proved (`position_to_bytes_refines`, `position_to_bytes_refines_array`). Digest is `toBE 29 (packOri2 eo)`. `even30` = `30!/2` on a zero accumulator. Not every legal position. Not `v_Hash`. |
| Link 2 | `big_from_be` on `k` zero bytes (`k` fits in an i64, including the 28-byte pad block) ≃ `fromBE = 0` | Proved (`big_from_be_zeros`, `big_from_be_zeros_fromBE`, `big_from_be_zero_pad`). Empty limb list. Not a general pad block. Not `phi_chunk`. Not `v_Hash`. |
| Link 2 | `big_factorial n` ≃ `factorial n` for `n ≤ 13`, and `peel_leading` of zero ≃ `(0, 0)` on that domain | Proved (`big_factorial_refines`, `peel_leading_zero`, `peel_leading_zero_digit`). `12!` is one limb; `13!` is the last one-limb×one-limb product. Digit `0 / d!`. Not `51!`. Not `phi_chunk`. Not `v_Hash`. |
| Link 2 | `big_from_be` ≃ `fromBE` on `BeShortWf` (length `≤ 3`, bytes `≤ 255`) | Proved (`big_from_be_short`, `big_from_be_short_array`, `big_from_be_byte`). Value `< 256^3 < 10^9`, one limb. Not length 4. Not the 28-byte pad block. Not `phi_chunk`. Not `v_Hash`. |
| Link 2 | `big_from_be` ≃ `fromBE` on `BeLimb2Wf` (length `≤ 7`, bytes `≤ 255`) | Proved (`big_from_be_limb2`, `big_from_be_limb2_array`, `big_add_byte`). Value `< 256^7 < 10^18`, at most two limbs. Not length 8. Not the 28-byte pad block. Not `phi_chunk`. Not `v_Hash`. |
| Link 2 | `peel_leading` ≃ factoradic digit on one limb (`d ≤ 12`, `n < 10^9`) | Proved (`peel_leading_limb`, `peel_leading_factorial`). Pair is `(n % d!, n / d!)`. Digit `1` on `d!` itself. Not `d ≥ 13`. Not `51!`. Not `phi_chunk`. Not `v_Hash`. |
| Link 2 | `big_factorial n` ≃ `factorial n` for `n ≤ 19`, and `peel_leading` of zero for `d ≤ 19` | Proved (`big_factorial_two`, `big_mul_two`, `peel_leading_zero_two`). `13!`–`19!` are two limbs (`19! < 10^18`); `20!` is three limbs. Zero digit `0 / d!`. Not a positive two-limb peel. Not `51!`. Not `phi_chunk`. Not `v_Hash`. |
| Link 2 | `peel_leading` of `d!` ≃ digit `1` for `d ≤ 19` | Proved (`peel_leading_factorial_two`, `divmod_sq`, `big_mul_one`). Remainder `0`. Two-limb division of values below `10^18`. Not an arbitrary positive rank. Not `20!`. Not `51!`. Not `phi_chunk`. Not `v_Hash`. |
| Link 2 | `big_factorial n` ≃ `factorial n` for `n ≤ 20` | Proved (`big_factorial_three`, `big_mul_three`). `20! = 19! · 20` is three limbs (`10^18 ≤ 20! < 10^27`). Not `51!`. Not `phi_chunk`. Not `v_Hash`. |
| Link 2 | `big_factorial n` ≃ `factorial n` for `n ≤ 26` | Proved (`big_factorial_acc3`, `big_mul_acc3`). `21!`–`26!` multiply a three-limb accumulator by `i ≤ 26` and stay below `10^27`. Not `27!`. Not `51!`. Not `phi_chunk`. Not `v_Hash`. |
| Link 2 | `peel_leading` of `d!` ≃ digit `1` for `d ≤ 26` | Proved (`peel_leading_factorial_three`, `divmod_cube`, `big_mul_one_three`). Remainder `0`. For `d ≥ 20`, `d!` is three limbs (`26! < 10^27`). Not an arbitrary positive rank. Not `27!`. Not `51!`. Not `phi_chunk`. Not `v_Hash`. |
| Link 2 | `peel_leading` of zero ≃ `(0, 0)` for `d ≤ 26` | Proved (`peel_leading_zero_three`, `peel_leading_zero_digit_three`). Digit `0 / d!`. For `d ≥ 20`, `d!` is three limbs; the closing multiply is the zero coefficient. Not a positive rank. Not `27!`. Not `51!`. Not `phi_chunk`. Not `v_Hash`. |
| Link 2 | `peel_leading` of `n < d!` ≃ `(n, 0)` for `d ≤ 26` | Proved (`peel_leading_below`, `peel_leading_below_digit`). Digit `0`. Positive two-limb ranks for `13 ≤ d` and three-limb ranks for `20 ≤ d`, strictly below `d!`. Not `d!` itself. Not a positive digit. Not `27!`. Not `51!`. Not `phi_chunk`. Not `v_Hash`. |
| Link 2 | `peel_leading` of `n` in `[d!, 2·d!)` ≃ digit `1` for `d ≤ 19` | Proved (`peel_leading_one`, `peel_leading_one_digit`). Remainder `n - d!`, which may be positive. For `13 ≤ d` the rank is two limbs (`2·19! < 10^18`). Not `d ≥ 20`. Not a digit `q ≥ 2`. Not `27!`. Not `51!`. Not `phi_chunk`. Not `v_Hash`. |
| Link 2 | `peel_leading` of `n` in `[d!, 2·d!)` ≃ digit `1` for `d ≤ 26` | Proved (`peel_leading_one_three`, `peel_leading_one_three_digit`, `mag_sub_three_le`). Remainder `n - d!`, which may be positive. For `20 ≤ d` the rank is three limbs (`2·26! < 10^27`). Not a digit `q ≥ 2`. Not `d ≥ 27`. Not `27!`. Not `51!`. Not `phi_chunk`. Not `v_Hash`. |
| Link 2 | `peel_leading` ≃ `(n % d!, n / d!)` for `d ≤ 26` and `n < limbCap d` | Proved (`peel_leading_cap`, `peel_leading_cube`, `peel_leading_sq`). Every digit, including `q ≥ 2`. Cap is `10^9` / `10^18` / `10^27`. Not `27!`. Not `51!`. Not `phi_chunk`. Not `v_Hash`. |
| Link 2 | `big_divmod_small` ≃ `n / d` on any width, divisor one limb | Proved (`big_divmod_small_refines`, `big_divmod_nat`). Not `big_mul`. Not `51!`. Not `phi_chunk`. Not `v_Hash`. |
| Link 2 | `big_mul` of a wide left factor by one limb ≃ `natLimbs (q · n)` | Proved (`big_mul_wide_refines`, `big_mul_nat`). Accumulator on the left. Not `v_Hash`. |
| Link 2 | `big_mul` of one limb on the left by a wide digit string ≃ `natLimbs (q · n)` | Proved (`big_mul_left_refines`, `big_mul_left_nat`). Digit times a wide factorial, the orientation `peel_leading` emits. Not `mag_sub`. Not `peel_leading` for `d > 26`. Not `v_Hash`. |
| Link 2 | `big_factorial n` ≃ `factorial n` for `n ≤ 51` | Proved (`big_factorial_51`). `51! < 10^72`, at most eight limbs. Not `peel_leading` for `d > 26`. Not `phi_chunk`. Not `v_Hash`. |
| Link 2 | `mag_sub` ≃ `n - m` on canonical limbs, any width, `m ≤ n` | Proved (`mag_sub_nat`). Trimmed digits are `natLimbs (n - m)`. Not `big_add`. Not `v_Hash`. |
| Link 2 | `peel_leading` ≃ `(n % d!, n / d!)` for `d ≤ 51` and `n / d! < 10^9` | Proved (`peel_leading_51`). One-limb digit. `n < 10^81`. Not a 28-byte `big_from_be`. Not `phi_chunk`. Not `v_Hash`. |

## What is open or not claimed

| Stone | Claim | Status |
| --- | --- | --- |
| M3 (glue) | Single `rankPosition` inverse on `isLegal` (even-perm Lehmer prefix + unrank) | Open; ingredients are in `Rank.lean` |
| M8 (nets) | Pairwise distinctness of the 60×52 concrete face-turn nets | OPEN. Too large for kernel `decide`. Not a blocker. |
| M9 | Abs-G2 L2 mid-block: no 2-card local collision | OPEN (sketch in STONES.md). Informal proof in research `G2_PROOF.md`. Not a blocker. |
| M13 | Proof-package digests of exported KATs equal `kats/megaminx_hash_kats.json` | OPEN; metadata only. Hexes refreshed 2026-09-24 to current sudo (Python = emitted Lean). No handwritten `Hash` body. |
| — | sudo text equals generated Lean; algebraic fold equals `Generated.v_Hash` | OPEN. See [`../ANTI_DRIFT.md`](../ANTI_DRIFT.md). |
| — | Full `Generated.v_Hash` refinement; Scramble algebraic ≃ Generated | OPEN. Pad, `compose`, `require_permutation`, `pack_ori2`, `pack_ori3`, length-20 `even_perm_rank_big` (`Rank20Wf`), zero-rank `position_to_bytes` (`PosBytesWf`), zero-byte `big_from_be`, short and two-limb `big_from_be`, `big_factorial` (`n ≤ 51`), `peel_leading` below `limbCap d` for `d ≤ 26`, `peel_leading` for `d ≤ 51` when `n / d! < 10^9` (`peel_leading_51`), arbitrary-width `mag_sub` (`mag_sub_nat`), arbitrary-width `big_divmod_small`, wide-by-small `big_mul`, and one-limb-times-wide `big_mul` (`big_mul_left_nat`) are closed. Still open: arbitrary-width `big_add` / `mag_add`, 28-byte `big_from_be`, and `phi_chunk` / `phi_inv`. Full `v_Hash` is still open. Not collision resistance. |
| — | Collision resistance of Hash; IV-anchored collision | Not claimed. Free-start `HashDeckBody` is broken; L3 collisions **exist** |
| — | Ideal-cipher-on-G / PRF of `E_m` | Not claimed |
| — | Birthday ≈ 2^113 as a theorem | SPEC honesty only |
| — | Relative reorient L2-safety | Disproved in research; abs only. Not a Lean target |
| — | PRESSURE.md attack tables | Evidence / research. Never theorems |

## Lean packages

Two Lake packages, toolchain **4.14.0**, no Mathlib — same pin as DoubleDeal.

**Generated (algorithm).** Do not edit:

```sh
proofs/emit_lean.sh megadreifach
cd proofs/megadreifach/lean/Generated && lake build && ./.lake/build/bin/megadreifach_test
```

**Proof-only.** From a checkout with [elan](https://github.com/leanprover/elan):

```sh
cd proofs/megadreifach/lean
lake build
```

`lake exe megadreifach` prints a one-line summary **and** runs the KAT metadata checks. The library target is `MegaDreifach`.

Shipped theorems contain no `sorry` and no `native_decide`. Kernel `decide` is used on closed numerals (`2^224 < 52!`, `|G| < 256^29`, IV-COOK12 list predicates). CI also emits Lean from `megadreifach.sudo` and runs Generated TAP.

## Reading order

M1 → M2 → M4 → M5 → M7 → M3 (packing) → M6 → M10/M11/M12 → M8 reduction. Leave M8 nets, M9, and M13 OPEN. Generated TAP is the Hash oracle; do not treat `hashBlocks` as Hash. Do not promote pressure tables or L3-absence slogans.
