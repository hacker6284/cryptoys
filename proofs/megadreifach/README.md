# MegaDreifach proofs

Normative product name: **MegaDreifach**. The puzzle/group library stays **megaminx**.

The published definition is [`primitives/hash/megadreifach/SPEC.md`](../../primitives/hash/megadreifach/SPEC.md) plus [`megadreifach.sudo`](../../primitives/hash/megadreifach/megadreifach.sudo). This directory is the obligation ledger for algebraic correctness of a **hand-written Lean model**. It is not a second specification. It does **not** claim that the sudo text equals the Lean model (that is a future emitter proof).

MegaDreifach is a toy Merkle–Damgård hash on the megaminx group. The Lean package below proves **correctness / algebraic** facts (position legality, group law, encodings, pad injectivity, DM algebra). It does **not** prove collision resistance, ideal-cipher-on-G, or AES-class security. A green `lake build` is not a security claim.

Length extension on bare `Hash` is **accepted by design** (SHA-2-shaped). Do not read the pad theorems as “LE is gone.”

## Three layers (be honest)

| Layer | What it is | Trust base |
| --- | --- | --- |
| **(a) Theorems about the Lean model** | Position legality, compose/inverse, rank packing, φ injectivity, pad injectivity, DM / 3-solve algebra, `require_permutation`, G2 one-card *reduction*. | Lean kernel. `lake build`. No `sorry`. No `native_decide`. |
| **(b) Vector agreement** | KAT *metadata* (pad lengths, block counts, digest width, `\|G\|`) in `vectors/` checked by `lake exe megadreifach`. Full Hash digest equality is OPEN. | Compiled Lean evaluation. **Not** kernel `decide`. **Not** a proof that sudo = Lean. |
| **(c) Future: emitter** | A sudocode terminating-subset Lean emitter that could prove the sudo text *is* the Lean model. | In progress elsewhere. Do not wait for it. Do not read (a) or (b) as a substitute. |

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

## What is open or not claimed

| Stone | Claim | Status |
| --- | --- | --- |
| M3 (glue) | Single `rankPosition` inverse on `isLegal` (even-perm Lehmer prefix + unrank) | Open; ingredients are in `Rank.lean` |
| M8 (nets) | Pairwise distinctness of the 60×52 concrete face-turn nets | OPEN. Too large for kernel `decide`. Not a blocker. |
| M9 | Abs-G2 L2 mid-block: no 2-card local collision | OPEN (sketch in STONES.md). Informal proof in research `G2_PROOF.md`. Not a blocker. |
| M13 | Lean digests of exported KATs equal `kats/megaminx_hash_kats.json` | OPEN; metadata only. Research Hash hexes are not sudo-asserted. |
| — | sudo text equals this Lean model | Not claimed. Emitter is future. |
| — | Collision resistance of Hash; IV-anchored collision | Not claimed. Free-start `HashDeckBody` is broken; L3 collisions **exist** |
| — | Ideal-cipher-on-G / PRF of `E_m` | Not claimed |
| — | Birthday ≈ 2^113 as a theorem | SPEC honesty only |
| — | Relative reorient L2-safety | Disproved in research; abs only. Not a Lean target |
| — | PRESSURE.md attack tables | Evidence / research. Never theorems |

## Lean package

Toolchain **4.14.0**, no Mathlib — same pin as TwoDeck. From a checkout with [elan](https://github.com/leanprover/elan):

```sh
cd proofs/megadreifach/lean
lake build
```

`lake exe megadreifach` prints a one-line summary **and** runs the KAT metadata checks. The library target is `MegaDreifach`. Namespaces are `MegaDreifach`.

Shipped theorems contain no `sorry` and no `native_decide`. Kernel `decide` is used on closed numerals (`2^224 < 52!`, `|G| < 256^29`, IV-COOK12 list predicates), matching TwoDeck S5. The proofs CI job (`proofs.yml`) runs a sorry / `native_decide` gate, `lake build`, and `lake exe megadreifach`.

## Reading order

M1 → M2 → M4 → M5 → M7 → M3 (packing) → M6 → M10/M11/M12 → M8 reduction. Leave M8 nets, M9, and M13 OPEN. Do not wait for the emitter. Do not promote pressure tables or L3-absence slogans.
