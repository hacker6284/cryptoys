# TwoDeck proofs

Normative definition: [`primitives/cipher/twodeck/SPEC.md`](../../primitives/cipher/twodeck/SPEC.md). Stones live in SPEC §6. This directory is the correctness ledger for those stones, not a second specification.

TwoDeck is a toy block cipher. It has no cryptographic security claim. The Lean package below proves **correctness / algebraic** facts (bijections, round-trip, content-preservation). It does **not** prove bit-security, MDS diffusion, or a strong key schedule.

## What is proved

Sorry-free Lean 4.14 theorems. Details and file tags are in [`STONES.md`](STONES.md).

| Stone | Claim | Status |
| --- | --- | --- |
| S1 | Lay/scoop, SumRanks, ShiftRows, GridCycle, Compose are invertible as stated | Proved (GridCycle: `invMix ∘ Mix = id`) |
| S2 | Full / final round and Nr=6 encrypt/decrypt round-trip | Proved under abstract Compose-key bijections |
| S3 | PassKey is deterministic and content-preserving | Proved (`List.Perm`) |
| S4 | PassKey is injective (constructive inverse) | Proved (`Function.LeftInverse` / right inverse). Cycle structure is not. |
| S5 | Factoradic `unrankPerm` returns a permutation of its items | Proved; injectivity only for `3!` in Lean |
| S6 | CTR `counter_deck` length and nonce-prefix stability | Proved |
| S11 | Compose known-plaintext uniqueness; CTR nonce prefix | Proved at the Compose algebra layer |
| S12 | Full round peels as Compose ∘ unkeyed stem | Proved (definitional) |

## What is open or evidence-only

| Stone | Claim | Status |
| --- | --- | --- |
| S4 (orbits) | PassKey cycle structure / orbit lengths | Evidence only |
| S5 (full) | `unrankPerm` injective for `13!` / `52!` | Partial; `3!` is `native_decide` |
| S7 | Hand sheet refines §3 math | Open |
| S8–S10 | Differentials, slide, randomness stats | Evidence only; never "security results" |
| S13 | §5.3 bytes ↔ deck | Evidence in `encoding.test.mjs` / `demos/twodeck/cards.js` |
| — | `mixColumns ∘ invMixColumns = id` on arbitrary packets | Open (needs image / seat characterization) |
| — | Concrete PassKey output wired as the Compose `pos` map | Open; S2 uses abstract bijections |

## Lean package

Toolchain **4.14.0**, no Mathlib. From a checkout with [elan](https://github.com/leanprover/elan):

```sh
cd proofs/twodeck/lean
lake build
```

`lake exe twodeck` prints a one-line summary. The library target is `TwoDeck`. Namespaces are `TwoDeck`, not a workspace lineage name.

Shipped theorems contain no `sorry`. A proofs CI job runs `lake build` here and does not gate the Pages demo build.

## Reading order

SPEC §6 suggested order: **S1 → S2 → S12 → S3 → S4 → S5 → S6 → S11 → S7**, S13 as an encoding property test, and S8–S10 as living evidence. PassKey injectivity is proved here; the normative SPEC still says “open” until a follow-up edits §3.7 / §6.

### Why PassKey is invertible

At step \(i\) the controller \(C\) is placed on top of the key pile, so the inverse can read it. Every branch (suit-rotate the hand; proper-cut the hand, the key, or neither) depends only on \(C\) and the two pile lengths — hand \(= 51-i\) after the pop, key \(= i\) — never on hidden card identities. So each step is a bijection on \((\mathrm{hand},\mathrm{key})\) states of those sizes, and \(F\) is their composition. `invPassKeyStep` undoes one step; `passToKeyCutFallbackInv` walks the composition backwards.
