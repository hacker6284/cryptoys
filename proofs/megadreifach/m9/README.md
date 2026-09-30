<!-- Owns: the M9 (v2 two-card window) search, its numbers, and what they do and do not show. Maintenance rules: ../../../DOCS.md. -->
# M9: two-card windows of the v2 E_m

M9 asks whether two different 2-card windows of E_m can reach the same state. The windows hold cards at the same deal positions `p`, `p+1` and start from the same state `(W, o)`. The adjacent-card swap, `(a, b)` against `(b, a)`, is the case the ledger names.

**Status: PARTIAL.** The claim is: for 2-card windows at the same deal positions `p`, `p+1`, starting from an `InjPos` `W`, any `GripOk` grip `o`, cards `< 52` and both parities of `p`, there is no state collision. The same-first-card half is kernel-checked (`twoCard_same_first_ne`). The different-first-card half is exhaustive computational evidence (`m9_search.py`), not a proof. Do not claim M9 from the Python scan.

## Kernel-checked (Lean, `../lean/MegaDreifach/G2Nets.lean`)

- `twoCard_same_first_ne`: from any `InjPos` position on any `GripOk` grip, two windows with the same first card and different second cards (both `< 52`) never reach the same state. This is M8 (`net2_ne`) applied at the intermediate grip.
- `twoCard_collision_nets`: suppose two windows start from a position with injective `cp` / `ep` and reach the same *position*. Then the net products at the intermediate grips are equal, `net2 o1 b ∘ net2 o a = net2 o2 d ∘ net2 o c`, because `W` cancels. That equality is the finite condition the search enumerates.

## Computational evidence, not a proof (`m9_search.py`)

`python3 m9_search.py` runs stdlib-only Python: about 20 s in CI, under 100 MB. It runs in CI, job `megadreifach-lean`. The script reuses the tables of [`Em.lean`](../lean/MegaDreifach/Em.lean) and first reproduces the 8 v2 KATs. That is evidence that its Python E_m matches `Em`, not proof that they are identical. It asserts every count it reports. The steps:

1. **Nets.** The 60×52 nets are pairwise distinct per grip. This repeats the Lean check `nets_nodup`.
2. **Read injectivity across all read configurations.** The script covers every held face, noon and read kind (corner or edge), every piece and every orientation. One ordered colour pair never comes from two different pieces, even across different read configurations: there are 60 corner pairs and 60 edge pairs, with 0 ambiguous. Every read pair is the (up, front) pair of exactly one rotation, and `abs_reorient` returns that rotation (asserted). So distinct pieces give distinct grips, even when the two windows read with different faces or noons (`o1 ≠ o2`, `b ≠ d`).
3. **Position candidates.** The search runs over every grip `o`, every intermediate grip pair `(o1, o2)` and every card quadruple with `a ≠ c`. The net products agree in **24,300** cases (`a < c`), and **420** of those are adjacent swaps (`c, d = b, a`). The intermediate grips range over all 60, so the count does not depend on which grips are reachable.
4. **Second read.** For each candidate and each read parity of `p`, the script finds the slot of `W` whose piece the second card reads, and compares that slot across the two windows. It is **never** the same: 0 of 48,600.

How the steps combine: if the positions agree (3), the two final grips come from reads of two different slots of `W` (4). Those slots hold different pieces because `W` is injective, so the grips differ (2) and so do the states. This argument depends on the Python computation for steps 2–4, so it is evidence, not a proof. M9 stays PARTIAL.

## Why it is not a Lean theorem yet

- **Size.** Step 3 compares about 9.7 million net products (60 grips × 52 × 60 × 52). M8 needed 3,120 nets and about 85 s of kernel `decide!`. List-based products under kernel evaluation are orders of magnitude slower than the Python, and `native_decide` is forbidden here. A kernel proof needs a reduction first. One candidate is covariance under the 60 rotations, which would cut the grip `o` down to one representative (not yet proved for `g2Step`). Another is a small certificate: for each non-candidate pair, one coordinate that differs, checked per grip.
- **Read model.** Steps 2 and 4 need Lean lemmas about `Em.readGrip` after the held-face turn: which slot of `W` is read, and that the read is injective across configurations. Both are finite (12 faces × 5 noons × 2 kinds) and look cheap, but neither is written yet.

## What this does not show

- It is not block-level. Two windows that end in different states can still reach the same state later in the block. From different grips the next nets differ, so left-cancellation no longer applies. [SPEC §8](../../../primitives/hash/megadreifach/SPEC.md#8-security-status) reports 0 whole-block swap collisions in IV-anchored searches (empirical, about 2^20 trials per test). Nothing here proves that.
- It is not collision resistance of `Hash`. Free-start pseudo-collisions are easy ([SPEC §8](../../../primitives/hash/megadreifach/SPEC.md#8-security-status)).
- A `W` that is not injective is outside the statement. Such a `W` is never a reachable chaining value, because every `InjPos` position is injective.
