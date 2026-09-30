<!-- Owns: the M9 (v2 two-card window) search, its numbers, and what they do and do not show. Maintenance rules: ../../../DOCS.md. -->
# M9: two-card windows of the v2 E_m

M9 asks whether two different 2-card windows of E_m (cards at positions `p`, `p+1`, from the same state `(W, o)`) can reach the same state. The adjacent-card swap `(a, b)` vs `(b, a)` is the case the ledger names. Status: **partial**. One half is kernel-checked. The other half is an exhaustive Python computation, not a Lean theorem.

## Kernel-checked (Lean, `../lean/MegaDreifach/G2Nets.lean`)

- `twoCard_same_first_ne`: same first card, different second cards (both `< 52`) never collide, from any `InjPos` position on any `GripOk` grip. This is M8 (`net2_ne`) applied at the intermediate grip.
- `twoCard_collision_nets`: if two windows from a position with injective `cp` / `ep` reach the same *position*, the net products at the intermediate grips are equal, `net2 o1 b ∘ net2 o a = net2 o2 d ∘ net2 o c`. `W` cancels. That is the finite condition the search enumerates.

## Computed, not kernel-checked (`m9_search.py`)

`python3 m9_search.py` (stdlib only, about 10 s, under 100 MB; run in CI, job `megadreifach-lean`). The script parses the SPEC tables from [`Em.lean`](../lean/MegaDreifach/Em.lean) and first reproduces all 8 v2 KATs, so it runs the same E_m that `em_block_refines` ties to `Generated.em_block`. Then:

1. **Nets.** The 60×52 nets are pairwise distinct per grip. This repeats the Lean check `nets_nodup`.
2. **Read injectivity.** At every read configuration (held face, noon, corner or edge), distinct pieces show distinct ordered colour pairs, whatever their orientations. `abs_reorient` is a lookup on that pair, so distinct pieces give distinct grips.
3. **Position candidates.** Over every grip `o`, every intermediate grip pair `(o1, o2)` and every card quadruple with `a ≠ c`, the net products agree in **24,300** cases (`a < c`). **420** of them are adjacent swaps (`c, d = b, a`). The intermediate grips range over all 60, so the count does not depend on which grips are reachable.
4. **Second read.** For each candidate and each read parity of `p`, the script finds the slot of `W` whose piece the second card reads, and compares that slot across the two windows. It is **never** the same: 0 of 48,600.

Taken together: if the positions agree (3), then the two final grips come from reads of different pieces of `W` (4). Those pieces differ because `W` is injective, so the grips differ (2) and the states differ. So there is no 2-card window collision from any position with injective `cp` / `ep`. Adjacent swaps included, for every grip and both parities. That completes M9 as stated in the ledger ("no 2-card local collision"), **on the strength of the Python computation**.

## Why it is not a Lean theorem yet

- **Size.** Step 3 compares about 9.7 million net products (60 grips × 52 × 60 × 52). M8 needed 3,120 nets and about 85 s of kernel `decide!`. List-based products under kernel evaluation are orders of magnitude slower than the Python, and `native_decide` is forbidden here. A kernel proof needs a reduction first. One candidate is covariance under the 60 rotations, which would cut the grip `o` to one representative (not yet proved for `g2Step`). Another is a small certificate: for each non-candidate pair, one coordinate that differs, checked per grip.
- **Read model.** Steps 2 and 4 need Lean lemmas about `Em.readGrip` after `held_turn`: which `W` slot is read, and injectivity of the read. Those are finite (12 faces × 5 noons × 2 parities) and look cheap. They are not written yet.

## What this does not show

- Not block-level. Two windows that end in different states can still reach the same state later in the block: from different grips the next nets differ, so left-cancellation no longer applies. [SPEC §8](../../../primitives/hash/megadreifach/SPEC.md#8-security-status) reports 0 whole-block swap collisions in IV-anchored searches (empirical, about 2^20 trials per test). Nothing here proves that.
- Not collision resistance of `Hash`. Free-start pseudo-collisions are easy ([SPEC §8](../../../primitives/hash/megadreifach/SPEC.md#8-security-status)).
- Non-injective `W` (not a reachable chaining value; every `InjPos` position is injective) is outside the statement.
