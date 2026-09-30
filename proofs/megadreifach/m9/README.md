<!-- Owns: M9 (v2 two-card windows): the proof route, the decoder certificate and its numbers, the Python cross-check and its numbers, and what they do and do not show. Maintenance rules: ../../../DOCS.md. -->
# M9: two-card windows of the v2 E_m

M9 asks whether two different 2-card windows of E_m can reach the same state. The windows hold cards at the same deal positions and start from the same state `(W, o)`. The adjacent-card swap, `(a, b)` against `(b, a)`, is the case the ledger names.

**Status: CLOSED for 2-card windows** (kernel-checked, `twoCard_ne` in [`M9.lean`](../lean/MegaDreifach/M9.lean)). The statement: from a position `W` with `InjPos W`, on any `GripOk` grip `o`, two 2-card windows `(a, b) ≠ (c, d)` with all four card ids `< 52`, dealt at the same deal positions `pos1`, `pos2`, never reach the same state. `pos1` and `pos2` are arbitrary naturals, so both read parities (corner and edge second reads) and in particular the positions `p`, `p+1` are covered. Scope: 2-card windows only. It is not block-level and not collision resistance (see [below](#what-this-does-not-show)).

## Kernel-checked (Lean)

- `twoCard_same_first_ne` ([`G2Nets.lean`](../lean/MegaDreifach/G2Nets.lean)): same first card, different second cards. M8 (`net2_ne`) at the intermediate grip.
- `twoCard_collision_nets` (`G2Nets.lean`): equal positions from a `W` with injective `cp` / `ep` give equal net products, `net2 o1 b ∘ net2 o a = net2 o2 d ∘ net2 o c` (`W` cancels).
- `g2Step_cov`, `net2_cov` ([`G2CovRead.lean`](../lean/MegaDreifach/G2CovRead.lean), tables in [`G2Cov.lean`](../lean/MegaDreifach/G2Cov.lean)): rotation covariance. For each of the 60 whole-puzzle rotations `s` and every `GripOk` grip `o`, `g2Step (conj s g, rotG s o) card pos = (conj s g', rotG s o')` where `(g', o') = g2Step (g, o) card pos`, for every card and deal position. Here `conj s g` relabels `g` by the rotation (corner orientations included) and `rotG s o` relabels the grip. So `net2 (rotAt s) card = conj s (net2 gripId card)`.
- `m9_canon` ([`M9.lean`](../lean/MegaDreifach/M9.lean)): the different-first-card half at the identity grip `gripId`.
- `twoCard_diff_first_ne` (`M9.lean`): the different-first-card half on every `GripOk` grip, from `m9_canon` by covariance (`twoCard_cov`).
- `twoCard_ne` (`M9.lean`): the two halves together.

All of them are sorry-free, use no `native_decide`, and depend only on `propext`, `Classical.choice` and `Quot.sound` (default axiom gate).

## Proof route for different first cards

1. **Reduce the grip.** `o = rotAt s`. The window from `(W, rotAt s)` is the rotation `s` of the window from `(unconj s W, gripId)` (`twoCard_cov`: `g2Step_cov` twice, the intermediate grip stays `GripOk`). `conj s` and `rotG s` are injective and `unconj s` keeps `InjPos`, so a collision at `o` gives one at `gripId`.
2. **Products at `gripId`.** A collision gives equal net products (`twoCard_collision_nets`). With intermediate grip `rotAt s1` the product is `compose (conj s1 (N0 b)) (N0 a)`, `N0 a = net2 gripId a` (`n0_table`, `net2_cov`). There are 52 × 60 × 52 = 162,240 items `(a, s1, b)` and 99,720 distinct products.
3. **Decode the first card.** The certificate is a decision tree over the 50 slot codes of a product. The kernel checks, for every item, that the tree walked on its product's codes ends at the leaf `a`, or at an ambiguity group listing `(a, s1, b)` (`m9dec_0` … `m9dec_59`, one per `s1`, collected in `dec_all`). Equal products walk alike, so two colliding windows with `a ≠ c` land in the same group.
4. **Separate the groups by the second read.** Each group entry also carries the two `W`-slots its second card reads: the corner slot (odd `pos2`) and the edge slot (even `pos2`). The kernel recomputes them (`inAmb`) and checks that entries with different first cards differ in both (`amb_table`). Equal states have equal final grips. Equal grips give equal colour pairs (`readColours_of_readGrip`, `absReorient` is injective on adjacent pairs). Equal colour pairs give equal pieces, across all read configurations (`corner_read_piece`: the two corner colours are cyclically consecutive on the cubie, `loc_next_table`; `edge_read_piece`). `W` is injective, so the two windows read the same `W`-slot, which step 4's check rules out.

## The certificate (`m9_cert.py`)

`python3 m9_cert.py` (stdlib only, about 8 s) writes [`M9Cert.lean`](../lean/MegaDreifach/M9Cert.lean); `python3 m9_cert.py --check` regenerates it in memory and fails if the committed file differs (CI, job `megadreifach-lean`). The certificate is untrusted data: a wrong tree or wrong slots fail the kernel checks, they cannot prove a false statement. It holds the 52 identity-grip nets, the tree (40,886 words of 26 bits in 65 `Nat` literals, greedy splits by weighted label entropy with integer tie-breaks) and 111 ambiguity groups with 384 entries. The file is about 330 KB.

**Kernel cost** (Lean v4.14.0, one core): `m9dec_<s1>` takes about 10 s and 2 GB each, so each `M9Dec<k>.lean` (10 grips) takes about 105 s and 2 GB, about 10.5 min in total; they build in parallel. The covariance tables take about 76 s (`G2Cov.lean`) and 41 s (`G2CovRead.lean`). The rest takes a few seconds.

## Python cross-check (`m9_search.py`)

`python3 m9_search.py` runs stdlib-only Python: about 20 s in CI, under 100 MB. It runs in CI, job `megadreifach-lean`, as an independent cross-check of the Lean proof; it is not part of the proof. It enumerates all 60 starting grips directly, with no covariance. The script reuses the tables of [`Em.lean`](../lean/MegaDreifach/Em.lean) and first reproduces the 8 v2 KATs. That is evidence that its Python E_m matches `Em`, not proof that they are identical. It asserts every count it reports. The steps:

1. **Nets.** The 60×52 nets are pairwise distinct per grip. This repeats the Lean check `nets_nodup`.
2. **Read injectivity across all read configurations.** The script covers every held face, noon and read kind (corner or edge), every piece and every orientation. One ordered colour pair never comes from two different pieces, even across different read configurations: there are 60 corner pairs and 60 edge pairs, with 0 ambiguous. Every read pair is the (up, front) pair of exactly one rotation, and `abs_reorient` returns that rotation (asserted).
3. **Position candidates.** The search runs over every grip `o`, every intermediate grip pair `(o1, o2)` and every card quadruple with `a ≠ c`. The net products agree in **24,300** cases (`a < c`), and **420** of those are adjacent swaps (`c, d = b, a`). `m9_cert.py` asserts 405 such pairs at the identity grip, and 60 × 405 = 24,300, as covariance predicts.
4. **Second read.** For each candidate and each read parity, the script finds the slot of `W` whose piece the second card reads, and compares that slot across the two windows. It is **never** the same: 0 of 48,600.

## What this does not show

- It is not block-level. Two windows that end in different states can still reach the same state later in the block. From different grips the next nets differ, so left-cancellation no longer applies. [SPEC §8](../../../primitives/hash/megadreifach/SPEC.md#8-security-status) reports 0 whole-block swap collisions in IV-anchored searches (empirical, about 2^20 trials per test). Nothing here proves that.
- It says nothing about windows of 3 or more cards.
- It is not collision resistance of `Hash`. Free-start pseudo-collisions are easy ([SPEC §8](../../../primitives/hash/megadreifach/SPEC.md#8-security-status)).
- A `W` that is not injective is outside the statement. Such a `W` is never a reachable chaining value, because every `InjPos` position is injective. Card ids `≥ 52` and grips that are not one of the 60 rotations are outside it too.
- Windows at different deal positions are outside it: both windows use the same `pos1` and the same `pos2`.
