# DoubleDeal v12: attacking `PrimeNonSwapCase` (the last open piece of the covariant round conjecture)

The conjecture `roundBody_covariant_iff_id` (`security/DoubleDealSecurity/Rounds.lean`,
DRAFT-SORRY) is **still open** and keeps its `sorry`. `PrimeNonSwapCase`
(`security/DoubleDealSecurity/CovariantNarrow.lean`) is **still open**. This note
records two new proved results (the affine relabellings; the rank-partition lemma, one
step toward `PrimeNonSwapCase`), the routes tried toward the full case, where each
breaks, and the counterexample search. No covariant pair
(σ ≠ 1 with some τ) was found.

Labels (as in `../v12-covariant/NOTES.md`): PROVED (Lean, audited), CONDITIONAL
(hypothesis in the statement), EXACT (exhaustive, C or Python), MEASURED (sampled,
fixed seed). `F = unkeyedWithMix` = GridCycle ∘ stem. `Covariant σ F` means
`∃ τ, ∀ deck m, F(σ·m) = τ·F(m)`. `Cell0Cov σ τ` is the seat-26 condition
`stem(σ·m)₀ = τ(stem(m)₀)` on every deck (implied by covariance,
`cell0Cov_of_covPair`).

## The remaining case, exactly

`PrimeNonSwapCase`: every σ of prime order p ≤ 52 that is neither a transposition
nor a `v10Sym a x` is non-covariant. `prime_nonswap_case_iff` (heavy) proves it is
EQUIVALENT to the conjecture. By cycle type, the σ left are:
* p = 2: products of c disjoint transpositions, 2 ≤ c ≤ 26, minus the 3 nontrivial
  label shifts `v10Sym 0 x` (c = 26);
* p odd, 3 ≤ p ≤ 47: products of c disjoint p-cycles, 1 ≤ c ≤ ⌊52/p⌋, minus the 12
  rank shifts `v10Sym a 0` (p = 13, c = 4).

Covariance is not known to be invariant under conjugation by `v10Sym` (only
`Cell0Cov` is, `cell0Cov_conj`; v10Sym itself is not covariant), nor under
conjugation by a general relabelling (if the conjecture holds, the covariant set is
{1} and every conjugation preserves it, but that is the open statement). So no proved
symmetry reduces the problem by cycle type to finitely many σ.

## New PROVED result: the affine relabellings outside v10Sym

(The affine relabellings are the normalizer of v10Sym; true by the holomorph count,
not a Lean theorem.)

`security/DoubleDealSecurity/CovariantAffine.lean` (+ generated
`CovariantAffineLists.lean`), heavy `security/DoubleDealSecurityHeavy/CovariantAffine.lean`
(+ generated `CovariantAffineChecks.lean`), generator `aff_witness.py` (log
`aff_witness.log`, CI `--check`).
* In `CovariantNarrow.lean` (next to `covPair_mul` / `covPair_inv`): `cell0Cov_one`,
  `cell0Cov_mul`, `cell0Cov_inv`, `cell0Cov_self_of_commutes` (the seat-26 condition is
  closed under products and inverses, and every SumRanks-commuting ρ satisfies it with
  τ = ρ), `cell0Subgroup` (the σ with some τ), `cell0Cov_conj` now derived from them;
  and the generic two-deck witness check `pairsCheck` / `witnessCheck` /
  `not_cell0Cov_of_checks`, used for both the transpositions and the affine family,
  with one pair list `cell0Pairs` and one check A (`cell0PairsCheck_ok`).
* `linSym k g`: `(r, l) ↦ ((k+1) r, A_g l)` on (rank index c % 13, GF(4) label),
  k : Fin 12, g : Fin 6 (GL(2,2)); its tables `glTab`, `glInvTab`, `unitInvTab` are
  generated from `../v12-covariant/cell0lib.py` (the data the search uses), and Lean
  proves they give inverse bijections (`linFn_left`, `linFn_right`) and linear label
  maps (`glApp_gfAdd`). The affine relabellings are `v10Sym a x * linSym k g`: 3744
  parameter tuples, pairwise distinct relabellings (`affine_params_inj`).
* `roundBody_not_covariant_affine` (heavy, unconditional): for `(k, g) ≠ (0, 0)`,
  `v10Sym a x * linSym k g` is not covariant for ANY τ (3692 parameter tuples, pairwise
  distinct); `…_right` states the same for `linSym k g * v10Sym a x` (the same
  relabellings, `linSym k g * v10Sym a x = v10Sym ((k+1)a) (A_g x) * linSym k g`, not a
  Lean theorem); `roundBody_covariant_affine_iff`: an affine relabelling is covariant
  iff it is the identity.
* Proof: `Cell0Cov` for `v10Sym a x * L` gives `Cell0Cov` for `L` (multiply by
  `(v10Sym a x)⁻¹`, which satisfies it with itself). For each of the 71 nontrivial
  linear parts one witness pair (identity deck, identity deck with seats (1,5), (1,8)
  or (1,12) exchanged; same stem cell 0, different stem cell 0 after `L`) is checked
  by kernel `decide!` (`check_lin_k_g`, two stem evaluations each; check A
  `cell0PairsCheck_ok`).
* Scope: all 3692 affine relabellings outside v10Sym, of any order; the prime-order ones
  are the part inside `PrimeNonSwapCase`. It is NOT `PrimeNonSwapCase`: almost all
  prime-order σ are not affine.

## Counterexample search (EXACT / MEASURED; `covsearch.c`, `logs/covsearch.log`)

τ is forced by one random deck (τ = F(σ·m₁) ∘ F(m₁)⁻¹), then σ is refuted when a
further random deck breaks `F(σ·m) = τ·F(m)` (up to 6 decks).

| family | σ tested | result |
|---|---|---|
| `norm`: all affine σ outside v10Sym (EXACT) | 3692 | all refuted at the 2nd deck |
| `dbl`: ALL products of 2 disjoint transpositions (EXACT) | 812175 | all refuted at the 2nd deck |
| `cyc3`: ALL 3-cycles (EXACT) | 44200 | all refuted at the 2nd deck |
| `prime`: random prime order, non-transposition (MEASURED, seed 6) | 10⁶ | all refuted at the 2nd deck |
| `prod`, `fiber`, `rand` (MEASURED, seeds 1–3) | 10⁶ each | all refuted at the 2nd deck |

This is evidence that the conjecture is true, not a proof of any case beyond the
Lean theorems above. The `dbl` and `cyc3` families are exhaustive in C; a kernel
check of them is out of reach (after v10Sym conjugation about 15.6k and 850
representatives; one seat-26 witness costs two stem evaluations, about 4.5 s of kernel
time per witness on the dev box and about 5.3 s on CI, as measured for
`CovariantAffineChecks`, so `dbl` alone would be about
20 hours of kernel time).

## New PROVED result: the seat-26 condition preserves the rank partition

One step toward `PrimeNonSwapCase`; it is NOT `PrimeNonSwapCase` and NOT the conjecture.

`security/DoubleDealSecurity/RankPartition.lean` (+ generated `RankPartitionLists.lean`),
heavy `security/DoubleDealSecurityHeavy/RankPartition.lean` (+ generated
`RankPartitionChecks.lean`), generator `rank_family.py` (log `rank_family.log`, CI
`--check`).
* Statement (`cell0Cov_rank`, heavy, unconditional; `cell0Cov_rank_of_checks` in the
  default library GIVEN the finite checks `RankChecks`): if `Cell0Cov σ τ` for some τ,
  then `a % 13 = b % 13 → σ a % 13 = σ b % 13` (`cell0Cov_rank_iff`: iff, via σ⁻¹).
  Hence every covariant σ permutes the 13 rank classes (`covariant_rank`). Nothing is
  claimed about the rank map σ induces (affine or not), about τ, or about labels.
* Symbolic stem facts (default library, no computation): `c0_eq` (stem cell 0 is the
  packet at the seat `(ρ, rowAmts ρ % 13)` of the row `ρ` that the last column step
  brings to seat 0), `rowAmts_eq_of_agree` (the row amounts of rows 1-3 read only rows
  0-2), `rowAmts_zero` (row 0's amount is the v10 row turn of row 3 read after row 3's
  turn).
* Argument (`rank_eq_of_family`, for EVERY σ, τ): take nine decks `π k i` agreeing
  outside row 3, member `(k, 1)` = member `(k, 0)` with cards x ≠ y (both in row 3)
  exchanged, member `(k, 2)` agreeing with `(k, 0)` in row 3 only at x and y, and stem
  cell 0 of class k at the row-0 seat `(0, col k)`, `col` injective. Their σ-images share
  rows 0-2, hence the amounts of rows 1-3, so `σ⁻¹τ(stem cell 0)` sits in one of four
  seats; row 3 is excluded by members 1 and 2 (it would put the card in and out of
  {x, y}), rows 1 and 2 by injectivity across the three classes (pigeonhole), so for some
  class the row-0 amount of members 0 and 1 agree mod 13; the swap formula
  (`StemCoupling.wsum_swap`, `wt_sub_ne`, `rk_sub_ne`) then gives rank σx = rank σy.
* Finite data: three families (x = card 0, y = 13, 26, 39), found by `rank_family.py`
  (seeded row-3 shuffles); the heavy library checks their structure and the 27 stem
  cell 0 values by kernel `decide!` (`fam_struct_D`, `fam_c0_D_k_i`, one stem evaluation
  per theorem). Every equal-rank pair is moved to (0, y) by a `v10Sym` (which satisfies
  `Cell0Cov` with itself), so three families suffice.
* Formalizing it exposed no hole in the paper argument.

## Routes tried toward the full case, and where each breaks

1. **Uniform deck witness by cycle type.** For transpositions one witness per v10Sym
   orbit works because conjugation by v10Sym preserves `Cell0Cov`. For a general
   prime-order σ, any witness pair (m₁, m₂) has to keep stem cell 0 for both m and
   σ·m, and stem cell 0 depends on the chained SumRanks amounts of the whole deck, so
   the witness depends on all of σ, not on its cycle type. Breaks: no finite reduction.
2. **Amount-preserving moves.** Found two local deck moves that keep every SumRanks
   amount (so every stem cell's source position): a "rectangle" (4 row pairs with
   equal ranks and a constant label difference, aligned in post-row-stage columns) and
   a "row 3-cycle" (three same-suit cards in consecutive columns with ranks in
   arithmetic progression). A witness needs the move to keep the amounts for m AND
   for σ·m, which needs σ to preserve the rank/label pattern of the move, i.e.
   σ-specific structure. Breaks: no way found to choose the move uniformly in σ.
3. **Commuting case first (τ = σ).** (Informal analysis, not in Lean.) Covariance with τ = σ forces the cell-0 source
   position to be σ-invariant on every deck; on SumRanks-survivor decks the seat-2
   argument (`seat2_inj`, except the K♣/K♠ collision) gives that card 0 is fixed by σ.
   With τ ≠ σ (δ = σ⁻¹τ) the same holds iff stem(m)₀ ∈ Fix(δ). Breaks: to conclude
   one needs a single-cell analogue of `sumRanksV10_commutes_iff` (which is about all
   52 cells and τ = σ) for one cell and τ ≠ σ; no such statement is known.
4. **Group theory.** K = {σ : ∃ τ, Cell0Cov σ τ} is a subgroup
   (`CovariantNarrow.cell0Subgroup`) containing v10Sym and no transposition (the
   argument of `not_covariant_swap_of_check`). Showing K = v10Sym in general needs a classification
   of the overgroups of a regular Z13 × Z2² in S52 (primitive / imprimitive cases), not
   viable in Lean here. Restricted to the affine relabellings (the normalizer of
   v10Sym; true by the holomorph count, not a Lean theorem) it is finite, which is the
   proved affine result.

## What a full proof would take

Either (a) a structural single-cell statement: if `stem(σ·m)₀ = τ(stem(m)₀)` on every
deck then σ ∈ v10Sym (`hcell` of `roundBody_covariant_iff_id_of_cell0`; sufficient,
not known true), proved symbolically from the SumRanks amount chain; or (b) a
classification of the subgroups of S52 containing v10Sym, plus a finite witness per
class. Neither is in reach of a computer-checked case split (the 52-card σ space has
no finite reduction, see route 1), and the rules exclude computer- or paper-checked
bounds as a fallback.
