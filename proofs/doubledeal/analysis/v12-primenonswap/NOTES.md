# DoubleDeal v12: `PrimeNonSwapCase` and the covariant round conjecture (statement proved in the heavy library)

The conjecture `roundBody_covariant_iff_id` (`security/DoubleDealSecurity/Rounds.lean`,
DRAFT-SORRY) keeps its `sorry`: that theorem is unchanged. Its STATEMENT is now proved in
the heavy library (`LabelStep.roundBody_covariant_iff_id_heavy`, unconditional) and in the
default library GIVEN the finite checks `V10SymChecks` as a hypothesis
(`LabelStep.roundBody_covariant_iff_id_of_checks`), via the single-cell statement `hcell`
of `CovariantNarrow.roundBody_covariant_iff_id_of_cell0` (steps 1-4 below: every σ with
the seat-26 condition `Cell0Cov σ τ` is a `v10Sym a x`, and τ = σ). Replacing the `sorry`
is a separate change. `PrimeNonSwapCase` (`security/DoubleDealSecurity/CovariantNarrow.lean`)
follows from it by `prime_nonswap_case_iff` (not stated as its own Lean theorem). This note
records the proved results (the affine relabellings; steps 1-4), the routes tried earlier,
and the counterexample search. No covariant pair (σ ≠ 1 with some τ) was found.

Labels (as in `../v12-covariant/NOTES.md`): PROVED (Lean, audited), CONDITIONAL
(hypothesis in the statement), EXACT (exhaustive, C or Python), MEASURED (sampled,
fixed seed). `F = unkeyedWithMix` = GridCycle ∘ stem. `Covariant σ F` means
`∃ τ, ∀ deck m, F(σ·m) = τ·F(m)`. `Cell0Cov σ τ` is the seat-26 condition
`stem(σ·m)₀ = τ(stem(m)₀)` on every deck (implied by covariance,
`cell0Cov_of_covPair`).

## The remaining case, exactly

(Written before steps 2-4 below; kept as the description of the case they close.)

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
  Hence every covariant σ permutes the 13 rank classes (`covariant_rank`). This step
  claims nothing about the rank map σ induces, about τ, or about labels (steps 2-4 below).
* `cell0Subgroup_le_rankStab` (heavy, unconditional): `cell0Subgroup` lies in the
  rank-partition stabiliser `rankStab` (≅ S4 ≀ S13; that identification is not a Lean
  theorem).
* Symbolic stem facts (default library, no computation, in the stem modules):
  `StemPosition.stemPos_zero` (stem cell 0 is the packet at the seat `(ρ, rowAmts ρ % 13)`
  of the row `ρ` that the last column step brings to seat 0),
  `StemCoupling.rowAmts_eq_of_agree` (the row amounts of rows 1-3 read only rows 0-2),
  `StemCoupling.rowAmts_prev` at row 0 (row 0's amount is the v10 row turn of row 3 read
  after row 3's turn).
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
* The argument is now stated for a general row-3 exchange `q` (`FamilyQ`,
  `FamilyQ.wsum_eq`: for some class the σ-images of the row-3 reads of members 0 and 1 have
  equal row totals mod 13); `rank_eq_of_family` (unchanged statement) is its case
  `q = swap x y`, and step 2 uses a double swap.

## New PROVED result: steps 2-4, every σ with the seat-26 condition is a `v10Sym`

`security/DoubleDealSecurity/RankAffine.lean`, `TauEq.lean`, `LabelStep.lean` (+ generated
`V10SymLists.lean`), heavy `security/DoubleDealSecurityHeavy/V10Sym.lean` (+ generated
`V10SymChecks.lean`), generator `v10sym_witness.py` (log `v10sym_witness.log`, CI
`--check`). `rk c` is the rank mod 13 (`ZMod 13`), `ri c = c % 13`.
* Statements (heavy, unconditional; `…_of_checks` in the default library GIVEN the finite
  checks as hypotheses):
  * `RankAffine.cell0Cov_rk_affine`: `Cell0Cov σ τ → ∃ l u, l ≠ 0 ∧ ∀ c, rk (σ c) = l · rk c + u`
    (checks `RankChecks`, `AffRankChecks`).
  * `TauEq.cell0Cov_tau`: `Cell0Cov σ τ → τ = σ ∧ ∃ u, ∀ c, rk (σ c) = rk c + u`
    (adds `TauChecks`).
  * `LabelStep.cell0Cov_mem_v10Sym`: `Cell0Cov σ τ → (∃ a x, σ = v10Sym a x) ∧ τ = σ`;
    `LabelStep.cell0Cov_iff`: and conversely (all checks, `V10SymChecks` =
    `RankChecks ∧ AffChecks ∧ AffRankChecks ∧ TauChecks ∧ LabelChecks`).
  * `LabelStep.roundBody_covariant_iff_id_heavy`: `Covariant σ unkeyedWithMix ↔ σ = 1`, the
    statement of `roundBody_covariant_iff_id`, from `roundBody_covariant_iff_id_of_cell0`.
* Step 2 (`RankAffine.rk_sum_of_family2`, for EVERY σ, τ): nine decks as in step 1, but
  member `(k, 1)` exchanges both 0 ↔ 1 and 2 ↔ 14 in row 3, whose columns in member
  `(k, 0)` satisfy `cx + cy2 = cy + cx2 (mod 13)`. `FamilyQ.wsum_eq` and `wsum_swap` twice
  give `δ · ((rk σ1 − rk σ0) + (rk σ14 − rk σ2)) = 0` with `δ = cy − cx ≠ 0` (the weight
  difference of two read positions is their column difference, `wt_sub_readIdx`).
  Transported by the rank shifts `v10Sym r 0`, the induced map `F` on ranks
  (`rk ∘ σ = F ∘ rk` by step 1) has zero second differences, so it is affine
  (`affine_of_second_diff`); `l ≠ 0` because σ permutes the rank classes.
* Step 3 (`TauEq`): row amounts read ranks mod 13 only (`rowAmts_congr`), so if
  `rk ∘ σ = l · rk`, stem cell 0 of `σ · m` is σ of the card of `m` at a seat
  `(ρ, rowAmts (scaleP l m) ρ % 13)` (`cand_of_cell0Cov`, from `stemPos_zero`). On two decks
  with stem cell 0 = card 0, these candidate sets meet only in card 0 for `l = 1` and are
  disjoint for `l = 2..12` (`TauChecks`), so `l = 1` and `σ 0 = τ 0` (`tau_step`).
  Composing with `v10Sym a 0` (`l · a = −u`) makes any affine rank map linear, and
  conjugating by the `v10Sym r y` sending card 0 to `c` gives `σ c = τ c`.
* Step 4 (`LabelStep`), for σ preserving every rank index (after step 3, `σ · v10Sym a 0`):
  * Column chain (`colAmt_congr_label`, symbolic): grids differing in labels by a constant
    per column get the same v10 column amounts (`1 ⊕ w ⊕ w² = 0` in the column value; four
    equal shifts cancel in the column suits).
  * Per-rank label translations `tr d` (`l ↦ l ⊕ d r` at rank index `r`): if `tr d`
    satisfies the seat-26 condition, `d` is constant (`tr_const_of_cell0`). By step 3 τ =
    `tr d`; on one deck whose post-row-stage columns are full rank classes of a rank index
    ≠ 0 or hold only rank indices 0 and 1 (`LabStruct`), `tr d` and `tr (eVec (d 0 ⊕ d 1))`
    differ by a constant per column, so they give the same source row of stem cell 0
    (`c0Row_tr_eq`), and `LabKill` says `tr (eVec e)` moves it for `e ≠ 0`; so `d 0 = d 1`,
    and conjugating by the rank shifts (`conj_tr`) gives `d r = d (r + 1)`.
  * Group step (`rankPres_mem_v10Sym`): σ has a label map `g r` per rank index. Every
    permutation of `Fin 4` is affine (`perm4_affine`, from `diag_table`: `decide!` over the
    4-tuples of distinct values), so `σ · v10Sym 0 x · σ⁻¹ = tr (δ · x)`, and the previous point
    makes `δ` rank-independent; so `g r = g 0 ∘ (· ⊕ c r)`. The commutator with
    `v10Sym 1 0` is `tr (c (r + 1) ⊕ c r)`, so `c (r + 1) = c r ⊕ κ`; 13 is odd, so `κ = 0`
    (`chain_const`) and σ is one label map on every rank, `v10Sym 0 x * linSym 0 g`;
    `not_cell0Cov_lin_of_check` (`AffChecks`) forces `g = 0`.
* Finite data (`v10sym_witness.py`, deterministic xorshift64 searches): 9 decks for step 2,
  2 for step 3, 1 for step 4. The heavy library checks them by kernel `decide!`, one stem
  evaluation per theorem (`aff_struct`, `aff_c0_k_i`, `tau_g0_i`, `tau_cand_l`,
  `lab_struct`, `lab_kill_e`).
* Formalizing steps 2-4 exposed no hole in the paper argument (column-chain lemma,
  per-rank decomposition and commutator reduction included).

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
   proved affine result. **Imprimitivity step, PROVED** (`RankPartition`, heavy
   `cell0Subgroup_le_rankStab`): K lies in the stabiliser of the rank partition (13
   blocks of 4 cards), `rankStab` (≅ S4 ≀ S13; that identification is not a Lean
   theorem). **Update:** steps 2-4 above (the induced rank map, then the suit parts)
   finish this route without a subgroup classification: K = v10Sym (heavy
   `LabelStep.cell0Cov_iff`).

## What a full proof would take (status)

Route (a) of the earlier plan, the structural single-cell statement `hcell` of
`roundBody_covariant_iff_id_of_cell0`, is now proved (steps 1-4; heavy library
unconditional, default library given `V10SymChecks`). What is left is bookkeeping, not
mathematics: `roundBody_covariant_iff_id` in the default library still has its `sorry`
because the finite checks live in the heavy library. Removing that `sorry` (for example
by moving the conjecture or its dependents, or by stating the default theorem with the
checks) is a separate, small follow-up, to be agreed before it is done. The
default-library docstrings (`Rounds.lean`, `CovariantNarrow.lean`) say this: proved in the
heavy library by kernel `decide!`, a hypothesis in the default library, `sorry` until the
follow-up.
