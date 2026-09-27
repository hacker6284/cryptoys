# Open lemmas of `sumRanksV10_survival_le` (10 `sorry`s, all in `Standalone.lean`)

**Main theorem** (proved, modulo the lemmas below), `Main.lean`:

```lean
theorem sumRanksV10_survival_le (τ : Relabel) (h : ¬ ∃ a x, τ = v10Sym a x) :
    64 * (survivors τ).card ≤ Fintype.card (Equiv.Perm (Fin 52))
-- survivors τ = univ.filter fun π => sumRanksV10 (relG τ (deckGrid π)) = relG τ (sumRanksV10 (deckGrid π))
-- deckGrid π = layColumnMajor (permDeck π)
```

`sumRanksV10_survival_le'` is the same bound with the filter written out and
`Nat.factorial 52` on the right.

## Legend

* **S** marks a lemma that is self-contained: it is in `Standalone.lean`,
  needs only `import Mathlib` plus the definitions in that file (all defined
  above their use), and can go to the Nemotron swarm as the whole file with one
  `sorry` left in.
* **R** marks a lemma that needs the repository (`DoubleDeal`,
  `DoubleDealSecurity`). Give these to a model with access to the repo.
* Difficulty is **E** (easy, under 30 lines), **M** (medium, 30–150 lines) or
  **H** (hard, over 150 lines, needs real design).
* Section numbers refer to PROOF.md.

## Already proved (no `sorry`)

**Standalone.lean:**
* `natCast_val_sub13`, `sum_seat_shift`, `wS_mul_rot1`: the rotation
  identity (0.3).
* `sum_seat_weights`, `lemma2c`, `sum_of_cancel`: Lemma 2(c).
* `card_filter_product_le`: the generic two-level fibre bound.
* `A3_const`: `1/81 + 4·4¹³/C(52,13) ≤ 1/64`.
* `sLab_of_offCount_zero`, `sLab_of_offCount_one`, `x4_solve`.

**Main.lean:**
* `deckGrid_apply`, `isDeck_deckGrid`, `survivors_eq_univ_of_commutes`.
* `gfAdd_eq_x4`.
* `sym_of_const` and `nonconst_of_not_sym`: (0.1), outside `v10Sym` either δ or
  ε is nonconstant, via `card_eq_of_rank_label`, `v10SymFn_rank` and
  `v10SymFn_label`.
* `sum_delta`.
* `rowTotal_cast`, `rowTurn_rel_iff` (0.2), `rowS_rotate` (0.3).
* `survives_iff_amounts`: Lemma 1 (1⇔2), via `sumRanksChain_eq`,
  `amounts_match`, `rowRotate_congr`, `colRotate_congr` and
  `relG_colRotate_rowRotate`.
* `rho_nonneg`, `rho_le_one`.
* `rho_le_hA` and `rho_le_third`, from Lemma 2(a),(b).
* `rho_eq_zero_of_cancel`, from Lemma 2(c).
* `exists_vStar`, `nStar_le_50` (from `maxClass_le_50`), `survivors_le_rhoSum`.
* `caseA_bound`: the case split and arithmetic.
* `colTurn_rel_iff`: the column functionals are GF(2)-linear.
* `phi_nonneg`.
* `caseB_bound`: the assembly.
* `sumRanksV10_survival_le`, `sumRanksV10_survival_le'`.
* The 11 formerly open repo-dependent lemmas (#11–#21 below): `traj_of_survives`,
  `rowEq_of_rowCondsTraj`, `thetaG_prefix`, `rowChain_le`, `caseA1`, `caseA2`,
  `caseA3`, `colConds_H_card`, `colChain_le`, `mStar_bounds`, `caseB_sum`, with
  their helpers (index facts `rowStepOf_le`, `prevRow_succ`, `colStep_read_iff`,
  `prevCol_eq_sub_one`, … by small `decide`; `rowAmt_congr`, `colAmt_congr`;
  `relG_colRotate`; the GF(4)-as-`ZMod 2 × ZMod 2` encoding `toZ`, `toZ_inj`,
  `sum_toZ_eps`; `gridPerm`, `deckGrid_gridPerm`, `card_filter_equiv`;
  `card_row_eq_zRow`, `card_col_eq_yCol`, `factorial_split`; `row_nonconst`,
  `rowDistinct`, `rho_prod_le_A3`; `pairCount_eq`, `card_seat_pairs`,
  `card_diffRow_pairs`, `card_ne_pairs`, `rho_of_single`, `rho_prod_le_A1`).

**Decomp.lean** (the shared decomposition, imports `SumRanksV10Iff` and `Standalone`):
* `nested_count`: if `Q r σ` depends only on `σ 0, …, σ r` and each level has
  at most `N r` extensions, then `#{σ : Fin n → α | ∀ r, Q r σ} ≤ ∏ r, N r`.
* `cmEquiv : Fin 52 ≃ Fin 4 × Fin 13`; `rowShuf σ` / `colShuf σ` (reorder each
  row / column by its own permutation) with `rowShuf_cmFlat`, `colShuf_cmFlat`.
* `sum_mul_card_shuf`: `#S · Σ_π f π = Σ_π Σ_{s ∈ S} f (π * ψ s)` (the
  "deck = block sets + per-block arrangements" fibre identity, used by both
  chain lemmas).

Remaining `sorry` dependencies of the 11 (all are swarm lemmas):
`rowChain_le` ← `lemma2a`; `caseA2` ← `hyper_rows`, `lemma2b`; `caseA3` ←
`distinct_row_count`, `lemma2b`; `mStar_bounds` ← `exists_class_ge_13`;
`caseB_sum` ← `hyper_cols`, `lemma4_count_le`. `traj_of_survives`,
`rowEq_of_rowCondsTraj`, `thetaG_prefix`, `caseA1`, `colConds_H_card` and
`colChain_le` are fully `sorry`-free (`#print axioms`: `propext`,
`Classical.choice`, `Quot.sound` only).

## Open: Standalone.lean (hand these to the swarm first)

Definitions used (all in `Standalone.lean`, namespace `SRDP`):
* `wS w σ = Σ_j (j.val : ZMod 13) * w (σ j)`.
* `zRow W π r = #{p : Fin 52 | p % 4 = r ∧ π p ∈ W}`.
* `yCol W π j = #{p | p / 4 = j ∧ π p ∈ W}`.
* `comps4 n` is the set of `z : Fin 4 → ℕ` with every `z r < 14` and `Σ z = n`.
* `comps13 m` is the same for `Fin 13`, with every entry `< 5`.
* `hA z = if z = 13 then 1 else 1/(z+1)`.
* `EA n`.
* `fB`, `EB m`.
* `x4`, `w4`, `vLab`, `sLab`, `offCount`.

| # | Lemma | Exact statement | Uses | Diff. | S/R |
|---|---|---|---|---|---|
| 1 | `lemma2a` (§2, Lemma 2(a)) | `(w : Fin 13 → ZMod 13) (hD : ∑ j, w j ≠ 0) (c : ZMod 13) : 13 * (univ.filter fun σ : Equiv.Perm (Fin 13) => wS w σ = c).card = Nat.factorial 13` | `wS_mul_rot1` (proved) | M | **S** |
| 2 | `lemma2b` (§2, Lemma 2(b)) | `(w : Fin 13 → ZMod 13) (v : ZMod 13) (hnc : ∃ i, w i ≠ v) (c : ZMod 13) : ((univ.filter fun i => w i = v).card + 1) * (univ.filter fun σ : Equiv.Perm (Fin 13) => wS w σ = c).card ≤ Nat.factorial 13` | `Finset.card_mul_le_card_mul` (Mathlib) | M–H | **S** |
| 3 | `maxClass_le_50` (§3) | `(f : Fin 52 → ZMod 13) (hs : ∑ c, f c = 0) (hnc : ∃ c, f c ≠ f 0) (v : ZMod 13) : (univ.filter fun c => f c = v).card ≤ 50` | — | E–M | **S** |
| 4 | `exists_class_ge_13` (§4) | `(f : Fin 52 → Fin 4) : ∃ x, 13 ≤ (univ.filter fun c => f c = x).card` | pigeonhole (`Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to` or similar) | E | **S** |
| 5 | `hyper_rows` (§3 (A2)) | `(W : Finset (Fin 52)) (F : (Fin 4 → ℕ) → ℚ) : ∑ π : Equiv.Perm (Fin 52), F (zRow W π) = ∑ z ∈ comps4 W.card, (∏ r, ((Nat.choose 13 (z r) : ℕ) : ℚ)) * (W.card.factorial * (52 - W.card).factorial : ℕ) * F z` | — | H | **S** |
| 6 | `hyper_cols` (§4 Thm B) | the same as `hyper_rows` with `yCol`, `comps13` and `Nat.choose 4 (y j)`, `F : (Fin 13 → ℕ) → ℚ` | the same proof as #5 | H | **S** |
| 7 | `distinct_row_count` (§3 (A3)) | `(val : Fin 52 → ZMod 13) (r : Fin 4) : (univ.filter fun π : Equiv.Perm (Fin 52) => ∀ p q : Fin 52, p.val % 4 = r.val → q.val % 4 = r.val → p ≠ q → val (π p) ≠ val (π q)).card * Nat.choose 52 13 ≤ 4 ^ 13 * Nat.factorial 52` | count is `13!·39!·Π_v n_v`; AM–GM `Π_v n_v ≤ 4¹³` for `Σ_v n_v = 52` over 13 values (`Real.geom_mean_le_arith_mean_weighted`, or an integer exchange argument) | H | **S** |
| 8 | `EA_le` (§3 (A2), table A) | `(n : ℕ) (h1 : 13 ≤ n) (h2 : n ≤ 49) : EA n ≤ 1 / 100` | — (numeric; max `0.008416` at n=49, `check_tables.py`) | M (numeric engineering) | **S** |
| 9 | `EB_le` (§4, table B) | `(m : ℕ) (h1 : 2 ≤ m) (h2 : m ≤ 39) : EB m ≤ 1 / 64` | — (numeric; `EB 2 = 1/68`, `EB 3 = 1/425`, `check_tables.py`) | M–H (needs a transfer-matrix rewrite: 5¹³ terms) | **S** |
| 10 | `lemma4_count_le` (§4, Lemma 4) | `(e : Fin 4 → Fin 4) (xs t : Fin 4) (y' : ℕ) (h0 : y' = 0 → t = 0) (h1 : y' = 1 → t ≠ 0) : ((univ.filter fun σ : Equiv.Perm (Fin 4) => vLab (e ∘ σ) = t).card : ℚ) / 24 ≤ fB (offCount e xs) y'` | — (finite check) | M | **S** |

Notes for the swarm:
* **#1:** the fibres over `c` and `c - D` are in bijection via `σ ↦ σ * rot1`
  (`wS_mul_rot1`). Iterating 13 times (`D` generates `ZMod 13`) makes all fibres
  equal. They partition `univ` (`Finset.card_eq_sum_card_fiberwise`), and
  `Fintype.card_perm` gives `13!`.
* **#2:** fix `i₀` with `w i₀ ≠ v`. Join `σ` to `σ' = Equiv.swap i₀ k * σ` for
  each `v`-index `k` (this swaps the seats of the entries `i₀` and `k`); `wS` changes by `(w i₀ − v)·(seat difference)`. Every neighbour of a good
  vertex is bad, and a bad vertex has at most one good neighbour, so
  `Finset.card_mul_le_card_mul` gives `z · #good ≤ #bad = 13! − #good`.
* **#3:** if the class of `v` has 52 elements, `f` is constant. If it has 51,
  the off element `c₀` has `f c₀ = −51 v = v` (because `52 v = 0` in
  `ZMod 13`), a contradiction.
* **#5 and #6:** double counting by the image set `π⁻¹(W)`. Standard but long:
  choose which positions of each block hold `W` (`Π C(13, z_r)`), then arrange
  `W` (`n!`) and the rest (`(52 − n)!`). A clean route is to push forward along
  `π ↦ (univ.filter fun p => π p ∈ W)` (a `Finset` of card `n`), count each
  fibre as `n!(52−n)!`, then count the `n`-subsets with given block counts via
  `Finset.card_pi`-style product.
* **#8 and #9:** kernel `decide` only, no `native_decide`. Define a
  Nat-scaled, List-based convolution (A) or transfer matrix (B), prove it equal
  to `EA` / `EB`, then use `decide` on the scaled Nat inequalities. If the
  kernel check takes more than a few seconds, that part goes to
  `DoubleDealSecurityHeavy` when promoted.
* **#10:** 256 · 4 cases (`e`, `t`) × 24 orders. First reduce: the count only
  depends on the multiset of `e`, and `fB (offCount e xs) y'` is monotone in the
  constraints. Or give `Equiv.Perm (Fin 4)` an explicit 24-element list and
  `decide`. Possibly heavy.

## Main.lean (repo-dependent): all proved

Kept for reference; every row below is now proved (see above).

Definitions (in `Main.lean`, namespace `DoubleDeal.Security.SumRanksDP`):
* `deckGrid π`.
* `rowOf π r j = π (cmFlat r j)`, `colOf π j r = π (cmFlat r j)`.
* `delta τ c = rk (τ c) − rk c : ZMod 13`, `eps τ c = x4 (lab (τ c)) (lab c)`.
* `rowS`, `rowD`.
* `RowCondsTraj τ g`, `ColCondsTraj τ H`: the turn equalities along `g`'s own
  trajectory.
* `thetaG π r = if r = 0 then 0 else (rowAmt rowTurnV10 (deckGrid π) r : ZMod 13)`.
* `rho`, `rhoSum`, `phi`, `nStar`, `mStar`.

| # | Lemma | Exact statement | Uses | Diff. | S/R |
|---|---|---|---|---|---|
| 11 | `traj_of_survives` (§1, Lemma 1 (1⇒3)) | `(τ) (g : Grid Nat) (hg : IsDeck (scoopColumnMajor g)) (h : sumRanksV10 (relG τ g) = relG τ (sumRanksV10 g)) : RowCondsTraj τ g ∧ ColCondsTraj τ (rowsDone rowTurnV10 g 4)` | `survives_iff_amounts`, `rowsDone_eq_partial`, `colsDone_eq_partial`, `turnRow_rel`, `turnCol_rel`, `rowRotate_congr`, `colRotate_congr` (induction on the step: while the amounts agree, `rowsDone (relG τ g) n = relG τ (rowsDone g n)`) | M | R |
| 12 | `rowEq_of_rowCondsTraj` (§1, Cor. 1) | `(τ) (π) (h : RowCondsTraj τ (deckGrid π)) : ∀ r, rowS τ (rowOf π r) = thetaG π r * rowD τ (rowOf π r)` | `rowsDone_eq_partial`, `rowRotate_apply`, `rowTurn_rel_iff`, `rowS_rotate`, `app_fin` | M | R |
| 13 | `thetaG_prefix` (§1, Cor. 1) | `(π π') (r : Fin 4) (h : ∀ r' < r, rowOf π r' = rowOf π' r') : thetaG π r = thetaG π' r` | `rowAmt` unfolding, `rowsDone_eq_partial`, `rowRotate_apply` (case split `r = 0,1,2,3`) | M | R |
| 14 | `rowChain_le` (§2, Lemma 3) | `(τ) (θ : Equiv.Perm (Fin 52) → Fin 4 → ZMod 13) (hθ : ∀ π π' r, (∀ r' < r, rowOf π r' = rowOf π' r') → θ π r = θ π' r) : ((univ.filter fun π => ∀ r, rowS τ (rowOf π r) = θ π r * rowD τ (rowOf π r)).card : ℚ) ≤ ∑ π, ∏ r, rho τ (rowOf π r)` | `lemma2a`, `rowS_comp`, `card_filter_product_le` | H | R (could be made S by abstracting `rowOf`, `delta`) |
| 15 | `caseA1` (§3 (A1)) | `(τ) (h : nStar τ = 50) : 221 * rhoSum τ ≤ (Nat.factorial 52 : ℕ)` | `rho_eq_zero_of_cancel`, `rho_le_one`, and "two given cards in the same row" has probability `12/51` | M–H | R |
| 16 | `caseA2` (§3 (A2)) | `(τ) (h1 : 13 ≤ nStar τ) (h2 : nStar τ ≤ 49) : rhoSum τ ≤ (Nat.factorial 52 : ℕ) * EA (nStar τ)` | `rho_le_hA` (v = v*), `exists_vStar`, `hyper_rows` (W = `cls τ v*`; the row-`r` count is `zRow W π r` since `cmFlat r j = r + 4j`), `n!(52−n)!·C(52,n) = 52!` | M | R |
| 17 | `caseA3` (§3 (A3)) | `(τ) (h : nStar τ ≤ 12) : rhoSum τ ≤ (Nat.factorial 52 : ℕ) * ((1 / 81 : ℚ) + 4 * 4 ^ 13 / (Nat.choose 52 13 : ℕ))` | `rho_le_third`, `rho_le_one`, `distinct_row_count` (`val = delta τ`) | M | R |
| 18 | `colConds_H_card` (§4, H uniform) | `(τ) : (univ.filter fun π => ColCondsTraj τ (rowsDone rowTurnV10 (deckGrid π) 4)).card = (univ.filter fun π => ColCondsTraj τ (deckGrid π)).card` | `rowsUndo_rowsDone`, `rowsDone_rowsUndo`, `isDeckG_rowsUndo`, `deckPerm`, `lay_scoop_columnMajor` (a `Finset.card_bij`) | M | R |
| 19 | `colChain_le` (§4, Lemma 5) | `(τ) : ((univ.filter fun π => ColCondsTraj τ (deckGrid π)).card : ℚ) ≤ ∑ π, ∏ j, phi τ (colOf π (prevCol j)) (colOf π j)` | `colTurn_rel_iff`, `colsDone_eq_partial`, `colRotate_apply`, `card_filter_product_le` (13 levels) | H | R |
| 20 | `mStar_bounds` (§4) | `(τ) (h : ∃ c, eps τ c ≠ eps τ 0) : 2 ≤ mStar τ ∧ mStar τ ≤ 39` | `exists_class_ge_13` (upper bound); lower bound: XOR-sum of `eps` is 0 (encode `Fin 4` as `ZMod 2 × ZMod 2`, `Equiv.sum_comp τ`), so exactly one off card is impossible | M | R |
| 21 | `caseB_sum` (§4, Thm B) | `(τ) (h : ∃ c, eps τ c ≠ eps τ 0) : ∑ π, ∏ j, phi τ (colOf π (prevCol j)) (colOf π j) ≤ (Nat.factorial 52 : ℕ) * EB (mStar τ)` | `lemma4_count_le`, `sLab_of_offCount_zero/one`, `hyper_cols` (W = off cards of a most common ε-value; the column-`j` count is `yCol W π j`), `prevCol j = j - 1` | M | R |

## Dependency order (suggested)

1. The swarm, in parallel: #3, #4, #1, #10, #2, then #5/#6, #7, and #8/#9
   (numeric engineering).
2. Repo side: done (#11–#21 all proved; `Decomp.lean` holds the shared
   decomposition used by #14 and #19). #5/#6 (`hyper_rows`/`hyper_cols`) remain
   with the swarm; `Decomp.lean`'s `cmEquiv` may help there.

## Honesty notes

* The Lean target is `1/64`, not the paper's `0.012768` or the exact
  `9/1105`.
* Case B is formalised via the column conditions alone, with the refined
  `fB 2 0 = 1/4`. This gives `≤ 1/64` (the table maximum is `EB 2 = 1/68`),
  not the paper's `1/425`, and it needs no hypothesis on δ.
* `rowChain_le` and `colChain_le` are stated as `≤`. The paper proves equality,
  but only `≤` is needed.
