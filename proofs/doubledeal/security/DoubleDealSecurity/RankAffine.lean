/-
  Step 2 toward `PrimeNonSwapCase` (NOT `PrimeNonSwapCase` by itself, NOT the covariant round
  conjecture `roundBody_covariant_iff_id`, which keeps its `sorry`): the rank map of a
  relabelling with the seat-26 condition is affine.

  Statement (`cell0Cov_rk_affine_of_checks`, GIVEN the finite checks `RankChecks` and
  `AffRankChecks`; unconditional in the heavy library): if `Cell0Cov σ τ`, then for some
  `l ≠ 0` and `u` in `ZMod 13`, `rk (σ c) = l * rk c + u` for every card `c`
  (`rk c = rank c mod 13`). Nothing is claimed here about labels or about τ.

  A. `rk_sum_of_family2`: for nine decks `π k i` of the shape `Family2` (as
     `RankPartition.Family`, but member `(k, 1)` exchanges BOTH x = 0 ↔ y = 1 and
     x2 = 2 ↔ y2 = 14 in row 3, whose columns in member `(k, 0)` satisfy
     `cx + cy2 = cy + cx2 (mod 13)`), every σ, τ with `Cell0Cov σ τ` have
     `(rk σ1 - rk σ0) + (rk σ14 - rk σ2) = 0`: `RankPartition.FamilyQ.wsum_eq` gives equal
     row totals of members 0 and 1 for some class, and `StemCoupling.wsum_swap` twice turns
     that into `δ · (that sum) = 0` with `δ = cy - cx ≠ 0`.
  B. `cell0Cov_rk_affine_of_checks`: the family of `V10SymLists.lean` (cards 0, 1, 2, 14 have
     ranks A, 2, 3, 2), transported by `v10Sym r 0` (rank shift by `r`) for every `r`, gives
     `F (t+2) - 2 F (t+1) + F t = 0` for the induced map `F` on ranks
     (`rk (σ c) = F (rk c)` by `RankPartition`), so `F` is affine; `l ≠ 0` because `σ`
     permutes the rank classes.

  Write-up: `../analysis/v12-primenonswap/NOTES.md`; data: `v10sym_witness.py`.
-/
import DoubleDealSecurity.RankPartition
import DoubleDealSecurity.V10SymLists

namespace DoubleDeal.Security.RankAffine

open DoubleDeal Relabel
open DoubleDeal.Security (permDeck isDeck_permDeck rel_permDeck)
open DoubleDeal.Security.CovariantNarrow (Cell0Cov cell0Cov_mul cell0Cov_v10Sym g0 g0_eq)
open DoubleDeal.Security.StemCoupling (wt wsum wsum_swap wt_sub_ne zmod13_mul_ne cmFlat_col_injective)
open DoubleDeal.Security.RankPartition (FamilyQ readIdx readIdx_injective readIdx_surj
  wt_sub_readIdx swapsPerm RankChecks cell0Cov_rank_of_checks cell0Cov_rank_iff_of_checks)

/-! ## A. The double-swap family -/

/-- The double exchange `0 ↔ 1`, `2 ↔ 14`. -/
def q2 : Relabel := Equiv.swap 0 1 * Equiv.swap 2 14

/-- The four exchanged cards. -/
abbrev S2 (z : Fin 52) : Prop := z = 0 ∨ z = 1 ∨ z = 2 ∨ z = 14

theorem q2_nofix : ∀ z, S2 z → q2 z ≠ z := by decide

/-- The hypotheses on the nine decks: a `FamilyQ` for `q2`, with the four cards in row 3 of
    every member `(k, 0)` at columns `cx, cy, cx2, cy2` with `cx + cy2 = cy + cx2 (mod 13)`. -/
structure Family2 (π : Fin 3 → Fin 3 → Relabel) (col : Fin 3 → Fin 13) : Prop where
  toQ : FamilyQ π col q2 S2
  pos : ∀ k, ∃ cx cy cx2 cy2 : Fin 13, π k 0 (cmFlat 3 cx) = 0 ∧ π k 0 (cmFlat 3 cy) = 1 ∧
    π k 0 (cmFlat 3 cx2) = 2 ∧ π k 0 (cmFlat 3 cy2) = 14 ∧
    (cx.val + cy2.val) % 13 = (cy.val + cx2.val) % 13

/-- (PROVED) For every σ, τ with the seat-26 condition, a `Family2` forces
    `(rk σ1 - rk σ0) + (rk σ14 - rk σ2) = 0`. -/
theorem rk_sum_of_family2 {π : Fin 3 → Fin 3 → Relabel} {col : Fin 3 → Fin 13}
    (hf : Family2 π col) {σ τ : Relabel} (hc : Cell0Cov σ τ) :
    (rk (σ 1) - rk (σ 0)) + (rk (σ 14) - rk (σ 2)) = 0 := by
  obtain ⟨k, K, hz⟩ := hf.toQ.wsum_eq hc
  set yv : Fin 13 → Fin 52 := fun j => σ (π k 0 (cmFlat 3 (readIdx K j))) with hyvd
  have hyv : Function.Injective yv := fun a b h =>
    readIdx_injective K (cmFlat_col_injective 3 ((π k 0).injective (σ.injective h)))
  obtain ⟨cx, cy, cx2, cy2, px, py, px2, py2, hcol⟩ := hf.pos k
  obtain ⟨j1, hj1⟩ := readIdx_surj K cx
  obtain ⟨j2, hj2⟩ := readIdx_surj K cy
  obtain ⟨j3, hj3⟩ := readIdx_surj K cx2
  obtain ⟨j4, hj4⟩ := readIdx_surj K cy2
  have hy1 : yv j1 = σ 0 := by simp only [yv, hj1, px]
  have hy2 : yv j2 = σ 1 := by simp only [yv, hj2, py]
  have hy3 : yv j3 = σ 2 := by simp only [yv, hj3, px2]
  have hy4 : yv j4 = σ 14 := by simp only [yv, hj4, py2]
  have hne : ∀ a b : Fin 52, a ≠ b → σ a ≠ σ b := fun a b h e => h (σ.injective e)
  have jne : ∀ {i i' : Fin 13} {a b : Fin 52}, yv i = σ a → yv i' = σ b → a ≠ b → i ≠ i' :=
    fun h1 h2 hab e => hne _ _ hab (by rw [← h1, ← h2, e])
  have h12 : j1 ≠ j2 := jne hy1 hy2 (by decide)
  have h34 : j3 ≠ j4 := jne hy3 hy4 (by decide)
  -- the σ-image of member 1's read
  have hs : ∀ z, σ (q2 z) = Equiv.swap (σ 0) (σ 1) (Equiv.swap (σ 2) (σ 14) (σ z)) := fun z => by
    simp only [q2, Equiv.Perm.mul_apply, Equiv.swap_apply_apply, Equiv.Perm.inv_apply_self]
  simp only [hs] at hz
  set yv' : Fin 13 → Fin 52 := fun j => Equiv.swap (yv j3) (yv j4) (yv j) with hyv'd
  have hyv' : Function.Injective yv' := (Equiv.injective _).comp hyv
  have hy1' : yv' j1 = σ 0 := by
    simp only [yv', hy1, hy3, hy4]
    exact Equiv.swap_apply_of_ne_of_ne (hne _ _ (by decide)) (hne _ _ (by decide))
  have hy2' : yv' j2 = σ 1 := by
    simp only [yv', hy2, hy3, hy4]
    exact Equiv.swap_apply_of_ne_of_ne (hne _ _ (by decide)) (hne _ _ (by decide))
  have e1 : (fun j => Equiv.swap (σ 0) (σ 1) (Equiv.swap (σ 2) (σ 14)
      (σ (π k 0 (cmFlat 3 (readIdx K j)))))) =
      fun j => Equiv.swap (yv' j1) (yv' j2) (yv' j) := by
    rw [hy1', hy2', ← hy3, ← hy4]
  rw [e1, wsum_swap yv' hyv' h12,
    show wsum yv' = wsum (fun j => Equiv.swap (yv j3) (yv j4) (yv j)) from rfl,
    wsum_swap yv hyv h34, hy1', hy2', hy3, hy4] at hz
  rw [wt_sub_readIdx hj1 hj2, wt_sub_readIdx hj3 hj4] at hz
  -- the column condition: the two weight differences agree
  have hcz : (cy2.val : ZMod 13) - (cx2.val : ZMod 13) = (cy.val : ZMod 13) - (cx.val : ZMod 13) := by
    rw [sub_eq_sub_iff_add_eq_add, ← Nat.cast_add, ← Nat.cast_add, ZMod.natCast_eq_natCast_iff']
    omega
  rw [hcz] at hz
  have hcne : (cy.val : ZMod 13) - (cx.val : ZMod 13) ≠ 0 := by
    rw [← wt_sub_readIdx hj1 hj2]; exact wt_sub_ne h12
  have hprod : ((cy.val : ZMod 13) - (cx.val : ZMod 13)) *
      ((rk (σ 1) - rk (σ 0)) + (rk (σ 14) - rk (σ 2))) = 0 := by
    linear_combination hz
  by_contra hr
  exact zmod13_mul_ne _ _ hcne hr hprod

/-! ## B. The family of `V10SymLists.lean`, transported to every rank shift -/

/-- Member `i` of class `k`, as a permutation (seat ↦ card). -/
def affPerm (k i : Fin 3) : Relabel := swapsPerm (affSwaps.getD (3 * k.val + i.val) [])

/-- The row-0 column holding stem cell 0 for class `k`. -/
def affColOf (k : Fin 3) : Fin 13 := affCol.getD k.val 0

/-- The column of the seat of deck `π` holding card `z`. -/
def colOf (π : Relabel) (z : Fin 52) : Fin 13 :=
  ⟨(π.symm z).val / 4, by have := (π.symm z).isLt; omega⟩

/-- The structure of the family (no stem evaluation): the hypotheses of `Family2` other than
    the stem-cell-0 values, with the columns of the four cards given by `colOf`. -/
abbrev AffStruct : Prop :=
  (∀ k i : Fin 3, ∀ s : Fin 52, (cmRow s).val ≠ 3 → affPerm k i s = affPerm 0 0 s) ∧
  affColOf 0 ≠ affColOf 1 ∧ affColOf 0 ≠ affColOf 2 ∧ affColOf 1 ≠ affColOf 2 ∧
  (∀ k : Fin 3, ∀ c : Fin 13, affPerm k 1 (cmFlat 3 c) = q2 (affPerm k 0 (cmFlat 3 c))) ∧
  (∀ k : Fin 3, ∀ c : Fin 13, affPerm k 2 (cmFlat 3 c) = affPerm k 0 (cmFlat 3 c) →
    S2 (affPerm k 0 (cmFlat 3 c))) ∧
  (∀ k : Fin 3, affPerm k 0 (cmFlat 3 (colOf (affPerm k 0) 0)) = 0 ∧
    affPerm k 0 (cmFlat 3 (colOf (affPerm k 0) 1)) = 1 ∧
    affPerm k 0 (cmFlat 3 (colOf (affPerm k 0) 2)) = 2 ∧
    affPerm k 0 (cmFlat 3 (colOf (affPerm k 0) 14)) = 14 ∧
    ((colOf (affPerm k 0) 0).val + (colOf (affPerm k 0) 14).val) % 13 =
      ((colOf (affPerm k 0) 1).val + (colOf (affPerm k 0) 2).val) % 13)

/-- Stem cell 0 of deck `(k, i)` is the card at the row-0 seat `(0, affColOf k)`. -/
abbrev affC0Check (k i : Fin 3) : Prop :=
  g0 (permDeck (affPerm k i)) = (affPerm k 0 (cmFlat 0 (affColOf k))).val

/-- The finite checks of step 2 (discharged by kernel `decide!` in the heavy library,
    `RankAffine.affRankChecks_ok`). -/
abbrev AffRankChecks : Prop := AffStruct ∧ ∀ k i, affC0Check k i

theorem family2_of_checks (h : AffRankChecks) : Family2 affPerm affColOf := by
  obtain ⟨hag, h01, h02, h12, hsw, hm, hpos⟩ := h.1
  refine ⟨⟨hag, ?_, fun k i => ?_, hsw, q2_nofix, hm⟩, fun k => ?_⟩
  · intro a b hab
    fin_cases a <;> fin_cases b <;> first
      | rfl
      | exact absurd hab h01 | exact absurd hab.symm h01
      | exact absurd hab h02 | exact absurd hab.symm h02
      | exact absurd hab h12 | exact absurd hab.symm h12
  · rw [← g0_eq]; exact h.2 k i
  · obtain ⟨a, b, c, d, e⟩ := hpos k
    exact ⟨_, _, _, _, a, b, c, d, e⟩

/-! ### Ranks mod 13 (`rk`, `rk_eq_iff`, `cardOfRk`, `rk_v10Sym`: `SumRanksV10.lean`) -/

theorem rk_small : rk 0 = 1 ∧ rk 1 = 2 ∧ rk 2 = 3 ∧ rk 14 = 2 := by decide

/-- A second-difference-zero map on `ZMod 13` is affine. -/
theorem affine_of_second_diff (F : ZMod 13 → ZMod 13)
    (h : ∀ t, F (t + 2) - 2 * F (t + 1) + F t = 0) (s : ZMod 13) :
    F s = F 0 + s * (F 1 - F 0) := by
  have hn : ∀ n : ℕ, F n = F 0 + n * (F 1 - F 0) ∧ F (n + 1) = F 0 + (n + 1) * (F 1 - F 0) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      refine ⟨by exact_mod_cast ih.2, ?_⟩
      have := h n
      push_cast
      rw [show (n : ZMod 13) + 1 + 1 = n + 2 by ring]
      linear_combination this + 2 * ih.2 - ih.1
  have := (hn s.val).1
  rwa [ZMod.natCast_zmod_val] at this

/-- (PROVED, GIVEN the finite checks `RankChecks` and `AffRankChecks` as hypotheses) If
    `Cell0Cov σ τ`, the rank map of σ is affine: `rk (σ c) = l * rk c + u` with `l ≠ 0`.
    Unconditional form: heavy library, `RankAffine.cell0Cov_rk_affine`. -/
theorem cell0Cov_rk_affine_of_checks (hR : RankChecks) (hA : AffRankChecks) {σ τ : Relabel}
    (h : Cell0Cov σ τ) : ∃ l u : ZMod 13, l ≠ 0 ∧ ∀ c, rk (σ c) = l * rk c + u := by
  set F : ZMod 13 → ZMod 13 := fun s => rk (σ (cardOfRk s)) with hFd
  have hF : ∀ c, rk (σ c) = F (rk c) := by
    intro c
    simp only [hFd]
    rw [rk_eq_iff]
    apply cell0Cov_rank_of_checks hR h
    rw [← rk_eq_iff, rk_cardOfRk]
  have hfam := family2_of_checks hA
  have hshift : ∀ r : Fin 13, F ((r.val : ZMod 13) + 1 + 2) - 2 * F ((r.val : ZMod 13) + 1 + 1) +
      F ((r.val : ZMod 13) + 1) = 0 := by
    intro r
    have hcv : Cell0Cov (σ * v10Sym r 0) (τ * v10Sym r 0) :=
      cell0Cov_mul h (cell0Cov_v10Sym r 0)
    have := rk_sum_of_family2 hfam hcv
    simp only [Equiv.Perm.mul_apply, hF, rk_v10Sym, rk_small] at this
    have e3 : (3 : ZMod 13) + r.val = (r.val + 1) + 2 := by ring
    have e2 : (2 : ZMod 13) + r.val = (r.val + 1) + 1 := by ring
    have e1 : (1 : ZMod 13) + r.val = (r.val : ZMod 13) + 1 := by ring
    rw [e3, e2, e1] at this
    linear_combination -this
  have hrec : ∀ t : ZMod 13, F (t + 2) - 2 * F (t + 1) + F t = 0 := by
    intro t
    have := hshift ⟨(t - 1).val, ZMod.val_lt _⟩
    simp only [ZMod.natCast_zmod_val, sub_add_cancel] at this
    exact this
  refine ⟨F 1 - F 0, F 0, ?_, fun c => ?_⟩
  · intro e
    have e' : F 1 = F 0 := sub_eq_zero.mp e
    simp only [hFd, rk_eq_iff, cell0Cov_rank_iff_of_checks hR h] at e'
    exact absurd e' (by decide)
  · rw [hF, affine_of_second_diff F hrec]
    ring

end DoubleDeal.Security.RankAffine
