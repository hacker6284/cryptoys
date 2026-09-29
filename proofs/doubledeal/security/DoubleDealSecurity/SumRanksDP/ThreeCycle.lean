/-
  The easy half of the exact worst case (PROOF.md §5b): the same-suit 3-cycle
  `A♣ → 2♣ → 3♣` (`threeCycle`, cards `0 → 1 → 2`) commutes with v10 SumRanks on
  exactly `(9/1105) · 52!` decks (`sumRanksV10_survival_threeCycle`). Hence the
  `1/64` constant of `sumRanksV10_survival_le` is within a factor `1105/(9·64) < 2`
  of tight (`sumRanksV10_survival_lower`).

  Only this one relabelling is treated. That `9/1105` is the maximum over all
  non-symmetries (PROOF.md §5b, `analysis/v10-sumranks/sbox-search`) is
  computer-assisted and not formalised here.

  Proof. The 3-cycle keeps suits, so every column condition holds and survival is
  exactly the four row equations (`survives_threeCycle_iff`, both directions of
  PROOF.md §1 Lemma 1 / Cor. 1). The row chain is exact (`rowChain_eq`), so the
  survivors number `Σ_π Π_r ρ(row r)`. A row holding `k` of the three moved cards
  has `ρ = 1, 1/13, 1/13, 1/11` for `k = 0, 1, 2, 3` (`rho_threeCycle`; for `k = 3`,
  `S = σ⁻¹i₀ + σ⁻¹i₁ + 11·σ⁻¹i₂` vanishes on `156` of the `1716` seat triples).
  The hypergeometric law then gives `3!·49!·180 = 1080·49! = (9/1105)·52!`.
  Kernel `decide!` is used only on small tables (`13³` seat triples, `4⁴` row
  vectors); no `native_decide`.
-/
import DoubleDealSecurity.SumRanksDP.Main
import DoubleDealSecurity.PermCount

namespace DoubleDeal.Security.SumRanksDP

open DoubleDeal Relabel Finset SRDP

/-! ## The permutation -/

/-- The same-suit 3-cycle `A♣ → 2♣ → 3♣ → A♣` (cards `0 → 1 → 2 → 0`). -/
def threeCycle : Relabel := Equiv.swap 0 2 * Equiv.swap 0 1

/-- The cards `threeCycle` moves. -/
def W3 : Finset (Fin 52) := {0, 1, 2}

theorem threeCycle_apply : threeCycle 0 = 1 ∧ threeCycle 1 = 2 ∧ threeCycle 2 = 0 := by decide

theorem threeCycle_not_sym : ¬ ∃ a x, threeCycle = v10Sym a x := by decide

theorem threeCycle_label : ∀ c : Fin 52, suitLabel (threeCycle c).val = suitLabel c.val := by
  decide

theorem delta3_off : ∀ c : Fin 52, c ∉ W3 → delta threeCycle c = 0 := by decide

theorem delta3_vals :
    delta threeCycle 0 = 1 ∧ delta threeCycle 1 = 1 ∧ delta threeCycle 2 = 11 := by decide

/-! ## Survival is exactly the four row equations -/

theorem threeCycle_app_label (n : ℕ) : suitLabel (threeCycle.app n) = suitLabel n := by
  unfold Relabel.app
  split
  · exact threeCycle_label ⟨n, ‹_›⟩
  · rfl

theorem colTurnV10_threeCycle (p y : Fin 4 → ℕ) :
    colTurnV10 (fun r => threeCycle.app (p r)) (fun r => threeCycle.app (y r)) =
      colTurnV10 p y := by
  simp only [colTurnV10, colValue, colSuits, threeCycle_app_label]

theorem colsDone_threeCycle (H : Grid Nat) (n : ℕ) :
    colsDone colTurnV10 (relG threeCycle H) n = relG threeCycle (colsDone colTurnV10 H n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show colStep _ (colsDone _ (relG _ H) n) _ = relG _ (colStep _ (colsDone _ H n) _)
    rw [ih]
    unfold colStep
    rw [show column (relG threeCycle (colsDone colTurnV10 H n)) =
        fun c r => threeCycle.app (column (colsDone colTurnV10 H n) c r) from rfl,
      colTurnV10_threeCycle]
    exact turnCol_rel _ _ _ _

/-- With the row turns matching along the trajectory, `τ G` rows track `τ` of `G` rows. -/
theorem rowsDone_rel_of_traj (τ : Relabel) (g : Grid Nat) (h : RowCondsTraj τ g) :
    ∀ n, n ≤ 4 → rowsDone rowTurnV10 (relG τ g) n = relG τ (rowsDone rowTurnV10 g n) := by
  intro n hn
  induction n with
  | zero => rfl
  | succ n ih =>
    let i : Fin 4 := ⟨(n + 1) % 4, Nat.mod_lt _ (by decide)⟩
    have hi : rowStepOf i - 1 = n := by simp only [rowStepOf, i]; split <;> omega
    have hc := h i
    rw [hi] at hc
    show rowStep _ (rowsDone _ (relG τ g) n) i = relG τ (rowStep _ (rowsDone _ g n) i)
    rw [ih (by omega)]
    unfold rowStep
    rw [hc]
    exact turnRow_rel _ _ _ _

/-- Row condition `r + 1` is the row equation of row `r` (both directions of
    `rowEq_of_rowCondsTraj`, PROOF.md §1 Cor. 1). -/
theorem rowCond_iff (τ : Relabel) (π : Equiv.Perm (Fin 52)) (p : Fin 4) :
    rowTurnV10 (relG τ (rowsDone rowTurnV10 (deckGrid π) (rowStepOf (p + 1) - 1))
        (prevRow (p + 1))) =
      rowTurnV10 (rowsDone rowTurnV10 (deckGrid π) (rowStepOf (p + 1) - 1) (prevRow (p + 1))) ↔
    rowS τ (rowOf π p) = thetaG π p * rowD τ (rowOf π p) := by
  rw [prevRow_succ, rowsDone_eq_partial _ _ _ (by have := rowStepOf_le (p + 1); omega)]
  set A := (if rowStepOf p ≤ rowStepOf (p + 1) - 1 then rowAmt rowTurnV10 (deckGrid π) p else 0)
    with hA
  let k : Fin 13 := ⟨A % 13, Nat.mod_lt _ (by decide)⟩
  have hrow : ∀ G : Grid Nat, G = deckGrid π →
      rowRotate G (fun r => if rowStepOf r ≤ rowStepOf (p + 1) - 1 then
        rowAmt rowTurnV10 (deckGrid π) r else 0) p = fun j => (rowOf π p (j + k)).val := by
    intro G hG
    funext j
    rw [rowRotate_apply, hG, deckGrid_apply]
    simp only [rowOf]
    congr 3
  have hrel : ∀ (G : Grid Nat), relG τ G p = fun j => τ.app (G p j) := fun _ => rfl
  rw [hrel, hrow _ rfl, rowTurn_rel_iff τ (fun j => rowOf π p (j + k)), rowS_rotate, sub_eq_zero]
  have hk : ((k.val : ℕ) : ZMod 13) = thetaG π p := by
    simp only [thetaG, k]
    by_cases hp : p = 0
    · rw [if_pos hp]
      have : A = 0 := by rw [hA, if_neg]; rw [rowStep_read_iff]; exact not_not.2 hp
      simp [this]
    · rw [if_neg hp]
      have : A = rowAmt rowTurnV10 (deckGrid π) p := by
        rw [hA, if_pos ((rowStep_read_iff p).2 hp)]
      rw [this, ZMod.natCast_mod]
  rw [hk]

/-- **Survival ⇔ row equations** for `threeCycle` (PROOF.md §1, Lemma 1 and
    Cor. 1, both directions): it preserves suits, so the column conditions
    always hold. -/
theorem survives_threeCycle_iff (π : Equiv.Perm (Fin 52)) :
    Survives threeCycle π ↔
      ∀ r, rowS threeCycle (rowOf π r) = thetaG π r * rowD threeCycle (rowOf π r) := by
  constructor
  · intro h
    exact rowEq_of_rowCondsTraj _ π (traj_of_survives _ _ (isDeck_deckGrid π) h).1
  · intro h
    have htraj : RowCondsTraj threeCycle (deckGrid π) := by
      intro r
      have := (rowCond_iff threeCycle π (r - 1)).2 (h (r - 1))
      rwa [sub_add_cancel] at this
    have hrows := rowsDone_rel_of_traj _ _ htraj
    unfold Survives
    rw [survives_iff_amounts _ _ (isDeck_deckGrid π)]
    refine ⟨fun r => ?_, fun c => ?_⟩
    · unfold rowAmt
      rw [hrows _ (by unfold rowStepOf; split <;> omega)]
      exact congrArg (· % 13) (htraj r)
    · rw [hrows 4 le_rfl]
      unfold colAmt
      rw [colsDone_threeCycle, show column (relG threeCycle
          (colsDone colTurnV10 (rowsDone rowTurnV10 (deckGrid π) 4) (colStepOf c - 1))) =
          fun c' r => threeCycle.app (column (colsDone colTurnV10
            (rowsDone rowTurnV10 (deckGrid π) 4) (colStepOf c - 1)) c' r) from rfl,
        colTurnV10_threeCycle]

/-! ## Three positions of a random arrangement

Instances of the generic counting lemmas of `DoubleDealSecurity/PermCount.lean`. -/

/-- All fibres of `σ ↦ (σ i₀, σ i₁, σ i₂)` over distinct triples have the same size. -/
theorem fibre_card (i0 i1 i2 : Fin 13) (t : Fin 13 × Fin 13 × Fin 13)
    (ht : t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2) :
    (univ.filter fun σ : Equiv.Perm (Fin 13) => (σ i0, σ i1, σ i2) = t).card =
      (univ.filter fun σ : Equiv.Perm (Fin 13) => (σ i0, σ i1, σ i2) = (0, 1, 2)).card :=
  PermCount.fibre3_card_eq i0 i1 i2 (0, 1, 2) t (by decide) ht

/-- Counting arrangements by the seats of three fixed cards. -/
theorem count_triples (i0 i1 i2 : Fin 13) (h01 : i0 ≠ i1) (h02 : i0 ≠ i2) (h12 : i1 ≠ i2)
    (P : Fin 13 × Fin 13 × Fin 13 → Prop) [DecidablePred P] :
    (univ.filter fun σ : Equiv.Perm (Fin 13) => P (σ i0, σ i1, σ i2)).card =
      (univ.filter fun t : Fin 13 × Fin 13 × Fin 13 =>
          t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 ∧ P t).card *
        (univ.filter fun σ : Equiv.Perm (Fin 13) => (σ i0, σ i1, σ i2) = (0, 1, 2)).card :=
  PermCount.count_triples_of i0 i1 i2 h01 h02 h12 (0, 1, 2) (by decide) P

theorem card_good_triples : (univ.filter fun t : Fin 13 × Fin 13 × Fin 13 =>
    t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 ∧
      (t.1.val : ZMod 13) + t.2.1.val + 11 * t.2.2.val = 0).card = 156 := by
  decide!

theorem card_distinct_triples : (univ.filter fun t : Fin 13 × Fin 13 × Fin 13 =>
    t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 ∧ True).card = 1716 := by
  decide!

/-- `σ i₀ + σ i₁ + 11·σ i₂ ≡ 0 (mod 13)` for exactly `1/11` of the arrangements. -/
theorem count_S3 (i0 i1 i2 : Fin 13) (h01 : i0 ≠ i1) (h02 : i0 ≠ i2) (h12 : i1 ≠ i2) :
    11 * (univ.filter fun σ : Equiv.Perm (Fin 13) =>
      ((σ i0).val : ZMod 13) + (σ i1).val + 11 * (σ i2).val = 0).card = Nat.factorial 13 := by
  have hP := count_triples i0 i1 i2 h01 h02 h12
    (fun t => (t.1.val : ZMod 13) + t.2.1.val + 11 * t.2.2.val = 0)
  have hT := count_triples i0 i1 i2 h01 h02 h12 (fun _ => True)
  rw [card_good_triples] at hP
  rw [card_distinct_triples, filter_True, card_univ, Fintype.card_perm, Fintype.card_fin] at hT
  rw [hP, hT]
  ring

/-! ## One row: `ρ` by the number of moved cards -/

/-- `ρ` of a row holding `k` of the three moved cards (PROOF.md §5b). -/
def g3 (k : ℕ) : ℚ := if k = 0 then 1 else if k ≤ 2 then 1 / 13 else if k = 3 then 1 / 11 else 0

theorem sum_sub_W3 {β : Type*} [AddCommMonoid β] (S : Finset (Fin 52)) (hS : S ⊆ W3)
    (f : Fin 52 → β) :
    ∑ c ∈ S, f c = (if (0 : Fin 52) ∈ S then f 0 else 0) +
      ((if (1 : Fin 52) ∈ S then f 1 else 0) + (if (2 : Fin 52) ∈ S then f 2 else 0)) := by
  calc ∑ c ∈ S, f c = ∑ c ∈ W3, if c ∈ S then f c else 0 := by
        rw [← sum_filter]
        congr 1
        ext c
        simp only [mem_filter]
        exact ⟨fun h => ⟨hS h, h⟩, fun h => h.2⟩
    _ = _ := by rw [W3, sum_insert (by decide), sum_insert (by decide), sum_singleton]

theorem rowS_three (x : Fin 13 → Fin 52) (hx : Function.Injective x) (i0 i1 i2 : Fin 13)
    (h0 : x i0 = 0) (h1 : x i1 = 1) (h2 : x i2 = 2) (σ : Equiv.Perm (Fin 13)) :
    rowS threeCycle (x ∘ σ) =
      ((σ⁻¹ i0).val : ZMod 13) + (σ⁻¹ i1).val + 11 * (σ⁻¹ i2).val := by
  have h01 : i0 ≠ i1 := fun e => by rw [e, h1] at h0; exact absurd h0 (by decide)
  have h02 : i0 ≠ i2 := fun e => by rw [e, h2] at h0; exact absurd h0 (by decide)
  have h12 : i1 ≠ i2 := fun e => by rw [e, h2] at h1; exact absurd h1 (by decide)
  unfold rowS
  rw [← Equiv.sum_comp σ⁻¹ (fun j => (j.val : ZMod 13) * delta threeCycle ((x ∘ σ) j))]
  simp only [Function.comp, Equiv.Perm.apply_inv_self]
  rw [← sum_subset (subset_univ {i0, i1, i2})]
  · rw [sum_insert (by simp [h01, h02]), sum_insert (by simp [h12]), sum_singleton, h0, h1, h2,
      delta3_vals.1, delta3_vals.2.1, delta3_vals.2.2]
    ring
  · intro j _ hj
    simp only [mem_insert, mem_singleton, not_or] at hj
    rw [delta3_off, mul_zero]
    intro hW
    simp only [W3, mem_insert, mem_singleton] at hW
    rcases hW with e | e | e
    · exact hj.1 (hx (e.trans h0.symm))
    · exact hj.2.1 (hx (e.trans h1.symm))
    · exact hj.2.2 (hx (e.trans h2.symm))

/-- `ρ` of a row of the 3-cycle (PROOF.md §5b): `1` with none of the three moved
    cards, `1/13` with one or two, `1/11` with all three. -/
theorem rho_threeCycle (x : Fin 13 → Fin 52) (hx : Function.Injective x) :
    rho threeCycle x = g3 (univ.filter fun j => x j ∈ W3).card := by
  set S := (univ.filter fun j => x j ∈ W3).image x with hSdef
  have hSW : S ⊆ W3 := by
    intro c hc
    simp only [hSdef, mem_image, mem_filter, mem_univ, true_and] at hc
    obtain ⟨j, hj, rfl⟩ := hc
    exact hj
  have hcard : S.card = (univ.filter fun j => x j ∈ W3).card :=
    card_image_of_injective _ hx
  have hD : rowD threeCycle x = ∑ c ∈ S, delta threeCycle c := by
    unfold rowD
    rw [hSdef, sum_image (fun a _ b _ h => hx h), sum_filter_of_ne]
    intro j _ hj
    by_contra hW
    exact hj (delta3_off _ hW)
  have hmem : ∀ c, c ∈ S ↔ ∃ j, x j = c ∧ c ∈ W3 := by
    intro c
    simp only [hSdef, mem_image, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨j, hj, rfl⟩; exact ⟨j, rfl, hj⟩
    · rintro ⟨j, rfl, hj⟩; exact ⟨j, hj, rfl⟩
  have hc := sum_sub_W3 S hSW (fun _ => (1 : ℕ))
  have hd := sum_sub_W3 S hSW (delta threeCycle)
  rw [← card_eq_sum_ones, hcard] at hc
  rw [← hD, delta3_vals.1, delta3_vals.2.1, delta3_vals.2.2] at hd
  rw [hc]
  by_cases hnone : (0 : Fin 52) ∉ S ∧ (1 : Fin 52) ∉ S ∧ (2 : Fin 52) ∉ S
  · -- none moved: every arrangement has `S = 0`
    obtain ⟨m0, m1, m2⟩ := hnone
    simp only [m0, m1, m2, if_false] at hd ⊢
    have hz : ∀ j, delta threeCycle (x j) = 0 := by
      intro j
      apply delta3_off
      intro hW
      have := (hmem (x j)).2 ⟨j, rfl, hW⟩
      simp only [W3, mem_insert, mem_singleton] at hW
      rcases hW with e | e | e <;> rw [e] at this <;> contradiction
    have hS0 : ∀ σ : Equiv.Perm (Fin 13), rowS threeCycle (x ∘ σ) = 0 := by
      intro σ
      simp only [rowS, Function.comp, hz, mul_zero, sum_const_zero]
    simp only [rho, hd, ne_eq, not_true_eq_false, if_false, hS0, filter_True, card_univ,
      Fintype.card_perm, Fintype.card_fin, g3]
    exact div_self (by exact_mod_cast (Nat.factorial_pos 13).ne')
  by_cases hall : (0 : Fin 52) ∈ S ∧ (1 : Fin 52) ∈ S ∧ (2 : Fin 52) ∈ S
  · -- all three moved
    obtain ⟨m0, m1, m2⟩ := hall
    simp only [m0, m1, m2, if_true] at hd ⊢
    obtain ⟨i0, h0, -⟩ := (hmem 0).1 m0
    obtain ⟨i1, h1, -⟩ := (hmem 1).1 m1
    obtain ⟨i2, h2, -⟩ := (hmem 2).1 m2
    have h01 : i0 ≠ i1 := fun e => by rw [e, h1] at h0; exact absurd h0 (by decide)
    have h02 : i0 ≠ i2 := fun e => by rw [e, h2] at h0; exact absurd h0 (by decide)
    have h12 : i1 ≠ i2 := fun e => by rw [e, h2] at h1; exact absurd h1 (by decide)
    have hD0 : rowD threeCycle x = 0 := by rw [hd]; decide
    have hcnt : (univ.filter fun σ : Equiv.Perm (Fin 13) => rowS threeCycle (x ∘ σ) = 0).card =
        (univ.filter fun σ : Equiv.Perm (Fin 13) =>
          ((σ i0).val : ZMod 13) + (σ i1).val + 11 * (σ i2).val = 0).card := by
      apply card_nbij' (fun σ => σ⁻¹) (fun σ => σ⁻¹)
      · intro σ hσ
        simp only [coe_filter, Set.mem_setOf_eq, mem_filter, mem_univ, true_and, mem_coe] at hσ ⊢
        rwa [rowS_three x hx i0 i1 i2 h0 h1 h2] at hσ
      · intro σ hσ
        simp only [coe_filter, Set.mem_setOf_eq, mem_filter, mem_univ, true_and, mem_coe] at hσ ⊢
        rwa [rowS_three x hx i0 i1 i2 h0 h1 h2, inv_inv]
      · intro σ _; exact inv_inv σ
      · intro σ _; exact inv_inv σ
    have h11 := count_S3 i0 i1 i2 h01 h02 h12
    rw [← hcnt] at h11
    have hne : ((univ.filter fun σ : Equiv.Perm (Fin 13) =>
        rowS threeCycle (x ∘ σ) = 0).card : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.2 fun h => by rw [h] at h11; exact Nat.factorial_ne_zero 13 h11.symm
    simp only [rho, hD0, ne_eq, not_true_eq_false, if_false, g3]
    norm_num
    rw [← h11]
    push_cast
    field_simp
    ring
  -- one or two moved: `D ≠ 0`
  have key : rowD threeCycle x ≠ 0 ∧
      ((if (0 : Fin 52) ∈ S then 1 else 0) + ((if (1 : Fin 52) ∈ S then 1 else 0) +
        (if (2 : Fin 52) ∈ S then 1 else 0)) = 1 ∨
      (if (0 : Fin 52) ∈ S then 1 else 0) + ((if (1 : Fin 52) ∈ S then 1 else 0) +
        (if (2 : Fin 52) ∈ S then 1 else 0)) = 2) := by
    rw [hd]
    by_cases m0 : (0 : Fin 52) ∈ S <;> by_cases m1 : (1 : Fin 52) ∈ S <;>
      by_cases m2 : (2 : Fin 52) ∈ S <;> simp only [m0, m1, m2, if_true, if_false]
    all_goals first
      | decide
      | (exfalso; clear hc hd hD hmem hcard hSW hSdef; tauto)
  simp only [rho, key.1, ne_eq, not_false_eq_true, if_true, g3]
  rcases key.2 with k | k <;> rw [k] <;> norm_num

/-! ## The row sum `Σ_π Π_r ρ` -/

/-- `C(13, k) · g3 k` (row `k`-subsets times their `ρ`). -/
def fN (k : ℕ) : ℕ := [1, 1, 6, 26].getD k 0

theorem choose_g3 (k : ℕ) : ((Nat.choose 13 k : ℕ) : ℚ) * g3 k = fN k := by
  by_cases hk : k ≤ 3
  · interval_cases k <;> norm_num [g3, fN, Nat.choose]
  · have h1 : g3 k = 0 := by simp only [g3]; split_ifs <;> first | rfl | omega
    have h2 : fN k = 0 := List.getD_eq_default _ _ (by simp; omega)
    rw [h1, h2]; simp

theorem sum_fN_fin : ∑ x ∈ (univ.filter fun x : Fin 4 → Fin 4 => ∑ r, (x r).val = 3),
    ∏ r, fN (x r).val = 180 := by
  decide!

theorem sum_fN : ∑ z ∈ comps4 3, ∏ r, (fN (z r) : ℚ) = 180 := by
  have h : ∑ z ∈ comps4 3, ∏ r, fN (z r) = 180 := by
    rw [← sum_fN_fin]
    symm
    apply sum_nbij' (fun x r => (x r).val)
      (fun z r => (⟨z r % 4, Nat.mod_lt _ (by norm_num)⟩ : Fin 4))
    · intro x hx
      simp only [coe_filter, mem_filter, mem_univ, true_and, Set.mem_setOf_eq, comps4,
        Fintype.mem_piFinset, mem_range, mem_coe] at hx ⊢
      exact ⟨fun r => by have := (x r).isLt; omega, hx⟩
    · intro z hz
      simp only [coe_filter, mem_filter, mem_univ, true_and, Set.mem_setOf_eq, comps4,
        Fintype.mem_piFinset, mem_range, mem_coe] at hz ⊢
      have hle : ∀ r, z r < 4 := fun r => by
        have := single_le_sum (f := z) (fun _ _ => Nat.zero_le _) (mem_univ r)
        omega
      rw [← hz.2]
      exact sum_congr rfl fun r _ => Nat.mod_eq_of_lt (hle r)
    · intro x _; funext r; apply Fin.ext; exact Nat.mod_eq_of_lt (x r).isLt
    · intro z hz
      simp only [coe_filter, mem_filter, comps4, Fintype.mem_piFinset, mem_range, mem_coe] at hz
      funext r
      have := single_le_sum (f := z) (fun _ _ => Nat.zero_le _) (mem_univ r)
      exact Nat.mod_eq_of_lt (by omega)
    · intro x _; rfl
  exact_mod_cast h

/-- `Σ_π Π_r ρ(row r) = 1080 · 49! = (9/1105) · 52!` for the 3-cycle (PROOF.md §5b):
    by rows `ρ = g3(z_r)`, then the hypergeometric law for the three moved cards. -/
theorem rhoSum_threeCycle : rhoSum threeCycle = 1080 * (Nat.factorial 49 : ℕ) := by
  unfold rhoSum
  have hrow : ∀ π : Equiv.Perm (Fin 52),
      ∏ r, rho threeCycle (rowOf π r) = ∏ r, g3 (zRow W3 π r) := fun π =>
    prod_congr rfl fun r _ => by
      rw [rho_threeCycle _ (rowOf_injective π r)]
      exact congrArg g3 (card_row_eq_zRow W3 π r (· ∈ W3) fun _ => Iff.rfl)
  simp only [hrow]
  rw [hyper_rows W3 (fun z => ∏ r, g3 (z r))]
  have hW : W3.card = 3 := rfl
  have hz : ∀ z : Fin 4 → ℕ, (∏ r, ((Nat.choose 13 (z r) : ℕ) : ℚ)) *
      ((Nat.factorial 3 * (52 - 3).factorial : ℕ) : ℚ) * ∏ r, g3 (z r) =
      ((Nat.factorial 3 * (52 - 3).factorial : ℕ) : ℚ) * ∏ r, (fN (z r) : ℚ) := by
    intro z
    rw [mul_comm (∏ r, _), mul_assoc, ← prod_mul_distrib]
    simp only [choose_g3]
  rw [hW]
  simp only [hz, ← mul_sum, sum_fN]
  norm_num [Nat.factorial]

/-! ## Main result -/

theorem survivors_threeCycle_card :
    ((survivors threeCycle).card : ℚ) = rhoSum threeCycle := by
  have h : survivors threeCycle = univ.filter fun π : Equiv.Perm (Fin 52) =>
      ∀ r, rowS threeCycle (rowOf π r) = thetaG π r * rowD threeCycle (rowOf π r) :=
    filter_congr fun π _ => survives_threeCycle_iff π
  rw [h]
  exact rowChain_eq _ thetaG thetaG_prefix

/-- **Exact survival of the same-suit 3-cycle** (PROOF.md §5b): `A♣ → 2♣ → 3♣`
    commutes with v10 SumRanks on exactly `(9/1105) · 52!` decks. This is one
    specific relabelling; that it is the worst case (the supremum over all
    non-symmetries) is computer-assisted and not formalised. -/
theorem sumRanksV10_survival_threeCycle :
    1105 * (survivors threeCycle).card = 9 * Fintype.card (Equiv.Perm (Fin 52)) := by
  have h := survivors_threeCycle_card
  rw [rhoSum_threeCycle] at h
  have h' : (survivors threeCycle).card = 1080 * Nat.factorial 49 := by exact_mod_cast h
  have h52 : Nat.factorial 52 = 52 * 51 * 50 * Nat.factorial 49 := by
    norm_num [Nat.factorial]
  rw [h', Fintype.card_perm, Fintype.card_fin, h52]
  ring

theorem lt_of_eq9 (c F : ℕ) (h : 1105 * c = 9 * F) (hF : 0 < F) : F < 123 * c := by omega

/-- **The `1/64` constant is within a factor `2` of tight**: some relabelling
    outside `v10Sym` survives on more than `52!/123` decks (`1105/9 < 123`),
    against the proved bound `52!/64` (`sumRanksV10_survival_le`). -/
theorem sumRanksV10_survival_lower :
    ∃ τ : Relabel, (¬ ∃ a x, τ = v10Sym a x) ∧
      Fintype.card (Equiv.Perm (Fin 52)) < 123 * (survivors τ).card := by
  refine ⟨threeCycle, threeCycle_not_sym, ?_⟩
  have h := sumRanksV10_survival_threeCycle
  rw [Fintype.card_perm, Fintype.card_fin] at h ⊢
  exact lt_of_eq9 _ _ h (Nat.factorial_pos 52)

end DoubleDeal.Security.SumRanksDP
