import DoubleDealSecurity.Differential

/-
  Roadmap item B1 (`dp1_le`, one mix round), as far as it is proved here.

  B1 asks for `max_{α ≠ 1, β} DP_1(α → β) ≤ ε₁` for one v12 MIX round (stem, then GridCycle;
  `Differential.dp1Count`, independent uniform key, so `DP_1 = dp1Count / 52!`). Two results:

  1. B1 IMPLIES THE COVARIANT CONJECTURE. Any bound with `ε₁ < 1` gives
     `roundBody_covariant_iff_id` (`covariant_iff_id_of_dp1_lt`, `covariant_iff_id_of_dp1Bound`):
     a covariant pair `(σ, τ)` has `dp1Count σ τ = 52!` (`dp1Count_eq_of_covPair`). Since the
     `v10Sym` rows are bounded (item 2), a bound below 1 on the rows OUTSIDE `v10Sym` alone is
     enough (`covariant_iff_id_of_dp1_lt_off_v10Sym`). That conjecture keeps the one allowed
     `sorry` (`Rounds.roundBody_covariant_iff_id`; its statement is proved in the heavy library
     by kernel `decide!`, `LabelStep.roundBody_covariant_iff_id_heavy`); B1 for those rows is
     not proved here.

  2. THE 51 `v10Sym` ROWS ARE PROVED, for every output `β`:
     * `dp1_le_v10Sym`: `52 · dp1Count (v10Sym a x) β ≤ 52!` for every `(a, x)` other than
       `(0, 0)` and `(0, 3)`;
     * `dp1_le_v10Sym_zero_three`: `17 · dp1Count (v10Sym 0 3) β ≤ 52!`;
     * `dp1_le_v10Sym_all`: `17 · dp1Count (v10Sym a x) β ≤ 52!` for every `(a, x) ≠ (0, 0)`.
     The stem passes `v10Sym a x` unchanged (`Differential.unkeyedNoMix_rel_v10Sym`), so these
     are bounds on GridCycle's own difference table at `v10Sym` inputs. They refine
     `Differential.dp1Count_v10Sym_le_agree` (D4, one seat) by a second seat. Method
     (`mixRound_v10Sym_reads`): with `y` the round output, the condition forces
     `β (y 26) = α (y 26)` (GridCycle's seat 26; `Differential.v10Sym_step_agree`) and
     `β (y p') = α (y p)` at the two seats `p = seat2Idx (y 26)`, `p' = seat2Idx (α (y 26))`
     where the walk puts the second card (`mixColumns_seat2`). `p ≠ p'` unless the first card
     is K♣ or K♠ and `α` swaps them (`sameSeat2`, empty unless `(a, x) = (0, 3)`); otherwise
     three distinct seats of a uniform deck give the factor `51 / (52 · 51 · 50)` per first
     card (`card_seat_link_le`), at most 50 first cards qualify when `β ≠ α`
     (`card_agree_le_fifty`), and the diagonal `β = α` is GridCycle survival
     (`dp1Count_v10Sym_self_le`: none, or at most `52!/26` for `(0, 3)`).
     The 17 for `(0, 3)` is a limit of this two-seat argument (the K♣/K♠ first cards are
     counted in full), not a measured value: sampled values are far smaller
     (`../analysis/v12-dp1/NOTES.md`, EMPIRICAL).

  NOT proved: B1 for any row `α` outside `v10Sym` (that would prove the covariant conjecture);
  any multi-round or real-schedule bound. Not a security claim.
-/

namespace DoubleDeal.Security.OneRoundDP

open DoubleDeal Relabel Finset
open DoubleDeal.Security.Differential (dp1Count dpCount unkeyedNoMix_rel_v10Sym
  v10Sym_step_agree layerPerm permDeck_layerPerm layerPerm_injective)
open DoubleDeal.Security.GridCycleSurvival (gcSurvivors GCSurvives gcSurvivors_v10Sym_eq_empty
  gc_survival_v10Sym03 v10Sym_fixfree v10SymFn_KC_KS v10SymFn_KS_KC)

/-! ## B1 implies the covariant conjecture -/

/-- Roadmap item B1 with `ε₁ = 1/p`, in count form: `p · dp1Count α β ≤ 52!` for every
    `α ≠ 1` and every `β` (one mix round, independent uniform key). A statement, NOT proved. -/
def DP1Bound (p : ℕ) : Prop :=
  ∀ α : Relabel, α ≠ 1 → ∀ β : Relabel, p * dp1Count α β ≤ Nat.factorial 52

/-- (PROVED) A covariant pair counts every deck. -/
theorem dp1Count_eq_of_covPair {σ τ : Relabel}
    (h : ∀ m, IsDeck m → unkeyedWithMix (rel σ m) = rel τ (unkeyedWithMix m)) :
    dp1Count σ τ = Nat.factorial 52 := by
  unfold dp1Count dpCount
  rw [filter_true_of_mem (fun π _ => h _ (isDeck_permDeck π)), card_univ, Fintype.card_perm,
    Fintype.card_fin]

/-- (PROVED) Any one-round bound below 1 (`dp1Count α β < 52!` for every `α ≠ 1` and `β`)
    implies the covariant conjecture `roundBody_covariant_iff_id`. (The `←` direction repeats
    the proved half of `Rounds.roundBody_covariant_iff_id`; citing that theorem would put its
    `sorry` in this closure.) -/
theorem covariant_iff_id_of_dp1_lt
    (h : ∀ α : Relabel, α ≠ 1 → ∀ β, dp1Count α β < Nat.factorial 52) (σ : Relabel) :
    Covariant σ unkeyedWithMix ↔ σ = 1 := by
  constructor
  · rintro ⟨τ, hτ⟩
    by_contra hσ
    exact absurd (dp1Count_eq_of_covPair hτ) (h σ hσ τ).ne
  · rintro rfl
    exact ⟨1, fun m _ => by rw [rel_one, rel_one]⟩

/-- (PROVED) B1 with any `ε₁ = 1/p ≤ 1/2` implies the covariant conjecture. -/
theorem covariant_iff_id_of_dp1Bound {p : ℕ} (hp : 2 ≤ p) (h : DP1Bound p) (σ : Relabel) :
    Covariant σ unkeyedWithMix ↔ σ = 1 := by
  refine covariant_iff_id_of_dp1_lt (fun α hα β => ?_) σ
  have h1 := h α hα β
  have hpos := Nat.factorial_pos 52
  generalize Nat.factorial 52 = F at h1 hpos ⊢
  generalize dp1Count α β = d at h1 ⊢
  by_contra hc
  push_neg at hc
  have : 2 * d ≤ p * d := Nat.mul_le_mul_right d hp
  omega

/-! ## GridCycle's first two seats, read on the output -/

theorem scoop_rmFlat {α : Type} (g : Grid α) (r : Fin 4) (c : Fin 13) :
    scoopRowMajor g (rmFlat r c) = g r c := by
  have h := rm_rmFlat r c
  simp only [scoopRowMajor, h.1, h.2]

theorem rmFlat_inj {r r' : Fin 4} {c c' : Fin 13} (h : rmFlat r c = rmFlat r' c') :
    r = r' ∧ c = c' := by
  have h1 := rm_rmFlat r c
  have h2 := rm_rmFlat r' c'
  rw [h] at h1
  exact ⟨h1.1.symm.trans h2.1, h1.2.symm.trans h2.2⟩

/-- The row-major output index of the seat where GridCycle's walk puts the second card when
    the first card is `v` (`seat2`, `mixColumns_seat2`). -/
def seat2Idx (v : ℕ) : Fin 52 := rmFlat (seat2 v).1 (seat2 v).2

/-- (PROVED) GridCycle puts the second card of `m` at the seat `seat2 (m 0)`. -/
theorem mixColumns_seat2 (m : Fin 52 → Nat) :
    mixColumns m (seat2Idx (m ⟨0, by decide⟩)) = m ⟨1, by decide⟩ := by
  rw [mixColumns_eq, seat2Idx, scoop_rmFlat]
  have h := gridW_at_seat chooseSeat! freeChooser m ⟨1, by decide⟩
  rw [← walkSeat_eq, walkSeat_one] at h
  exact h

/-- (PROVED, kernel `decide!`) The second seat is never the start seat. -/
theorem seat2_ne_start : ∀ c : Fin 52, seat2 c.val ≠ asStart := by
  decide!

theorem seat2Idx_ne_26 (c : Fin 52) : seat2Idx c.val ≠ 26 := by
  intro h
  have hs : rmFlat asStart.1 asStart.2 = 26 := rfl
  obtain ⟨h1, h2⟩ := rmFlat_inj (h.trans hs.symm)
  exact seat2_ne_start c (Prod.ext h1 h2)

theorem seat2_eq_of_seat2Idx_eq {v w : ℕ} (h : seat2Idx v = seat2Idx w) : seat2 v = seat2 w :=
  Prod.ext (rmFlat_inj h).1 (rmFlat_inj h).2

/-- (PROVED) For an input difference `α = v10Sym a x`: if the round sends `(x₀, α·x₀)`
    (`x₀ = permDeck π`) to difference `β`, and `ρ` is the output deck, then
    `β (ρ 26) = α (ρ 26)` (`Differential.v10Sym_step_agree`) and `β (ρ p') = α (ρ p)` with
    `p = seat2Idx (ρ 26)` and `p' = seat2Idx (α (ρ 26))`. -/
theorem mixRound_v10Sym_reads (a : Fin 13) (x : Fin 4) (β : Relabel) (π ρ : Equiv.Perm (Fin 52))
    (hρ : permDeck ρ = unkeyedWithMix (permDeck π))
    (h : unkeyedWithMix (rel (v10Sym a x) (permDeck π)) = rel β (unkeyedWithMix (permDeck π))) :
    β (ρ 26) = v10Sym a x (ρ 26) ∧
      β (ρ (seat2Idx (v10Sym a x (ρ 26)).val)) = v10Sym a x (ρ (seat2Idx (ρ 26).val)) := by
  have hA := v10Sym_step_agree a x β (isDeck_permDeck π) h
  simp only [unkeyedWithMix] at h hρ
  rw [unkeyedNoMix_rel_v10Sym a x (isDeck_permDeck π).1] at h
  set z := unkeyedNoMix (permDeck π) with hz
  have hzd : IsDeck z := isDeck_unkeyedNoMix (isDeck_permDeck π)
  have hρv : ∀ i, (ρ i).val = mixColumns z i := fun i => congrFun hρ i
  have e26 : ρ 26 = ⟨z ⟨0, by decide⟩, hzd.1 _⟩ := by
    apply Fin.ext; rw [hρv]; exact mixColumns_seat26 z
  have e1 : ρ (seat2Idx (z ⟨0, by decide⟩)) = ⟨z ⟨1, by decide⟩, hzd.1 _⟩ := by
    apply Fin.ext; rw [hρv]; exact mixColumns_seat2 z
  rw [e26]
  refine ⟨hA.symm, ?_⟩
  have e := congrFun h (seat2Idx (rel (v10Sym a x) z ⟨0, by decide⟩))
  rw [mixColumns_seat2 (rel (v10Sym a x) z)] at e
  simp only [rel] at e
  have ea : (v10Sym a x).app (z ⟨0, by decide⟩) =
      (v10Sym a x ⟨z ⟨0, by decide⟩, hzd.1 _⟩).val := app_fin _ ⟨_, hzd.1 _⟩
  rw [ea] at e
  show β (ρ (seat2Idx (v10Sym a x ⟨z ⟨0, by decide⟩, hzd.1 _⟩).val)) =
    v10Sym a x (ρ (seat2Idx (z ⟨0, by decide⟩)))
  rw [e1]
  apply Fin.ext
  rw [← app_fin β, hρv, ← e]
  exact app_fin _ ⟨_, hzd.1 _⟩

/-! ## Counting decks by three seats -/

/-- (PROVED) For three distinct seats, `52·51·50 · #{σ | σ i₀ = c ∧ β (σ i₂) = α (σ i₁)} ≤
    51 · 52!`: the card at `i₂` is determined by the card at `i₁`. -/
theorem card_seat_link_le {i0 i1 i2 : Fin 52} (h01 : i0 ≠ i1) (h02 : i0 ≠ i2) (h12 : i1 ≠ i2)
    (c : Fin 52) (α β : Relabel) :
    Nat.descFactorial 52 3 * (univ.filter fun σ : Equiv.Perm (Fin 52) =>
      σ i0 = c ∧ β (σ i2) = α (σ i1)).card ≤ 51 * Nat.factorial 52 := by
  have hall := PermCount.count_triples_of i0 i1 i2 h01 h02 h12
    ((0, 1, 2) : Fin 52 × Fin 52 × Fin 52) (by decide) (fun _ => True)
  rw [filter_True, card_univ, Fintype.card_perm, Fintype.card_fin] at hall
  simp only [and_true] at hall
  rw [PermCount.card_distinct_triples_eq, Fintype.card_fin] at hall
  rw [PermCount.count_triples_of i0 i1 i2 h01 h02 h12 ((0, 1, 2) : Fin 52 × Fin 52 × Fin 52)
    (by decide) (fun t => t.1 = c ∧ β t.2.2 = α t.2.1)]
  have hT : (univ.filter fun t : Fin 52 × Fin 52 × Fin 52 =>
      t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 ∧ (t.1 = c ∧ β t.2.2 = α t.2.1)).card ≤ 51 := by
    have hsub : (univ.filter fun t : Fin 52 × Fin 52 × Fin 52 =>
        t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 ∧ (t.1 = c ∧ β t.2.2 = α t.2.1)) ⊆
        (univ.erase c).image fun u => (c, u, β⁻¹ (α u)) := by
      intro t ht
      simp only [mem_filter, mem_univ, true_and] at ht
      obtain ⟨h1, -, -, hc, hb⟩ := ht
      rw [mem_image]
      refine ⟨t.2.1, mem_erase.mpr ⟨fun e => h1 (hc.trans e.symm), mem_univ _⟩, ?_⟩
      obtain ⟨t0, t1, t2⟩ := t
      simp only at hc hb ⊢
      rw [hc, ← hb, Equiv.Perm.inv_apply_self]
    refine (card_le_card hsub).trans (card_image_le.trans ?_)
    rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
  generalize (univ.filter fun σ : Equiv.Perm (Fin 52) =>
    (σ i0, σ i1, σ i2) = ((0, 1, 2) : Fin 52 × Fin 52 × Fin 52)).card = Fb at hall ⊢
  calc Nat.descFactorial 52 3 * ((univ.filter fun t : Fin 52 × Fin 52 × Fin 52 =>
        t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 ∧ (t.1 = c ∧ β t.2.2 = α t.2.1)).card * Fb)
      = (univ.filter fun t : Fin 52 × Fin 52 × Fin 52 =>
        t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 ∧ (t.1 = c ∧ β t.2.2 = α t.2.1)).card *
          (Nat.descFactorial 52 3 * Fb) := by ring
    _ ≤ 51 * (Nat.descFactorial 52 3 * Fb) := Nat.mul_le_mul_right _ hT
    _ = 51 * Nat.factorial 52 := by rw [hall]

/-! ## The `v10Sym` rows -/

/-- First cards for which the two second-seat reads coincide (`seat2 (α c) = seat2 c`). -/
def sameSeat2 (α : Relabel) : Finset (Fin 52) :=
  univ.filter fun c => seat2 (α c).val = seat2 c.val

/-- (PROVED) For a nontrivial `v10Sym a x`, only K♣ and K♠ can be such first cards. -/
theorem sameSeat2_subset (a : Fin 13) (x : Fin 4) (hne : ¬ (a = 0 ∧ x = 0)) :
    sameSeat2 (v10Sym a x) ⊆ {KC, KS} := by
  intro c hc
  simp only [sameSeat2, mem_filter, mem_univ, true_and] at hc
  rcases seat2_inj _ _ hc with h | ⟨-, h2⟩ | ⟨-, h2⟩
  · exact absurd h (v10Sym_fixfree a x hne c)
  · rw [h2]; simp
  · rw [h2]; simp

/-- (PROVED) For `(a, x)` other than `(0, 0)` and `(0, 3)` there are none. -/
theorem sameSeat2_eq_empty (a : Fin 13) (x : Fin 4) (hne : ¬ (a = 0 ∧ x = 0))
    (h03 : ¬ (a = 0 ∧ x = 3)) : sameSeat2 (v10Sym a x) = ∅ := by
  rw [eq_empty_iff_forall_not_mem]
  intro c hc
  simp only [sameSeat2, mem_filter, mem_univ, true_and] at hc
  rcases seat2_inj _ _ hc with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact v10Sym_fixfree a x hne c h
  · subst h2; exact h03 (v10SymFn_KS_KC a x h1)
  · subst h2; exact h03 (v10SymFn_KC_KS a x h1)

/-- (PROVED) Two different relabellings agree on at most 50 cards. -/
theorem card_agree_le_fifty {α β : Relabel} (h : β ≠ α) :
    (univ.filter fun c : Fin 52 => β c = α c).card ≤ 50 := by
  have hs := Equiv.Perm.two_le_card_support_of_ne_one (f := α⁻¹ * β)
    (fun e => h (inv_mul_eq_one.mp e).symm)
  have e : (α⁻¹ * β).support = univ.filter fun c : Fin 52 => ¬ (β c = α c) := by
    ext c
    simp only [Equiv.Perm.mem_support, Equiv.Perm.mul_apply, mem_filter, mem_univ, true_and]
    rw [Ne, Equiv.Perm.inv_eq_iff_eq]
  have hsum := filter_card_add_filter_neg_card_eq_card (s := (univ : Finset (Fin 52)))
    (fun c : Fin 52 => β c = α c)
  rw [← e, card_univ, Fintype.card_fin] at hsum
  omega

/-- (PROVED) The two-seat count for an input `v10Sym a x` and any `β` (refines D4,
    `Differential.dp1Count_v10Sym_le_agree`):
    `52·51·50 · dp1Count (v10Sym a x) β ≤ Σ_c w(c) · 52!`, where `w(c) = 0` unless
    `β c = v10Sym a x c`, `w(c) = 51` for such `c` with distinct second-seat reads, and
    `w(c) = 50 · 51` (the whole first-card share, `51!`) for `c ∈ sameSeat2`. -/
theorem dp1Count_v10Sym_le_sum (a : Fin 13) (x : Fin 4) (β : Relabel) :
    Nat.descFactorial 52 3 * dp1Count (v10Sym a x) β ≤
      ∑ c : Fin 52, (if β c = v10Sym a x c then
        (if c ∈ sameSeat2 (v10Sym a x) then 50 * 51 else 51) else 0) * Nat.factorial 52 := by
  set α := v10Sym a x with hα
  let f := layerPerm unkeyedWithMix (fun _ h => isDeck_unkeyedWithMix h)
  have h1 : dp1Count α β ≤ (univ.filter fun ρ : Equiv.Perm (Fin 52) =>
      β (ρ 26) = α (ρ 26) ∧
        β (ρ (seat2Idx (α (ρ 26)).val)) = α (ρ (seat2Idx (ρ 26).val))).card := by
    unfold dp1Count dpCount
    apply card_le_card_of_injOn f
    · intro π hπ
      simp only [coe_filter, Set.mem_setOf_eq, mem_filter, mem_univ, true_and, mem_coe] at hπ ⊢
      exact mixRound_v10Sym_reads a x β π (f π) (permDeck_layerPerm _ _ π) hπ
    · exact fun π₁ _ π₂ _ h => layerPerm_injective _ _ unkeyedWithMix_injective h
  refine (Nat.mul_le_mul_left _ h1).trans ?_
  rw [card_eq_sum_card_fiberwise (f := fun ρ : Equiv.Perm (Fin 52) => ρ 26) (t := univ)
    (fun _ _ => mem_univ _), mul_sum]
  refine sum_le_sum fun c _ => ?_
  rw [filter_filter]
  have hcong : (univ.filter fun ρ : Equiv.Perm (Fin 52) =>
      (β (ρ 26) = α (ρ 26) ∧
        β (ρ (seat2Idx (α (ρ 26)).val)) = α (ρ (seat2Idx (ρ 26).val))) ∧ ρ 26 = c) =
      univ.filter fun ρ : Equiv.Perm (Fin 52) =>
        ρ 26 = c ∧ (β c = α c ∧ β (ρ (seat2Idx (α c).val)) = α (ρ (seat2Idx c.val))) :=
    filter_congr fun ρ _ => by
      constructor
      · rintro ⟨h, rfl⟩; exact ⟨rfl, h⟩
      · rintro ⟨rfl, h⟩; exact ⟨h, rfl⟩
  rw [hcong]
  by_cases hb : β c = α c
  · rw [if_pos hb]
    by_cases hc : c ∈ sameSeat2 α
    · rw [if_pos hc]
      have hle : (univ.filter fun ρ : Equiv.Perm (Fin 52) =>
          ρ 26 = c ∧ (β c = α c ∧
            β (ρ (seat2Idx (α c).val)) = α (ρ (seat2Idx c.val)))).card ≤
          Nat.factorial 51 := by
        rw [← PermCount.card_apply_eq 26 c]
        exact card_le_card fun ρ hρ => by
          simp only [mem_filter, mem_univ, true_and] at hρ ⊢
          exact hρ.1
      have h52 : Nat.factorial 52 = 52 * Nat.factorial 51 := Nat.factorial_succ 51
      have hdf : Nat.descFactorial 52 3 = 52 * 51 * 50 := by decide
      rw [h52, hdf]
      generalize Nat.factorial 51 = F at hle ⊢
      omega
    · rw [if_neg hc]
      have h12 : seat2Idx c.val ≠ seat2Idx (α c).val := fun e =>
        hc (mem_filter.mpr ⟨mem_univ _, (seat2_eq_of_seat2Idx_eq e).symm⟩)
      refine le_trans (Nat.mul_le_mul_left _ (card_le_card fun ρ hρ => ?_))
        (card_seat_link_le (seat2Idx_ne_26 c).symm (seat2Idx_ne_26 (α c)).symm h12 c α β)
      simp only [mem_filter, mem_univ, true_and] at hρ ⊢
      exact ⟨hρ.1, hρ.2.2⟩
  · rw [if_neg hb, zero_mul, Nat.mul_eq_zero.mpr (Or.inr _)]
    rw [card_eq_zero, filter_eq_empty_iff]
    exact fun ρ _ h => hb h.2.1

/-- (PROVED) The diagonal entry of a `v10Sym` row is GridCycle survival: at most
    `#gcSurvivors (v10Sym a x)`. -/
theorem dp1Count_v10Sym_self_le (a : Fin 13) (x : Fin 4) :
    dp1Count (v10Sym a x) (v10Sym a x) ≤ (gcSurvivors (v10Sym a x)).card := by
  let g := layerPerm unkeyedNoMix (fun _ h => isDeck_unkeyedNoMix h)
  unfold dp1Count dpCount gcSurvivors
  apply card_le_card_of_injOn g
  · intro π hπ
    simp only [coe_filter, Set.mem_setOf_eq, mem_filter, mem_univ, true_and, mem_coe] at hπ ⊢
    simp only [unkeyedWithMix] at hπ
    rw [unkeyedNoMix_rel_v10Sym a x (isDeck_permDeck π).1] at hπ
    show mixColumns (rel (v10Sym a x) (permDeck (g π))) =
      rel (v10Sym a x) (mixColumns (permDeck (g π)))
    rw [permDeck_layerPerm]
    exact hπ
  · exact fun π₁ _ π₂ _ h => layerPerm_injective _ _ unkeyedNoMix_injective h

/-- (PROVED; B1 on 50 of the 51 `v10Sym` rows) For `(a, x)` other than `(0, 0)` and
    `(0, 3)`, `52 · dp1Count (v10Sym a x) β ≤ 52!` for EVERY output difference `β`: one mix
    round takes `v10Sym a x` to any fixed `β` with probability at most 1/52 (independent
    uniform key). The diagonal is `0` (`gcSurvivors_v10Sym_eq_empty`). -/
theorem dp1_le_v10Sym (a : Fin 13) (x : Fin 4) (hne : ¬ (a = 0 ∧ x = 0))
    (h03 : ¬ (a = 0 ∧ x = 3)) (β : Relabel) :
    52 * dp1Count (v10Sym a x) β ≤ Nat.factorial 52 := by
  by_cases hβ : β = v10Sym a x
  · subst hβ
    have h := dp1Count_v10Sym_self_le a x
    rw [gcSurvivors_v10Sym_eq_empty a x hne h03, card_empty] at h
    rw [Nat.le_zero.mp h]
    exact Nat.zero_le _
  · have hs := dp1Count_v10Sym_le_sum a x β
    rw [sameSeat2_eq_empty a x hne h03] at hs
    simp only [not_mem_empty, if_false] at hs
    rw [← sum_mul, sum_ite, sum_const_zero, add_zero, sum_const, smul_eq_mul] at hs
    have hA := card_agree_le_fifty hβ
    have hdf : Nat.descFactorial 52 3 = 132600 := by decide
    rw [hdf] at hs
    have h2 := hs.trans (Nat.mul_le_mul_right (Nat.factorial 52) (Nat.mul_le_mul_right 51 hA))
    generalize Nat.factorial 52 = F at h2 ⊢
    generalize dp1Count (v10Sym a x) β = d at h2 ⊢
    omega

/-- (PROVED; B1 on the row `v10Sym 0 3`) `17 · dp1Count (v10Sym 0 3) β ≤ 52!` for every `β`.
    The off-diagonal count is at most `(50 · 51 + 2 · (50 · 51 − 51)) · 52! / (52 · 51 · 50)`;
    the K♣/K♠ first cards, whose two second-seat reads coincide, are counted in full. The
    diagonal is at most `52!/26` (`gc_survival_v10Sym03`; `52!/4420` in the heavy library). -/
theorem dp1_le_v10Sym_zero_three (β : Relabel) :
    17 * dp1Count (v10Sym 0 3) β ≤ Nat.factorial 52 := by
  by_cases hβ : β = v10Sym 0 3
  · subst hβ
    have h := (Nat.mul_le_mul_left 26 (dp1Count_v10Sym_self_le 0 3)).trans gc_survival_v10Sym03
    omega
  · have hs := dp1Count_v10Sym_le_sum 0 3 β
    have hpt : ∀ c : Fin 52, (if β c = v10Sym 0 3 c then
        (if c ∈ sameSeat2 (v10Sym 0 3) then 50 * 51 else 51) else 0) * Nat.factorial 52 ≤
        (if β c = v10Sym 0 3 c then 51 else 0) * Nat.factorial 52 +
          (if c ∈ sameSeat2 (v10Sym 0 3) then 50 * 51 - 51 else 0) * Nat.factorial 52 := by
      intro c
      rw [← add_mul]
      apply Nat.mul_le_mul_right
      split_ifs <;> omega
    have h2 := hs.trans (sum_le_sum fun c _ => hpt c)
    rw [sum_add_distrib, ← sum_mul, ← sum_mul] at h2
    rw [sum_ite, sum_ite] at h2
    simp only [sum_const_zero, add_zero, sum_const, smul_eq_mul] at h2
    have hA := card_agree_le_fifty hβ
    have hS : (univ.filter fun c : Fin 52 => c ∈ sameSeat2 (v10Sym 0 3)).card ≤ 2 :=
      (card_le_card fun c hc => sameSeat2_subset 0 3 (by decide) (mem_filter.mp hc).2).trans
        card_le_two
    have hdf : Nat.descFactorial 52 3 = 132600 := by decide
    rw [hdf] at h2
    have h3 := h2.trans (add_le_add
      (Nat.mul_le_mul_right (Nat.factorial 52) (Nat.mul_le_mul_right 51 hA))
      (Nat.mul_le_mul_right (Nat.factorial 52) (Nat.mul_le_mul_right (50 * 51 - 51) hS)))
    generalize Nat.factorial 52 = F at h3 ⊢
    generalize dp1Count (v10Sym 0 3) β = d at h3 ⊢
    omega

/-- (PROVED; B1 on all 51 `v10Sym` rows) `17 · dp1Count (v10Sym a x) β ≤ 52!` for every
    nontrivial `v10Sym a x` and every `β` (1/52 for all of them but `v10Sym 0 3`,
    `dp1_le_v10Sym`). NOT B1: rows outside `v10Sym` are not covered
    (`covariant_iff_id_of_dp1_lt_off_v10Sym`). -/
theorem dp1_le_v10Sym_all (a : Fin 13) (x : Fin 4) (hne : ¬ (a = 0 ∧ x = 0)) (β : Relabel) :
    17 * dp1Count (v10Sym a x) β ≤ Nat.factorial 52 := by
  by_cases h03 : a = 0 ∧ x = 3
  · obtain ⟨rfl, rfl⟩ := h03
    exact dp1_le_v10Sym_zero_three β
  · have := dp1_le_v10Sym a x hne h03 β
    omega

/-- (PROVED) A bound below 1 on the rows OUTSIDE `v10Sym` alone implies the covariant
    conjecture: the `v10Sym` rows are covered by `dp1_le_v10Sym_all`. -/
theorem covariant_iff_id_of_dp1_lt_off_v10Sym
    (h : ∀ α : Relabel, α ≠ 1 → (¬ ∃ a x, α = v10Sym a x) → ∀ β,
      dp1Count α β < Nat.factorial 52) (σ : Relabel) :
    Covariant σ unkeyedWithMix ↔ σ = 1 := by
  refine covariant_iff_id_of_dp1_lt (fun α hα β => ?_) σ
  by_cases hv : ∃ a x, α = v10Sym a x
  · obtain ⟨a, x, rfl⟩ := hv
    have hne : ¬ (a = 0 ∧ x = 0) := fun ⟨ha, hx⟩ => hα (by rw [ha, hx, v10Sym_zero_zero])
    have h17 := dp1_le_v10Sym_all a x hne β
    have hpos := Nat.factorial_pos 52
    omega
  · exact h α hα hv β

end DoubleDeal.Security.OneRoundDP
