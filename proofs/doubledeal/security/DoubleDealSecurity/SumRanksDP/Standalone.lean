/-
  v10 SumRanks survival bound, the self-contained part.

  Mathlib-only lemmas with no repository definitions: the one-row lemma
  (Lemma 2), the GF(4) column table (Lemma 4), a generic fibre bound, the two
  hypergeometric counting identities, and the numeric tables. It imports only
  Mathlib and uses only the definitions in this file.

  `PROOF.md §n` refers to the paper proof
  `proofs/doubledeal/security/sumranks-dp-paper/PROOF.md`.
-/
import Mathlib

namespace SRDP

open Finset

instance fact_prime_13 : Fact (Nat.Prime 13) := ⟨by norm_num⟩

/-! ## §2 One row: Lemma 2, over arrangements of a fixed row

A row is a fixed list of 13 difference values `w : Fin 13 → ZMod 13` (the
values `δ(c)` of its 13 cards in some reference order). An arrangement is a
permutation `σ` of the 13 seats; the card in seat `j` has value `w (σ j)`. -/

/-- `S` of an arrangement, `Σ_j j · w(σ j)` in `ZMod 13` (PROOF.md §0 (0.2)). -/
def wS (w : Fin 13 → ZMod 13) (σ : Equiv.Perm (Fin 13)) : ZMod 13 :=
  ∑ j : Fin 13, (j.val : ZMod 13) * w (σ j)

theorem natCast_val_sub13 : ∀ i k : Fin 13,
    (((i - k : Fin 13).val : ℕ) : ZMod 13) = (i.val : ZMod 13) - (k.val : ZMod 13) := by decide

/-- Seat shift: `Σ_j j·f(j+k) = Σ_j j·f(j) − k·Σ_j f(j)` (PROOF.md §0 (0.3)). -/
theorem sum_seat_shift (f : Fin 13 → ZMod 13) (k : Fin 13) :
    ∑ j : Fin 13, (j.val : ZMod 13) * f (j + k) =
      ∑ j : Fin 13, (j.val : ZMod 13) * f j - (k.val : ZMod 13) * ∑ j, f j := by
  rw [Fintype.sum_equiv (Equiv.addRight k) (fun j => (j.val : ZMod 13) * f (j + k))
    (fun i => ((i - k : Fin 13).val : ZMod 13) * f i) (fun j => by simp)]
  simp only [natCast_val_sub13, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]

/-- The seat rotation `j ↦ j + 1`. -/
def rot1 : Equiv.Perm (Fin 13) := Equiv.addRight 1

/-- (0.3) for one step: rotating the seats by one lowers `S` by `D = Σ w`
    (PROOF.md §0 (0.3), used in §2 Lemma 2(a)). -/
theorem wS_mul_rot1 (w : Fin 13 → ZMod 13) (σ : Equiv.Perm (Fin 13)) :
    wS w (σ * rot1) = wS w σ - ∑ j, w j := by
  have h := sum_seat_shift (fun j => w (σ j)) 1
  simp only [wS, rot1, Equiv.Perm.mul_apply, Equiv.coe_addRight]
  rw [h, Equiv.sum_comp σ w]
  simp

/-- The fibre over `c` and the fibre over `c - D` have the same size (`σ ↦ σ * rot1`). -/
theorem card_fib_rot (w : Fin 13 → ZMod 13) (c : ZMod 13) :
    (univ.filter fun σ : Equiv.Perm (Fin 13) => wS w σ = c).card =
      (univ.filter fun σ : Equiv.Perm (Fin 13) => wS w σ = c - ∑ j, w j).card := by
  apply card_nbij' (fun σ => σ * rot1) (fun σ => σ * rot1⁻¹)
  · intro σ hσ
    simp only [coe_filter, mem_filter, mem_univ, true_and, Set.mem_setOf_eq] at hσ ⊢
    rw [wS_mul_rot1, hσ]
  · intro σ hσ
    simp only [coe_filter, mem_filter, mem_univ, true_and, Set.mem_setOf_eq] at hσ ⊢
    have h := wS_mul_rot1 w (σ * rot1⁻¹)
    rw [mul_assoc, inv_mul_cancel, mul_one, hσ] at h
    linear_combination -h
  · intro σ _; simp [mul_assoc]
  · intro σ _; simp [mul_assoc]

theorem card_fib_rot_iter (w : Fin 13 → ZMod 13) (c : ZMod 13) (k : ℕ) :
    (univ.filter fun σ : Equiv.Perm (Fin 13) => wS w σ = c).card =
      (univ.filter fun σ : Equiv.Perm (Fin 13) => wS w σ = c - k * ∑ j, w j).card := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ih, card_fib_rot, show c - (k : ZMod 13) * ∑ j, w j - ∑ j, w j =
      c - ((k + 1 : ℕ) : ZMod 13) * ∑ j, w j by push_cast; ring]

/-- **Lemma 2(a)** (PROOF.md §2): if `D = Σ w ≠ 0`, every value of `S` is taken
    by exactly `13!/13` arrangements. Suggested proof: `wS_mul_rot1` gives a
    bijection from the fibre over `c` to the fibre over `c - D`; `D` generates
    `ZMod 13`, so all 13 fibres have the same size, and they partition `Perm`. -/
theorem lemma2a (w : Fin 13 → ZMod 13) (hD : ∑ j, w j ≠ 0) (c : ZMod 13) :
    13 * (univ.filter fun σ : Equiv.Perm (Fin 13) => wS w σ = c).card = Nat.factorial 13 := by
  have hall : ∀ c' : ZMod 13, (univ.filter fun σ : Equiv.Perm (Fin 13) => wS w σ = c').card =
      (univ.filter fun σ : Equiv.Perm (Fin 13) => wS w σ = c).card := by
    intro c'
    rw [card_fib_rot_iter w c ((c - c') / ∑ j, w j).val, ZMod.natCast_zmod_val,
      div_mul_cancel₀ _ hD, sub_sub_cancel]
  have h := card_eq_sum_card_fiberwise (s := (univ : Finset (Equiv.Perm (Fin 13))))
    (t := (univ : Finset (ZMod 13))) (f := wS w) (fun _ _ => mem_univ _)
  rw [card_univ, Fintype.card_perm, Fintype.card_fin] at h
  rw [h, sum_congr rfl fun c' _ => hall c', sum_const, card_univ, ZMod.card, smul_eq_mul]

theorem wS_eq_inv (w : Fin 13 → ZMod 13) (σ : Equiv.Perm (Fin 13)) :
    wS w σ = ∑ i, ((σ⁻¹ i).val : ZMod 13) * w i := by
  unfold wS; exact Fintype.sum_equiv σ _ _ (fun j => by simp)

/-- Swapping the seats of entry `i₀` and a `v`-entry `k` shifts `S` by
    `(w i₀ − v)·(pos k − pos i₀)` (PROOF.md §2, one-card switching). -/
theorem wS_swap (w : Fin 13 → ZMod 13) (v : ZMod 13) (i₀ k : Fin 13) (hk : k ≠ i₀)
    (hwk : w k = v) (σ : Equiv.Perm (Fin 13)) :
    wS w (Equiv.swap i₀ k * σ) =
      wS w σ + (w i₀ - v) * (((σ⁻¹ k).val : ZMod 13) - ((σ⁻¹ i₀).val : ZMod 13)) := by
  rw [wS_eq_inv, wS_eq_inv]
  have h1 : ∀ i, (Equiv.swap i₀ k * σ)⁻¹ i = σ⁻¹ (Equiv.swap i₀ k i) := by
    intro i; simp [mul_inv_rev, Equiv.swap_inv]
  simp only [h1]
  rw [← Equiv.sum_comp (Equiv.swap i₀ k)
    (fun i => ((σ⁻¹ (Equiv.swap i₀ k i)).val : ZMod 13) * w i)]
  simp only [Equiv.swap_apply_self]
  have hd : ∑ i, ((σ⁻¹ i).val : ZMod 13) * w (Equiv.swap i₀ k i) -
      ∑ i, ((σ⁻¹ i).val : ZMod 13) * w i =
      ((σ⁻¹ i₀).val : ZMod 13) * (w k - w i₀) +
        ((σ⁻¹ k).val : ZMod 13) * (w i₀ - w k) := by
    rw [← sum_sub_distrib, Fintype.sum_eq_add i₀ k hk.symm]
    · simp only [Equiv.swap_apply_left, Equiv.swap_apply_right]; ring
    · intro i hi
      rw [Equiv.swap_apply_of_ne_of_ne hi.1 hi.2, sub_self]
  rw [hwk] at hd
  linear_combination hd

/-- **Lemma 2(b)** (PROOF.md §2, one-card switching): if some seat value
    differs from `v`, and `v` occurs `z` times, at most `13!/(z+1)` arrangements
    have `S = c`. Suggested proof: double counting with
    `Finset.card_mul_le_card_mul` on the relation "`σ'` is `σ` with the seats of
    one fixed non-`v` card and one `v`-card swapped" (good–bad edges only; a bad
    vertex has at most one good neighbour because the `z` shifts
    `(u - v)(pos w - pos c*)` are distinct and nonzero). -/
theorem lemma2b (w : Fin 13 → ZMod 13) (v : ZMod 13) (hnc : ∃ i, w i ≠ v) (c : ZMod 13) :
    ((univ.filter fun i => w i = v).card + 1) *
        (univ.filter fun σ : Equiv.Perm (Fin 13) => wS w σ = c).card ≤ Nat.factorial 13 := by
  classical
  obtain ⟨i₀, hi₀⟩ := hnc
  set V := univ.filter fun i => w i = v with hV
  set G := univ.filter fun σ : Equiv.Perm (Fin 13) => wS w σ = c with hG
  set B := univ.filter fun σ : Equiv.Perm (Fin 13) => ¬ wS w σ = c with hB
  have hd : w i₀ - v ≠ 0 := sub_ne_zero.2 hi₀
  have hcast : ∀ a b : Fin 13, ((a.val : ℕ) : ZMod 13) = (b.val : ZMod 13) → a = b := by
    decide
  have hVw : ∀ k ∈ V, w k = v := fun k hk => (mem_filter.1 hk).2
  have hVne : ∀ k ∈ V, k ≠ i₀ := fun k hk e => hi₀ (by rw [← e]; exact hVw k hk)
  have huniq : ∀ (σ' : Equiv.Perm (Fin 13)) k₁ k₂, k₁ ∈ V → k₂ ∈ V →
      wS w (Equiv.swap i₀ k₁ * σ') = c → wS w (Equiv.swap i₀ k₂ * σ') = c →
        k₁ = k₂ := by
    intro σ' k₁ k₂ h1 h2 e1 e2
    rw [wS_swap w v i₀ k₁ (hVne k₁ h1) (hVw k₁ h1)] at e1
    rw [wS_swap w v i₀ k₂ (hVne k₂ h2) (hVw k₂ h2)] at e2
    have : (w i₀ - v) * ((σ'⁻¹ k₁).val : ZMod 13) =
        (w i₀ - v) * ((σ'⁻¹ k₂).val : ZMod 13) := by
      linear_combination e1 - e2
    exact σ'⁻¹.injective (hcast _ _ (mul_left_cancel₀ hd this))
  have hinj : (G ×ˢ V).card ≤ B.card := by
    apply card_le_card_of_injOn (fun x => Equiv.swap i₀ x.2 * x.1)
    · intro x hx
      simp only [hG, hV, hB, coe_product, coe_filter, Set.mem_prod, Set.mem_setOf_eq, mem_coe,
        mem_product, mem_filter, mem_univ, true_and] at hx ⊢
      rw [wS_swap w v i₀ x.2 (hVne x.2 (by simp [hV, hx.2])) hx.2, hx.1]
      intro e
      have h0 : (w i₀ - v) *
          (((x.1⁻¹ x.2).val : ZMod 13) - ((x.1⁻¹ i₀).val : ZMod 13)) = 0 := by
        linear_combination e
      rcases mul_eq_zero.1 h0 with h | h
      · exact hd h
      · exact hVne x.2 (by simp [hV, hx.2]) (x.1⁻¹.injective (hcast _ _ (sub_eq_zero.1 h)))
    · intro x hx y hy e
      simp only [hG, hV, coe_product, coe_filter, Set.mem_prod, Set.mem_setOf_eq, mem_coe,
        mem_product, mem_filter, mem_univ, true_and] at hx hy
      simp only at e
      have ex : x.1 = Equiv.swap i₀ x.2 * (Equiv.swap i₀ x.2 * x.1) := by
        rw [Equiv.swap_mul_self_mul]
      have ey : y.1 = Equiv.swap i₀ y.2 * (Equiv.swap i₀ x.2 * x.1) := by
        rw [e, Equiv.swap_mul_self_mul]
      have hk : x.2 = y.2 := huniq _ x.2 y.2 (by simp [hV, hx.2]) (by simp [hV, hy.2])
        (by rw [← ex]; exact hx.1) (by rw [← ey]; exact hy.1)
      have h1 : x.1 = y.1 := by rw [hk] at e; exact mul_left_cancel e
      exact Prod.ext h1 hk
  rw [card_product] at hinj
  have htot := filter_card_add_filter_neg_card_eq_card (s := (univ : Finset (Equiv.Perm (Fin 13))))
    (fun σ => wS w σ = c)
  rw [card_univ, Fintype.card_perm, Fintype.card_fin] at htot
  rw [← hG, ← hB] at htot
  nlinarith

/-- `Σ_j j = 78 ≡ 0 (mod 13)`: a constant row has `S = 0` (PROOF.md §1, Case B remark). -/
theorem sum_seat_weights : ∑ j : Fin 13, (j.val : ZMod 13) = 0 := by
  decide

/-- **Lemma 2(c)** (PROOF.md §2, cancelling pair): values `{v¹¹, v+u, v−u}` with
    `u ≠ 0` never give `S = 0` (`S = 78v + u(j₁ − j₂)`, and `78 ≡ 0`). -/
theorem lemma2c (w : Fin 13 → ZMod 13) (v u : ZMod 13) (hu : u ≠ 0) (i₁ i₂ : Fin 13)
    (h12 : i₁ ≠ i₂) (hw₁ : w i₁ = v + u) (hw₂ : w i₂ = v - u)
    (hw : ∀ i, i ≠ i₁ → i ≠ i₂ → w i = v) (σ : Equiv.Perm (Fin 13)) :
    wS w σ ≠ 0 := by
  have hwi : ∀ i, w i = v + (if i = i₁ then u else 0) - (if i = i₂ then u else 0) := by
    intro i
    by_cases h1 : i = i₁
    · subst h1; simp [h12, hw₁]
    · by_cases h2 : i = i₂
      · subst h2; simp [h1, hw₂]
      · simp [h1, h2, hw i h1 h2]
  have hre : wS w σ = ∑ i : Fin 13, ((σ.symm i).val : ZMod 13) * w i := by
    unfold wS
    exact Fintype.sum_equiv σ _ _ (fun j => by simp)
  have hsum : ∑ i : Fin 13, ((σ.symm i).val : ZMod 13) = 0 := by
    rw [Equiv.sum_comp σ.symm (fun j : Fin 13 => (j.val : ZMod 13))]; exact sum_seat_weights
  rw [hre]
  simp only [hwi, mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib, mul_ite,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← Finset.sum_mul, hsum, zero_mul, zero_add, ← mul_sub_right_distrib]
  refine mul_ne_zero ?_ hu
  intro e
  rw [sub_eq_zero] at e
  have hne : σ.symm i₁ ≠ σ.symm i₂ := fun h => h12 (σ.symm.injective h)
  have hv : ∀ a b : Fin 13, ((a.val : ℕ) : ZMod 13) = (b.val : ZMod 13) → a = b := by decide
  exact hne (hv _ _ e)

/-- Lemma 2(c), the other half: a cancelling-pair row has `D = 0`. -/
theorem sum_of_cancel (w : Fin 13 → ZMod 13) (v u : ZMod 13) (i₁ i₂ : Fin 13)
    (h12 : i₁ ≠ i₂) (hw₁ : w i₁ = v + u) (hw₂ : w i₂ = v - u)
    (hw : ∀ i, i ≠ i₁ → i ≠ i₂ → w i = v) : ∑ i, w i = 0 := by
  have hwi : ∀ i, w i = v + (if i = i₁ then u else 0) - (if i = i₂ then u else 0) := by
    intro i
    by_cases h1 : i = i₁
    · subst h1; simp [h12, hw₁]
    · by_cases h2 : i = i₂
      · subst h2; simp [h1, hw₂]
      · simp [h1, h2, hw i h1 h2]
  simp only [hwi, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have : (13 : ℕ) • v = 0 := by
    rw [nsmul_eq_mul]; rw [show ((13 : ℕ) : ZMod 13) = 0 from rfl, zero_mul]
  rw [this]; ring

/-- Largest class of a nonconstant `ZMod 13` labelling of the 52 cards with sum
    `0` has at most 50 elements (PROOF.md §3: `n* = 51` contradicts `Σ δ = 0`). -/
theorem maxClass_le_50 (f : Fin 52 → ZMod 13) (hs : ∑ c, f c = 0) (hnc : ∃ c, f c ≠ f 0)
    (v : ZMod 13) : (univ.filter fun c => f c = v).card ≤ 50 := by
  by_contra hlt
  push_neg at hlt
  set S := univ.filter fun c => f c = v with hS
  have hSc : Sᶜ.card ≤ 1 := by
    have := card_compl S; simp only [Fintype.card_fin] at this; omega
  -- every element outside S is the unique one
  obtain ⟨c, hc⟩ := hnc
  have hsplit : ∑ x, f x = ∑ x ∈ S, f x + ∑ x ∈ Sᶜ, f x := (sum_add_sum_compl S f).symm
  have hSv : ∑ x ∈ S, f x = S.card • v := by
    rw [← sum_const]; exact sum_congr rfl fun x hx => (mem_filter.mp hx).2
  rcases Nat.lt_or_ge Sᶜ.card 1 with h0 | h1
  · have hSe : Sᶜ = ∅ := card_eq_zero.mp (by omega)
    have hall : ∀ x, f x = v := fun x => by
      have : x ∉ Sᶜ := by simp [hSe]
      simpa [hS] using this
    exact hc (by rw [hall c, hall 0])
  · have hc1 : Sᶜ.card = 1 := by omega
    obtain ⟨d, hd⟩ := card_eq_one.mp hc1
    have hScard : S.card = 51 := by
      have := card_compl S; simp only [Fintype.card_fin] at this; omega
    rw [hsplit, hSv, hd, sum_singleton, hScard] at hs
    have hdv : f d ≠ v := by
      have : d ∈ Sᶜ := by rw [hd]; exact mem_singleton_self d
      simpa [hS] using this
    apply hdv
    have h51 : (51 : ℕ) • v = -v := by
      rw [nsmul_eq_mul]; have : ((51 : ℕ) : ZMod 13) = -1 := by decide
      rw [this]; ring
    rw [h51] at hs
    linear_combination hs

/-- Pigeonhole (PROOF.md §4): some label class has at least 13 of the 52 cards. -/
theorem exists_class_ge_13 (f : Fin 52 → Fin 4) :
    ∃ x, 13 ≤ (univ.filter fun c => f c = x).card := by
  by_contra h
  push_neg at h
  have hsum := Finset.card_eq_sum_card_fiberwise (s := (univ : Finset (Fin 52)))
    (t := (univ : Finset (Fin 4))) (f := f) (fun _ _ => mem_univ _)
  have hle : ∑ x : Fin 4, (univ.filter fun c => f c = x).card ≤ ∑ _x : Fin 4, 12 :=
    Finset.sum_le_sum fun x _ => Nat.lt_succ_iff.mp (h x)
  simp only [card_univ, Fintype.card_fin, sum_const, smul_eq_mul] at hsum hle
  omega

/-! ## Hypergeometric counting (PROOF.md §3 (A2) and §4 Theorem B)

Positions `p : Fin 52` are the grid cells in column-major order, so row `r` is
`{p | p % 4 = r}` and column `j` is `{p | p / 4 = j}` (`cmFlat r j = r + 4j`).
A deck is a permutation `π` (card in position `p` is `π p`). -/

/-- Number of cards of `W` in row `r`. -/
def zRow (W : Finset (Fin 52)) (π : Equiv.Perm (Fin 52)) (r : Fin 4) : ℕ :=
  (univ.filter fun p : Fin 52 => p.val % 4 = r.val ∧ π p ∈ W).card

/-- Number of cards of `W` in column `j`. -/
def yCol (W : Finset (Fin 52)) (π : Equiv.Perm (Fin 52)) (j : Fin 13) : ℕ :=
  (univ.filter fun p : Fin 52 => p.val / 4 = j.val ∧ π p ∈ W).card

/-- Row-count vectors `(z₀,…,z₃)`, `0 ≤ z_r ≤ 13`, summing to `n`. -/
def comps4 (n : ℕ) : Finset (Fin 4 → ℕ) :=
  (Fintype.piFinset fun _ => range 14).filter fun z => ∑ r, z r = n

/-- Column-count vectors `(y₀,…,y₁₂)`, `0 ≤ y_j ≤ 4`, summing to `m`. -/
def comps13 (m : ℕ) : Finset (Fin 13 → ℕ) :=
  (Fintype.piFinset fun _ => range 5).filter fun y => ∑ j, y j = m

/-! ### Generic block hypergeometric count -/

theorem exists_perm_mapsTo {α : Type*} [Fintype α] [DecidableEq α] (A A' : Finset α)
    (h : A.card = A'.card) : ∃ τ : Equiv.Perm α, ∀ p, p ∈ A' ↔ τ p ∈ A := by
  have e : {x // x ∈ A'} ≃ {x // x ∈ A} := Fintype.equivOfCardEq (by simp [h])
  have f : {x // ¬ x ∈ A'} ≃ {x // ¬ x ∈ A} := Fintype.equivOfCardEq (by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl]; simp [h])
  refine ⟨Equiv.subtypeCongr e f, fun p => ?_⟩
  by_cases hp : p ∈ A'
  · have := (e ⟨p, hp⟩).2
    simp [Equiv.subtypeCongr, hp] at this ⊢
  · have := (f ⟨p, hp⟩).2
    simpa [Equiv.subtypeCongr, hp] using this

/-- The seats holding cards of `W`. -/
def preW (W : Finset (Fin 52)) (π : Equiv.Perm (Fin 52)) : Finset (Fin 52) :=
  univ.filter fun p => π p ∈ W

theorem card_preW (W : Finset (Fin 52)) (π : Equiv.Perm (Fin 52)) : (preW W π).card = W.card := by
  have : preW W π = W.map π.symm.toEmbedding := by
    ext p; simp [preW, mem_map_equiv]
  rw [this, card_map]

theorem card_fibre_preW_eq (W A A' : Finset (Fin 52)) (h : A.card = A'.card) :
    (univ.filter fun π => preW W π = A).card = (univ.filter fun π => preW W π = A').card := by
  obtain ⟨τ, hτ⟩ := exists_perm_mapsTo A A' h
  apply card_nbij' (fun π => π * τ) (fun π => π * τ⁻¹)
  · intro π hπ
    simp only [coe_filter, mem_filter, mem_univ, true_and, Set.mem_setOf_eq] at hπ ⊢
    ext p
    rw [hτ p, ← hπ]
    simp [preW]
  · intro π hπ
    simp only [coe_filter, mem_filter, mem_univ, true_and, Set.mem_setOf_eq] at hπ ⊢
    ext p
    have := hτ (τ⁻¹ p)
    simp only [Equiv.Perm.apply_inv_self] at this
    rw [← this, ← hπ]
    simp [preW]
  · intro π _; simp [mul_assoc]
  · intro π _; simp [mul_assoc]

/-- Each `n`-set of seats is the `W`-seat set of exactly `n!(52−n)!` decks. -/
theorem card_fibre_preW (W A : Finset (Fin 52)) (h : A.card = W.card) :
    (univ.filter fun π => preW W π = A).card = W.card.factorial * (52 - W.card).factorial := by
  set n := W.card
  have hn : n ≤ 52 := by simpa using card_le_univ W
  have hsum := card_eq_sum_card_fiberwise (s := (univ : Finset (Equiv.Perm (Fin 52))))
    (t := powersetCard n (univ : Finset (Fin 52))) (f := preW W)
    (fun π _ => mem_powersetCard.2 ⟨subset_univ _, card_preW W π⟩)
  rw [sum_congr rfl fun A' hA' => card_fibre_preW_eq W A' A
    ((mem_powersetCard.1 hA').2.trans h.symm), sum_const, card_powersetCard] at hsum
  simp only [card_univ, Fintype.card_perm, Fintype.card_fin, smul_eq_mul] at hsum
  have hc := Nat.choose_mul_factorial_mul_factorial hn
  rw [mul_assoc] at hc
  exact Nat.eq_of_mul_eq_mul_left (Nat.choose_pos hn) (hsum.symm.trans hc.symm)

section HyperGen

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Block counts of a seat set. -/
def bvec (e : Fin 52 ≃ ι × κ) (A : Finset (Fin 52)) (i : ι) : ℕ :=
  (univ.filter fun p => (e p).1 = i ∧ p ∈ A).card

omit [Fintype ι] [DecidableEq κ] in
theorem card_block (e : Fin 52 ≃ ι × κ) (i : ι) (P : Fin 52 → Prop) [DecidablePred P] :
    (univ.filter fun p => (e p).1 = i ∧ P p).card =
      (univ.filter fun k => P (e.symm (i, k))).card := by
  apply card_nbij' (fun p => (e p).2) (fun k => e.symm (i, k))
  · intro p hp
    simp only [coe_filter, mem_filter, mem_univ, true_and, Set.mem_setOf_eq] at hp ⊢
    rw [← hp.1, Prod.mk.eta, Equiv.symm_apply_apply]; exact hp.2
  · intro k hk
    simp only [coe_filter, mem_filter, mem_univ, true_and, Set.mem_setOf_eq] at hk ⊢
    simpa using hk
  · intro p hp
    simp only [coe_filter, mem_filter, mem_univ, true_and, Set.mem_setOf_eq] at hp
    rw [← hp.1, Prod.mk.eta, Equiv.symm_apply_apply]
  · intro k _; simp

/-- Admissible block-count vectors. -/
def bcomps (n : ℕ) : Finset (ι → ℕ) :=
  (Fintype.piFinset fun _ => range (Fintype.card κ + 1)).filter fun z => ∑ i, z i = n

omit [Fintype κ] [DecidableEq κ] in
theorem sum_bvec (e : Fin 52 ≃ ι × κ) (A : Finset (Fin 52)) : ∑ i, bvec e A i = A.card := by
  have := card_eq_sum_card_fiberwise (s := A) (t := (univ : Finset ι)) (f := fun p => (e p).1)
    (fun _ _ => mem_univ _)
  rw [this]
  apply sum_congr rfl; intro i _
  unfold bvec; congr 1; ext p; simp [and_comm]

omit [DecidableEq κ] in
theorem bvec_mem (e : Fin 52 ≃ ι × κ) (A : Finset (Fin 52)) :
    bvec e A ∈ bcomps (κ := κ) A.card := by
  simp only [bcomps, mem_filter, Fintype.mem_piFinset, mem_range]
  refine ⟨fun i => ?_, sum_bvec e A⟩
  rw [bvec, card_block]
  exact Nat.lt_succ_of_le (card_le_univ _)

/-- Number of seat sets with block counts `z`. -/
theorem card_sets_bvec (e : Fin 52 ≃ ι × κ) (n : ℕ) (z : ι → ℕ)
    (hz : z ∈ bcomps (κ := κ) n) :
    ((powersetCard n univ).filter fun A => bvec e A = z).card =
      ∏ i, Nat.choose (Fintype.card κ) (z i) := by
  have hzs : ∑ i, z i = n := (mem_filter.1 hz).2
  rw [show ∏ i, Nat.choose (Fintype.card κ) (z i) =
      (Fintype.piFinset fun i => powersetCard (z i) (univ : Finset κ)).card by
    rw [Fintype.card_piFinset]; simp [card_powersetCard]]
  apply card_nbij' (fun A i => univ.filter fun k => e.symm (i, k) ∈ A)
    (fun B => univ.filter fun p => (e p).2 ∈ B (e p).1)
  · intro A hA
    simp only [mem_coe, mem_filter, mem_powersetCard, Fintype.mem_piFinset] at hA ⊢
    intro i
    refine ⟨subset_univ _, ?_⟩
    rw [← hA.2]; unfold bvec; rw [card_block]
  · intro B hB
    simp only [mem_coe, mem_filter, mem_powersetCard, Fintype.mem_piFinset] at hB ⊢
    have hb : bvec e (univ.filter fun p => (e p).2 ∈ B (e p).1) = z := by
      funext i; unfold bvec; rw [card_block]; simp only [mem_filter, mem_univ, true_and,
        Equiv.apply_symm_apply]
      rw [filter_mem_eq_inter, univ_inter]; exact (hB i).2
    refine ⟨⟨subset_univ _, ?_⟩, hb⟩
    rw [← sum_bvec e, hb, hzs]
  · intro A _; ext p; simp
  · intro B _; funext i; ext k; simp


theorem hyper_gen (e : Fin 52 ≃ ι × κ) (W : Finset (Fin 52)) (F : (ι → ℕ) → ℚ) :
    ∑ π : Equiv.Perm (Fin 52), F (bvec e (preW W π)) =
      ∑ z ∈ bcomps (κ := κ) W.card,
        (∏ i, ((Nat.choose (Fintype.card κ) (z i) : ℕ) : ℚ)) *
          (W.card.factorial * (52 - W.card).factorial : ℕ) * F z := by
  rw [← sum_fiberwise_of_maps_to (fun π (_ : π ∈ (univ : Finset (Equiv.Perm (Fin 52)))) =>
    mem_powersetCard.2 ⟨subset_univ (preW W π), card_preW W π⟩)]
  have h1 : ∀ A ∈ powersetCard W.card (univ : Finset (Fin 52)),
      ∑ π ∈ univ.filter (fun π => preW W π = A), F (bvec e (preW W π)) =
        ((W.card.factorial * (52 - W.card).factorial : ℕ) : ℚ) * F (bvec e A) := by
    intro A hA
    rw [sum_congr rfl fun π hπ => congrArg (fun B => F (bvec e B)) (mem_filter.1 hπ).2,
      sum_const, card_fibre_preW W A (mem_powersetCard.1 hA).2, nsmul_eq_mul]
  rw [sum_congr rfl h1]
  rw [← sum_fiberwise_of_maps_to
    (fun A (hA : A ∈ powersetCard W.card (univ : Finset (Fin 52))) =>
    (show bvec e A ∈ bcomps (κ := κ) W.card by
      have := bvec_mem e A; rwa [(mem_powersetCard.1 hA).2] at this))]
  apply sum_congr rfl
  intro z hz
  rw [sum_congr rfl fun A hA =>
      congrArg (fun y => ((W.card.factorial * (52 - W.card).factorial : ℕ) : ℚ) * F y)
        (mem_filter.1 hA).2, sum_const, card_sets_bvec e _ z hz, nsmul_eq_mul]
  push_cast; ring


end HyperGen

/-- Seats as (row, column): `p ↦ (p % 4, p / 4)`. -/
def rcEquiv : Fin 52 ≃ Fin 4 × Fin 13 where
  toFun p := (⟨p.val % 4, by omega⟩, ⟨p.val / 4, by omega⟩)
  invFun x := ⟨x.1.val + 4 * x.2.val, by omega⟩
  left_inv p := by apply Fin.ext; simp only; omega
  right_inv x := by
    ext
    · simp only; omega
    · simp only; omega

/-- Seats as (column, row). -/
def crEquiv : Fin 52 ≃ Fin 13 × Fin 4 := rcEquiv.trans (Equiv.prodComm _ _)

theorem zRow_eq_bvec (W : Finset (Fin 52)) (π : Equiv.Perm (Fin 52)) :
    zRow W π = bvec rcEquiv (preW W π) := by
  funext r
  unfold zRow bvec
  apply congrArg card; apply filter_congr; intro p _
  simp [preW, rcEquiv, Fin.ext_iff]

theorem yCol_eq_bvec (W : Finset (Fin 52)) (π : Equiv.Perm (Fin 52)) :
    yCol W π = bvec crEquiv (preW W π) := by
  funext j
  unfold yCol bvec
  apply congrArg card; apply filter_congr; intro p _
  simp [preW, crEquiv, rcEquiv, Fin.ext_iff]

/-- **Multivariate hypergeometric law, rows** (PROOF.md §3 (A2)): the number of
    decks with row counts `z` is `Π_r C(13, z_r) · n! · (52 − n)!`. -/
theorem hyper_rows (W : Finset (Fin 52)) (F : (Fin 4 → ℕ) → ℚ) :
    ∑ π : Equiv.Perm (Fin 52), F (zRow W π) =
      ∑ z ∈ comps4 W.card, (∏ r, ((Nat.choose 13 (z r) : ℕ) : ℚ)) *
        (W.card.factorial * (52 - W.card).factorial : ℕ) * F z := by
  simp only [zRow_eq_bvec]
  rw [hyper_gen rcEquiv W F]
  simp only [bcomps, comps4, Fintype.card_fin]

/-- **Multivariate hypergeometric law, columns** (PROOF.md §4 Theorem B). -/
theorem hyper_cols (W : Finset (Fin 52)) (F : (Fin 13 → ℕ) → ℚ) :
    ∑ π : Equiv.Perm (Fin 52), F (yCol W π) =
      ∑ y ∈ comps13 W.card, (∏ j, ((Nat.choose 4 (y j) : ℕ) : ℚ)) *
        (W.card.factorial * (52 - W.card).factorial : ℕ) * F y := by
  simp only [yCol_eq_bvec]
  rw [hyper_gen crEquiv W F]
  simp only [bcomps, comps13, Fintype.card_fin]

/-- AM–GM for 13 class sizes summing to 52: `Π_v n_v ≤ 4¹³`. -/
theorem amgm13 (n : ZMod 13 → ℕ) (h : ∑ v, n v = 52) : ∏ v, n v ≤ 4 ^ 13 := by
  have hw := Real.geom_mean_le_arith_mean_weighted (s := univ) (fun _ => (1 / 13 : ℝ))
    (fun v => (n v : ℝ)) (fun _ _ => by norm_num)
    (by rw [sum_const, card_univ, ZMod.card, nsmul_eq_mul]; norm_num) (fun _ _ => by positivity)
  rw [← mul_sum] at hw
  have hs : (∑ v, (n v : ℝ)) = 52 := by exact_mod_cast h
  rw [hs] at hw
  have hp : (∏ v, ((n v : ℝ) ^ (1 / 13 : ℝ))) ^ (13 : ℕ) = ∏ v, (n v : ℝ) := by
    rw [← prod_pow]
    apply prod_congr rfl; intro v _
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
  have h0 : 0 ≤ ∏ v, ((n v : ℝ) ^ (1 / 13 : ℝ)) := prod_nonneg fun v _ => by positivity
  have : (∏ v, (n v : ℝ)) ≤ 4 ^ 13 := by
    rw [← hp]
    calc _ ≤ ((1 / 13) * 52 : ℝ) ^ 13 := pow_le_pow_left₀ h0 hw 13
      _ = 4 ^ 13 := by norm_num
  exact_mod_cast this

/-- 13-card sets with pairwise distinct values number at most `4¹³`
    (they are transversals of the value classes). -/
theorem card_transversals_le (val : Fin 52 → ZMod 13) :
    ((powersetCard 13 (univ : Finset (Fin 52))).filter fun B =>
      ∀ a ∈ B, ∀ b ∈ B, a ≠ b → val a ≠ val b).card ≤ 4 ^ 13 := by
  classical
  set cl : ZMod 13 → Finset (Fin 52) := fun v => univ.filter fun c => val c = v
  have hsub : ((powersetCard 13 (univ : Finset (Fin 52))).filter fun B =>
      ∀ a ∈ B, ∀ b ∈ B, a ≠ b → val a ≠ val b) ⊆
      (Fintype.piFinset cl).image (fun f => univ.image f) := by
    intro B hB
    have hB' := mem_filter.1 hB
    have hBc := (mem_powersetCard.1 hB'.1).2
    have inj : Set.InjOn val B := fun a ha b hb e => by
      by_contra hne; exact hB'.2 a ha b hb hne e
    have himg : B.image val = univ :=
      eq_univ_of_card _ (by rw [card_image_of_injOn inj, hBc, ZMod.card])
    have hsurj : ∀ v, ∃ b ∈ B, val b = v := fun v => by
      have : v ∈ B.image val := by rw [himg]; exact mem_univ v
      simpa using this
    choose f hfB hfv using hsurj
    refine mem_image.2 ⟨f, Fintype.mem_piFinset.2 fun v => by simp [cl, hfv v], ?_⟩
    ext b
    simp only [mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨v, rfl⟩; exact hfB v
    · intro hb
      exact ⟨val b, inj (hfB (val b)) hb (hfv (val b))⟩
  refine (card_le_card hsub).trans (card_image_le.trans ?_)
  rw [Fintype.card_piFinset]
  apply amgm13
  have := card_eq_sum_card_fiberwise (s := (univ : Finset (Fin 52))) (t := univ) (f := val)
    (fun _ _ => mem_univ _)
  rw [card_univ, Fintype.card_fin] at this
  exact this.symm

/-- Rows with no repeated value (PROOF.md §3 (A3)): if the 52 cards carry
    values `val : Fin 52 → ZMod 13`, the decks whose row `r` holds 13 distinct
    values number `13! · 39! · Π_v n_v ≤ 4¹³ · 52! / C(52,13)` (AM–GM on
    `Σ n_v = 52`). -/
theorem distinct_row_count (val : Fin 52 → ZMod 13) (r : Fin 4) :
    (univ.filter fun π : Equiv.Perm (Fin 52) =>
        ∀ p q : Fin 52, p.val % 4 = r.val → q.val % 4 = r.val → p ≠ q →
          val (π p) ≠ val (π q)).card * Nat.choose 52 13 ≤ 4 ^ 13 * Nat.factorial 52 := by
  classical
  set R := univ.filter fun p : Fin 52 => p.val % 4 = r.val with hR
  have hRc : R.card = 13 := by
    have : ∀ r : Fin 4, (univ.filter fun p : Fin 52 => p.val % 4 = r.val).card = 13 := by decide
    exact this r
  set T := (powersetCard 13 (univ : Finset (Fin 52))).filter fun B =>
    ∀ a ∈ B, ∀ b ∈ B, a ≠ b → val a ≠ val b with hT
  have hST : (univ.filter fun π : Equiv.Perm (Fin 52) =>
      ∀ p q : Fin 52, p.val % 4 = r.val → q.val % 4 = r.val → p ≠ q →
        val (π p) ≠ val (π q)).card = T.card * (Nat.factorial 13 * Nat.factorial 39) := by
    rw [card_eq_sum_card_fiberwise (f := fun π : Equiv.Perm (Fin 52) => R.map π.toEmbedding)
      (t := T)]
    · rw [← smul_eq_mul, ← sum_const]
      apply sum_congr rfl
      intro B hB
      have hB' := mem_filter.1 hB
      have hBc := (mem_powersetCard.1 hB'.1).2
      have hK := card_fibre_preW B R (hRc.trans hBc.symm)
      rw [hBc] at hK
      rw [← hK]
      apply congrArg card
      ext π
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨-, hm⟩
        ext p
        simp only [preW, mem_filter, mem_univ, true_and]
        rw [← hm, mem_map_equiv]; simp
      · intro hp
        have hm : R.map π.toEmbedding = B := by
          ext c
          rw [mem_map_equiv, ← hp]; simp [preW]
        refine ⟨fun p q hpr hqr hpq => ?_, hm⟩
        have hpB : π p ∈ B := by rw [← hm, mem_map_equiv]; simpa [hR] using hpr
        have hqB : π q ∈ B := by rw [← hm, mem_map_equiv]; simpa [hR] using hqr
        exact hB'.2 _ hpB _ hqB (fun e => hpq (π.injective e))
    · intro π hπ
      simp only [mem_filter, mem_univ, true_and] at hπ
      simp only [hT, mem_filter, mem_powersetCard, subset_univ, true_and, card_map, hRc]
      intro a ha b hb hab
      rw [mem_map_equiv] at ha hb
      simp only [hR, mem_filter, mem_univ, true_and] at ha hb
      have := hπ _ _ ha hb (fun e => hab (π.symm.injective e))
      simpa using this
  rw [hST]
  have hc : Nat.choose 52 13 * Nat.factorial 13 * Nat.factorial 39 = Nat.factorial 52 :=
    Nat.choose_mul_factorial_mul_factorial (n := 52) (k := 13) (by norm_num)
  calc T.card * (Nat.factorial 13 * Nat.factorial 39) * Nat.choose 52 13
      = T.card * Nat.factorial 52 := by rw [← hc]; ring
    _ ≤ 4 ^ 13 * Nat.factorial 52 := Nat.mul_le_mul_right _ (card_transversals_le val)

/-! ## Numeric tables (PROOF.md §3 and §4)

`EA n` and `EB m` are the exact expectations of the pointwise bounds under the
hypergeometric law. The paper evaluates them in rational arithmetic
(`sumranks-dp-paper/alt_analytic_bigm_output.txt` and
`sumranks-dp-paper/caseB_analytic_output.txt`). Here each is shown equal to a
Nat-scaled convolution (Table A) or transfer matrix (Table B), and the resulting
inequalities are checked by kernel `decide!` (the largest takes about 1.5 s). -/

/-- Pointwise row bound `h(z)` (PROOF.md §3 (A2)): `1/(z+1)`, and `1` for a
    full row (`z = 13`). -/
def hA (z : ℕ) : ℚ := if z = 13 then 1 else 1 / (z + 1)

/-- `E_A(n)` (PROOF.md §3 (A2)). -/
def EA (n : ℕ) : ℚ :=
  (∑ z ∈ comps4 n, ∏ r, ((Nat.choose 13 (z r) : ℕ) : ℚ) * hA (z r)) /
    (Nat.choose 52 n : ℕ)


/-! ### Table A by kernel check

`f k = C(13,k)·h(k)` scaled by `D = 360360 = lcm(1,…,14)` is the integer `GA k`.
The 4-block sum is the coefficient of `Xⁿ` in `(Σ f k Xᵏ)⁴`, computed as a
convolution square of the 27-entry table `LA2` (checked against `GA`). -/

/-- Generating-function form of a 4-block sum: the coefficient of `Xⁿ` in
    `(Σ_{j<14} f j Xʲ)⁴`. -/
theorem sum_comps4_eq_coeff (f : ℕ → ℚ) (n : ℕ) :
    ∑ z ∈ comps4 n, ∏ r, f (z r) =
      ((∑ j ∈ range 14, Polynomial.C (f j) * Polynomial.X ^ j) ^ 4).coeff n := by
  rw [← Fin.prod_const, prod_univ_sum]
  simp only [prod_mul_distrib, prod_pow_eq_pow_sum, ← map_prod]
  rw [Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [comps4, sum_filter]
  apply sum_congr rfl; intro z _
  split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; omega)

/-- `360360 · C(13,k) · h(k)`. -/
def GA (k : ℕ) : ℕ :=
  [360360, 2342340, 9369360, 25765740, 51531480, 77297220, 88339680, 77297220, 51531480,
    25765740, 9369360, 2342340, 360360, 360360].getD k 0

/-- The convolution square of `GA` (entries `0 … 26`). -/
def LA2 : List ℕ :=
  [129859329600, 1688171284800, 12239241814800, 62462337537600, 245628921938400, 779935133577600,
    2055288247412400, 4573497177849600, 8693358614740800, 14227184086315200, 20155740179374800,
    24807194695483200, 26579155725064800, 24807454414142400, 20157428350659600, 14233936771454400,
    8711928498873600, 4610636946115200, 2110997899810800, 843603307747200, 301338574336800,
    99602105803200, 30809125947600, 8440856424000, 1818030614400, 259718659200, 129859329600]

theorem GA_eq_zero (k : ℕ) (hk : 14 ≤ k) : GA k = 0 :=
  List.getD_eq_default _ _ (by simp; omega)

theorem GA_spec (k : ℕ) :
    (if k ∈ range 14 then ((Nat.choose 13 k : ℕ) : ℚ) * hA k else 0) =
      (GA k : ℚ) / 360360 := by
  by_cases hk : k < 14
  · rw [if_pos (mem_range.2 hk)]
    interval_cases k <;> simp [GA, hA, Nat.choose] <;> norm_num
  · rw [if_neg (by simpa using hk), GA_eq_zero k (by omega)]; simp

theorem LA2_spec : ∀ n < 27, ∑ x ∈ antidiagonal n, GA x.1 * GA x.2 = LA2.getD n 0 := by
  decide!

theorem LA2_spec' (n : ℕ) : ∑ x ∈ antidiagonal n, GA x.1 * GA x.2 = LA2.getD n 0 := by
  by_cases hn : n < 27
  · exact LA2_spec n hn
  · rw [List.getD_eq_default _ _ (by simp [LA2]; omega)]
    apply sum_eq_zero
    intro x hx
    rw [mem_antidiagonal] at hx
    by_cases h1 : 14 ≤ x.1
    · rw [GA_eq_zero _ h1, zero_mul]
    · rw [GA_eq_zero x.2 (by omega), mul_zero]

theorem tableA_nat : ∀ n < 50, 13 ≤ n →
    100 * (∑ x ∈ antidiagonal n, LA2.getD x.1 0 * LA2.getD x.2 0) *
      (Nat.factorial n * Nat.factorial (52 - n)) ≤ 360360 ^ 4 * Nat.factorial 52 := by
  decide!

theorem EA_numer (n : ℕ) :
    (∑ z ∈ comps4 n, ∏ r, ((Nat.choose 13 (z r) : ℕ) : ℚ) * hA (z r)) =
      ((∑ x ∈ antidiagonal n, LA2.getD x.1 0 * LA2.getD x.2 0 : ℕ) : ℚ) / 360360 ^ 4 := by
  rw [sum_comps4_eq_coeff (fun k => ((Nat.choose 13 k : ℕ) : ℚ) * hA k)]
  set p :=
    ∑ j ∈ range 14, Polynomial.C (((Nat.choose 13 j : ℕ) : ℚ) * hA j) * Polynomial.X ^ j
  have hp : ∀ k, p.coeff k = (GA k : ℚ) / 360360 := by
    intro k
    rw [Polynomial.finset_sum_coeff]
    simp only [Polynomial.coeff_C_mul_X_pow]
    rw [sum_ite_eq]
    exact GA_spec k
  have hp2 : ∀ k, (p ^ 2).coeff k = (LA2.getD k 0 : ℚ) / 360360 ^ 2 := by
    intro k
    rw [pow_two, Polynomial.coeff_mul, ← LA2_spec' k]
    push_cast
    rw [sum_div]
    apply sum_congr rfl; intro x _
    rw [hp, hp]; ring
  rw [show p ^ 4 = p ^ 2 * p ^ 2 by ring, Polynomial.coeff_mul]
  push_cast
  rw [sum_div]
  apply sum_congr rfl; intro x _
  rw [hp2, hp2]; ring

/-- **Table A** (PROOF.md §3 (A2)): `E_A(n) ≤ 1/100` for `13 ≤ n ≤ 49`
    (exact values: `0.003975` at `n = 13`, decreasing then increasing, maximum
    `0.008416` at `n = 49`). -/
theorem EA_le (n : ℕ) (h1 : 13 ≤ n) (h2 : n ≤ 49) : EA n ≤ 1 / 100 := by
  have hn := tableA_nat n (by omega) h1
  have hc := Nat.choose_mul_factorial_mul_factorial (n := 52) (k := n) (by omega)
  have hpos : 0 < Nat.factorial n * Nat.factorial (52 - n) := by positivity
  set B := ∑ x ∈ antidiagonal n, LA2.getD x.1 0 * LA2.getD x.2 0
  have key : 100 * B ≤ 360360 ^ 4 * Nat.choose 52 n := by
    rw [← hc] at hn
    have : 100 * B * (Nat.factorial n * Nat.factorial (52 - n)) ≤
        360360 ^ 4 * Nat.choose 52 n * (Nat.factorial n * Nat.factorial (52 - n)) := by
      calc _ ≤ _ := hn
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_right this hpos
  unfold EA
  rw [EA_numer]
  have hC : (0 : ℚ) < (Nat.choose 52 n : ℕ) := by exact_mod_cast Nat.choose_pos (by omega)
  rw [div_div, div_le_div_iff₀ (by positivity) (by norm_num)]
  have : ((100 * B : ℕ) : ℚ) ≤ ((360360 ^ 4 * Nat.choose 52 n : ℕ) : ℚ) := by
    exact_mod_cast key
  push_cast at this
  linarith

/-- (A3) constant: `1/81 + 4 · 4¹³ / C(52,13) ≤ 1/64` (value `0.012768`). -/
theorem A3_const : (1 / 81 : ℚ) + 4 * 4 ^ 13 / (Nat.choose 52 13 : ℕ) ≤ 1 / 64 := by
  have : Nat.choose 52 13 = 635013559600 := by
    rw [Nat.choose_eq_factorial_div_factorial (by norm_num)]
    decide
  rw [this]
  norm_num

/-- Pointwise column bound `f(y, y')` (PROOF.md §4 Theorem B), with the Lean
    refinement `f(2, 0) = 1/4` (a `{x*,x*,a,a}` column is type P, `φ(P,0) = 0`;
    otherwise it is type U). The refinement makes the `m' = 2` case a table
    entry (`E_B(2) = 1/68`) instead of a separate argument. -/
def fB (y y' : ℕ) : ℚ :=
  match y with
  | 0 => if y' = 1 then 0 else 1
  | 1 => 1 / 4
  | 2 => if y' = 0 then 1 / 4 else 1 / 3
  | 3 => 1 / 2
  | _ => 1

/-- `E_B(m)` (PROOF.md §4 Theorem B); `j - 1` is the previous column (cyclic). -/
def EB (m : ℕ) : ℚ :=
  (∑ y ∈ comps13 m, ∏ j : Fin 13, ((Nat.choose 4 (y j) : ℕ) : ℚ) * fB (y (j - 1)) (y j)) /
    (Nat.choose 52 m : ℕ)

/-! ### Table B by kernel check

`E_B(m)` has a cyclic dependence between neighbouring columns, so its
numerator is the coefficient of `Xᵐ` in `tr(M(X)¹³)` with the 5×5 transfer
matrix `M(X)_{u,v} = 12·C(4,v)·f(u,v)·Xᵛ`. Instead of polynomials we evaluate
at `X = B = 10³⁰` in `ℕ` (every coefficient is below `tr(M(1)¹³) < B`) and read
the coefficients off as base-`B` digits. -/
/-- The path through `s`, the interior vertices `y`, and `t`. -/
def pathZ {q k : ℕ} (s : Fin q) (y : Fin k → Fin q) (t : Fin q) : Fin (k + 2) → Fin q :=
  Fin.cons s (Fin.snoc y t)

/-- Entries of a matrix power as sums over paths. -/
theorem pow_apply_paths {q : ℕ} (A : Matrix (Fin q) (Fin q) ℕ) (k : ℕ) (s t : Fin q) :
    (A ^ (k + 1)) s t = ∑ y : Fin k → Fin q,
      ∏ i : Fin (k + 1), A (pathZ s y t i.castSucc) (pathZ s y t i.succ) := by
  induction k generalizing s with
  | zero =>
    simp [pathZ, Fin.snoc]
  | succ k ih =>
    rw [pow_succ', Matrix.mul_apply]
    simp only [ih, mul_sum]
    rw [← Fintype.sum_equiv (Fin.consEquiv fun _ => Fin q) _ _ (fun _ => rfl),
      Fintype.sum_prod_type]
    apply sum_congr rfl; intro u _
    apply sum_congr rfl; intro y _
    have hz : pathZ s (Fin.consEquiv (fun _ => Fin q) (u, y)) t =
        Fin.cons s (pathZ u y t) := by
      simp only [pathZ, Fin.consEquiv, Equiv.coe_fn_mk, Fin.cons_snoc_eq_snoc_cons]
    rw [hz]
    symm
    rw [Fin.prod_univ_succ]
    congr 1

/-- `tr(A¹³)` is the sum over cyclic 13-sequences of the edge products. -/
theorem trace_pow13 {q : ℕ} (A : Matrix (Fin q) (Fin q) ℕ) :
    Matrix.trace (A ^ 13) = ∑ x : Fin 13 → Fin q, ∏ j : Fin 13, A (x (j - 1)) (x j) := by
  rw [Matrix.trace]
  simp only [Matrix.diag, pow_apply_paths A 12]
  rw [← Fintype.sum_equiv (Fin.consEquiv fun _ => Fin q) _ _ (fun _ => rfl),
    Fintype.sum_prod_type]
  apply sum_congr rfl; intro s _
  apply sum_congr rfl; intro y _
  set x := Fin.consEquiv (fun _ => Fin q) (s, y)
  have hx0 : x 0 = s := rfl
  have hz : pathZ s y s = Fin.snoc x (x 0) := by
    simp only [pathZ, hx0, x, Fin.consEquiv, Equiv.coe_fn_mk, Fin.cons_snoc_eq_snoc_cons,
      Fin.cons_zero]
  rw [hz]
  have hs : ∀ i : Fin 13, Fin.snoc (α := fun _ => Fin q) x (x 0) i.succ = x (i + 1) := by
    intro i
    refine Fin.lastCases ?_ (fun i' => ?_) i
    · rw [Fin.succ_last, Fin.snoc_last]; rfl
    · rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.coeSucc_eq_succ]
  simp only [Fin.snoc_castSucc, hs]
  exact Fintype.prod_equiv (Equiv.addRight 1) _ _ (fun i => by simp)

/-- Digit extraction: if every `S k < B`, the base-`B` digits of `Σ S k Bᵏ` are the `S k`. -/
theorem sum_lt_pow (S : ℕ → ℕ) (B : ℕ) (hS : ∀ k, S k < B) (m : ℕ) :
    ∑ k ∈ range m, S k * B ^ k < B ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, pow_succ]
    have := hS m
    nlinarith [Nat.pos_pow_of_pos m (show 0 < B by omega)]

theorem digit_sum (S : ℕ → ℕ) (B : ℕ) (hS : ∀ k, S k < B) (m r : ℕ) :
    (∑ k ∈ range (m + 1 + r), S k * B ^ k) / B ^ m % B = S m := by
  have hB : 0 < B := lt_of_le_of_lt (Nat.zero_le _) (hS 0)
  rw [show m + 1 + r = m + (1 + r) by ring, sum_range_add]
  have e : ∑ k ∈ range r, S (m + 1 + k) * B ^ (m + 1 + k) =
      B ^ m * (B * ∑ k ∈ range r, S (m + 1 + k) * B ^ k) := by
    rw [mul_sum, mul_sum]; apply sum_congr rfl; intro k _; ring
  have e2 : ∑ k ∈ range (1 + r), S (m + k) * B ^ (m + k) =
      B ^ m * (S m + B * ∑ k ∈ range r, S (m + 1 + k) * B ^ k) := by
    rw [add_comm 1 r, sum_range_succ']
    simp only [add_zero]
    rw [show ∑ k ∈ range r, S (m + (k + 1)) * B ^ (m + (k + 1)) =
      ∑ k ∈ range r, S (m + 1 + k) * B ^ (m + 1 + k) from
        sum_congr rfl fun k _ => by rw [show m + (k + 1) = m + 1 + k by ring], e]
    ring
  rw [e2, Nat.add_mul_div_left _ _ (Nat.pos_pow_of_pos m hB),
    Nat.div_eq_of_lt (sum_lt_pow S B hS m), zero_add, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (hS m)

/-- `12 · C(4,v) · f(u,v)` (all integers). -/
def aN : Fin 5 → Fin 5 → ℕ :=
  ![![12, 0, 72, 48, 12], ![3, 12, 18, 12, 3], ![3, 16, 24, 16, 4], ![6, 24, 36, 24, 6],
    ![12, 48, 72, 48, 12]]

theorem aN_spec : ∀ u v : Fin 5,
    ((aN u v : ℕ) : ℚ) = 12 * (((Nat.choose 4 v.val : ℕ) : ℚ) * fB u.val v.val) := by
  intro u v
  fin_cases u <;> fin_cases v <;> simp [aN, fB, Nat.choose] <;> norm_num

/-- Size `Σ_j x_j` of a column-count vector with entries in `Fin 5`. -/
def sz (x : Fin 13 → Fin 5) : ℕ := ∑ j, (x j).val

theorem sz_le (x : Fin 13 → Fin 5) : sz x ≤ 52 := by
  have : sz x ≤ ∑ _j : Fin 13, 4 := sum_le_sum fun j _ => Nat.lt_succ_iff.1 (x j).isLt
  simpa using this

/-- Scaled numerator of `E_B(m)`. -/
def SB (m : ℕ) : ℕ :=
  ∑ x ∈ univ.filter (fun x : Fin 13 → Fin 5 => sz x = m), ∏ j : Fin 13, aN (x (j - 1)) (x j)

/-- The transfer-matrix trace with the size tracked in base `B`. -/
def TB (B : ℕ) : ℕ := Matrix.trace (Matrix.of (fun u v : Fin 5 => aN u v * B ^ v.val) ^ 13)

theorem TB_eq (B : ℕ) : TB B = ∑ m ∈ range 53, SB m * B ^ m := by
  rw [TB, trace_pow13]
  simp only [Matrix.of_apply, prod_mul_distrib, prod_pow_eq_pow_sum]
  rw [← sum_fiberwise_of_maps_to (g := sz) (t := range 53)
    (fun x _ => mem_range.2 (Nat.lt_succ_of_le (sz_le x)))]
  apply sum_congr rfl; intro m _
  rw [SB, sum_mul]
  apply sum_congr rfl; intro x hx
  rw [(mem_filter.1 hx).2.symm]; rfl

theorem SB_le (m : ℕ) : SB m ≤ TB 1 := by
  rw [TB, trace_pow13]
  simp only [Matrix.of_apply, one_pow, mul_one]
  exact sum_le_sum_of_subset (subset_univ _)

theorem TB1_lt : TB 1 < 10 ^ 30 := by decide!

theorem tableB_nat : ∀ m < 40, 2 ≤ m → 64 * (TB (10 ^ 30) / (10 ^ 30) ^ m % 10 ^ 30) *
    (Nat.factorial m * Nat.factorial (52 - m)) ≤ 12 ^ 13 * Nat.factorial 52 := by decide!

theorem SB_digit (m : ℕ) (hm : m < 53) : TB (10 ^ 30) / (10 ^ 30) ^ m % 10 ^ 30 = SB m := by
  obtain ⟨r, hr⟩ : ∃ r, 53 = m + 1 + r := ⟨52 - m, by omega⟩
  rw [TB_eq, hr]
  exact digit_sum SB _ (fun k => (SB_le k).trans_lt TB1_lt) m r

theorem EB_numer (m : ℕ) :
    (∑ y ∈ comps13 m, ∏ j : Fin 13,
        ((Nat.choose 4 (y j) : ℕ) : ℚ) * fB (y (j - 1)) (y j)) =
      (SB m : ℚ) / 12 ^ 13 := by
  rw [SB, Nat.cast_sum, sum_div]
  symm
  apply sum_nbij' (fun x j => (x j).val)
    (fun y j => (⟨y j % 5, Nat.mod_lt _ (by norm_num)⟩ : Fin 5))
  · intro x hx
    simp only [coe_filter, mem_filter, mem_univ, true_and, Set.mem_setOf_eq, comps13,
      Fintype.mem_piFinset, mem_range, mem_coe] at hx ⊢
    exact ⟨fun j => (x j).isLt, hx⟩
  · intro y hy
    simp only [coe_filter, mem_filter, mem_univ, true_and, Set.mem_setOf_eq, comps13,
      Fintype.mem_piFinset, mem_range, mem_coe] at hy ⊢
    rw [sz]; simp only
    rw [← hy.2]; apply sum_congr rfl; intro j _; exact Nat.mod_eq_of_lt (hy.1 j)
  · intro x _; funext j; apply Fin.ext; simp only; exact Nat.mod_eq_of_lt (x j).isLt
  · intro y hy
    simp only [coe_filter, mem_filter, comps13, Fintype.mem_piFinset, mem_range, mem_coe] at hy
    funext j; exact Nat.mod_eq_of_lt (hy.1 j)
  · intro x _
    push_cast
    simp only [aN_spec, prod_mul_distrib, prod_const, card_univ, Fintype.card_fin]
    field_simp

/-- **Table B** (PROOF.md §4 Theorem B): `E_B(m) ≤ 1/64` for `2 ≤ m ≤ 39`. The
    paper's sharper value is `1/425` for `m ≥ 3` (transfer matrix); `E_B(2) = 1/68`
    with the `f(2,0)` refinement. Needs a transfer-matrix reformulation: the sum
    has `5¹³` terms. -/
theorem EB_le (m : ℕ) (h1 : 2 ≤ m) (h2 : m ≤ 39) : EB m ≤ 1 / 64 := by
  have hn := tableB_nat m (by omega) h1
  rw [SB_digit m (by omega)] at hn
  have hc := Nat.choose_mul_factorial_mul_factorial (n := 52) (k := m) (by omega)
  have hpos : 0 < Nat.factorial m * Nat.factorial (52 - m) := by positivity
  have key : 64 * SB m ≤ 12 ^ 13 * Nat.choose 52 m := by
    rw [← hc] at hn
    have : 64 * SB m * (Nat.factorial m * Nat.factorial (52 - m)) ≤
        12 ^ 13 * Nat.choose 52 m * (Nat.factorial m * Nat.factorial (52 - m)) := by
      calc _ ≤ _ := hn
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_right this hpos
  unfold EB
  rw [EB_numer]
  have hC : (0 : ℚ) < (Nat.choose 52 m : ℕ) := by exact_mod_cast Nat.choose_pos (by omega)
  rw [div_div, div_le_div_iff₀ (by positivity) (by norm_num)]
  have : ((64 * SB m : ℕ) : ℚ) ≤ ((12 ^ 13 * Nat.choose 52 m : ℕ) : ℚ) := by
    exact_mod_cast key
  push_cast at this
  linarith

/-! ## §4 One column: GF(4) labels (Lemma 4)

Labels are `Fin 4` with `0 = ♣`, `1 = ♦`, `2 = w = ♥`, `3 = w² = ♠`; addition is
XOR, `w·` is `1 → 2 → 3 → 1`. -/

/-- GF(4) addition (XOR of two-bit labels); same formula as `DoubleDeal.gfAdd`. -/
def x4 (a b : Fin 4) : Fin 4 :=
  ⟨(a.val % 2 + b.val % 2) % 2 + 2 * ((a.val / 2 + b.val / 2) % 2), by omega⟩

/-- Multiplication by `w`; same formula as `DoubleDeal.gfTimesW`. -/
def w4 (a : Fin 4) : Fin 4 := if a = 0 then 0 else ⟨a.val % 3 + 1, by omega⟩

/-- `V(e) = e₁ + w e₂ + w² e₃`. -/
def vLab (e : Fin 4 → Fin 4) : Fin 4 := x4 (x4 (e 1) (w4 (e 2))) (w4 (w4 (e 3)))

/-- `Σ(e) = e₀ + e₁ + e₂ + e₃`. -/
def sLab (e : Fin 4 → Fin 4) : Fin 4 := x4 (x4 (x4 (e 0) (e 1)) (e 2)) (e 3)

/-- Number of entries different from `xs`. -/
def offCount (e : Fin 4 → Fin 4) (xs : Fin 4) : ℕ := (univ.filter fun i => e i ≠ xs).card

/-- The 24 permutations of `Fin 4`, as functions (for a cheap kernel check). -/
def perms4 : List (Fin 4 → Fin 4) :=
  [![0,1,2,3], ![0,1,3,2], ![0,2,1,3], ![0,2,3,1], ![0,3,1,2], ![0,3,2,1],
   ![1,0,2,3], ![1,0,3,2], ![1,2,0,3], ![1,2,3,0], ![1,3,0,2], ![1,3,2,0],
   ![2,0,1,3], ![2,0,3,1], ![2,1,0,3], ![2,1,3,0], ![2,3,0,1], ![2,3,1,0],
   ![3,0,1,2], ![3,0,2,1], ![3,1,0,2], ![3,1,2,0], ![3,2,0,1], ![3,2,1,0]]

theorem perms4_eq : (univ : Finset (Equiv.Perm (Fin 4))).map
    ⟨fun σ : Equiv.Perm (Fin 4) => (σ : Fin 4 → Fin 4), DFunLike.coe_injective⟩ =
      perms4.toFinset := by decide!

theorem perms4_nodup : perms4.Nodup := by decide

theorem card_perm4_filter (P : (Fin 4 → Fin 4) → Prop) [DecidablePred P] :
    (univ.filter fun σ : Equiv.Perm (Fin 4) => P σ).card =
      (perms4.filter fun f => P f).length := by
  have h1 : (univ.filter fun σ : Equiv.Perm (Fin 4) => P σ).card =
      (((univ : Finset (Equiv.Perm (Fin 4))).map
        ⟨fun σ : Equiv.Perm (Fin 4) => (σ : Fin 4 → Fin 4),
          DFunLike.coe_injective⟩).filter P).card := by
    rw [filter_map, card_map]; rfl
  rw [h1, perms4_eq, ← List.toFinset_card_of_nodup (perms4_nodup.filter _)]
  congr 1; ext f; simp

/-- Count of orders hitting target `t`. -/
def cnt4 (e : Fin 4 → Fin 4) (t : Fin 4) : ℕ :=
  (univ.filter fun σ : Equiv.Perm (Fin 4) => vLab (e ∘ σ) = t).card

theorem cnt4_comp_perm (e : Fin 4 → Fin 4) (τ : Equiv.Perm (Fin 4)) (t : Fin 4) :
    cnt4 (e ∘ τ) t = cnt4 e t := by
  unfold cnt4
  apply card_nbij' (fun σ => τ * σ) (fun σ => τ⁻¹ * σ)
  · intro σ hσ
    simp only [coe_filter, mem_filter, mem_univ, true_and, Set.mem_setOf_eq] at hσ ⊢
    rw [← hσ]; rfl
  · intro σ hσ
    simp only [coe_filter, mem_filter, mem_univ, true_and, Set.mem_setOf_eq] at hσ ⊢
    rw [← hσ]; congr 1; funext i; simp
  · intro σ _; simp
  · intro σ _; simp

theorem offCount_comp_perm (e : Fin 4 → Fin 4) (τ : Equiv.Perm (Fin 4)) (xs : Fin 4) :
    offCount (e ∘ τ) xs = offCount e xs := by
  unfold offCount
  apply card_nbij' (fun i => τ i) (fun i => τ⁻¹ i)
  · intro i hi; simpa using hi
  · intro i hi; simpa using hi
  · intro i _; simp
  · intro i _; simp

theorem vLab_shift : ∀ a b c x : Fin 4,
    x4 (x4 (x4 a x) (w4 (x4 b x))) (w4 (w4 (x4 c x))) = x4 (x4 a (w4 b)) (w4 (w4 c)) := by
  decide

theorem cnt4_shift (e : Fin 4 → Fin 4) (x t : Fin 4) :
    cnt4 (fun i => x4 (e i) x) t = cnt4 e t := by
  unfold cnt4
  apply congrArg card; apply filter_congr; intro σ _
  simp only [vLab, Function.comp_apply, vLab_shift]

theorem x4_ne_iff : ∀ a x : Fin 4, x4 a x ≠ 0 ↔ a ≠ x := by decide

theorem offCount_shift (e : Fin 4 → Fin 4) (x : Fin 4) :
    offCount (fun i => x4 (e i) x) 0 = offCount e x := by
  unfold offCount
  apply congrArg card; apply filter_congr; intro i _
  exact x4_ne_iff _ _

/-- The finite check behind Lemma 4, on sorted shifted columns (35 · 4 cases). -/
theorem lemma4_core : ∀ a b c d t : Fin 4, a ≤ b → b ≤ c → c ≤ d →
    (offCount ![a, b, c, d] 0 = 0 → t ≠ 0 →
      (perms4.filter fun f => vLab (![a, b, c, d] ∘ f) = t).length = 0) ∧
    (offCount ![a, b, c, d] 0 = 1 →
      (perms4.filter fun f => vLab (![a, b, c, d] ∘ f) = t).length ≤ 6) ∧
    (offCount ![a, b, c, d] 0 = 2 →
      (perms4.filter fun f => vLab (![a, b, c, d] ∘ f) = t).length ≤ 8) ∧
    (offCount ![a, b, c, d] 0 = 2 → t = 0 →
      (perms4.filter fun f => vLab (![a, b, c, d] ∘ f) = t).length ≤ 6) ∧
    (offCount ![a, b, c, d] 0 = 3 →
      (perms4.filter fun f => vLab (![a, b, c, d] ∘ f) = t).length ≤ 12) := by
  decide!

/-- **Lemma 4 as used** (PROOF.md §4): the probability over the 24 orders that
    `V` hits the target `t` is at most `f(y, y')`, where `y` is the column's off
    count and the next column's off count `y'` constrains the target through
    `sLab_of_offCount_zero` / `sLab_of_offCount_one`. A finite check
    (256 · 4 · 4 label cases × 24 orders); if kernel `decide` is too slow, first
    prove that the count depends only on the multiset of `e` (35 cases). -/
theorem lemma4_count_le (e : Fin 4 → Fin 4) (xs t : Fin 4) (y' : ℕ)
    (h0 : y' = 0 → t = 0) (h1 : y' = 1 → t ≠ 0) :
    ((univ.filter fun σ : Equiv.Perm (Fin 4) => vLab (e ∘ σ) = t).card : ℚ) / 24 ≤
      fB (offCount e xs) y' := by
  set d : Fin 4 → Fin 4 := fun i => x4 (e i) xs
  set s := Tuple.sort d
  have hm := Tuple.monotone_sort d
  set d' := d ∘ s
  have hN : (univ.filter fun σ : Equiv.Perm (Fin 4) => vLab (e ∘ σ) = t).card =
      (perms4.filter fun f => vLab (![d' 0, d' 1, d' 2, d' 3] ∘ f) = t).length := by
    have h2 : ![d' 0, d' 1, d' 2, d' 3] = d' := by
      funext i; fin_cases i <;> rfl
    rw [h2, ← card_perm4_filter]
    change cnt4 e t = cnt4 (d ∘ s) t
    rw [cnt4_comp_perm, cnt4_shift]
  have hO : offCount e xs = offCount ![d' 0, d' 1, d' 2, d' 3] 0 := by
    have h2 : ![d' 0, d' 1, d' 2, d' 3] = d' := by
      funext i; fin_cases i <;> rfl
    rw [h2, offCount_comp_perm, offCount_shift]
  have hc := lemma4_core (d' 0) (d' 1) (d' 2) (d' 3) t (hm (by decide)) (hm (by decide))
    (hm (by decide))
  rw [hN, hO]
  set N := (perms4.filter fun f => vLab (![d' 0, d' 1, d' 2, d' 3] ∘ f) = t).length
  set y := offCount ![d' 0, d' 1, d' 2, d' 3] 0
  have hN24 : N ≤ 24 := (List.length_filter_le _ _).trans (by rfl)
  have hy4 : y ≤ 4 := (card_le_univ _).trans (by simp)
  have hN24q : (N : ℚ) ≤ 24 := by exact_mod_cast hN24
  obtain ⟨c0, c1, c2, c2', c3⟩ := hc
  interval_cases y
  · simp only [fB]
    split_ifs with hy
    · rw [c0 rfl (h1 hy)]; norm_num
    · linarith
  · have : (N : ℚ) ≤ 6 := by exact_mod_cast c1 rfl
    simp only [fB]; linarith
  · simp only [fB]
    split_ifs with hy
    · have : (N : ℚ) ≤ 6 := by exact_mod_cast c2' rfl (h0 hy)
      linarith
    · have : (N : ℚ) ≤ 8 := by exact_mod_cast c2 rfl
      linarith
  · have : (N : ℚ) ≤ 12 := by exact_mod_cast c3 rfl
    simp only [fB]; linarith
  · simp only [fB]; linarith

/-- A column with no off entries has `Σ = 0` (`4 x = 0` in characteristic 2). -/
theorem sLab_of_offCount_zero (e : Fin 4 → Fin 4) (xs : Fin 4) (h : offCount e xs = 0) :
    sLab e = 0 := by
  have he : e = fun _ => xs := by
    funext i
    by_contra hi
    have : i ∈ univ.filter fun i => e i ≠ xs := by simp [hi]
    rw [offCount, card_eq_zero] at h
    simp [h] at this
  subst he
  revert xs; decide

/-- A column with exactly one off entry has `Σ ≠ 0` (`3 x + a = x + a ≠ 0`). -/
theorem sLab_of_offCount_one (e : Fin 4 → Fin 4) (xs : Fin 4) (h : offCount e xs = 1) :
    sLab e ≠ 0 := by
  obtain ⟨i, hi⟩ := card_eq_one.1 h
  have hei : e i ≠ xs := by
    have : i ∈ univ.filter fun i => e i ≠ xs := by rw [hi]; exact mem_singleton_self i
    simpa using this
  have he : e = Function.update (fun _ => xs) i (e i) := by
    funext k
    by_cases hk : k = i
    · subst hk; simp
    · rw [Function.update_noteq hk]
      by_contra hne
      have : k ∈ univ.filter fun i => e i ≠ xs := by simp [hne]
      rw [hi, mem_singleton] at this
      exact hk this
  rw [he]
  have key : ∀ (xs a : Fin 4) (i : Fin 4), a ≠ xs →
      sLab (Function.update (fun _ => xs) i a) ≠ 0 := by decide
  exact key xs (e i) i hei

/-- `x4` can be solved for its first argument (used for the symmetry case (0.1)). -/
theorem x4_solve : ∀ a b x : Fin 4, x4 a b = x → a = x4 x b := by decide

end SRDP
