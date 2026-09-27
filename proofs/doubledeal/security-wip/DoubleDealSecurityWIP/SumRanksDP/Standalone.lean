/-
  WIP (not built by CI): v10 SumRanks survival bound, the self-contained part.

  Mathlib-only lemmas with no repository definitions: the one-row lemma
  (Lemma 2), the GF(4) column table (Lemma 4), a generic fibre bound, the two
  hypergeometric counting identities, and the numeric tables. Section numbers
  refer to PROOF.md of the paper proof (`docs/sumranks-dp/PROOF.md` once it is
  copied into the repo; currently in the working notes).

  Every lemma here is stated so that it can be proved in isolation: it only
  needs `import Mathlib` and the definitions in this file.
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
      ((σ⁻¹ i₀).val : ZMod 13) * (w k - w i₀) + ((σ⁻¹ k).val : ZMod 13) * (w i₀ - w k) := by
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
  have hcast : ∀ a b : Fin 13, ((a.val : ℕ) : ZMod 13) = (b.val : ZMod 13) → a = b := by decide
  have hVw : ∀ k ∈ V, w k = v := fun k hk => (mem_filter.1 hk).2
  have hVne : ∀ k ∈ V, k ≠ i₀ := fun k hk e => hi₀ (by rw [← e]; exact hVw k hk)
  have huniq : ∀ (σ' : Equiv.Perm (Fin 13)) k₁ k₂, k₁ ∈ V → k₂ ∈ V →
      wS w (Equiv.swap i₀ k₁ * σ') = c → wS w (Equiv.swap i₀ k₂ * σ') = c → k₁ = k₂ := by
    intro σ' k₁ k₂ h1 h2 e1 e2
    rw [wS_swap w v i₀ k₁ (hVne k₁ h1) (hVw k₁ h1)] at e1
    rw [wS_swap w v i₀ k₂ (hVne k₂ h2) (hVw k₂ h2)] at e2
    have : (w i₀ - v) * ((σ'⁻¹ k₁).val : ZMod 13) = (w i₀ - v) * ((σ'⁻¹ k₂).val : ZMod 13) := by
      linear_combination e1 - e2
    exact σ'⁻¹.injective (hcast _ _ (mul_left_cancel₀ hd this))
  have hinj : (G ×ˢ V).card ≤ B.card := by
    apply card_le_card_of_injOn (fun x => Equiv.swap i₀ x.2 * x.1)
    · intro x hx
      simp only [hG, hV, hB, coe_product, coe_filter, Set.mem_prod, Set.mem_setOf_eq, mem_coe,
        mem_product, mem_filter, mem_univ, true_and] at hx ⊢
      rw [wS_swap w v i₀ x.2 (hVne x.2 (by simp [hV, hx.2])) hx.2, hx.1]
      intro e
      have h0 : (w i₀ - v) * (((x.1⁻¹ x.2).val : ZMod 13) - ((x.1⁻¹ i₀).val : ZMod 13)) = 0 := by
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
    (hw : ∀ i, i ≠ i₁ → i ≠ i₂ → w i = v) (σ : Equiv.Perm (Fin 13)) : wS w σ ≠ 0 := by
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
    have hScard : S.card = 51 := by have := card_compl S; simp only [Fintype.card_fin] at this; omega
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
theorem exists_class_ge_13 (f : Fin 52 → Fin 4) : ∃ x, 13 ≤ (univ.filter fun c => f c = x).card := by
  by_contra h
  push_neg at h
  have hsum := Finset.card_eq_sum_card_fiberwise (s := (univ : Finset (Fin 52))) (t := (univ : Finset (Fin 4))) (f := f) (fun _ _ => mem_univ _)
  have hle : ∑ x : Fin 4, (univ.filter fun c => f c = x).card ≤ ∑ _x : Fin 4, 12 :=
    Finset.sum_le_sum fun x _ => Nat.lt_succ_iff.mp (h x)
  simp only [card_univ, Fintype.card_fin, sum_const, smul_eq_mul] at hsum hle
  omega

/-! ## Generic fibre bound (PROOF.md §2 Lemma 3 and §4 Lemma 5: "nest the sums") -/

/-- Two-level fibre bound: if at most `m` first coordinates pass `P`, and for
    each of them at most `n` second coordinates pass `Q a`, then at most `m * n`
    pairs pass. Iterating it gives the row chain (4 levels) and the column chain
    (13 levels). -/
theorem card_filter_product_le {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (t : Finset β) (P : α → Prop) [DecidablePred P]
    (Q : α → β → Prop) [∀ a, DecidablePred (Q a)] (m n : ℕ)
    (hP : (s.filter P).card ≤ m) (hQ : ∀ a ∈ s, P a → (t.filter (Q a)).card ≤ n) :
    ((s ×ˢ t).filter fun p => P p.1 ∧ Q p.1 p.2).card ≤ m * n := by
  have h1 := card_le_mul_card_image_of_maps_to (s := (s ×ˢ t).filter fun p => P p.1 ∧ Q p.1 p.2)
    (t := s.filter P) (f := Prod.fst) (by
      intro p hp
      simp only [mem_filter, mem_product] at hp ⊢
      exact ⟨hp.1.1, hp.2.1⟩) n (by
      intro a ha
      simp only [mem_filter] at ha
      calc (((s ×ˢ t).filter fun p => P p.1 ∧ Q p.1 p.2).filter fun p => p.1 = a).card
          ≤ (t.filter (Q a)).card := by
            apply card_le_card_of_injOn Prod.snd
            · intro p hp
              simp only [coe_filter, mem_filter, mem_product, Set.mem_setOf_eq] at hp
              simp only [coe_filter, Set.mem_setOf_eq, mem_filter]
              obtain ⟨⟨⟨_, ht⟩, _, hq⟩, rfl⟩ := hp
              exact ⟨ht, hq⟩
            · intro p hp q hq e
              simp only [coe_filter, mem_filter, Set.mem_setOf_eq] at hp hq
              exact Prod.ext (hp.2.trans hq.2.symm) e
        _ ≤ n := hQ a ha.1 ha.2)
  calc _ ≤ n * (s.filter P).card := h1
    _ ≤ n * m := Nat.mul_le_mul_left _ hP
    _ = m * n := Nat.mul_comm _ _

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

/-- **Multivariate hypergeometric law, rows** (PROOF.md §3 (A2)): the number of
    decks with row counts `z` is `Π_r C(13, z_r) · n! · (52 − n)!`. -/
theorem hyper_rows (W : Finset (Fin 52)) (F : (Fin 4 → ℕ) → ℚ) :
    ∑ π : Equiv.Perm (Fin 52), F (zRow W π) =
      ∑ z ∈ comps4 W.card, (∏ r, ((Nat.choose 13 (z r) : ℕ) : ℚ)) *
        (W.card.factorial * (52 - W.card).factorial : ℕ) * F z := by
  sorry

/-- **Multivariate hypergeometric law, columns** (PROOF.md §4 Theorem B). -/
theorem hyper_cols (W : Finset (Fin 52)) (F : (Fin 13 → ℕ) → ℚ) :
    ∑ π : Equiv.Perm (Fin 52), F (yCol W π) =
      ∑ y ∈ comps13 W.card, (∏ j, ((Nat.choose 4 (y j) : ℕ) : ℚ)) *
        (W.card.factorial * (52 - W.card).factorial : ℕ) * F y := by
  sorry

/-- Rows with no repeated value (PROOF.md §3 (A3)): if the 52 cards carry
    values `val : Fin 52 → ZMod 13`, the decks whose row `r` holds 13 distinct
    values number `13! · 39! · Π_v n_v ≤ 4¹³ · 52! / C(52,13)` (AM–GM on
    `Σ n_v = 52`). -/
theorem distinct_row_count (val : Fin 52 → ZMod 13) (r : Fin 4) :
    (univ.filter fun π : Equiv.Perm (Fin 52) =>
        ∀ p q : Fin 52, p.val % 4 = r.val → q.val % 4 = r.val → p ≠ q →
          val (π p) ≠ val (π q)).card * Nat.choose 52 13 ≤ 4 ^ 13 * Nat.factorial 52 := by
  sorry

/-! ## Numeric tables (PROOF.md §3 and §4)

`EA n` and `EB m` are the exact expectations of the pointwise bounds under the
hypergeometric law. The paper evaluates them in rational arithmetic
(`alt_analytic_bigm_output.txt`, `caseB_analytic_output.txt`). In Lean they
should be proved by kernel `decide` on a Nat-scaled convolution / transfer
matrix that is first shown equal to these sums; if that takes more than a few
seconds it belongs in the heavy target (`DoubleDealSecurityHeavy`), never in the
default build. -/

/-- Pointwise row bound `h(z)` (PROOF.md §3 (A2)): `1/(z+1)`, and `1` for a
    full row (`z = 13`). -/
def hA (z : ℕ) : ℚ := if z = 13 then 1 else 1 / (z + 1)

/-- `E_A(n)` (PROOF.md §3 (A2)). -/
def EA (n : ℕ) : ℚ :=
  (∑ z ∈ comps4 n, ∏ r, ((Nat.choose 13 (z r) : ℕ) : ℚ) * hA (z r)) / (Nat.choose 52 n : ℕ)

/-- **Table A** (PROOF.md §3 (A2)): `E_A(n) ≤ 1/100` for `13 ≤ n ≤ 49`
    (exact values: `0.003975` at `n = 13`, decreasing then increasing, maximum
    `0.008416` at `n = 49`). -/
theorem EA_le (n : ℕ) (h1 : 13 ≤ n) (h2 : n ≤ 49) : EA n ≤ 1 / 100 := by
  sorry

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

/-- **Table B** (PROOF.md §4 Theorem B): `E_B(m) ≤ 1/64` for `2 ≤ m ≤ 39`. The
    paper's sharper value is `1/425` for `m ≥ 3` (transfer matrix); `E_B(2) = 1/68`
    with the `f(2,0)` refinement. Needs a transfer-matrix reformulation: the sum
    has `5¹³` terms. -/
theorem EB_le (m : ℕ) (h1 : 2 ≤ m) (h2 : m ≤ 39) : EB m ≤ 1 / 64 := by
  sorry

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
  sorry

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
