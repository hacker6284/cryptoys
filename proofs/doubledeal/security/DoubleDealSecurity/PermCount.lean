/-
  Counting permutations by a statistic, for every finite type (no cipher content).

  The whole counting argument used by `SumRanksDP/ThreeCycle.lean` (arrangements of
  `Fin 13`) and `GridCycleSurvival.lean` (decks, `Fin 52`, one and three positions):
  * `exists_perm_two`, `exists_perm_three` (in `PermWitness.lean`, same namespace): a
    permutation with prescribed images of two / three distinct points;
  * `card_fibre_eq_of_mul`: left multiplication by `ρ` moves one fibre of a statistic
    onto another, so the two are equinumerous;
  * `card_filter_comp_eq`: if every fibre over the range `S` has `F` elements, then
    `#{π | P (f π)} = #{t ∈ S | P t} · F`;
  * `card_distinct_triples_eq`: `n · (n - 1) · (n - 2)` ordered distinct triples;
  * `fibre3_card_eq`: the fibres of `σ ↦ (σ i₀, σ i₁, σ i₂)` over distinct triples are
    equinumerous;
  * `count_triples_of`: counting by the images of three distinct points.
-/
import DoubleDealSecurity.PermWitness
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.FinCases

namespace DoubleDeal.Security.PermCount

open Finset

/-- Left multiplication by `ρ` is a bijection from the fibre of `f` over `s` onto the
    fibre over `t` when `f (ρ * π) = t ↔ f π = s`; so the two fibres are equinumerous. -/
theorem card_fibre_eq_of_mul {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]
    (f : Equiv.Perm α → β) (ρ : Equiv.Perm α) (s t : β) (h : ∀ π, f (ρ * π) = t ↔ f π = s) :
    (univ.filter fun π => f π = t).card = (univ.filter fun π => f π = s).card := by
  apply card_nbij' (fun π => ρ⁻¹ * π) (fun π => ρ * π)
  · intro π hπ
    simp only [coe_filter, Set.mem_setOf_eq, mem_filter, mem_univ, true_and, mem_coe] at hπ ⊢
    rw [← h, mul_inv_cancel_left]
    exact hπ
  · intro π hπ
    simp only [coe_filter, Set.mem_setOf_eq, mem_filter, mem_univ, true_and, mem_coe] at hπ ⊢
    exact (h π).2 hπ
  · intro π _; simp only [mul_inv_cancel_left]
  · intro π _; simp only [inv_mul_cancel_left]

/-- The counting argument: if the statistic `f` takes values in `S` and every fibre
    over `S` has `F` elements, then `#{π | P (f π)} = #{t ∈ S | P t} · F`. -/
theorem card_filter_comp_eq {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]
    (f : Equiv.Perm α → β) (S : Finset β) (hS : ∀ π, f π ∈ S) (F : ℕ)
    (hF : ∀ t ∈ S, (univ.filter fun π => f π = t).card = F)
    (P : β → Prop) [DecidablePred P] :
    (univ.filter fun π => P (f π)).card = (S.filter P).card * F := by
  rw [card_eq_sum_card_fiberwise (f := f) (t := S.filter P)
    (fun π hπ => by
      simp only [mem_filter, mem_univ, true_and] at hπ ⊢
      exact ⟨hS π, hπ⟩)]
  rw [← smul_eq_mul, ← sum_const]
  apply sum_congr rfl
  intro t ht
  simp only [mem_filter] at ht
  rw [filter_filter, ← hF t ht.1]
  congr 1
  apply filter_congr
  intro π _
  constructor
  · exact fun h => h.2
  · intro h; exact ⟨by rw [h]; exact ht.2, h⟩

/-- `(Fintype.card α)·(… - 1)·(… - 2)` ordered triples of distinct elements. -/
theorem card_distinct_triples_eq (α : Type*) [Fintype α] [DecidableEq α] :
    (univ.filter fun t : α × α × α => t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2).card =
      (Fintype.card α).descFactorial 3 := by
  have he := Fintype.card_embedding_eq (α := Fin 3) (β := α)
  rw [Fintype.card_fin] at he
  rw [← he, ← Fintype.card_subtype]
  refine Fintype.card_congr
    { toFun := fun t => ⟨![t.1.1, t.1.2.1, t.1.2.2], ?_⟩
      invFun := fun e => ⟨(e 0, e 1, e 2), e.injective.ne (by decide),
        e.injective.ne (by decide), e.injective.ne (by decide)⟩
      left_inv := fun t => rfl
      right_inv := fun e => by
        ext i
        fin_cases i <;> rfl }
  obtain ⟨⟨a, b, c⟩, hab, hac, hbc⟩ := t
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [eq_comm, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]

/-- The fibres of `σ ↦ (σ i₀, σ i₁, σ i₂)` over any two distinct triples have the same
    size (every finite type; the positions need not be distinct). -/
theorem fibre3_card_eq {α : Type*} [Fintype α] [DecidableEq α] (i0 i1 i2 : α)
    (s t : α × α × α) (hs : s.1 ≠ s.2.1 ∧ s.1 ≠ s.2.2 ∧ s.2.1 ≠ s.2.2)
    (ht : t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2) :
    (univ.filter fun σ : Equiv.Perm α => (σ i0, σ i1, σ i2) = t).card =
      (univ.filter fun σ : Equiv.Perm α => (σ i0, σ i1, σ i2) = s).card := by
  obtain ⟨s0, s1, s2⟩ := s
  obtain ⟨t0, t1, t2⟩ := t
  dsimp only at hs ht
  obtain ⟨ρ, h0, h1, h2⟩ :=
    exists_perm_three s0 s1 s2 t0 t1 t2 hs.1 hs.2.1 hs.2.2 ht.1 ht.2.1 ht.2.2
  apply card_fibre_eq_of_mul (fun σ : Equiv.Perm α => (σ i0, σ i1, σ i2)) ρ
  intro π
  simp only [Equiv.Perm.mul_apply, Prod.mk.injEq]
  rw [← h0, ← h1, ← h2, ρ.injective.eq_iff, ρ.injective.eq_iff, ρ.injective.eq_iff]

/-- Counting arrangements of any finite type by the images of three distinct points:
    `#{σ | P (σ i₀, σ i₁, σ i₂)} = #{distinct t | P t} · #(fibre over s)`. -/
theorem count_triples_of {α : Type*} [Fintype α] [DecidableEq α] (i0 i1 i2 : α)
    (h01 : i0 ≠ i1) (h02 : i0 ≠ i2) (h12 : i1 ≠ i2) (s : α × α × α)
    (hs : s.1 ≠ s.2.1 ∧ s.1 ≠ s.2.2 ∧ s.2.1 ≠ s.2.2)
    (P : α × α × α → Prop) [DecidablePred P] :
    (univ.filter fun σ : Equiv.Perm α => P (σ i0, σ i1, σ i2)).card =
      (univ.filter fun t : α × α × α =>
          t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 ∧ P t).card *
        (univ.filter fun σ : Equiv.Perm α => (σ i0, σ i1, σ i2) = s).card := by
  rw [card_filter_comp_eq (fun σ : Equiv.Perm α => (σ i0, σ i1, σ i2))
    (univ.filter fun t : α × α × α => t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2)
    (fun σ => by
      simp only [mem_filter, mem_univ, true_and]
      exact ⟨fun e => h01 (σ.injective e), fun e => h02 (σ.injective e),
        fun e => h12 (σ.injective e)⟩)
    _ (fun t ht => fibre3_card_eq i0 i1 i2 s t hs (by simpa using ht)) P, filter_filter]
  congr 2
  ext t
  simp only [and_assoc]

end DoubleDeal.Security.PermCount
