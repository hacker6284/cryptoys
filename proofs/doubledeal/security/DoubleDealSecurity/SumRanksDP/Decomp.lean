/-
  Shared decomposition lemmas for the row and column
  chains (PROOF.md §2 Lemma 3, §4 Lemma 5). `PROOF.md §n` refers to
  `proofs/doubledeal/security/sumranks-dp-paper/PROOF.md`.

  * `nested_count`: counting tuples `σ : Fin n → α` subject to conditions
    `Q r σ` that depend only on `σ 0, …, σ r`, with at most `N r` good choices
    of `σ r` for every prefix, gives at most `Π N r`.
  * `rowShuf σ` / `colShuf σ`: the position permutation that reorders each row
    (column) of the column-major grid by `σ r` (`σ j`). Averaging over them
    (`sum_mul_card_shuf`) is the "fix the row sets, shuffle inside rows" step.
-/
import DoubleDealSecurity.SumRanksV10Iff
import DoubleDealSecurity.SumRanksDP.Standalone

namespace DoubleDeal.Security.SumRanksDP

open DoubleDeal Finset

/-! ## Nested counting -/

theorem nested_count {α : Type*} [Fintype α] [DecidableEq α] :
    ∀ (n : ℕ) (Q : Fin n → (Fin n → α) → Prop) [∀ r, DecidablePred (Q r)]
      (N : Fin n → ℕ),
    (∀ r σ σ', (∀ i, i ≤ r → σ i = σ' i) → (Q r σ ↔ Q r σ')) →
    (∀ r σ, (univ.filter fun a => Q r (Function.update σ r a)).card ≤ N r) →
    (univ.filter fun σ : Fin n → α => ∀ r, Q r σ).card ≤ ∏ r, N r
  | 0, Q, _, N, _, _ => by
    simp only [univ_eq_empty, prod_empty]
    exact (card_filter_le _ _).trans (by simp)
  | n + 1, Q, inst, N, hpre, hN => by
    classical
    rcases isEmpty_or_nonempty α with hα | ⟨⟨a₀⟩⟩
    · have : (univ : Finset (Fin (n + 1) → α)) = ∅ := by
        rw [univ_eq_empty_iff]; exact ⟨fun σ => hα.false (σ 0)⟩
      simp [this]
    -- the first coordinate's condition depends only on `σ 0`
    have h0 : ∀ σ : Fin (n + 1) → α, Q 0 σ ↔ Q 0 (fun _ => σ 0) := fun σ =>
      hpre 0 _ _ fun i hi => by rw [Fin.le_zero_iff.1 hi]
    let M : ℕ := ∏ r : Fin n, N r.succ
    have hinner : ∀ a : α,
        (univ.filter fun τ : Fin n → α =>
          ∀ r : Fin n, Q r.succ (Fin.cons a τ)).card ≤ M := by
      intro a
      refine nested_count n (fun r τ => Q r.succ (Fin.cons a τ)) (fun r => N r.succ) ?_ ?_
      · intro r τ τ' h
        apply hpre
        intro i
        refine Fin.cases (fun _ => rfl) (fun i' hi' => ?_) i
        simp only [Fin.cons_succ]
        exact h i' (Fin.succ_le_succ_iff.1 hi')
      · intro r τ
        simp only [Fin.cons_update]
        exact hN r.succ _
    have hfirst : (univ.filter fun a : α => Q 0 (fun _ => a)).card ≤ N 0 := by
      refine le_trans (le_of_eq ?_) (hN 0 (fun _ => a₀))
      congr 1
      apply filter_congr
      intro a _
      rw [h0 (Function.update _ 0 a)]
      simp
    have hsplit : (univ.filter fun σ : Fin (n + 1) → α => ∀ r, Q r σ).card =
        ∑ a : α, if Q 0 (fun _ => a) then
          (univ.filter fun τ : Fin n → α =>
            ∀ r : Fin n, Q r.succ (Fin.cons a τ)).card else 0 := by
      rw [card_eq_sum_ones, sum_filter]
      rw [← (Fin.consEquiv fun _ => α).sum_comp, Fintype.sum_prod_type]
      refine sum_congr rfl fun a _ => ?_
      have e : ∀ τ : Fin n → α, (Fin.consEquiv (fun _ : Fin (n + 1) => α)) (a, τ) =
          (Fin.cons a τ : Fin (n + 1) → α) := fun _ => rfl
      have hq0 : ∀ τ : Fin n → α, Q 0 (Fin.cons a τ) ↔ Q 0 (fun _ => a) := fun τ => by
        rw [h0]; simp
      split_ifs with hq
      · rw [card_eq_sum_ones, sum_filter]
        refine sum_congr rfl fun τ _ => ?_
        simp only [e, Fin.forall_fin_succ, hq0, hq, true_and]
      · refine sum_eq_zero fun τ _ => ?_
        simp only [e, Fin.forall_fin_succ, hq0, hq, false_and, if_false]
    rw [hsplit, Fin.prod_univ_succ]
    calc (∑ a : α, if Q 0 (fun _ => a) then
          (univ.filter fun τ : Fin n → α =>
            ∀ r : Fin n, Q r.succ (Fin.cons a τ)).card else 0)
        ≤ ∑ a : α, if Q 0 (fun _ => a) then M else 0 :=
          sum_le_sum fun a _ => by split_ifs; exacts [hinner a, le_rfl]
      _ = (univ.filter fun a : α => Q 0 (fun _ => a)).card * M := by
          rw [← sum_filter, sum_const, smul_eq_mul]
      _ ≤ N 0 * M := Nat.mul_le_mul_right _ hfirst

/-! ## Row and column shuffles of the column-major grid -/

/-- Positions `Fin 52` as seats `(row, column)` of the column-major grid. -/
def cmEquiv : Fin 52 ≃ Fin 4 × Fin 13 where
  toFun k := (cmRow k, cmCol k)
  invFun p := cmFlat p.1 p.2
  left_inv k := cmFlat_cm k
  right_inv p := by
    obtain ⟨h1, h2⟩ := cm_cmFlat p.1 p.2
    exact Prod.ext h1 h2

/-- Reorder row `r` by `σ r`: seat `(r, j)` ↦ `(r, σ r j)`. -/
def rowShuf (σ : Fin 4 → Equiv.Perm (Fin 13)) : Equiv.Perm (Fin 52) :=
  cmEquiv.trans ((Equiv.prodShear (Equiv.refl _) σ).trans cmEquiv.symm)

/-- Reorder column `j` by `σ j`: seat `(r, j)` ↦ `(σ j r, j)`. -/
def colShuf (σ : Fin 13 → Equiv.Perm (Fin 4)) : Equiv.Perm (Fin 52) :=
  cmEquiv.trans ((Equiv.prodComm _ _).trans ((Equiv.prodShear (Equiv.refl _) σ).trans
    ((Equiv.prodComm _ _).trans cmEquiv.symm)))

theorem rowShuf_cmFlat (σ : Fin 4 → Equiv.Perm (Fin 13)) (r : Fin 4) (j : Fin 13) :
    rowShuf σ (cmFlat r j) = cmFlat r (σ r j) := by
  obtain ⟨h1, h2⟩ := cm_cmFlat r j
  simp [rowShuf, cmEquiv, Equiv.prodShear, h1, h2]

theorem colShuf_cmFlat (σ : Fin 13 → Equiv.Perm (Fin 4)) (r : Fin 4) (j : Fin 13) :
    colShuf σ (cmFlat r j) = cmFlat (σ j r) j := by
  obtain ⟨h1, h2⟩ := cm_cmFlat r j
  simp [colShuf, cmEquiv, Equiv.prodShear, h1, h2]

/-- Averaging over a family of position permutations: right multiplication by a
    fixed permutation is a bijection of decks. -/
theorem sum_mul_card_shuf {S : Type*} [Fintype S] (ψ : S → Equiv.Perm (Fin 52))
    (f : Equiv.Perm (Fin 52) → ℚ) :
    (Fintype.card S : ℚ) * ∑ π, f π = ∑ π, ∑ s, f (π * ψ s) := by
  rw [sum_comm]
  have : ∀ s, ∑ π, f (π * ψ s) = ∑ π, f π := fun s =>
    Fintype.sum_equiv (Equiv.mulRight (ψ s)) _ _ (fun _ => rfl)
  simp only [this, sum_const, card_univ, nsmul_eq_mul]

end DoubleDeal.Security.SumRanksDP
