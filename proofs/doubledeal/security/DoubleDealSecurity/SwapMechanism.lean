/-
  T1 addendum: why the v9 K♣↔Q♥ distinguisher does not contradict T1.
  DEPRECATED-v9 MODEL: every statement here is about `sumRanksV9`, the
  deprecated v9 SumRanks, and explains the vulnerability that retired it.
  v10 SumRanks (`sumRanksV10`) chains rows and columns; its same-row swap
  survival is measured, not proved (`proofs/doubledeal/analysis/v10-sumranks/`).

  T1 (`SumRanks.lean`) characterises relabellings that commute with SumRanks
  on EVERY deck: exactly the constant weight shifts (`v9Sym`), and no
  transposition (`v9_no_swap_commutes_sumRanks`). The distinguisher filed in
  `proofs/deprecated/doubledeal-v9/` needs much less: commutation on the decks
  that actually occur, with some probability. This module proves the
  deck-by-deck condition behind it:

  * `sumRanks_rel_iff_sums`: on one deck, SumRanks commutes with σ iff σ
    leaves every row weight sum (mod 13) and every column weight sum after
    the row stage (mod 4) unchanged (`sumRanks_rel_of_sums` and T1's
    `commute_rotations`).
  * `sumRanksV9_swap_commutes_of_same_row`: a transposition of two cards with
    equal column weight (rank + suit) mod 4 commutes with v9 SumRanks on every
    deck where the two cards share a row, whatever their ranks. For K♣ (rank
    13, suit 0) and Q♥ (rank 12, suit 1) both weights are 13
    (`KC_QH_weights`). For a uniformly placed deck the two cards share a
    row with probability 12/51; that probability is measured, not proved here.

  So the universal statements of T1 stay true, and the attack uses the gap
  between "on all decks" and "on a 12/51 share of decks".
-/
import DoubleDealSecurity.SumRanks
import Mathlib.Algebra.BigOperators.Fin

namespace DoubleDeal.Security

open DoubleDeal Relabel
open scoped BigOperators

/-- The row stage commutes with σ on a grid whose row sums σ leaves unchanged. -/
theorem applyRowRotates_rel_of_sums (σ : Relabel) (rowW : Nat → Nat) (g : Grid Nat)
    (hr : ∀ r, rowWeightSum rowW (relG σ g) r % 13 = rowWeightSum rowW g r % 13) :
    applyRowRotates rowW (relG σ g) = relG σ (applyRowRotates rowW g) := by
  unfold applyRowRotates
  exact rowRotate_rel σ g _ _ hr

/-- (PROVED) Deck-by-deck SumRanks commutation from unchanged sums. The column
    condition is stated on the row stage of the relabelled grid, exactly as
    `commute_rotations` concludes it, so the two combine into an iff
    (`sumRanks_rel_iff_sums`). -/
theorem sumRanks_rel_of_sums (σ : Relabel) (rowW colW : Nat → Nat) (g : Grid Nat)
    (hr : ∀ r, rowWeightSum rowW (relG σ g) r % 13 = rowWeightSum rowW g r % 13)
    (hc : ∀ c, colWeightSum colW (applyRowRotates rowW (relG σ g)) c % 4 =
      colWeightSum colW (applyRowRotates rowW g) c % 4) :
    sumRanks rowW colW (relG σ g) = relG σ (sumRanks rowW colW g) := by
  have h1 := applyRowRotates_rel_of_sums σ rowW g hr
  unfold sumRanks
  rw [h1]
  rw [h1] at hc
  unfold applyColRotates
  exact colRotate_rel σ _ _ _ hc

/-- (PROVED) On one deck, SumRanks commutes with σ iff σ leaves every row weight
    sum (mod 13) and every column weight sum after the row stage (mod 4) unchanged. -/
theorem sumRanks_rel_iff_sums (σ : Relabel) (rowW colW : Nat → Nat) (g : Grid Nat)
    (hg : IsDeck (scoopColumnMajor g)) :
    sumRanks rowW colW (relG σ g) = relG σ (sumRanks rowW colW g) ↔
      (∀ r, rowWeightSum rowW (relG σ g) r % 13 = rowWeightSum rowW g r % 13) ∧
      (∀ c, colWeightSum colW (applyRowRotates rowW (relG σ g)) c % 4 =
        colWeightSum colW (applyRowRotates rowW g) c % 4) :=
  ⟨commute_rotations σ rowW colW g hg, fun h => sumRanks_rel_of_sums σ rowW colW g h.1 h.2⟩

theorem weightSum_toList13 (w : Nat → Nat) (f : Fin 13 → Nat) :
    weightSum w (toList13 f) = ∑ c : Fin 13, w (f c) := by
  simp only [weightSum, toList13, List.map, sumNats, Fin.sum_univ_succ, Fin.sum_univ_zero]
  rfl

/-- (PROVED) A transposition of two cards with equal column weight mod 4 commutes
    with v9 SumRanks on every deck where the two cards share a row. -/
theorem sumRanksV9_swap_commutes_of_same_row (a b : Fin 52) (g : Grid Nat)
    (hg : IsDeck (scoopColumnMajor g)) (r : Fin 4) (ca cb : Fin 13)
    (ha : g r ca = a.val) (hb : g r cb = b.val)
    (hw : cardColumnWeight a.val % 4 = cardColumnWeight b.val % 4) :
    sumRanksV9 (relG (swap a b) g) = relG (swap a b) (sumRanksV9 g) := by
  have hr : ∀ r', rowWeightSum cardRank (relG (swap a b) g) r' % 13 =
      rowWeightSum cardRank g r' % 13 := by
    intro r'
    by_cases hr : r' = r
    · subst hr
      -- inside the row, the swap of values is the swap of the two columns
      have hcol : ∀ c, (swap a b).app (g r' c) = g r' (Equiv.swap ca cb c) := by
        intro c
        rw [swap_app_eq]; unfold swapNat
        by_cases h1 : c = ca
        · subst h1; simp [ha, hb, Equiv.swap_apply_left]
        · by_cases h2 : c = cb
          · subst h2; simp [ha, hb, Equiv.swap_apply_right]
          · have e1 : g r' c ≠ a.val := fun e => h1 (grid_inj hg (e.trans ha.symm)).2
            have e2 : g r' c ≠ b.val := fun e => h2 (grid_inj hg (e.trans hb.symm)).2
            simp [e1, e2, Equiv.swap_apply_of_ne_of_ne h1 h2]
      have hsum : (∑ c : Fin 13, cardRank ((swap a b).app (g r' c))) = ∑ c, cardRank (g r' c) := by
        simp only [hcol]
        exact Equiv.sum_comp (Equiv.swap ca cb) (fun c => cardRank (g r' c))
      show weightSum cardRank (toList13 (fun c => (swap a b).app (g r' c))) % 13 =
        weightSum cardRank (toList13 (g r')) % 13
      rw [weightSum_toList13, weightSum_toList13, hsum]
    · -- the other rows hold neither card, so nothing moves
      have hfix : ∀ c, (swap a b).app (g r' c) = g r' c := by
        intro c
        rw [swap_app_eq]; unfold swapNat
        have e1 : g r' c ≠ a.val := fun e => hr (grid_inj hg (e.trans ha.symm)).1
        have e2 : g r' c ≠ b.val := fun e => hr (grid_inj hg (e.trans hb.symm)).1
        simp [e1, e2]
      have hrow : relG (swap a b) g r' = g r' := funext hfix
      simp only [rowWeightSum, hrow]
  refine sumRanks_rel_of_sums _ _ _ _ hr ?_
  intro c
  rw [applyRowRotates_rel_of_sums _ _ _ hr]
  have hl : toList4 (fun r' => relG (swap a b) (applyRowRotates cardRank g) r' c) =
      (toList4 (fun r' => applyRowRotates cardRank g r' c)).map (swap a b).app := rfl
  have hk : ∀ x : Fin 52, cardColumnWeight ((swap a b) x).val % 4 =
      (cardColumnWeight x.val + 0) % 4 := by
    intro x
    have := congrFun (swap_app_eq a b) x.val
    rw [Relabel.app_fin] at this
    rw [this, Nat.add_zero]
    unfold swapNat
    split_ifs with h1 h2
    · rw [h1]; exact hw.symm
    · rw [h2]; exact hw
    · rfl
  have hlt : ∀ r' c', g r' c' < 52 := fun r' c' => by
    simpa [scoopColumnMajor, (cm_cmFlat r' c').1, (cm_cmFlat r' c').2] using hg.1 (cmFlat r' c')
  have hxs : ∀ x ∈ toList4 (fun r' => applyRowRotates cardRank g r' c), x < 52 := by
    have hA : ∀ r' c', applyRowRotates cardRank g r' c' < 52 := by
      intro r' c'
      simp only [applyRowRotates, rowRotate_apply]
      exact hlt _ _
    intro x hx
    simp only [toList4, List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with h | h | h | h <;> (rw [h]; exact hA _ _)
  simp only [colWeightSum]
  rw [hl, weightSum_map_app_mod (swap a b) cardColumnWeight 4 0 hk _ hxs, Nat.mul_zero, Nat.add_zero]

/-- K♣ (12) and Q♥ (24): different ranks, equal column weight (13). -/
theorem KC_QH_weights :
    cardRank 12 = 13 ∧ cardRank 24 = 12 ∧ cardColumnWeight 12 = 13 ∧ cardColumnWeight 24 = 13 := by
  decide

/-- (PROVED) Instance: K♣↔Q♥ commutes with v9 SumRanks on every deck where they share a row. -/
theorem sumRanksV9_KC_QH_of_same_row (g : Grid Nat) (hg : IsDeck (scoopColumnMajor g))
    (r : Fin 4) (ca cb : Fin 13) (ha : g r ca = 12) (hb : g r cb = 24) :
    sumRanksV9 (relG (swap KC QH) g) = relG (swap KC QH) (sumRanksV9 g) :=
  sumRanksV9_swap_commutes_of_same_row KC QH g hg r ca cb ha hb (by decide)

end DoubleDeal.Security
