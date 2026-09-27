/-
  T1 addendum: why the v9 K♣↔Q♥ distinguisher does not contradict T1.

  T1 (`SumRanks.lean`) characterises relabellings that commute with SumRanks
  on EVERY deck: exactly the constant weight shifts (`v9Sym`), and no
  transposition (`v9_no_swap_commutes_sumRanks`). The distinguisher filed in
  `proofs/deprecated/doubledeal-v9/` needs much less: commutation on the decks
  that actually occur, with some probability. This module proves the
  deck-by-deck condition behind it:

  * `sumRanks_rel_of_sums`: on one grid, if σ leaves every row weight sum
    (mod 13) and every column weight sum after the row stage (mod 4)
    unchanged, SumRanks commutes with σ on that grid.
  * `sumRanksV9_swap_commutes_of_same_row`: a transposition of two cards with
    equal column weight (rank + suit) mod 4 commutes with v9 SumRanks on every
    deck where the two cards share a row, whatever their ranks. For K♣ (rank
    13, suit 0) and Q♥ (rank 12, suit 1) both weights are 13
    (`KC_QH_columnWeight`). For a uniformly placed deck the two cards share a
    row with probability 12/51; that probability is measured, not proved here.

  So the universal statements of T1 stay true, and the attack uses the gap
  between "on all decks" and "on a 12/51 share of decks".
-/
import DoubleDealSecurity.SumRanks
import Mathlib.Algebra.BigOperators.Fin

namespace DoubleDeal.Security

open DoubleDeal Relabel
open scoped BigOperators

/-- (PROVED) Deck-by-deck SumRanks commutation from unchanged sums. -/
theorem sumRanks_rel_of_sums (σ : Relabel) (rowW colW : Nat → Nat) (g : Grid Nat)
    (hr : ∀ r, rowWeightSum rowW (relG σ g) r % 13 = rowWeightSum rowW g r % 13)
    (hc : ∀ c, colWeightSum colW (relG σ (applyRowRotates rowW g)) c % 4 =
      colWeightSum colW (applyRowRotates rowW g) c % 4) :
    sumRanks rowW colW (relG σ g) = relG σ (sumRanks rowW colW g) := by
  unfold sumRanks
  have h1 : applyRowRotates rowW (relG σ g) = relG σ (applyRowRotates rowW g) := by
    unfold applyRowRotates
    exact rowRotate_rel σ g _ _ hr
  rw [h1]
  unfold applyColRotates
  exact colRotate_rel σ _ _ _ hc

/-- A weight sum mod `M` does not change when every element keeps its weight mod `M`. -/
theorem weightSum_map_mod (w : Nat → Nat) (f : Nat → Nat) (M : Nat)
    (hf : ∀ x, w (f x) % M = w x % M) :
    ∀ xs : List Nat, weightSum w (xs.map f) % M = weightSum w xs % M
  | [] => rfl
  | x :: xs => by
    have ih := weightSum_map_mod w f M hf xs
    simp only [weightSum, List.map, sumNats] at ih ⊢
    rw [Nat.add_mod, hf x, ih, ← Nat.add_mod]

theorem swap_app_eq (a b : Fin 52) (x : Nat) :
    (swap a b).app x = if x = a.val then b.val else if x = b.val then a.val else x := by
  unfold Relabel.app
  by_cases hx : x < 52
  · simp only [hx, ↓reduceDIte]
    by_cases ha : x = a.val
    · subst ha; simp [Equiv.swap_apply_left]
    · by_cases hb : x = b.val
      · subst hb; simp [Equiv.swap_apply_right, ha]
      · have ha' : (⟨x, hx⟩ : Fin 52) ≠ a := fun e => ha (congrArg Fin.val e)
        have hb' : (⟨x, hx⟩ : Fin 52) ≠ b := fun e => hb (congrArg Fin.val e)
        simp [Equiv.swap_apply_of_ne_of_ne ha' hb', ha, hb]
  · have ha : x ≠ a.val := fun e => hx (e ▸ a.isLt)
    have hb : x ≠ b.val := fun e => hx (e ▸ b.isLt)
    simp [hx, ha, hb]

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
  apply sumRanks_rel_of_sums
  · intro r'
    by_cases hr : r' = r
    · subst hr
      -- inside the row, the swap of values is the swap of the two columns
      have hcol : ∀ c, (swap a b).app (g r' c) = g r' (Equiv.swap ca cb c) := by
        intro c
        rw [swap_app_eq]
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
        rw [swap_app_eq]
        have e1 : g r' c ≠ a.val := fun e => hr (grid_inj hg (e.trans ha.symm)).1
        have e2 : g r' c ≠ b.val := fun e => hr (grid_inj hg (e.trans hb.symm)).1
        simp [e1, e2]
      have hrow : relG (swap a b) g r' = g r' := funext hfix
      simp only [rowWeightSum, hrow]
  · intro c
    have hl : toList4 (fun r' => relG (swap a b) (applyRowRotates cardRank g) r' c) =
        (toList4 (fun r' => applyRowRotates cardRank g r' c)).map (swap a b).app := rfl
    simp only [colWeightSum]
    rw [hl]
    apply weightSum_map_mod
    intro x
    rw [swap_app_eq]
    split_ifs with h1 h2
    · subst h1; exact hw.symm
    · subst h2; exact hw
    · rfl

/-- K♣ (12) and Q♥ (24): different ranks, equal column weight (13). -/
theorem KC_QH_columnWeight :
    cardRank 12 = 13 ∧ cardRank 24 = 12 ∧ cardColumnWeight 12 = 13 ∧ cardColumnWeight 24 = 13 := by
  decide

/-- (PROVED) Instance: K♣↔Q♥ commutes with v9 SumRanks on every deck where they share a row. -/
theorem sumRanksV9_KC_QH_of_same_row (g : Grid Nat) (hg : IsDeck (scoopColumnMajor g))
    (r : Fin 4) (ca cb : Fin 13) (ha : g r ca = 12) (hb : g r cb = 24) :
    sumRanksV9 (relG (swap KC ⟨24, by decide⟩) g) = relG (swap KC ⟨24, by decide⟩) (sumRanksV9 g) :=
  sumRanksV9_swap_commutes_of_same_row KC ⟨24, by decide⟩ g hg r ca cb ha hb (by decide)

end DoubleDeal.Security
