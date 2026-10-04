/-
  Link 2 for the v3 neighbour helpers `lowest_nbr_index` and `suit_nbrs`: exact on every
  colour (and every suit amount `k ∈ 1..4`), by finite tables (kernel `decide!`, no
  native_decide). No sorry.
-/
import MegaDreifach.Link2.EmEdge
import MegaDreifachV3.Em

namespace MegaDreifachV3.Link2

open MegaDreifach MegaDreifach.Em MegaDreifach.Link2 MegaDreifachV3.Em

theorem lowest_nbr_index_table :
    allFin12 (fun f => isOkEq (Megadreifach.lowest_nbr_index (Int.ofNat f.val))
      (Int.ofNat (lowestNbrIndex f))) = true := by
  decide!

/-- v3 `lowest_nbr_index` is the model `lowestNbrIndex` on every colour. -/
theorem lowest_nbr_index_refines (f : Fin 12) :
    Megadreifach.lowest_nbr_index (Int.ofNat f.val) = .ok (Int.ofNat (lowestNbrIndex f)) :=
  isOkEq_spec (allFin12_spec lowest_nbr_index_table f)

theorem suit_nbrs_table :
    allFin12 (fun c => [1, 2, 3, 4].all (fun k =>
      isOkPair (Megadreifach.suit_nbrs (Int.ofNat c.val) (Int.ofNat k))
        (Int.ofNat (suitNbrs c k).1.val) (Int.ofNat (suitNbrs c k).2.val))) = true := by
  decide!

/-- v3 `suit_nbrs` is the model `suitNbrs` on every colour and suit amount `1..4`. -/
theorem suit_nbrs_refines (c : Fin 12) (k : Nat) (hk1 : 1 ≤ k) (hk4 : k ≤ 4) :
    Megadreifach.suit_nbrs (Int.ofNat c.val) (Int.ofNat k) =
      .ok (Int.ofNat (suitNbrs c k).1.val, Int.ofNat (suitNbrs c k).2.val) := by
  have ht := allFin12_spec suit_nbrs_table c
  rw [List.all_eq_true] at ht
  have hk : k ∈ [1, 2, 3, 4] := by
    rcases (by omega : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) with h | h | h | h <;> simp [h]
  exact isOkPair_spec (ht k hk)

end MegaDreifachV3.Link2
