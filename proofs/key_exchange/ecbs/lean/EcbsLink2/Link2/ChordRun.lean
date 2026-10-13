/-
  The run of `chord_add_demo`: copy the base across into the bottom and take the
  accumulator across away. That is `fieldSub`. An empty run is the reroll branch.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.Add
import EcbsLink2.Link2.WalkCopy

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- `a + (−a) = 0` in GF(3), for a trit. -/
theorem trit_cancel (c : Nat) (hc : c ≤ 2) : tritAdd c (flipTrit c) = 0 := by
  have h : c = 0 ∨ c = 1 ∨ c = 2 := by omega
  rcases h with rfl | rfl | rfl <;> decide

/-- A length-`n` trit list subtracted from itself is the zero home. -/
theorem fieldSub_self (n : Nat) (xs : List Nat)
    (hx : xs.length = n) (htri : allTritList xs) :
    fieldSub n xs xs = List.replicate n 0 := by
  unfold fieldSub fieldAdd
  apply List.ext_getElem
  · simp [List.length_map, List.length_range, List.length_replicate]
  · intro i h1 h2
    have hi : i < n := by simpa [List.length_replicate] using h2
    have hix : i < xs.length := by rw [hx]; exact hi
    simp only [List.getElem_map, List.getElem_range, List.getElem_replicate]
    have hget : coeff xs i = xs[i] := by
      unfold coeff
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hix]
      simp
    have hmir : coeff (mirrorTrits xs) i = flipTrit (xs[i]) := by
      rw [mirrorTrits_flip]
      unfold coeff
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hix]
      simp
    rw [hmir, hget, trit_cancel _ (trit_get htri hix)]

/-- The chord op bump. Slot `op_chord` grows by one; every other field stays. -/
theorem chord_bump (b : Ecbs.Board) (cOps : Nat)
    (hops : 3 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop : b.sudo_5Board_4cost.sudo_5Costs_3ops[3]'(hops) = (cOps : Int))
    (hf : FitsLen (cOps + 1)) :
    (do
        let t ← SudoRt.atL b.sudo_5Board_4cost.sudo_5Costs_3ops Ecbs.op_chord
        let t ← SudoRt.addI t (1 : Int)
        let t ← SudoRt.putL b.sudo_5Board_4cost.sudo_5Costs_3ops Ecbs.op_chord t
        pure ({ b with sudo_5Board_4cost :=
          { b.sudo_5Board_4cost with sudo_5Costs_3ops := t } } : Ecbs.Board)) =
      .ok (bumpOp b 3 cOps hops) := by
  rw [show Ecbs.op_chord = Int.ofNat 3 from rfl, atL_ofNat _ 3 hops, hop, ok_bind]
  rw [← ofNat_eq_natCast cOps, addI_ofNat_one cOps hf, ok_bind]
  rw [putL_ofNat _ 3 (Int.ofNat (cOps + 1)) hops, ok_bind, pure_eq_ok]
  rfl

end EcbsLink2.Link2
