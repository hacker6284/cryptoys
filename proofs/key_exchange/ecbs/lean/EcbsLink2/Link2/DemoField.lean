/-
  Demo success for the exported field operations. The one-peg list is a unit,
  so both exports return it. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.Export
import EcbsLink2.Link2.OneField

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- Demo `multiply` of the one-peg list by itself returns that list. -/
theorem demo_multiply_one :
    Ecbs.multiply (embTier Spec.demo) (embed (onePeg Spec.demo.n))
        (embed (onePeg Spec.demo.n)) =
      .ok (embed (onePeg Spec.demo.n)) := by
  have hpos : 0 < Spec.demo.n := demo_board.n_pos
  have hn : Spec.demo.n ≤ Spec.demo.benchlen :=
    mul_span_n _ _ hpos demo_tier_sat.mul_span
  rw [multiply_refines Spec.demo demo_lay (onePeg Spec.demo.n) (onePeg Spec.demo.n)
      (onePeg_length _ hpos) (onePeg_length _ hpos) (onePeg_trits _),
    fieldMul_one _ _ _ hpos hn]

/-- Demo `cube_number` of the one-peg list returns that list. -/
theorem demo_cube_one :
    Ecbs.cube_number (embTier Spec.demo) (embed (onePeg Spec.demo.n)) =
      .ok (embed (onePeg Spec.demo.n)) := by
  have hpos : 0 < Spec.demo.n := demo_board.n_pos
  have hn : Spec.demo.n ≤ Spec.demo.benchlen :=
    mul_span_n _ _ hpos demo_tier_sat.mul_span
  rw [cube_number_refines Spec.demo demo_lay (onePeg Spec.demo.n)
      (onePeg_length _ hpos) (onePeg_trits _) demo_tier_sat.cube_span,
    fieldCube_one _ _ _ hpos hn]

/-- A red peg in hole 0 and empty holes after it. In GF(3) this is `-1`, not the unit. -/
def negPeg (n : Nat) : List Nat := 2 :: List.replicate (n - 1) 0

private theorem negPeg_trits (n : Nat) : allTritList (negPeg n) := by
  intro x hx
  simp [negPeg, List.mem_cons, List.mem_replicate] at hx
  rcases hx with rfl | ⟨_, rfl⟩ <;> decide

private theorem demo_neg_rungs : (rungList (Spec.demo.n - 1)).reverse = [2, 1] := by
  rw [demo_rungs]
  decide

private theorem demo_neg_step1 :
    invRung Spec.demo.n Spec.demo.k Spec.demo.benchlen
        (negPeg Spec.demo.n) (negPeg Spec.demo.n) 1 2 [1].isEmpty =
      (negPeg Spec.demo.n, 3) := by
  decide

private theorem demo_neg_step2 :
    invRung Spec.demo.n Spec.demo.k Spec.demo.benchlen
        (negPeg Spec.demo.n) (negPeg Spec.demo.n) 3 1 (List.isEmpty ([] : List Nat)) =
      (onePeg Spec.demo.n, 3) := by
  decide

private theorem demo_neg_climb :
    invClimb Spec.demo.n Spec.demo.k Spec.demo.benchlen
        (negPeg Spec.demo.n) (negPeg Spec.demo.n, 1) [2, 1] =
      (onePeg Spec.demo.n, 3) := by
  rw [invClimb, demo_neg_step1, invClimb, demo_neg_step2, invClimb]

private theorem demo_neg_cube :
    fieldCube Spec.demo.n Spec.demo.k Spec.demo.benchlen (onePeg Spec.demo.n) =
      onePeg Spec.demo.n := by
  decide

private theorem demo_neg_gap :
    invGap Spec.demo.n Spec.demo.k Spec.demo.benchlen (negPeg Spec.demo.n) =
      onePeg Spec.demo.n := by
  unfold invGap
  rw [demo_neg_rungs, demo_neg_climb, demo_neg_cube]

private theorem demo_neg_check :
    fieldMul Spec.demo.n Spec.demo.k Spec.demo.benchlen
        (onePeg Spec.demo.n) (negPeg Spec.demo.n) =
      negPeg Spec.demo.n := by
  decide

private theorem demo_neg_mirror : mirrorTrits (onePeg Spec.demo.n) = negPeg Spec.demo.n := by
  decide

private theorem demo_neg_fieldInv :
    fieldInv Spec.demo.n Spec.demo.k Spec.demo.benchlen (negPeg Spec.demo.n) =
      some (negPeg Spec.demo.n) := by
  unfold fieldInv
  rw [demo_neg_gap]
  simp only [demo_neg_check, demo_neg_mirror]
  decide

private theorem demo_neg_fieldMul :
    fieldMul Spec.demo.n Spec.demo.k Spec.demo.benchlen
        (negPeg Spec.demo.n) (negPeg Spec.demo.n) =
      onePeg Spec.demo.n := by
  decide

/-- Demo `multiply` of the constant red peg by itself is the unit, through `multiply_refines`. -/
theorem demo_multiply_neg :
    Ecbs.multiply (embTier Spec.demo) (embed (negPeg Spec.demo.n))
        (embed (negPeg Spec.demo.n)) =
      .ok (embed (onePeg Spec.demo.n)) := by
  rw [multiply_refines Spec.demo demo_lay (negPeg Spec.demo.n) (negPeg Spec.demo.n)
      (by decide) (by decide) (negPeg_trits _), demo_neg_fieldMul]

/-- Demo `invert_number` of the constant red peg returns that peg, through
    `invert_number_refines`. With `demo_multiply_neg`, the peg times its inverse is the unit. -/
theorem demo_invert_neg :
    Ecbs.invert_number (embTier Spec.demo) (embed (negPeg Spec.demo.n)) =
      .ok (embed (negPeg Spec.demo.n)) := by
  have hR : 0 < tierR Spec.demo := by rw [tierR, demo_rungs]; decide
  exact invert_number_refines Spec.demo demo_board (negPeg Spec.demo.n)
    (by decide) (negPeg_trits _) demo_tier_sat hR demo_shape _ demo_neg_fieldInv

end EcbsLink2.Link2
