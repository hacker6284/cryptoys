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

end EcbsLink2.Link2
