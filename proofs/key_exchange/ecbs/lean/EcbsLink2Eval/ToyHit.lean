/-
  Hole 2 is a root on Toy: the exponent root squares to the curve side.
-/
import EcbsLink2Eval.ToyRoot

namespace EcbsLink2.Spec

theorem toy_square :
    fieldMul 23 15 72
        [2, 0, 0, 1, 1, 2, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 2, 0, 2, 0]
        [2, 0, 0, 1, 1, 2, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 2, 0, 2, 0] =
      [1, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  set_option maxRecDepth 8192 in decide

theorem toy_root_hole2 :
    rootHit 23 15 72 (basisPeg 23 2) = true := by
  unfold rootHit
  rw [toy_rootY, toy_side, toy_square]
  decide

end EcbsLink2.Spec
