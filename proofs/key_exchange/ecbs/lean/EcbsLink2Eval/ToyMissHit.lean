/-
  The hole-1 exponent root does not square to the curve side.
-/
import EcbsLink2Eval.ToyMissRoot

namespace EcbsLink2.Spec

theorem toy_miss_square :
    (fieldMul 23 15 72 [2, 1, 0, 1, 0, 1, 1, 1, 1, 1, 2, 2, 0, 1, 2, 0, 1, 1, 1, 2, 2, 0, 0] [2, 1, 0, 1, 0, 1, 1, 1, 1, 1, 2, 2, 0, 1, 2, 0, 1, 1, 1, 2, 2, 0, 0] == [1, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) = false := by
  set_option maxRecDepth 8192 in decide

theorem toy_root_hole1 :
    rootHit 23 15 72 (basisPeg 23 1) = false := by
  unfold rootHit
  rw [toy_rootY_1, toy_side_1, toy_miss_square]

end EcbsLink2.Spec
