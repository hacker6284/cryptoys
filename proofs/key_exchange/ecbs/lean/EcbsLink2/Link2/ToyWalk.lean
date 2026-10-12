/-
  The cofactor walk on Toy's hole-2 root, one cell at a time.
  SPEC.md §5.1 lines 193 and 196: white, red, white, red.
-/
import EcbsLink2.SpecBase

namespace EcbsLink2.Spec

def toyBase : List Nat × List Nat :=
  (basisPeg 23 2, [2, 0, 0, 1, 1, 2, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 2, 0, 2, 0])

def toyW : List Nat := [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem toy_walk_0 :
    walkStep 23 15 72 toyBase false (toyW, toyW) 1 =
      some (true, ([0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [2, 0, 0, 1, 1, 2, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 2, 0, 2, 0])) := by
  set_option maxRecDepth 8192 in decide

end EcbsLink2.Spec
