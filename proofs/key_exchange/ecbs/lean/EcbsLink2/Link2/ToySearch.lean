/-
  Toy's search hits at hole 2. The cofactor walk of that root is still open:
  one chord does not fit in a single kernel evaluation.
-/
import EcbsLink2.Link2.ToyHit
import EcbsLink2.Link2.ToyMissHit

namespace EcbsLink2.Spec

theorem toy_searchRoot :
    searchRoot 23 15 72 23 1 =
      some (basisPeg 23 2,
        [2, 0, 0, 1, 1, 2, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 2, 0, 2, 0]) := by
  have hmiss := searchRoot_miss 23 15 72 22 1 (by decide) toy_root_hole1
  have h23 : (22 + 1) = 23 := by decide
  simp only [h23] at hmiss
  have hstep : searchRoot 23 15 72 22 (1 + 1) = searchRoot 23 15 72 22 2 := rfl
  have hhit := searchRoot_hit 23 15 72 21 2 (by decide) toy_root_hole2
  have h22 : (21 + 1) = 22 := by decide
  simp only [h22] at hhit
  rw [hmiss, hstep, hhit, toy_rootY]

end EcbsLink2.Spec
