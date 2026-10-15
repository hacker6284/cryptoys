/-
  Demo's base point is the coordinate pair written in SPEC.md §5.1 line 198.
  The root checks are kernel evaluations in `BaseSpec`; this file only assembles them.
-/
import EcbsLink2.Link2.BaseSpec

namespace EcbsLink2.Spec

theorem demo_basePoint :
    basePoint demo = some ([0, 2, 1, 2, 0, 1, 1], [2, 0, 0, 2, 2, 1, 2]) := by
  have h1 : rootHit 7 5 20 (basisPeg 7 1) = false := by
    simpa [demo] using demo_root_hole1
  have h2 : rootHit 7 5 20 (basisPeg 7 2) = true := by
    simpa [demo] using demo_root_hole2
  have hy : rootY 7 5 20 (basisPeg 7 2) = [1, 1, 2, 0, 0, 1, 2] := by
    simpa [demo] using demo_rootY
  have hc : cofactorWalk 7 5 20 (basisPeg 7 2, [1, 1, 2, 0, 0, 1, 2]) =
      some ([0, 2, 1, 2, 0, 1, 1], [2, 0, 0, 2, 2, 1, 2]) := by
    simpa [demo] using demo_cofactor
  have hmiss := searchRoot_miss 7 5 20 6 1 (by decide) h1
  have h6 : (6 + 1) = 7 := by decide
  simp only [h6] at hmiss
  have hstep : searchRoot 7 5 20 6 (1 + 1) = searchRoot 7 5 20 6 2 := rfl
  have hhit := searchRoot_hit 7 5 20 5 2 (by decide) h2
  have h5 : (5 + 1) = 6 := by decide
  simp only [h5] at hhit
  unfold basePoint
  simp only [demo, hmiss, hstep, hhit, hy, hc]

end EcbsLink2.Spec
