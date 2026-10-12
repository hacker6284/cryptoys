/-
  The §5.1 base point, evaluated on the two tiers whose coordinates are written out.
-/
import EcbsLink2.SpecBase

namespace EcbsLink2.Spec

/-- SPEC.md §5.1 line 198, Demo, hole 0 first: x = `.RWR.WW`, y = `R..RRWR`.
    Line 197: the first working hole is 2, so hole 1 is not a hit. -/
theorem demo_root_hole1 :
    rootHit demo.n demo.k demo.benchlen (basisPeg demo.n 1) = false := by
  set_option maxRecDepth 32768 in decide

theorem demo_root_hole2 :
    rootHit demo.n demo.k demo.benchlen (basisPeg demo.n 2) = true := by
  set_option maxRecDepth 65536 in decide

theorem demo_rootY :
    rootY demo.n demo.k demo.benchlen (basisPeg demo.n 2) = [1, 1, 2, 0, 0, 1, 2] := by
  set_option maxRecDepth 65536 in decide

theorem demo_cofactor :
    cofactorWalk demo.n demo.k demo.benchlen
        (basisPeg demo.n 2, [1, 1, 2, 0, 0, 1, 2]) =
      some ([0, 2, 1, 2, 0, 1, 1], [2, 0, 0, 2, 2, 1, 2]) := by
  set_option maxRecDepth 65536 in decide

end EcbsLink2.Spec
