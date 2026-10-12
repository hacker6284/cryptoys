/-
  The first red cell of the Toy cofactor, from the field steps.
-/
import EcbsLink2.Link2.ToyChord

namespace EcbsLink2.Spec

theorem toy_chord_red :
    chordAdd 23 15 72 (toyPx, toyPy) (basisPeg 23 2, mirrorTrits toyY) =
      some (toyX3, toyY3) := by
  unfold chordAdd
  dsimp only
  rw [toy_run_sub]
  rw [show specInv 23 15 72 toyRun = some toyInvL from toy_run_inv]
  dsimp only
  rw [toy_rise_sub, toy_slope_mul, toy_slope2_mul, toy_x3_add, toy_y3_sub]

theorem toy_walk_red :
    walkStep 23 15 72 (basisPeg 23 2, toyY) true (basisPeg 23 2, toyY) 2 =
      some (true, (toyX3, toyY3)) := by
  unfold walkStep pointCube
  dsimp only
  rw [toy_cube_px, toy_cube_py]
  simp only [reduceIte, reduceCtorEq]
  rw [toy_chord_red]
  decide

end EcbsLink2.Spec
