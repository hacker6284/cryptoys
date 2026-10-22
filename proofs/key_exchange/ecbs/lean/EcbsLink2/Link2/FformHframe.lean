/-
  One live cell of `hframe`. A zero run is the doubling case: `walkStep`
  returns `none`, so the success hypothesis `some (true, _)` is impossible.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FformLine
import EcbsLink2.Link2.ChordRun

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

private theorem zero_trits (n : Nat) : allTritList (List.replicate n 0) := by
  intro x hx
  rcases List.mem_replicate.mp hx with ⟨_, rfl⟩
  exact Nat.zero_le _

/-- A right inverse cancels a zero product: `a · Z = 0` and `Z · w = 1` give `a = 0`. -/
theorem mul_right_inv_zero (n k bench : Nat) (a z w : List Nat)
    (hn : 0 < n) (hk : k < n) (hb : n ≤ bench)
    (h2 : 2 * (n - 1) < bench)
    (ha : allTritList a) (hz : allTritList z) (hw : allTritList w)
    (haL : a.length = n)
    (hzw : fieldMul n k bench z w = onePeg n)
    (h0 : fieldMul n k bench a z = zeroPeg n) :
    a = zeroPeg n := by
  have hassoc := fieldMul_assoc n k bench a z w hn hk hb h2 ha hz hw
  have hone := fieldMul_one_right n k bench a hn hk hb h2 ha haL
  have hkill : fieldMul n k bench (zeroPeg n) w = zeroPeg n := by
    rw [fieldMul_comm n k bench (zeroPeg n) w (by simpa [zeroPeg] using zero_trits n) hw,
      fieldMul_zero n k bench w hb]
  have h0w : fieldMul n k bench (fieldMul n k bench a z) w = zeroPeg n := by
    rw [h0, hkill]
  have hunit : fieldMul n k bench a (fieldMul n k bench z w) = a := by
    rw [hzw, hone]
  exact hunit.symm.trans (hassoc.symm.trans h0w)

/-- `v = x₂Z − X` is the zero home only when the affine run is zero,
    once `Z` is right-invertible and `X = x · Z`. -/
theorem run_zero_of_v (n k bench : Nat) (x x2 z w : List Nat)
    (hn : 0 < n) (hk : k < n) (hb : n ≤ bench)
    (h2 : 2 * (n - 1) < bench)
    (hx : allTritList x) (hx2 : allTritList x2) (hz : allTritList z) (hw : allTritList w)
    (hsubL : (fieldSub n x2 x).length = n)
    (hzw : fieldMul n k bench z w = onePeg n)
    (hv : fformRun n k bench x2 z (fieldMul n k bench x z) = List.replicate n 0) :
    fieldSub n x2 x = List.replicate n 0 := by
  have hrunT : allTritList (fieldSub n x2 x) := fieldAdd_trits n x2 (mirrorTrits x)
  have hv' : fieldMul n k bench (fieldSub n x2 x) z = zeroPeg n := by
    rw [← run_over_z n k bench x x2 z hb hx hx2 hz, hv]
    rfl
  simpa [zeroPeg] using
    mul_right_inv_zero n k bench (fieldSub n x2 x) z w hn hk hb h2 hrunT hz hw hsubL hzw hv'

/-- A white or red cell whose run `v` is zero. `walkStep` is `none`,
    so it is not `some (true, _)`. -/
theorem v_zero_excludes_success (n k bench : Nat) (x2 y2 ax ay : List Nat)
    (c : Nat) (p : Bool × (List Nat × List Nat)) (z w : List Nat)
    (hn : 0 < n) (hk : k < n) (hb : n ≤ bench)
    (h2 : 2 * (n - 1) < bench)
    (hc : c = 1 ∨ c = 2)
    (hx : allTritList (fieldCube n k bench ax)) (hx2 : allTritList x2)
    (hz : allTritList z) (hw : allTritList w)
    (hzw : fieldMul n k bench z w = onePeg n)
    (hv : fformRun n k bench x2 z
        (fieldMul n k bench (fieldCube n k bench ax) z) = List.replicate n 0) :
    walkStep n k bench (x2, y2) true (ax, ay) c = some p → False := by
  intro hstep
  have hsubL : (fieldSub n x2 (fieldCube n k bench ax)).length = n := by
    simp [fieldSub, fieldAdd, List.length_map, List.length_range]
  have hsub := run_zero_of_v n k bench (fieldCube n k bench ax) x2 z w
    hn hk hb h2 hx hx2 hz hw hsubL hzw hv
  have hnone := walkStep_empty_run n k bench (x2, y2) (ax, ay) c hc hsub hn hb
  rw [hnone] at hstep
  cases hstep

end EcbsLink2.Link2
