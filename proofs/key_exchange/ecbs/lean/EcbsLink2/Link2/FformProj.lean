/-
  One live cell's projective point. The denominator stays left-invertible:
  a zero cell cubes it, and `fieldInv` on a successful run is a left inverse.
  Neither fact assumes the modulus is irreducible.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FieldCube
import EcbsLink2.Link2.CheckTail
import EcbsLink2.Link2.WalkFformInd

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

theorem mirror_red_peg (n : Nat) (_hn : 0 < n) :
    mirrorTrits (2 :: List.replicate (n - 1) 0) = onePeg n := by
  unfold mirrorTrits onePeg
  have hmap : (List.replicate (n - 1) 0).map (fun c => if c = 0 then 0 else 3 - c) =
      List.replicate (n - 1) 0 := by
    simp [List.map_replicate]
  simp [hmap]

/-- If `fieldInv` returns a gap, that gap is a left inverse. The two branches
    are the hole-0 pegs `1` and `2`; a red peg is mirrored. -/
theorem fieldInv_mul (t : Spec.Tier) (x g : List Nat)
    (sat : TierSat t) (lay : TierShape t)
    (hpos : 0 < t.n) (hxL : x.length = t.n) (hx : allTritList x)
    (h : fieldInv t.n t.k t.benchlen x = some g) :
    fieldMul t.n t.k t.benchlen g x = onePeg t.n := by
  have hgT := invGap_trits t x sat lay hpos hxL hx
  unfold fieldInv at h
  dsimp only at h
  by_cases h1 : fieldMul t.n t.k t.benchlen (invGap t.n t.k t.benchlen x) x =
      1 :: List.replicate (t.n - 1) 0
  · rw [if_pos h1] at h
    cases h
    rw [h1]
    rfl
  · rw [if_neg h1] at h
    by_cases h2 : fieldMul t.n t.k t.benchlen (invGap t.n t.k t.benchlen x) x =
        2 :: List.replicate (t.n - 1) 0
    · rw [if_pos h2] at h
      cases h
      rw [fieldMul_mirror_left t.n t.k t.benchlen (invGap t.n t.k t.benchlen x) x hgT hx, h2,
        mirror_red_peg t.n hpos]
    · rw [if_neg h2] at h
      simp at h

/-- Cubing preserves a left inverse, and the cube of the denominator is not zero. -/
theorem cube_left_inv (n k bench : Nat) (z w : List Nat)
    (hn : 0 < n) (hk : k < n) (hb : n ≤ bench)
    (h2 : 2 * (n - 1) < bench) (h3 : 3 * (n - 1) < bench)
    (hz : allTritList z) (hw : allTritList w)
    (hzL : z.length = n) (hwL : w.length = n)
    (hinv : fieldMul n k bench z w = onePeg n) :
    fieldMul n k bench (fieldCube n k bench z) (fieldCube n k bench w) = onePeg n ∧
      fieldCube n k bench z ≠ zeroPeg n := by
  have hzC := fieldCube_trits n k bench z hz h3 (Nat.le_of_lt hk)
  have hwC := fieldCube_trits n k bench w hw h3 (Nat.le_of_lt hk)
  have hcu := fieldCube_mul n k bench z w hn hk hb h2 h3 hz hw
  have hone := fieldCube_one n k bench hn hb
  have hprod : fieldMul n k bench (fieldCube n k bench z) (fieldCube n k bench w) =
      onePeg n := by
    rw [← hcu, hinv, hone]
  refine ⟨hprod, ?_⟩
  intro hz0
  have hkill : fieldMul n k bench (zeroPeg n) (fieldCube n k bench w) = zeroPeg n := by
    rw [fieldMul_comm n k bench (zeroPeg n) (fieldCube n k bench w)
        (by simpa [zeroPeg] using replicate_trits n) hwC,
      fieldMul_zero n k bench (fieldCube n k bench w) hb]
  have hne : onePeg n ≠ zeroPeg n := by
    intro heq
    have hn1 : n = (n - 1) + 1 := by omega
    rw [onePeg, zeroPeg, hn1, List.replicate_succ] at heq
    simp at heq
  exact hne (hprod.symm.trans (by rw [hz0, hkill]))

end EcbsLink2.Link2
