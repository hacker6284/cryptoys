/-
  Clearing the denominator. SPEC.md §3 R8: the other tiers run the F-form and
  then multiply by the inverse of `Z`. `fieldInv` is a left inverse, and
  multiplication is commutative, so `g · (p · Z) = p`. That is the affine
  point `Spec.basePoint` names.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FformProj
import EcbsLink2.Link2.FieldUnit
import EcbsLink2.Link2.FieldComm
import EcbsLink2.Link2.FieldNeg
import EcbsLink2.Link2.FieldOk
import EcbsLink2.Link2.ClimbEmit

namespace EcbsLink2.Link2

open EcbsLink2.Spec

private theorem k_lt (t : Spec.Tier) (hsh : TierShape t) : t.k < t.n := by
  have hgap : 0 < t.n - t.k := by
    rw [hsh.gap]
    exact Nat.mul_pos hsh.w0 hsh.r0
  omega

/-- `g · Z = 1` sends `p · Z` back to `p`. -/
theorem denom_clear (n k bench : Nat) (p z g : List Nat)
    (hn : 0 < n) (hk : k < n) (hb : n ≤ bench) (hspan : 2 * (n - 1) < bench)
    (hp : allTritList p) (hz : allTritList z) (hg : allTritList g)
    (hpL : p.length = n)
    (hinv : fieldMul n k bench g z = onePeg n) :
    fieldMul n k bench g (fieldMul n k bench p z) = p := by
  have hpz : allTritList (fieldMul n k bench p z) :=
    prod_trits n k bench p z hspan hb
  have hcomm := fieldMul_comm n k bench g (fieldMul n k bench p z) hg hpz
  have hassoc := fieldMul_assoc n k bench p z g hn hk hb hspan hp hz hg
  have hswap : fieldMul n k bench p (fieldMul n k bench z g) =
      fieldMul n k bench p (fieldMul n k bench g z) := by
    rw [fieldMul_comm n k bench z g hz hg]
  have hunit : fieldMul n k bench p (fieldMul n k bench g z) =
      fieldMul n k bench p (onePeg n) := by rw [hinv]
  have hdone := fieldMul_one_right n k bench p hn hk hb hspan hp hpL
  exact hcomm.trans (hassoc.trans (hswap.trans (hunit.trans hdone)))

/-- Both coordinates. `FieldOk` supplies `g` when `Z` is not zero, and
    `fieldInv_mul` makes it a left inverse. -/
theorem affine_clear (t : Spec.Tier) (px py z g : List Nat)
    (hOk : BoardOk t) (hsh : TierShape t) (sat : TierSat t)
    (hpx : allTritList px) (hpy : allTritList py) (hz : allTritList z)
    (hpxL : px.length = t.n) (hpyL : py.length = t.n) (hzL : z.length = t.n)
    (hinv : fieldInv t.n t.k t.benchlen z = some g) :
    fieldMul t.n t.k t.benchlen g (fieldMul t.n t.k t.benchlen px z) = px ∧
      fieldMul t.n t.k t.benchlen g (fieldMul t.n t.k t.benchlen py z) = py := by
  have hn := hOk.n_pos
  have hk := k_lt t hsh
  have hb : t.n ≤ t.benchlen := mul_span_n t.n t.benchlen hn sat.mul_span
  have hspan := sat.mul_span
  have hg : allTritList g := by
    rcases fieldInv_some_shape t.n t.k t.benchlen z g hinv with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact invGap_trits t z sat hsh hn hzL hz
    · exact mirror_trits _
  have hleft := fieldInv_mul t z g sat hsh hn hzL hz hinv
  exact ⟨denom_clear t.n t.k t.benchlen px z g hn hk hb hspan hpx hz hg hpxL hleft,
    denom_clear t.n t.k t.benchlen py z g hn hk hb hspan hpy hz hg hpyL hleft⟩

/-- `Z` nonzero and `FieldOk` give the inverse `affine_clear` uses. -/
theorem affine_inv (t : Spec.Tier) (z : List Nat)
    (hF : FieldOk t) (hz : allTritList z) (hzL : z.length = t.n)
    (hne : z ≠ zeroHome t.n) :
    ∃ g, fieldInv t.n t.k t.benchlen z = some g := by
  have hnot := hF z hz hzL hne
  revert hnot
  generalize hfi : fieldInv t.n t.k t.benchlen z = o
  intro hnot
  cases o with
  | none => exact absurd rfl hnot
  | some g => exact ⟨g, rfl⟩

end EcbsLink2.Link2
