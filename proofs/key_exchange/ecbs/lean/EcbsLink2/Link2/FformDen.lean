/-
  The new denominator stays right-invertible when the spec step succeeds.
  `walk_run_inv` is the witness `hready` used to assume, and `z3_den_inv`
  turns it into the inverse `ProjOn` stores. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FformCellInv
import EcbsLink2.Link2.FformCellWalk

namespace EcbsLink2.Link2

open EcbsLink2.Spec

/-- A live white or red step makes `Z₃` right-invertible. The inverse is the
    one `walk_run_inv` reads off `walkStep`, rewritten to `fieldInv`. -/
theorem z3_of_walk (t : Spec.Tier) (px py baseX baseY z w : List Nat) (c : Nat)
    (ax' ay' : List Nat)
    (sat : TierSat t) (lay : TierShape t)
    (hn : 0 < t.n) (hk : t.k < t.n) (hb : t.n ≤ t.benchlen)
    (h2 : 2 * (t.n - 1) < t.benchlen) (h3 : 3 * (t.n - 1) < t.benchlen)
    (hpx : allTritList px) (hpy : allTritList py)
    (hbx : allTritList baseX) (hz : allTritList z) (hw : allTritList w)
    (hzL : z.length = t.n) (hwL : w.length = t.n)
    (hzw : fieldMul t.n t.k t.benchlen z w = onePeg t.n)
    (hc : c = 1 ∨ c = 2)
    (hwalk : walkStep t.n t.k t.benchlen (baseX, baseY) true (px, py) c =
      some (true, (ax', ay'))) :
    let n := t.n
    let k := t.k
    let bench := t.benchlen
    let zC := fieldCube n k bench z
    let xC := fieldCube n k bench px
    let z3 := fformBottom n k bench
      (fformRun n k bench baseX zC (fieldMul n k bench xC zC)) zC
    ∃ w3, w3.length = n ∧ allTritList w3 ∧ allTritList z3 ∧
      fieldMul n k bench z3 w3 = onePeg n ∧
      z3 ≠ List.replicate n 0 := by
  obtain ⟨g, hspec⟩ :=
    walk_run_inv t.n t.k t.benchlen baseX baseY px py ax' ay' c hc hwalk
  have hfi : fieldInv t.n t.k t.benchlen
      (fieldSub t.n baseX (fieldCube t.n t.k t.benchlen px)) = some g := by
    rw [← specInv_fieldInv]
    exact hspec
  exact z3_den_inv t px py baseX z w g sat lay hn hk hb h2 h3
    hpx hpy hbx hz hw hzL hwL hzw hfi

end EcbsLink2.Link2
