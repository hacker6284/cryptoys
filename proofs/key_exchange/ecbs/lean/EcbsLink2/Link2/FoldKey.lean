/-
  One column of `fold_key`: add `x[i]` into `out[j]` in GF(3).
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.Board
import EcbsLink2.Link2.School

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

private theorem embed_get (xs : List Nat) (i : Nat) (hi : i < xs.length) :
    (embed xs)[i]'(by rw [size_embed]; exact hi) = Int.ofNat (xs[i]) := by
  simp [embed, Array.getElem_mk, List.getElem_map]

/-- One nonzero column of the fold. Both entries are trits, so the sum fits an i64
    and `mod 3` is `Spec.add3`. -/
theorem fold_cell (out x : List Nat) (i j : Nat)
    (hi : i < x.length) (hj : j < out.length)
    (hx : x[i] ≤ 2) (ho : out[j] ≤ 2) :
    (do
        let cur ← SudoRt.atL (embed out) (j : Int)
        let xv ← SudoRt.atL (embed x) (i : Int)
        let sum ← SudoRt.addI cur xv
        let m ← SudoRt.modI sum (3 : Int)
        SudoRt.putL (embed out) (j : Int) m) =
      .ok (embed (out.set j ((out[j] + x[i]) % 3))) := by
  have hfi : FitsLen (out[j] + x[i]) := fits_small (by omega)
  have hjA : j < (embed out).size := by rw [size_embed]; exact hj
  have hiA : i < (embed x).size := by rw [size_embed]; exact hi
  rw [← ofNat_eq_natCast j, atL_ofNat _ j hjA, ok_bind, embed_get out j hj]
  rw [← ofNat_eq_natCast i, atL_ofNat _ i hiA, ok_bind, embed_get x i hi]
  rw [addI_ofNat _ _ hfi, ok_bind]
  rw [show (3 : Int) = Int.ofNat 3 from rfl, modI_ofNat _ (by decide), ok_bind]
  rw [putL_ofNat _ j (Int.ofNat ((out[j] + x[i]) % 3)) hjA]
  exact congrArg Except.ok (embed_set out j ((out[j] + x[i]) % 3) hj)

end EcbsLink2.Link2
