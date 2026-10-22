/-
  The hit test in the base-point search. The gap holds the squared root up
  and the bottom holds the curve side. `SEq.beq` of those arrays is `rootHit`.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.Add
import EcbsLink2.SpecBase

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open Ecbs
open EcbsLink2.Spec

private theorem list_beq_decide (xs ys : List Nat) :
    (xs == ys) = decide (xs = ys) := by
  by_cases h : xs = ys
  · simp [h]
  · simp [h]

/-- The emitted compare of the two homes is the spec hit bit. -/
theorem root_hit_cmp (b : Ecbs.Board) (n k bench : Nat) (x : List Nat)
    (hY : value b gap =
      .ok (embed (fieldMul n k bench (rootY n k bench x) (rootY n k bench x))))
    (hS : value b bottom = .ok (embed (curveSide n k bench x))) :
    (do
        let y2 ← value b gap
        let side ← value b bottom
        pure (SudoRt.SEq.beq y2 side)) =
      .ok (rootHit n k bench x) := by
  rw [hY, ok_bind, hS, ok_bind]
  have hbeq := embed_beq
    (fieldMul n k bench (rootY n k bench x) (rootY n k bench x))
    (curveSide n k bench x)
  rw [hbeq, pure_eq_ok]
  have hlist := list_beq_decide
    (fieldMul n k bench (rootY n k bench x) (rootY n k bench x))
    (curveSide n k bench x)
  unfold rootHit
  rw [hlist]

end EcbsLink2.Link2
