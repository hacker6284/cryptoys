/-
  Finite facts about the v3 card naming (kernel `decide`, no native_decide): for every colour
  `c` and suit amount `k ∈ 1..4`, `suit_nbrs c k = (n, n2)` names a real edge `(c, n)` and a real
  corner `(c, n, n2)` (in clockwise order, so `corner_slot` finds it), and each edge slot is
  found again from its own two faces. These are the side conditions of the piece searches in
  `edge_face_of` / `corner_face_of`. No sorry.
-/
import MegaDreifachV3.Em

namespace MegaDreifachV3.Link2

open MegaDreifach MegaDreifach.Em MegaDreifachV3.Em

/-- `(c, k)` names an edge `(c, n)` whose slot has faces `{c, n}`, and a corner `(c, n, n2)`
    whose slot has faces a rotation of `(c, n, n2)`. -/
def tripleOk (c : Fin 12) (k : Nat) : Bool :=
  let n := (suitNbrs c k).1
  let n2 := (suitNbrs c k).2
  (match edgeSlot? c n with
   | some s => (edgeFace s.val 0 == c && edgeFace s.val 1 == n) ||
       (edgeFace s.val 0 == n && edgeFace s.val 1 == c)
   | none => false) &&
  (match cornerSlot? c n n2 with
   | some t =>
       let p := (cornerFace t.val 0, cornerFace t.val 1, cornerFace t.val 2)
       p == (c, n, n2) || p == (n, n2, c) || p == (n2, c, n)
   | none => false)

/-- The finite check on all 48 `(c, k)` pairs. -/
theorem triples_ok : ∀ c : Fin 12, ∀ k : Fin 4, tripleOk c (k.val + 1) = true := by
  decide

/-- Every edge slot is the `edgeSlot?` of its own two faces. -/
theorem edgeSlot?_faces : ∀ s : Fin 30, edgeSlot? (edgeFace s.val 0) (edgeFace s.val 1) = some s := by
  decide

/-- Every corner slot is the `cornerSlot?` of its own three faces. -/
theorem cornerSlot?_faces :
    ∀ s : Fin 20, cornerSlot? (cornerFace s.val 0) (cornerFace s.val 1) (cornerFace s.val 2) = some s := by
  decide

end MegaDreifachV3.Link2
