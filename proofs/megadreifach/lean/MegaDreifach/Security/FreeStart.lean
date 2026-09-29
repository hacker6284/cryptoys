/-
  SECURITY (structural weakness, proved) — RESULT ABOUT v1 OF THE GRIP RULE.

  Grip-rule status: `emBlock_word_legal` and `dmStep_pseudo_collision` rest on
  `CornerDriven.dmStep_word`, hence on the v1 grip rule (Recipe A reads only
  corner cubies).  They document why the grip rule is being redesigned, and
  must be deleted or restated for a redesigned rule.  `dmStep_collision_of_sq`
  is plain group algebra (it assumes a shared word `W`) and does not depend on
  the grip rule, but it only applies when such a `W` exists.

  Universal pseudo-collisions of the MegaDreifach compression function (v1).

  With `W` the (shared) face-turn word of `CornerDriven.dmStep_word`,
  `dm(h, m) = h W h`.  For `h, h'` with the same corners,
  `dm(h, m) = dm(h', m)` as soon as `(h W)² = (h' W)²` — a squaring
  collision in the group.  Squaring is far from injective (e.g. any two
  involutions), so for EVERY block and EVERY corner part there are distinct
  chaining values with the same output, found with a few block encryptions
  (3 in `proofs/megadreifach/security/pseudo_collision.py`).  Under v1 the
  compression function is therefore not collision resistant, and the MD
  reduction of `DigestInj.lean` can never be instantiated with a
  collision-resistant compression function: it yields no collision
  resistance for Hash.  (IV-anchored Hash collisions of v1 are in fact
  practical, by a different mechanism: see `SwapCollision.lean`.)

  What Lean proves is the reduction (`dmStep_collision_of_sq`,
  `dmStep_pseudo_collision`: same corners and a squaring collision give a
  compression collision).  That distinct squaring-collision pairs exist for
  every block and corner part is the paper argument above, checked on the
  real function by the script; it is not a Lean theorem here.

  Zero sorry.  No native_decide.
-/
import MegaDreifach.Security.CornerDriven
import MegaDreifach.Security.Parity

namespace MegaDreifach.Security

open MegaDreifach MegaDreifach.Link2

/-- Squaring collision ⇒ compression collision (same block, same corners). -/
theorem dmStep_collision_of_sq (h h' : Position) (deal : List Nat)
    (W : Position) (hW : Em.emBlock h deal = compose W h ∧ Em.emBlock h' deal = compose W h')
    (hWinj : InjPos W)
    (hsq : compose (compose h W) (compose h W) = compose (compose h' W) (compose h' W)) :
    Em.dmStep h deal = Em.dmStep h' deal := by
  unfold Em.dmStep
  rw [hW.1, hW.2]
  have e1 : compose (compose h W) (compose h W) = compose (compose h (compose W h)) W := by
    simp only [compose_assoc]
  have e2 : compose (compose h' W) (compose h' W) = compose (compose h' (compose W h')) W := by
    simp only [compose_assoc]
  rw [e1, e2] at hsq
  exact leftMul_cancel _ _ W hWinj.1 hWinj.2 hsq

/-- The shared word is a product of face moves (so it is injective/legal). -/
theorem emBlock_word_legal (h h' : Position) (hc : SameCorners h h') (deal : List Nat) :
    ∃ W, Word W ∧ Em.emBlock h deal = compose W h ∧ Em.emBlock h' deal = compose W h' :=
  emBlock_wordInv h h' hc deal

/-- **Pseudo-collision criterion.**  Same corners and a squaring collision
    `(hW)² = (h'W)²` of the shared word give equal compression outputs. -/
theorem dmStep_pseudo_collision (h h' : Position) (hc : SameCorners h h') (deal : List Nat) :
    ∃ W, Word W ∧
      (compose (compose h W) (compose h W) = compose (compose h' W) (compose h' W) →
        Em.dmStep h deal = Em.dmStep h' deal) := by
  obtain ⟨W, hWw, hW1, hW2⟩ := emBlock_word_legal h h' hc deal
  have hinj : InjPos W := injPos_of_isLegal _ (word_isLegal hWw)
  exact ⟨W, hWw, fun hsq => dmStep_collision_of_sq h h' deal W ⟨hW1, hW2⟩ hinj hsq⟩

end MegaDreifach.Security
