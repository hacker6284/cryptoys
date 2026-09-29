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
  collision-resistant compression function: Hash security rests entirely on
  IV-anchoring.

  What Lean proves is the reduction (`dmStep_collision_of_sq`,
  `dmStep_pseudo_collision`: same corners and a squaring collision give a
  compression collision).  That distinct squaring-collision pairs exist for
  every block and corner part is the paper argument above, checked on the
  real function by the script; it is not a Lean theorem here.

  Zero sorry.  No native_decide.
-/
import MegaDreifach.Security.IdealCount

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
  exact compose_right_cancel _ _ W hWinj hsq

/-- The shared word is a product of face moves (so it is injective/legal). -/
theorem emBlock_word_legal (h h' : Position) (hc : SameCorners h h') (deal : List Nat) :
    ∃ W, Word W ∧ Em.emBlock h deal = compose W h ∧ Em.emBlock h' deal = compose W h' := by
  -- strengthen the invariant with `Word W`
  have key : ∀ (cards : List Nat) (st st' : Position × Em.Grip),
      (st.2 = st'.2 ∧ ∃ W, Word W ∧ st.1 = compose W h ∧ st'.1 = compose W h') →
      ((cards.foldl Em.g2Step st).2 = (cards.foldl Em.g2Step st').2 ∧
        ∃ W, Word W ∧ (cards.foldl Em.g2Step st).1 = compose W h ∧
          (cards.foldl Em.g2Step st').1 = compose W h') := by
    intro cards
    induction cards with
    | nil => intro st st' hi; exact hi
    | cons c cs ih =>
        intro st st' ⟨ho, W, hWw, e1, e2⟩
        apply ih
        obtain ⟨st1, st2⟩ := st
        obtain ⟨st1', st2'⟩ := st'
        dsimp only at ho e1 e2
        subst ho; subst e1; subst e2
        have f1 := g2Step_fst (compose W h) st2 c
        have f2 := g2Step_fst (compose W h') st2 c
        rw [← compose_assoc] at f1 f2
        refine ⟨?_, _, ?_, f1, f2⟩
        · rw [g2Step_snd, g2Step_snd, f1, f2]
          exact recipeA_sameCorners _ _ (sameCorners_compose_left _ _ _ hc) _ _
        · exact word_compose (by
            have := word_g2Step (identity, st2) c Word.id
            exact this) hWw
  have key3 : ∀ (n : Nat) (st st' : Position × Em.Grip),
      (st.2 = st'.2 ∧ ∃ W, Word W ∧ st.1 = compose W h ∧ st'.1 = compose W h') →
      ((Em.f3Iter n st).2 = (Em.f3Iter n st').2 ∧
        ∃ W, Word W ∧ (Em.f3Iter n st).1 = compose W h ∧ (Em.f3Iter n st').1 = compose W h') := by
    intro n
    induction n with
    | zero => intro st st' hi; exact hi
    | succ n ih =>
        intro st st' ⟨ho, W, hWw, e1, e2⟩
        apply ih
        obtain ⟨st1, st2⟩ := st
        obtain ⟨st1', st2'⟩ := st'
        dsimp only at ho e1 e2
        subst ho; subst e1; subst e2
        have f1 := f3Step_fst (compose W h) st2
        have f2 := f3Step_fst (compose W h') st2
        rw [← compose_assoc] at f1 f2
        refine ⟨?_, _, word_compose (word_faceTurn _ _ _ Word.id) hWw, f1, f2⟩
        show Em.recipeA (Em.f3Step (compose W h, st2)).1 (st2 0) st2 =
          Em.recipeA (Em.f3Step (compose W h', st2)).1 (st2 0) st2
        rw [f1, f2]
        exact recipeA_sameCorners _ _ (sameCorners_compose_left _ _ _ hc) _ _
  have hstart : (h, Em.gripId).2 = (h', Em.gripId).2 ∧
      ∃ W, Word W ∧ (h, Em.gripId).1 = compose W h ∧ (h', Em.gripId).1 = compose W h' :=
    ⟨rfl, identity, Word.id, (compose_id_left h).symm, (compose_id_left h').symm⟩
  obtain ⟨_, W, hWw, e1, e2⟩ := key3 f3T _ _ (key (deal.take 52) _ _ hstart)
  exact ⟨W, hWw, e1, e2⟩

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
