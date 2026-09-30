/-
  SECURITY support.  RULE-INDEPENDENT step lemmas: every E_m step
  left-multiplies the position by a product of face moves.

  * `leftIter_compose`, `faceTurn_compose`, `faceTurn_eq`: a face turn is a
    left multiplication.
  * `g2Step_fst`, `f3Step_fst`: the position part of a G2 / F3 step is
    `compose W g` with `W` depending only on the grip and the card.
  * `Word`: positions that are products of face moves; `word_g2Step`,
    `word_f3Iter`, `word_foldl_g2`, `word_emBlock`, `word_dmStep`.

  Used by `Parity` (legality of reachable chaining values, hence M3 and
  `v_Hash_collision_comp`) and by the v1-only `CornerDriven` / `FreeStart`.
  Keeping them here means deleting the v1 files does not take M3 with it.

  Grip-rule status: INDEPENDENT of the grip rule (no statement mentions how
  the grip is chosen).  They unfold the (v1) `Em.g2Step` / `Em.f3Step` /
  `Em.emBlock`, so they need re-proof only if those step definitions change
  (they go through again if each step still left-multiplies by face moves).

  Zero sorry.  No native_decide.
-/
import MegaDreifachV1.Link2.VHash

namespace MegaDreifachV1.Security

open MegaDreifachV1 MegaDreifachV1.Link2

/-! ## Steps are left multiplications -/

theorem leftIter_compose (T : Position) : ∀ (n : Nat) (W h : Position),
    Em.leftIter T n (compose W h) = compose (Em.leftIter T n W) h
  | 0, _, _ => rfl
  | n + 1, W, h => by
      simp only [Em.leftIter]
      rw [leftIter_compose T n W h, compose_assoc]

theorem faceTurn_compose (W h : Position) (f : Fin 12) (a : Nat) :
    Em.faceTurn (compose W h) f a = compose (Em.faceTurn W f a) h :=
  leftIter_compose _ _ _ _

theorem faceTurn_eq (g : Position) (f : Fin 12) (a : Nat) :
    Em.faceTurn g f a = compose (Em.faceTurn identity f a) g := by
  rw [← faceTurn_compose, compose_id_left]

/-- The position part of a G2 step is a left multiplication whose word depends
    only on the grip and the card. -/
theorem g2Step_fst (g : Position) (o : Em.Grip) (card : Nat) :
    (Em.g2Step (g, o) card).1 = compose (Em.g2Step (identity, o) card).1 g := by
  unfold Em.g2Step
  dsimp only
  by_cases hr : card / 4 < 12
  · simp only [hr, dite_true]
    split
    · rw [← faceTurn_compose, ← faceTurn_compose, ← faceTurn_compose, compose_id_left]
    · rw [← faceTurn_compose, ← faceTurn_compose, compose_id_left]
  · simp only [hr, dite_false]
    split
    · rw [← faceTurn_compose, ← faceTurn_compose, ← faceTurn_compose, compose_id_left]
    · rw [← faceTurn_compose, ← faceTurn_compose, compose_id_left]

theorem f3Step_fst (g : Position) (o : Em.Grip) :
    (Em.f3Step (g, o)).1 = compose (Em.faceTurn identity (o 0) 1) g := faceTurn_eq _ _ _


/-! ## Words in face moves -/

/-- Positions that are products of face moves. -/
inductive Word : Position → Prop
  | id : Word identity
  | step (f : Fin 12) (g : Position) : Word g → Word (compose (Em.faceMove f) g)

theorem word_compose {a b : Position} (ha : Word a) (hb : Word b) : Word (compose a b) := by
  induction ha with
  | id => rw [compose_id_left]; exact hb
  | step f g _ ih => rw [compose_assoc]; exact Word.step f _ ih

theorem word_leftIter (f : Fin 12) : ∀ (n : Nat) (g : Position), Word g →
    Word (Em.leftIter (Em.faceMove f) n g)
  | 0, _, h => h
  | n + 1, g, h => Word.step f _ (word_leftIter f n g h)

theorem word_faceTurn (g : Position) (f : Fin 12) (a : Nat) (h : Word g) :
    Word (Em.faceTurn g f a) := word_leftIter f _ _ h

theorem word_g2Step (st : Position × Em.Grip) (card : Nat) (h : Word st.1) :
    Word (Em.g2Step st card).1 := by
  obtain ⟨g, o⟩ := st
  rw [g2Step_fst]
  refine word_compose ?_ h
  unfold Em.g2Step
  dsimp only
  by_cases hr : card / 4 < 12
  · simp only [hr, dite_true]
    apply word_faceTurn
    split
    · exact word_faceTurn _ _ _ (word_faceTurn _ _ _ Word.id)
    · exact word_faceTurn _ _ _ Word.id
  · simp only [hr, dite_false]
    apply word_faceTurn
    split
    · exact word_faceTurn _ _ _ (word_faceTurn _ _ _ Word.id)
    · exact word_faceTurn _ _ _ Word.id

theorem word_f3Iter : ∀ (n : Nat) (st : Position × Em.Grip), Word st.1 → Word (Em.f3Iter n st).1
  | 0, _, h => h
  | n + 1, _, h => word_f3Iter n _ (word_faceTurn _ _ _ h)

theorem word_foldl_g2 : ∀ (cards : List Nat) (st : Position × Em.Grip), Word st.1 →
    Word (cards.foldl Em.g2Step st).1
  | [], _, h => h
  | c :: cs, st, h => word_foldl_g2 cs _ (word_g2Step st c h)

theorem word_emBlock (h : Position) (deal : List Nat) (hh : Word h) : Word (Em.emBlock h deal) :=
  word_f3Iter _ _ (word_foldl_g2 _ (h, Em.gripId) hh)

theorem word_dmStep (h : Position) (deal : List Nat) (hh : Word h) : Word (Em.dmStep h deal) :=
  word_compose hh (word_emBlock h deal hh)

end MegaDreifachV1.Security
