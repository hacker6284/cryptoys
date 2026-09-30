/-
  SECURITY support.  RULE-INDEPENDENT step lemmas: every E_m step
  left-multiplies the position by a product of face moves.

  * `leftIter_compose`, `faceTurn_compose`, `faceTurn_eq`: a face turn is a
    left multiplication.
  * `g2Step_fst`, `f3Step_fst`: the position part of a G2 / F3 step is
    `compose W g` with `W` the step's word at the identity (so `W` does not
    depend on `g`; in `Em.g2Step` / `Em.f3Step` the read index `pos` / `rnd`
    only enters the new grip).
  * `Word`: positions that are products of face moves; `word_g2Step`,
    `word_f3Run`, `word_g2Run`, `word_emBlock`, `word_dmStep`.

  Used by `Parity` (legality of reachable chaining values, hence M3 and
  `v_Hash_collision_comp`).

  Grip-rule status: INDEPENDENT of the grip rule (no statement mentions how
  the grip is chosen).  They unfold the v2 `Em.g2Step` / `Em.f3Step` /
  `Em.emBlock`; they would need re-proof only if a step stopped being a left
  multiplication by face moves.  (The v1 versions are in
  `proofs/deprecated/megadreifach-v1/`.)

  Zero sorry.  No native_decide.
-/
import MegaDreifach.Link2.VHash

namespace MegaDreifach.Security

open MegaDreifach MegaDreifach.Link2

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

/-- The position part of a G2 step is a left multiplication by the step's word
    at the identity (independent of `g`). -/
theorem g2Step_fst (g : Position) (o : Em.Grip) (card pos : Nat) :
    (Em.g2Step (g, o) card pos).1 = compose (Em.g2Step (identity, o) card pos).1 g := by
  unfold Em.g2Step
  dsimp only
  by_cases hr : card / 4 < 12
  · simp only [hr, dite_true]
    rw [← faceTurn_compose, ← faceTurn_compose, ← faceTurn_compose, compose_id_left]
  · simp only [hr, dite_false]
    rw [← faceTurn_compose, ← faceTurn_compose, ← faceTurn_compose, compose_id_left]

theorem f3Step_fst (g : Position) (o : Em.Grip) (rnd : Nat) :
    (Em.f3Step (g, o) rnd).1 = compose (Em.faceTurn identity (o 0) 1) g := faceTurn_eq _ _ _


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

theorem word_g2Step (st : Position × Em.Grip) (card pos : Nat) (h : Word st.1) :
    Word (Em.g2Step st card pos).1 := by
  obtain ⟨g, o⟩ := st
  rw [g2Step_fst]
  refine word_compose ?_ h
  unfold Em.g2Step
  dsimp only
  by_cases hr : card / 4 < 12
  · simp only [hr, dite_true]
    exact word_faceTurn _ _ _ (word_faceTurn _ _ _ (word_faceTurn _ _ _ Word.id))
  · simp only [hr, dite_false]
    exact word_faceTurn _ _ _ (word_faceTurn _ _ _ (word_faceTurn _ _ _ Word.id))

theorem word_f3Run : ∀ (n r : Nat) (st : Position × Em.Grip), Word st.1 → Word (Em.f3Run r n st).1
  | 0, _, _, h => h
  | n + 1, _, _, h => word_f3Run n _ _ (word_faceTurn _ _ _ h)

theorem word_g2Run : ∀ (cards : List Nat) (p : Nat) (st : Position × Em.Grip), Word st.1 →
    Word (Em.g2Run p cards st).1
  | [], _, _, h => h
  | c :: cs, p, st, h => word_g2Run cs (p + 1) _ (word_g2Step st c p h)

theorem word_emBlock (h : Position) (deal : List Nat) (hh : Word h) : Word (Em.emBlock h deal) :=
  word_f3Run _ _ _ (word_g2Run _ _ (h, Em.gripId) hh)

theorem word_dmStep (h : Position) (deal : List Nat) (hh : Word h) : Word (Em.dmStep h deal) :=
  word_compose hh (word_emBlock h deal hh)

end MegaDreifach.Security
