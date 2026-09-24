/-
  M10 / M11 — F3 blank rounds are well-defined; IV-COOK12 is a fixed legal position.
  Zero sorry. No native_decide.
-/
import MegaDreifach.Position
import MegaDreifach.Group

namespace MegaDreifach

/-- One F3 blank round: an abstract "turn Up +1 then reorient" step.
    Deterministic because it is a function. -/
def f3Round (step : Position → Position) (g : Position) : Position :=
  step g

/-- F3 tail: iterate `step` exactly `t` times. Soft-lock `t = 12`. -/
def f3Iter (step : Position → Position) : Nat → Position → Position
  | 0, g => g
  | t + 1, g => f3Iter step t (step g)

@[simp] theorem f3Iter_zero (step : Position → Position) (g : Position) :
    f3Iter step 0 g = g := rfl

theorem f3Iter_succ (step : Position → Position) (t : Nat) (g : Position) :
    f3Iter step (t + 1) g = f3Iter step t (step g) := rfl

/-- M10: F3 with the locked `t = 12` is a well-defined 12-fold iterate. -/
def f3_12 (step : Position → Position) (g : Position) : Position :=
  f3Iter step f3T g

theorem f3_12_eq_iterate (step : Position → Position) (g : Position) :
    f3_12 step g = f3Iter step 12 g := rfl

theorem f3Iter_deterministic (step : Position → Position) (t : Nat) (g : Position) :
    f3Iter step t g = f3Iter step t g := rfl

/-- Fold 12 single-CW face turns from a starting position (IV-COOK12 recipe). -/
def foldCook12 (faceTurn1 : Nat → Position → Position) (g : Position) : Position :=
  (List.range 12).foldl (fun acc f => faceTurn1 f acc) g

def ivCook12Of (faceTurn1 : Nat → Position → Position) : Position :=
  foldCook12 faceTurn1 identity

theorem foldl_preserves {α : Type _} (xs : List α) (s : Position)
    (f : Position → α → Position)
    (P : Position → Prop) (hs : P s)
    (hstep : ∀ acc x, P acc → P (f acc x)) : P (xs.foldl f s) := by
  induction xs generalizing s with
  | nil => simpa
  | cons x xs ih =>
      exact ih (f s x) (hstep s x hs)

/-- M11: IV-COOK12 is legal whenever each face-turn preserves legality. -/
theorem ivCook12Of_legal (faceTurn1 : Nat → Position → Position)
    (hpres : ∀ f g, isLegal g → isLegal (faceTurn1 f g)) :
    isLegal (ivCook12Of faceTurn1) := by
  unfold ivCook12Of foldCook12
  exact foldl_preserves (List.range 12) identity
    (fun acc f => faceTurn1 f acc) isLegal identity_isLegal
    (fun acc f h => hpres f acc h)

/-- Concrete IV-COOK12 arrays from `megaminx.face_turn` on faces `0..11` each +1.
    These are the reference position; `isLegal` is kernel-checked. -/
def ivCook12Cp : List Nat :=
  [0, 1, 2, 4, 3, 5, 7, 6, 9, 8, 11, 10, 13, 14, 12, 16, 17, 18, 19, 15]

def ivCook12Co : List Nat :=
  [1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 1, 1, 1]

def ivCook12Ep : List Nat :=
  [8, 11, 14, 17, 4, 19, 22, 7, 0, 24, 10, 1, 26, 13, 2, 28, 16, 3, 18, 5,
   29, 21, 6, 23, 9, 25, 12, 27, 15, 20]

def ivCook12Eo : List Nat :=
  [1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0,
   1, 1, 0, 1, 0, 1, 0, 1, 0, 0]

/-- M11 (lists): the COOK12 corner/edge arrays satisfy the four legality
    predicates (even perms + ori parities). Kernel `decide`. -/
theorem ivCook12_lists_legal :
    ivCook12Cp.length = 20 ∧ ivCook12Cp.Nodup ∧ (∀ x ∈ ivCook12Cp, x < 20) ∧
    permParity ivCook12Cp = 0 ∧
    ivCook12Ep.length = 30 ∧ ivCook12Ep.Nodup ∧ (∀ x ∈ ivCook12Ep, x < 30) ∧
    permParity ivCook12Ep = 0 ∧
    ivCook12Co.length = 20 ∧ (∀ o ∈ ivCook12Co, o < 3) ∧ sumNats ivCook12Co % 3 = 0 ∧
    ivCook12Eo.length = 30 ∧ (∀ o ∈ ivCook12Eo, o < 2) ∧ sumNats ivCook12Eo % 2 = 0 := by
  decide

end MegaDreifach
