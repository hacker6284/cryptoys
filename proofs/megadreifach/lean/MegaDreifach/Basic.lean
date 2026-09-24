/-
  MegaDreifach constants, factorial, and card ids.
  Algebraic / combinatorial layer only. Zero sorry. No native_decide.
-/
namespace MegaDreifach

/-- Function injectivity (Lean 4.14 Init does not export `Function.Injective`). -/
def Injective {α β : Type _} (f : α → β) : Prop :=
  ∀ {x y}, f x = f y → x = y

theorem id_injective {α : Type _} : Injective (@id α) := fun h => h

/-- Factorial, same recurrence as TwoDeck. -/
def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

@[simp] theorem factorial_zero : factorial 0 = 1 := rfl
@[simp] theorem factorial_succ (n : Nat) : factorial (n + 1) = (n + 1) * factorial n := rfl

theorem factorial_pos (n : Nat) : 0 < factorial n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have : 0 < n + 1 := Nat.succ_pos n
      exact Nat.mul_pos this ih

theorem factorial_dvd_succ (n : Nat) : factorial n ∣ factorial (n + 1) :=
  ⟨n + 1, by rw [factorial_succ, Nat.mul_comm]⟩

/-- `n! / 2` for even-permutation ranks. Defined for all `n`; used at `n ≥ 2`. -/
def evenPermCount (n : Nat) : Nat := factorial n / 2

/-- Locked pad block size (bytes). -/
def padBlock : Nat := 28

/-- Locked length-field width (bytes). -/
def lenField : Nat := 8

/-- Locked digest width (bytes). -/
def digestLen : Nat := 29

/-- Locked G2 body length (cards). -/
def bodyLen : Nat := 52

/-- Locked F3 blank-round count. -/
def f3T : Nat := 12

/-- Image of φ: ranks `< 2^224 < 52!`. -/
def phiMax : Nat := 2 ^ 224

/-- Card id in `0..51`. Soft-lock: `id ↦ (rank = id / 4, suit = id % 4)`. -/
abbrev CardId := Fin 52

def cardRank (c : Nat) : Nat := c / 4
def cardSuit (c : Nat) : Nat := c % 4
def cardId (rank suit : Nat) : Nat := rank * 4 + suit

theorem cardId_lt_52 (rank suit : Nat) (hr : rank < 13) (hs : suit < 4) :
    cardId rank suit < 52 := by
  simp [cardId]
  omega

/-- Group order `|G| = (20!/2) · 3^19 · (30!/2) · 2^29`. -/
def groupOrder : Nat :=
  evenPermCount 20 * (3 ^ 19) * evenPermCount 30 * (2 ^ 29)

end MegaDreifach
