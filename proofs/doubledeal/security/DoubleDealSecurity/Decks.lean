/-
  Named cards, witness decks, and the cell-map interface used by the Link 2
  transfer (`Link.lean`).
-/
import DoubleDeal.Basic

namespace DoubleDeal.Security

/-! ## Named cards (CHaSeD ids: suit ♣0 ♥1 ♠2 ♦3, id = 13·suit + rank − 1) -/

def KC : Fin 52 := ⟨12, by decide⟩   -- K♣
def KH : Fin 52 := ⟨25, by decide⟩   -- K♥
def KS : Fin 52 := ⟨38, by decide⟩   -- K♠
def KD : Fin 52 := ⟨51, by decide⟩   -- K♦
def QH : Fin 52 := ⟨24, by decide⟩   -- Q♥

/-- The deck `c, 0, 1, …` (card `c` first, then the rest in order). -/
def firstDeck (c : Nat) : Fin 52 → Nat := fun i =>
  if i.val = 0 then c else if i.val ≤ c then i.val - 1 else i.val

theorem firstDeck_lt : ∀ i, firstDeck 51 i < 52 := by decide

/-- A map on cells that keeps card values card values (a relabelling's
    action on `Nat` cells is one; see `Relabel.app_cardMap`). -/
structure CardMap (f : Nat → Nat) : Prop where
  lt : ∀ n, n < 52 → f n < 52

/-- The transposition of two values, on `Nat` cells. -/
def swapNat (a b n : Nat) : Nat := if n = a then b else if n = b then a else n

end DoubleDeal.Security
