/-
  PROOF-ONLY. CHaSeD card ids and rank/suit for DoubleDeal stones (SPEC §2).
  Algorithm source of truth is primitives/cipher/doubledeal/doubledeal.sudo;
  executable Lean is lean/Generated/ (see proofs/ANTI_DRIFT.md).
-/
namespace DoubleDeal

/-- Card id in `0..51`. -/
abbrev Card := Fin 52

def suit (c : Nat) : Nat := c / 13
def rank (c : Nat) : Nat := c % 13 + 1  -- A=1 .. K=13

def suitCard (c : Card) : Nat := suit c.val
def rankCard (c : Card) : Nat := rank c.val

def NR : Nat := 6
def ROWS : Nat := 4
def COLS : Nat := 13

end DoubleDeal
