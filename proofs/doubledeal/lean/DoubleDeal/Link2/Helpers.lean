/-
  LINK 2. Generated helpers refine the algebraic stones on the well-formed
  domain. Proof-only. Not emitter soundness.
-/
import Doubledeal
import DoubleDeal.Basic
import DoubleDeal.Rotate
import DoubleDeal.Link2.Embed
import DoubleDeal.Link2.Sudo

namespace DoubleDeal.Link2

theorem suit_of_refines (c : Nat) :
    Doubledeal.suit_of (Int.ofNat c) = .ok (Int.ofNat (DoubleDeal.suit c)) := by
  unfold Doubledeal.suit_of DoubleDeal.suit
  exact divI_ofNat c (by decide : (13 : Nat) ≠ 0)

theorem rank_of_refines (c : Nat) :
    Doubledeal.rank_of (Int.ofNat c) = .ok (Int.ofNat (DoubleDeal.rank c)) := by
  have hmod : SudoRt.modI (Int.ofNat c) 13 = .ok (Int.ofNat (c % 13)) :=
    modI_ofNat c (by decide : (13 : Nat) ≠ 0)
  have hfits : FitsLen (c % 13 + 1) := by
    have : c % 13 ≤ 12 := Nat.lt_succ_iff.mp (Nat.mod_lt c (by decide : 0 < 13))
    exact Nat.le_trans (Nat.succ_le_succ this) (by decide : 13 ≤ i64MaxNat)
  have hadd : SudoRt.addI (Int.ofNat (c % 13)) 1 = .ok (Int.ofNat (c % 13 + 1)) :=
    addI_ofNat_one (c % 13) hfits
  unfold Doubledeal.rank_of
  rw [hmod]
  simp only [ok_bind]
  rw [hadd]
  rfl

/-- Generated cut-predicate: nonempty pile and `rank c < length`. -/
theorem suit_of_refines_natCast (c : Nat) :
    Doubledeal.suit_of (c : Int) = .ok (Int.ofNat (DoubleDeal.suit c)) := by
  rw [← ofNat_eq_natCast c]
  exact suit_of_refines c

theorem rank_of_refines_natCast (c : Nat) :
    Doubledeal.rank_of (c : Int) = .ok (Int.ofNat (DoubleDeal.rank c)) := by
  rw [← ofNat_eq_natCast c]
  exact rank_of_refines c

theorem rank_lt_flag (c : Nat) (xs : List Nat) :
    (if decide (SudoRt.listLen (embed xs) > (0 : Int)) then
      (do
        let r ← Doubledeal.rank_of (Int.ofNat c)
        pure (decide (r < SudoRt.listLen (embed xs))))
     else pure false) =
      Except.ok (decide (0 < xs.length ∧ DoubleDeal.rank c < xs.length)) := by
  rw [listLen_pos_decide]
  by_cases hpos : 0 < xs.length
  · rw [decide_eq_true hpos]
    simp only []
    rw [rank_of_refines]
    simp only [ok_bind, listLen_embed, decide_ofNat_lt]
    simp [hpos]
    rfl
  · rw [decide_eq_false hpos]
    simp [hpos]
    rfl

end DoubleDeal.Link2
