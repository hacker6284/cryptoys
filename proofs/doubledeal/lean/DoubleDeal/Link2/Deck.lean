/-
  LINK 2. Grids, rotates, and list updates used by encrypt refinement.
  Proof-only. Not emitter soundness.
-/
import Doubledeal
import DoubleDeal.Grid
import DoubleDeal.Rotate
import DoubleDeal.SumRanks
import DoubleDeal.ShiftRows
import DoubleDeal.Link2.Embed
import DoubleDeal.Link2.Sudo
import DoubleDeal.Link2.Rotate

namespace DoubleDeal.Link2

theorem fits_52 : FitsLen 52 := by
  unfold FitsLen i64MaxNat
  decide

theorem fits52 {n : Nat} (h : n ≤ 52) : FitsLen n :=
  FitsLen.of_le fits_52 h

theorem fits_succ_lt {n m : Nat} (hn : n < m) (hm : m ≤ 52) : FitsLen (n + 1) :=
  fits52 (Nat.succ_le_of_lt (Nat.lt_of_lt_of_le hn hm))

theorem putL_ofNat {α : Type} (a : Array α) (i : Nat) (v : α) (h : i < a.size) :
    SudoRt.putL a (Int.ofNat i) v = .ok (a.set ⟨i, h⟩ v) := by
  unfold SudoRt.putL
  rw [idxCheck_ofNat a.size i h]
  simp only [ok_bind]
  exact dif_pos h

theorem negI_one : SudoRt.negI (1 : Int) = .ok (-1) := by
  unfold SudoRt.negI SudoRt.narrowI
  have hmin : ¬ (-1 : Int) < SudoRt.i64Min := by decide
  have hmax : ¬ (-1 : Int) > SudoRt.i64Max := by decide
  simp [hmin, hmax]

theorem mulI_ofNat (a b : Nat) (h : FitsLen (a * b)) :
    SudoRt.mulI (Int.ofNat a) (Int.ofNat b) = .ok (Int.ofNat (a * b)) := by
  unfold SudoRt.mulI
  have : Int.ofNat a * Int.ofNat b = Int.ofNat (a * b) := by
    simp [ofNat_eq_natCast, Int.ofNat_mul]
  rw [this]
  exact narrowI_ofNat _ h

theorem addI_ofNat (a b : Nat) (h : FitsLen (a + b)) :
    SudoRt.addI (Int.ofNat a) (Int.ofNat b) = .ok (Int.ofNat (a + b)) := by
  unfold SudoRt.addI
  have : Int.ofNat a + Int.ofNat b = Int.ofNat (a + b) := by
    simp [ofNat_eq_natCast]
  rw [this]
  exact narrowI_ofNat _ h

theorem ofNat_not_gt {a b : Nat} (h : a ≤ b) : ¬ (Int.ofNat a > Int.ofNat b) :=
  Int.not_lt.mpr (Int.ofNat_le.mpr h)

theorem beq_ofNat_eq_true_iff (a b : Nat) :
    ((Int.ofNat a) == (Int.ofNat b)) = true ↔ a = b := by
  rw [beq_int_iff, ofNat_eq_natCast, ofNat_eq_natCast]
  exact Int.ofNat_inj

/-- `Int.fmod (a - b) n` is the nonnegative residue when `a, b < n`. -/
theorem fmod_sub_small (a b n : Nat) (ha : a < n) (hb : b < n) (hn : 0 < n) :
    Int.fmod ((a : Int) - (b : Int)) (n : Int) =
      Int.ofNat ((a + (n - b)) % n) := by
  have hn0 : (0 : Int) ≤ (n : Int) := Int.ofNat_zero_le _
  rw [Int.fmod_eq_emod _ hn0]
  have hnat : (a + (n - b)) % n = if b ≤ a then a - b else n - (b - a) := by
    by_cases hba : b ≤ a
    · have : a + (n - b) = n + (a - b) := by omega
      rw [if_pos hba, this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    · rw [if_neg hba, Nat.mod_eq_of_lt (by omega : a + (n - b) < n)]
      omega
  rw [hnat]
  by_cases hba : b ≤ a
  · have hsub : (a : Int) - (b : Int) = Int.ofNat (a - b) := by
      simpa [ofNat_eq_natCast] using (Int.ofNat_sub hba).symm
    have hlt : Int.ofNat (a - b) < Int.ofNat n :=
      Int.ofNat_lt.mpr (by omega : a - b < n)
    rw [if_pos hba, hsub]
    exact Int.emod_eq_of_lt (Int.ofNat_zero_le _) hlt
  · have hk : 0 < b - a := by omega
    have hsub : (a : Int) - (b : Int) = - (Int.ofNat (b - a)) := by
      have hbsub : (b : Int) - (a : Int) = Int.ofNat (b - a) := by
        simpa [ofNat_eq_natCast] using (Int.ofNat_sub (Nat.le_of_not_ge hba)).symm
      omega
    rw [if_neg hba, hsub, Int.neg_emod]
    have hlt : b - a < n := by omega
    have hnonneg : (0 : Int) ≤ (n : Int) - Int.ofNat (b - a) := by
      have : (n : Int) - Int.ofNat (b - a) = Int.ofNat (n - (b - a)) := by
        simpa [ofNat_eq_natCast] using (Int.ofNat_sub (Nat.le_of_lt hlt)).symm
      rw [this]
      exact Int.ofNat_zero_le _
    have hsmall : (n : Int) - Int.ofNat (b - a) < (n : Int) := by
      have hpos : (0 : Int) < Int.ofNat (b - a) := Int.ofNat_pos.mpr hk
      omega
    have hem : ((n : Int) - Int.ofNat (b - a)) % (n : Int) =
        (n : Int) - Int.ofNat (b - a) :=
      Int.emod_eq_of_lt hnonneg hsmall
    have hcast : (n : Int) - Int.ofNat (b - a) = Int.ofNat (n - (b - a)) := by
      simpa [ofNat_eq_natCast] using (Int.ofNat_sub (Nat.le_of_lt hlt)).symm
    rw [hem, hcast]

end DoubleDeal.Link2
