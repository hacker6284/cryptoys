/-
  One lane-fold peg: the emitted row/column arithmetic is `laneDest` / `laneDest2`,
  hence `e - n` and `e - (n - k)`. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.Layout
import EcbsLink2.Link2.Loop

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

private theorem narrow_sub (a b : Nat) (ha : a ≤ 1000000) (hb : b ≤ 1000000) :
    SudoRt.subI (Int.ofNat a) (Int.ofNat b) = .ok ((a : Int) - (b : Int)) := by
  unfold SudoRt.subI
  rw [show Int.ofNat a - Int.ofNat b = (a : Int) - (b : Int) by
    rw [ofNat_eq_natCast a, ofNat_eq_natCast b]]
  exact narrowI_small _ (by omega) (by omega)

private theorem addI_shift (row h : Nat) (hge : h ≤ row + 1) (hpos : 0 < h)
    (hs : row ≤ 1000000) :
    SudoRt.addI ((row : Int) - (h : Int)) (1 : Int) = .ok (Int.ofNat (row + 1 - h)) := by
  unfold SudoRt.addI
  have : Int.ofNat row - Int.ofNat h + 1 = Int.ofNat (row + 1 - h) := by
    by_cases hle : h ≤ row
    · have hsub : Int.ofNat row - Int.ofNat h = Int.ofNat (row - h) := (Int.ofNat_sub hle).symm
      rw [hsub, show (1 : Int) = Int.ofNat 1 from rfl]
      have hadd : Int.ofNat (row - h) + Int.ofNat 1 = Int.ofNat (row - h + 1) :=
        (Int.ofNat_add (row - h) 1).symm
      rw [hadd]
      apply congrArg Int.ofNat
      omega
    · have hlt : row < h := Nat.lt_of_not_le hle
      have heq : h = row + 1 := by omega
      subst heq
      have hsum : Int.ofNat (row + 1) = Int.ofNat row + Int.ofNat 1 := (Int.ofNat_add row 1).symm
      rw [hsum, show Int.ofNat 1 = (1 : Int) from rfl]
      have hzero : Int.ofNat row - (Int.ofNat row + 1) + 1 = 0 := by omega
      rw [hzero, Nat.sub_self, show (0 : Int) = Int.ofNat 0 from rfl]
  have hcast : (row : Int) - (h : Int) = Int.ofNat row - Int.ofNat h := by
    rw [ofNat_eq_natCast row, ofNat_eq_natCast h]
  rw [hcast, this]
  have hle : row + 1 - h ≤ 1000000 := by
    have : row + 1 ≤ row + h := Nat.add_le_add_left (Nat.succ_le_of_lt hpos) row
    exact Nat.le_trans (Nat.sub_le_of_le_add this) hs
  exact narrowI_ofNat (row + 1 - h) (fits_small hle)

private theorem sub_nonneg (a b : Nat) (h : b ≤ a) :
    (a : Int) - (b : Int) = Int.ofNat (a - b) :=
  (Int.ofNat_sub h).symm

private theorem addI_zero (a : Nat) (ha : FitsLen a) :
    SudoRt.addI (Int.ofNat a) (0 : Int) = .ok (Int.ofNat a) := by
  rw [show (0 : Int) = Int.ofNat 0 from rfl, addI_ofNat a 0 (by simpa using ha)]
  simp

private theorem fits_sum (n : Nat) (h : n ≤ 2000000) : FitsLen n := by
  unfold FitsLen i64MaxNat
  omega

private theorem row_ge (w h e : Nat) (hw : 0 < w) (hh : 0 < h) (he : w * h - 1 ≤ e) :
    h - 1 ≤ e / w := by
  have hmul : (h - 1) * w ≤ w * h - 1 := by
    have eq : (h - 1) * w = w * h - w := by
      rw [Nat.mul_sub_right_distrib, Nat.one_mul, Nat.mul_comm h w]
    have : w ≤ w * h := Nat.le_mul_of_pos_right w hh
    omega
  exact (Nat.le_div_iff_mul_le hw).mpr (Nat.le_trans hmul he)

/-- The emitted `d1` / `d2` block, wrap and non-wrap. -/
def foldGeom (w h r e : Nat) : Except SudoRt.Trap (Int × Int) :=
  do
    let row ← SudoRt.divI (Int.ofNat e) (Int.ofNat w)
    let col ← SudoRt.modI (Int.ofNat e) (Int.ofNat w)
    let r1 ← SudoRt.subI row (Int.ofNat h)
    let c1 ← SudoRt.addI col (1 : Int)
    if SudoRt.SEq.beq c1 (Int.ofNat w) then
      do
        let r1 ← SudoRt.addI r1 (1 : Int)
        let c1 := (0 : Int)
        let t ← SudoRt.mulI r1 (Int.ofNat w)
        let d1 ← SudoRt.addI t c1
        let u ← SudoRt.subI row (Int.ofNat r)
        let v ← SudoRt.mulI u (Int.ofNat w)
        let d2 ← SudoRt.addI v col
        pure (d1, d2)
    else
      do
        let t ← SudoRt.mulI r1 (Int.ofNat w)
        let d1 ← SudoRt.addI t c1
        let u ← SudoRt.subI row (Int.ofNat r)
        let v ← SudoRt.mulI u (Int.ofNat w)
        let d2 ← SudoRt.addI v col
        pure (d1, d2)

theorem foldGeom_refines (w h r e : Nat) (hw : 0 < w) (hh : 0 < h) (hr : r < h)
    (he : w * h - 1 ≤ e) (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ e ≤ 1000000) :
    foldGeom w h r e = .ok (Int.ofNat (laneDest w h e), Int.ofNat (laneDest2 w r e)) := by
  have hrw : r ≤ e / w := by
    have := row_ge w h e hw hh he
    have : r ≤ h - 1 := Nat.le_sub_one_of_lt hr
    omega
  have hdiv : e / w ≤ 1000000 := Nat.le_trans (Nat.div_le_self e w) hsm.2.2.2
  have hmod : e % w + 1 ≤ 1000000 := Nat.le_trans (Nat.succ_le_of_lt (Nat.mod_lt e hw)) hsm.1
  unfold foldGeom laneDest laneDest2
  rw [divI_ofNat e (Nat.ne_of_gt hw), ok_bind, modI_ofNat e (Nat.ne_of_gt hw), ok_bind,
    narrow_sub (e / w) h hdiv hsm.2.1, ok_bind,
    addI_ofNat_one (e % w) (fits_small hmod), ok_bind]
  by_cases hc : e % w + 1 = w
  · have hbeq : SudoRt.SEq.beq (Int.ofNat (e % w + 1)) (Int.ofNat w) = true := by
      rw [sEq_ofNat]; simp [hc]
    simp only [hbeq, ite_true, ok_bind]
    have hge : h ≤ e / w + 1 := by
      have := row_ge w h e hw hh he
      omega
    rw [addI_shift (e / w) h hge hh hdiv, ok_bind]
    have hmul : FitsLen ((e / w + 1 - h) * w) := by
      have h1 : (e / w + 1 - h) * w ≤ (e / w + 1) * w :=
        Nat.mul_le_mul_right w (Nat.sub_le _ _)
      have h2 : (e / w + 1) * w = e / w * w + w := by rw [Nat.add_mul, Nat.one_mul]
      have h3 : e / w * w + w ≤ e + w := Nat.add_le_add_right (Nat.div_mul_le_self e w) w
      exact fits_sum _ (Nat.le_trans (Nat.le_trans h1 (by rw [h2]; exact h3))
        (Nat.add_le_add hsm.2.2.2 hsm.1))
    rw [mulI_ofNat (e / w + 1 - h) w hmul, ok_bind, addI_zero _ hmul, ok_bind]
    have hsub : r ≤ e / w := hrw
    have hpR : (e / w - r) * w ≤ 1000000 :=
      Nat.le_trans (Nat.mul_le_mul_right w (Nat.sub_le _ _))
        (Nat.le_trans (Nat.div_mul_le_self e w) hsm.2.2.2)
    have hsumR : (e / w - r) * w + e % w ≤ 2000000 := by
      have h1 : (e / w - r) * w ≤ e / w * w := Nat.mul_le_mul_right w (Nat.sub_le _ _)
      have h2 : e % w ≤ w := Nat.le_of_lt (Nat.mod_lt e hw)
      exact Nat.le_trans (Nat.add_le_add h1 h2)
        (Nat.le_trans (Nat.add_le_add_right (Nat.div_mul_le_self e w) w)
          (Nat.add_le_add hsm.2.2.2 hsm.1))
    rw [narrow_sub (e / w) r hdiv hsm.2.2.1, sub_nonneg (e / w) r hsub, ok_bind,
      mulI_ofNat (e / w - r) w (fits_small hpR), ok_bind,
      addI_ofNat _ (e % w) (fits_sum _ hsumR), ok_bind, pure_eq_ok]
    simp [hc]
  · have hbeq : SudoRt.SEq.beq (Int.ofNat (e % w + 1)) (Int.ofNat w) = false := by
      rw [sEq_ofNat]; simp [hc]
    simp only [hbeq, Bool.false_eq_true, if_false, ok_bind]
    have hsplit : e = e / w * w + e % w := by
      rw [Nat.mul_comm]; exact (Nat.div_add_mod e w).symm
    have hmodLt : e % w < w := Nat.mod_lt e hw
    have hrow : h ≤ e / w := by
      cases Nat.lt_or_ge (e / w) h with
      | inl hlt =>
        have hlow : e / w ≤ h - 1 := Nat.le_sub_one_of_lt hlt
        have hbound : e ≤ (h - 1) * w + (w - 1) := by
          conv => lhs; rw [hsplit]
          have h1 : e / w * w ≤ (h - 1) * w := Nat.mul_le_mul_right w hlow
          have h2 : e % w ≤ w - 1 := Nat.le_sub_one_of_lt hmodLt
          exact Nat.add_le_add h1 h2
        have step : (h - 1) * w + (w - 1) + 1 = (h - 1) * w + w := by omega
        have full : (h - 1) * w + w = h * w := by
          have hadd : (h - 1) * w + 1 * w = ((h - 1) + 1) * w := (Nat.add_mul (h - 1) 1 w).symm
          rw [Nat.one_mul] at hadd
          rw [hadd]
          have : h - 1 + 1 = h := Nat.sub_add_cancel (Nat.succ_le_of_lt hh)
          rw [this]
        have hid : (h - 1) * w + (w - 1) = w * h - 1 := by
          have : (h - 1) * w + (w - 1) + 1 = w * h := by
            rw [step, full, Nat.mul_comm]
          omega
        have hle : e ≤ w * h - 1 := by rwa [← hid]
        have heq : e = w * h - 1 := Nat.le_antisymm hle he
        have hlast : e % w = w - 1 := by
          rw [heq, ← hid, Nat.mul_comm (h - 1) w, Nat.mul_add_mod w (h - 1) (w - 1)]
          exact Nat.mod_eq_of_lt (Nat.pred_lt (Nat.ne_of_gt hw))
        exact absurd (by rw [hlast]; exact Nat.sub_add_cancel (Nat.succ_le_of_lt hw)) hc
      | inr hge => exact hge
    have hp : (e / w - h) * w ≤ 1000000 :=
      Nat.le_trans (Nat.mul_le_mul_right w (Nat.sub_le _ _))
        (Nat.le_trans (Nat.div_mul_le_self e w) hsm.2.2.2)
    have hp2 : (e / w - r) * w ≤ 1000000 :=
      Nat.le_trans (Nat.mul_le_mul_right w (Nat.sub_le _ _))
        (Nat.le_trans (Nat.div_mul_le_self e w) hsm.2.2.2)
    have hsum1 : (e / w - h) * w + (e % w + 1) ≤ 2000000 := by
      have h1 : (e / w - h) * w ≤ e / w * w := Nat.mul_le_mul_right w (Nat.sub_le _ _)
      have h2 : e % w + 1 ≤ w := Nat.succ_le_of_lt (Nat.mod_lt e hw)
      exact Nat.le_trans (Nat.add_le_add h1 h2)
        (Nat.le_trans (Nat.add_le_add_right (Nat.div_mul_le_self e w) w)
          (Nat.add_le_add hsm.2.2.2 hsm.1))
    have hsum2 : (e / w - r) * w + e % w ≤ 2000000 := by
      have h1 : (e / w - r) * w ≤ e / w * w := Nat.mul_le_mul_right w (Nat.sub_le _ _)
      have h2 : e % w ≤ w := Nat.le_of_lt (Nat.mod_lt e hw)
      exact Nat.le_trans (Nat.add_le_add h1 h2)
        (Nat.le_trans (Nat.add_le_add_right (Nat.div_mul_le_self e w) w)
          (Nat.add_le_add hsm.2.2.2 hsm.1))
    rw [sub_nonneg (e / w) h hrow, mulI_ofNat (e / w - h) w (fits_small hp), ok_bind,
      addI_ofNat _ (e % w + 1) (fits_sum _ hsum1), ok_bind,
      narrow_sub (e / w) r hdiv hsm.2.2.1, sub_nonneg (e / w) r hrw, ok_bind,
      mulI_ofNat (e / w - r) w (fits_small hp2), ok_bind,
      addI_ofNat _ (e % w) (fits_sum _ hsum2), ok_bind, pure_eq_ok]
    simp [hc]

/-- Under the layout `n = w·h − 1` and `n − k = w·r`, those indices are the reduction. -/
theorem foldGeom_dest (w h r k e : Nat) (hw : 0 < w) (hh : 0 < h) (hr : r < h)
    (hk : (w * h - 1) - k = w * r) (he : w * h - 1 ≤ e)
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ e ≤ 1000000) :
    foldGeom w h r e =
      .ok (Int.ofNat (e - (w * h - 1)), Int.ofNat (e - ((w * h - 1) - k))) := by
  have hrw : r ≤ e / w := by
    have := row_ge w h e hw hh he
    have : r ≤ h - 1 := Nat.le_sub_one_of_lt hr
    omega
  rw [foldGeom_refines w h r e hw hh hr he hsm, laneDest_eq hw hh he, laneDest2_eq hw hrw,
    Nat.mul_comm r w, ← hk]

end EcbsLink2.Link2
