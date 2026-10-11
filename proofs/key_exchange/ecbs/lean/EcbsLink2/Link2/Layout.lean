/-
  The lane-fold geometry (SPEC §3 R3). With `n = w·h − 1` and `n − k = w·r`,
  the emitted row/column arithmetic is exactly `e − n` and `e − (n − k)`.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Spec

namespace EcbsLink2.Link2

open EcbsLink2.Spec

/-- Destination of "one band up and one hole on", with the end-of-row carry.
    `Nat` subtraction on `row - h` is only used when the hole does not wrap;
    a wrap uses `row + 1 - h`, which is what `subI` then `addI 1` computes
    when `row = h - 1`. -/
def laneDest (w h e : Nat) : Nat :=
  let row := e / w
  let col := e % w
  if col + 1 = w then (row + 1 - h) * w else (row - h) * w + (col + 1)

/-- "r rows up", same column. -/
def laneDest2 (w r e : Nat) : Nat := (e / w - r) * w + e % w

private theorem div_split (e w : Nat) : e = e / w * w + e % w := by
  rw [Nat.mul_comm]
  exact (Nat.div_add_mod e w).symm

theorem laneDest_eq {w h e : Nat} (hw : 0 < w) (hh : 0 < h) (he : w * h - 1 ≤ e) :
    laneDest w h e = e - (w * h - 1) := by
  unfold laneDest
  have hsplit := div_split e w
  have hmod : e % w < w := Nat.mod_lt e hw
  by_cases hc : e % w + 1 = w
  · simp only [hc, ite_true]
    have hcol : e % w = w - 1 := by omega
    have hsum : e + 1 = (e / w + 1) * w := by
      have heq : e = e / w * w + (w - 1) := by
        conv =>
          lhs
          rw [hsplit]
        rw [hcol]
      calc
        e + 1 = e / w * w + (w - 1) + 1 := by
          conv =>
            lhs
            rw [heq]
        _ = e / w * w + w := by omega
        _ = (e / w + 1) * w := by
          conv =>
            lhs
            arg 2
            rw [← Nat.one_mul w]
          exact (Nat.add_mul (e / w) 1 w).symm
    have hge : h ≤ e / w + 1 := by
      have hmul : w * h ≤ w * (e / w + 1) := by
        rw [Nat.mul_comm w (e / w + 1), ← hsum]
        omega
      exact Nat.le_of_mul_le_mul_left hmul hw
    have hsub : (e / w + 1 - h) * w = (e / w + 1) * w - h * w :=
      Nat.mul_sub_right_distrib _ _ _
    rw [hsub]
    have hshift : (e / w + 1) * w - h * w = (e + 1) - h * w := by rw [hsum]
    rw [hshift, Nat.mul_comm h w]
    have hpos : 0 < w * h := Nat.mul_pos hw hh
    have : w * h = (w * h - 1) + 1 := by omega
    rw [this]
    exact Nat.succ_sub_succ e (w * h - 1)
  · simp only [hc, ite_false]
    have hrow : h ≤ e / w := by
      cases Nat.lt_or_ge (e / w) h with
      | inl hlt =>
        have hlow : e / w ≤ h - 1 := Nat.le_sub_one_of_lt hlt
        have hbound : e ≤ (h - 1) * w + (w - 1) := by
          conv =>
            lhs
            rw [hsplit]
          have h1 : e / w * w ≤ (h - 1) * w := Nat.mul_le_mul_right w hlow
          have h2 : e % w ≤ w - 1 := Nat.le_sub_one_of_lt hmod
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
    have hsub : (e / w - h) * w = e / w * w - h * w := Nat.mul_sub_right_distrib _ _ _
    have hleW : h * w ≤ e / w * w := Nat.mul_le_mul_right w hrow
    have hform : (e / w - h) * w + (e % w + 1) = e + 1 - h * w := by
      rw [hsub, (Nat.sub_add_comm hleW).symm]
      rw [← Nat.add_assoc, ← hsplit]
    have htail : e + 1 - w * h = e - (w * h - 1) := by
      rw [← Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.mul_pos hw hh))]
      exact Nat.succ_sub_succ e (w * h - 1)
    rw [hform, Nat.mul_comm h w, htail]

theorem laneDest2_eq {w r e : Nat} (hw : 0 < w) (hr : r ≤ e / w) :
    laneDest2 w r e = e - r * w := by
  unfold laneDest2
  have hsplit := div_split e w
  have hsub : (e / w - r) * w = e / w * w - r * w := Nat.mul_sub_right_distrib _ _ _
  have hleW : r * w ≤ e / w * w := Nat.mul_le_mul_right w hr
  rw [hsub, (Nat.sub_add_comm hleW).symm, ← hsplit, Nat.mul_comm r w]

end EcbsLink2.Link2
