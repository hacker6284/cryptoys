/-
  ECBS Link 2: `coordinate` (SPEC §5.2). Proof-only.
-/
import EcbsLink2.Link2.Basic

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

private theorem half_le (home : Nat) (_hh : home < 7) : demoHalf.getD home 0 ≤ 1 := by
  have h : home = 0 ∨ home = 1 ∨ home = 2 ∨ home = 3 ∨ home = 4 ∨ home = 5 ∨ home = 6 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem lanes_le (home : Nat) (_hh : home < 7) : demoLanes.getD home 0 ≤ 5 := by
  have h : home = 0 ∨ home = 1 ∨ home = 2 ∨ home = 3 ∨ home = 4 ∨ home = 5 ∨ home = 6 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem lanes_pos (home : Nat) (_hh : home < 7) : 0 < demoLanes.getD home 0 := by
  have h : home = 0 ∨ home = 1 ∨ home = 2 ∨ home = 3 ∨ home = 4 ∨ home = 5 ∨ home = 6 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem two_lanes_pos (home : Nat) (hh : home < 7) : 0 < 2 * demoLanes.getD home 0 := by
  have := lanes_pos home hh
  omega

private theorem half_elem (home : Nat)
    (h : home < (#[(0 : Int), 0, 0, 0, 1, 1, 1] : Array Int).size) :
    (#[(0 : Int), 0, 0, 0, 1, 1, 1] : Array Int)[home] =
      Int.ofNat (demoHalf.getD home 0) := by
  have hh : home < 7 := by simp at h; omega
  have hc : home = 0 ∨ home = 1 ∨ home = 2 ∨ home = 3 ∨ home = 4 ∨ home = 5 ∨ home = 6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem lanes_elem (home : Nat)
    (h : home < (#[(2 : Int), 3, 4, 5, 2, 3, 4] : Array Int).size) :
    (#[(2 : Int), 3, 4, 5, 2, 3, 4] : Array Int)[home] =
      Int.ofNat (demoLanes.getD home 0) := by
  have hh : home < 7 := by simp at h; omega
  have hc : home = 0 ∨ home = 1 ∨ home = 2 ∨ home = 3 ∨ home = 4 ∨ home = 5 ∨ home = 6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem demo_row_fits (t : Spec.Tier) (ht : GridOk t) (home i : Nat)
    (hh : home < 7) (hi : i < t.n) : FitsLen (4 * demoHalf.getD home 0 + i / 2) := by
  have hh4 := half_le home hh
  have hdiv : i / 2 ≤ i := Nat.div_le_self _ _
  have hi' : i ≤ t.n := Nat.le_of_lt hi
  exact FitsLen.of_le (fits_of ht.fits_n) (by omega)

private theorem demo_col_fits (t : Spec.Tier) (ht : GridOk t) (home i : Nat)
    (hh : home < 7) (hi : i < t.n) :
    FitsLen (2 * demoLanes.getD home 0 - 1 + i % 2) := by
  have hl := lanes_le home hh
  have hm : i % 2 ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt i (by decide))
  exact FitsLen.of_le (fits_of ht.fits_n) (by omega)

private theorem four_half_fits (home : Nat) (hh : home < 7) :
    FitsLen (4 * demoHalf.getD home 0) :=
  fits_small (by have := half_le home hh; omega)

private theorem two_lanes_fits (home : Nat) (hh : home < 7) :
    FitsLen (2 * demoLanes.getD home 0) :=
  fits_small (by have := lanes_le home hh; omega)

private theorem band_le (home geoper : Nat) (hh : home < 7) : home % geoper ≤ 6 :=
  Nat.le_trans (Nat.mod_le _ _) (Nat.le_of_lt_succ hh)

private theorem unit_le (home geoper : Nat) (hh : home < 7) : home / geoper ≤ 6 :=
  Nat.le_trans (Nat.div_le_self _ _) (Nat.le_of_lt_succ hh)

private theorem two_unit_le (home geoper : Nat) (hh : home < 7) : 2 * (home / geoper) ≤ 12 := by
  have := unit_le home geoper hh
  omega

private theorem two_unit_fits (home geoper : Nat) (hh : home < 7) :
    FitsLen (2 * (home / geoper)) :=
  fits_small (Nat.le_trans (two_unit_le home geoper hh) (by decide))

private theorem mulI_four (b : Nat) (h : FitsLen (4 * b)) :
    SudoRt.mulI (4 : Int) (Int.ofNat b) = .ok (Int.ofNat (4 * b)) :=
  mulI_ofNat 4 b h

private theorem mulI_two (b : Nat) (h : FitsLen (2 * b)) :
    SudoRt.mulI (2 : Int) (Int.ofNat b) = .ok (Int.ofNat (2 * b)) :=
  mulI_ofNat 2 b h

private theorem divI_two (a : Nat) :
    SudoRt.divI (a : Int) (2 : Int) = .ok (Int.ofNat (a / 2)) :=
  divI_cast a (by decide)

private theorem modI_two (a : Nat) :
    SudoRt.modI (a : Int) (2 : Int) = .ok (Int.ofNat (a % 2)) :=
  modI_cast a (by decide)

private theorem row_bound (home i w geoper georows n geofirst : Nat)
    (hh : home < 7) (hi : i < n) :
    home % geoper * georows + i / w ≤ 8 * georows + n + geofirst + 16 := by
  have hb := band_le home geoper hh
  have hmul : home % geoper * georows ≤ 6 * georows := Nat.mul_le_mul_right _ hb
  have hdiv : i / w ≤ i := Nat.div_le_self _ _
  have hi' : i ≤ n := Nat.le_of_lt hi
  omega

private theorem row_fits (t : Spec.Tier) (ht : GridOk t) (home i : Nat)
    (hh : home < 7) (hi : i < t.n) :
    FitsLen (home % t.geoper * t.georows + i / t.w) :=
  FitsLen.of_le (fits_of ht.fits_grid)
    (row_bound home i t.w t.geoper t.georows t.n t.geofirst hh hi)

private theorem band_rows_fits (t : Spec.Tier) (ht : GridOk t) (home : Nat) (hh : home < 7) :
    FitsLen (home % t.geoper * t.georows) := by
  have hb := band_le home t.geoper hh
  have hmul : home % t.geoper * t.georows ≤ 6 * t.georows := Nat.mul_le_mul_right _ hb
  exact FitsLen.of_le (fits_of ht.fits_grid) (by omega)

private theorem g_fits (t : Spec.Tier) (ht : GridOk t) (home : Nat) (hh : home < 7) :
    FitsLen (t.geofirst + 2 * (home / t.geoper)) := by
  have := two_unit_le home t.geoper hh
  exact FitsLen.of_le (fits_of ht.fits_grid) (by omega)

private theorem g1_fits (t : Spec.Tier) (ht : GridOk t) (home : Nat) (hh : home < 7) :
    FitsLen (t.geofirst + 2 * (home / t.geoper) + 1) := by
  have := two_unit_le home t.geoper hh
  exact FitsLen.of_le (fits_of ht.fits_grid) (by omega)

private theorem unit_add_fits (t : Spec.Tier) (ht : GridOk t) (home : Nat) (hh : home < 7) :
    FitsLen (t.geofirst + home / t.geoper) := by
  have := unit_le home t.geoper hh
  exact FitsLen.of_le (fits_of ht.fits_grid) (by omega)

private theorem col10_fits (c : Nat) : FitsLen (c % 10 + 1) :=
  fits_small (by have h := Nat.mod_lt c (by decide : 0 < 10); omega)

private theorem col_fits (t : Spec.Tier) (ht : GridOk t) (i : Nat) (hi : i < t.n) :
    FitsLen (i % t.w + 1) := by
  have hmod : i % t.w ≤ i := Nat.mod_le _ _
  exact FitsLen.of_le (fits_of ht.fits_grid) (by omega)

private theorem dec_nonneg (n : Nat) : decide ((n : Int) ≥ 0) = true := by
  rw [decide_eq_true_eq]; exact Int.ofNat_nonneg _

private theorem mulI_ofNat_cast (a b : Nat) (h : FitsLen (a * b)) :
    SudoRt.mulI (Int.ofNat a) (b : Int) = .ok (Int.ofNat (a * b)) := by
  rw [ofNat_eq_natCast a]
  exact mulI_cast a b h

private theorem addI_cast_ofNat (a b : Nat) (h : FitsLen (a + b)) :
    SudoRt.addI (a : Int) (Int.ofNat b) = .ok (Int.ofNat (a + b)) := by
  rw [ofNat_eq_natCast b]
  exact addI_cast a b h

private theorem modI_ten (a : Nat) :
    SudoRt.modI (Int.ofNat a) (10 : Int) = .ok (Int.ofNat (a % 10)) :=
  modI_ofNat a (by decide)

private theorem dec_ge10 (a : Nat) (h : 10 ≤ a) :
    decide (Int.ofNat a ≥ (10 : Int)) = true := by
  rw [decide_eq_true_eq]
  exact (ofNat_le_iff 10 a).mpr h

private theorem dec_not_ge10 (a : Nat) (h : ¬ 10 ≤ a) :
    decide (Int.ofNat a ≥ (10 : Int)) = false := by
  rw [decide_eq_false_iff_not]
  intro hle
  exact h ((ofNat_le_iff 10 a).mp hle)

/-- §5.2. For `home < 7` and `i < n`, on a tier whose non-Demo geometry divides
    (`w` and `geoper` positive) and whose products fit an i64, `coordinate` is the model. -/
theorem coordinate_refines (t : Spec.Tier) (ht : GridOk t) (home i : Nat)
    (hh : home < 7) (hi : i < t.n) :
    Ecbs.coordinate (embTier t) (home : Int) (i : Int) =
      .ok (embHole (Spec.coordinate t home i)) := by
  unfold Ecbs.coordinate Spec.coordinate embHole
  have hnfield : (embTier t).sudo_4Tier_1n = (t.n : Int) := rfl
  have hdemo : (embTier t).sudo_4Tier_4demo = t.demo := rfl
  have hdouble : (embTier t).sudo_4Tier_9geodouble = t.geodouble := rfl
  have hwfield : (embTier t).sudo_4Tier_1w = (t.w : Int) := rfl
  have hgfield : (embTier t).sudo_4Tier_6geoper = (t.geoper : Int) := rfl
  have hrfield : (embTier t).sudo_4Tier_7georows = (t.georows : Int) := rfl
  have hffeld : (embTier t).sudo_4Tier_8geofirst = (t.geofirst : Int) := rfl
  have hH : decide ((home : Int) < 7) = true := by
    rw [decide_eq_true_eq, ← ofNat_eq_natCast home, show (7 : Int) = Int.ofNat 7 from rfl]
    exact (ofNat_lt_iff home 7).mpr hh
  rw [dec_nonneg home, if_pos rfl, pure_eq_ok, ok_bind, hH, if_pos rfl, pure_eq_ok, ok_bind,
    dec_nonneg i, if_pos rfl, pure_eq_ok, ok_bind]
  have hIi : decide ((i : Int) < (t.n : Int)) = true := by
    rw [decide_eq_true_eq, ← ofNat_eq_natCast i, ← ofNat_eq_natCast t.n]
    exact (ofNat_lt_iff i t.n).mpr hi
  rw [hnfield, hIi]
  simp only [if_true, pure_eq_ok, ok_bind, sudoAssert_true]
  rw [hdemo]
  by_cases hd : t.demo
  · simp only [hd, ite_true]
    have hhalf : home < (#[(0 : Int), 0, 0, 0, 1, 1, 1] : Array Int).size := by simp; omega
    have hlanes : home < (#[(2 : Int), 3, 4, 5, 2, 3, 4] : Array Int).size := by simp; omega
    have hatH := atL_ofNat (#[(0 : Int), 0, 0, 0, 1, 1, 1] : Array Int) home hhalf
    have hatL := atL_ofNat (#[(2 : Int), 3, 4, 5, 2, 3, 4] : Array Int) home hlanes
    simp only [ofNat_eq_natCast] at hatH hatL
    rw [hatH, hatL, half_elem home hhalf, lanes_elem home hlanes]
    simp only [ok_bind]
    rw [mulI_four _ (four_half_fits home hh), ok_bind,
      divI_two i, ok_bind,
      addI_ofNat _ _ (demo_row_fits t ht home i hh hi), ok_bind,
      mulI_two _ (two_lanes_fits home hh), ok_bind,
      subI_ofNat_one _ (two_lanes_pos home hh) (two_lanes_fits home hh), ok_bind,
      modI_two i, ok_bind,
      addI_ofNat _ _ (demo_col_fits t ht home i hh hi), ok_bind]
    rfl
  · have hdf : t.demo = false := eq_false_of_ne_true hd
    simp only [hdf, Bool.false_eq_true, ite_false, if_false]
    rw [hwfield, hgfield, hrfield, hffeld, hdouble]
    have hw := ht.w_pos hd
    have hg := ht.geoper_pos hd
    rw [divI_cast home (Nat.ne_of_gt hg), modI_cast home (Nat.ne_of_gt hg),
      divI_cast i (Nat.ne_of_gt hw), modI_cast i (Nat.ne_of_gt hw)]
    simp only [ok_bind]
    rw [mulI_ofNat_cast _ _ (band_rows_fits t ht home hh), ok_bind,
      addI_ofNat _ _ (row_fits t ht home i hh hi), ok_bind]
    by_cases hgd : t.geodouble
    · simp only [hgd, ite_true]
      rw [mulI_two _ (two_unit_fits home t.geoper hh), ok_bind,
        addI_cast_ofNat _ _ (g_fits t ht home hh), ok_bind]
      by_cases hc : 10 ≤ i % t.w
      · rw [dec_ge10 _ hc]
        simp only [ite_true, if_true]
        rw [addI_ofNat_one _ (g1_fits t ht home hh), ok_bind,
          modI_ten _, ok_bind,
          addI_ofNat_one _ (col10_fits _), ok_bind, if_pos hc]
      · rw [dec_not_ge10 _ hc]
        simp only [Bool.false_eq_true, ite_false, if_false, if_neg hc, Nat.add_zero]
        rw [modI_ten _, ok_bind, addI_ofNat_one _ (col10_fits _), ok_bind]
    · have hgdf : t.geodouble = false := eq_false_of_ne_true hgd
      simp only [hgdf, Bool.false_eq_true, ite_false, if_false]
      rw [addI_cast_ofNat _ _ (unit_add_fits t ht home hh), ok_bind,
        addI_ofNat_one _ (col_fits t ht i hi), ok_bind]

end EcbsLink2.Link2
