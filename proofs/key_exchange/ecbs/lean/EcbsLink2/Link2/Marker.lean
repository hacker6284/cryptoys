/-
  `marker_step` is the script-marker frame around a cube or a multiply.
  It writes the marker index, the control counter, and the script-marker max.
  Every field a cube, a multiply, or an add reads or writes stays put.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.Loop

namespace EcbsLink2.Link2

open MegaDreifach.Link2

/-- The marker is already up (`marker < 0`, the state `marker_lift` leaves).
    `marker_step` seats it at hole 0, charges one control move, and raises the
    recorded max when `1` passes it. -/
theorem marker_step_down (b : Ecbs.Board) (ctrl mx script : Nat)
    (hm : b.sudo_5Board_6marker < 0)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hs : b.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script)
    (hpos : 0 < script)
    (hfit : FitsLen (ctrl + 1)) :
    Ecbs.marker_step b =
      .ok { b with
        sudo_5Board_6marker := 0
        sudo_5Board_4cost := { b.sudo_5Board_4cost with
          sudo_5Costs_4ctrl := Int.ofNat (ctrl + 1)
          sudo_5Costs_17script_marker_max := Int.ofNat (max mx 1) } } := by
  unfold Ecbs.marker_step
  have hdec : decide (b.sudo_5Board_6marker < (0 : Int)) = true := decide_eq_true hm
  rw [hdec, if_pos rfl]
  dsimp
  rw [hc, addI_ofNat_one ctrl hfit, ok_bind]
  have hs0 : decide ((0 : Int) < Int.ofNat script) = true := by
    rw [decide_eq_true_eq, show (0 : Int) = Int.ofNat 0 from rfl, ofNat_lt_iff]
    exact hpos
  rw [hs, hs0, sudoAssert_true, ok_bind]
  rw [show (0 : Int) = Int.ofNat 0 from rfl, addI_ofNat_one 0 (fits_small (by decide)), ok_bind]
  rw [hx]
  by_cases hlt : mx < 1
  · have hgt : decide (Int.ofNat 1 > Int.ofNat mx) = true := by
      rw [decide_eq_true_eq, gt_iff_lt, ofNat_lt_iff]
      exact hlt
    rw [hgt, if_pos rfl, ok_bind, pure_eq_ok]
    have hmax : max mx 1 = 1 := Nat.max_eq_right (Nat.le_of_lt hlt)
    simp [Nat.zero_add, hmax]
  · have hge : ¬ mx < 1 := hlt
    have hgt : decide (Int.ofNat 1 > Int.ofNat mx) = false := by
      rw [decide_eq_false_iff_not, gt_iff_lt, ofNat_lt_iff]
      exact hge
    rw [hgt]
    simp only [Bool.false_eq_true, if_false, pure_eq_ok]
    have hmax : max mx 1 = mx := Nat.max_eq_left (by omega)
    simp [hmax]

/-- The marker is on the script (`marker = m`). `marker_step` advances it one
    hole, charges two control moves, and raises the recorded max when the next
    hole passes it. The assert is `m + 1 < script`. -/
theorem marker_step_up (b : Ecbs.Board) (m ctrl mx script : Nat)
    (hm : b.sudo_5Board_6marker = Int.ofNat m)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hs : b.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script)
    (hbound : m + 1 < script)
    (hfitM : FitsLen (m + 1))
    (hfitC : FitsLen (ctrl + 2))
    (hfit2 : FitsLen (m + 2)) :
    Ecbs.marker_step b =
      .ok { b with
        sudo_5Board_6marker := Int.ofNat (m + 1)
        sudo_5Board_4cost := { b.sudo_5Board_4cost with
          sudo_5Costs_4ctrl := Int.ofNat (ctrl + 2)
          sudo_5Costs_17script_marker_max := Int.ofNat (max mx (m + 2)) } } := by
  unfold Ecbs.marker_step
  rw [hm]
  have hdec : decide (Int.ofNat m < (0 : Int)) = false := by
    rw [decide_eq_false_iff_not]
    exact fun h => absurd h (Int.not_lt.mpr (Int.ofNat_nonneg m))
  rw [hdec]
  simp only [Bool.false_eq_true, if_false]
  dsimp
  rw [← ofNat_eq_natCast m, addI_ofNat_one m hfitM, ok_bind, hc]
  rw [show (2 : Int) = Int.ofNat 2 from rfl, addI_ofNat ctrl 2 hfitC, ok_bind]
  have hlt : decide (Int.ofNat (m + 1) < Int.ofNat script) = true := by
    rw [decide_eq_true_eq, ofNat_lt_iff]
    exact hbound
  rw [hs, hlt, sudoAssert_true, ok_bind]
  rw [← ofNat_eq_natCast (m + 1), addI_ofNat_one (m + 1) hfit2, ok_bind]
  rw [hx]
  by_cases hlt2 : mx < m + 2
  · have hgt : decide (Int.ofNat (m + 2) > Int.ofNat mx) = true := by
      rw [decide_eq_true_eq, gt_iff_lt, ofNat_lt_iff]
      exact hlt2
    rw [hgt, if_pos rfl, ok_bind, pure_eq_ok]
    have hmax : max mx (m + 2) = m + 2 := Nat.max_eq_right (Nat.le_of_lt hlt2)
    have hadd : m + 1 + 1 = m + 2 := by omega
    simp [hadd, hmax]
  · have hgt : decide (Int.ofNat (m + 2) > Int.ofNat mx) = false := by
      rw [decide_eq_false_iff_not, gt_iff_lt, ofNat_lt_iff]
      exact hlt2
    rw [hgt]
    simp only [Bool.false_eq_true, if_false, pure_eq_ok]
    have hmax : max mx (m + 2) = mx := Nat.max_eq_left (by omega)
    simp [hmax]

/-- Seating a lifted marker leaves the card alone: homes, held flags, the bench,
    the tier, the move and peak counters, and the op tally. -/
theorem marker_step_down_frame (b : Ecbs.Board) (ctrl mx script : Nat)
    (hm : b.sudo_5Board_6marker < 0)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hs : b.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script)
    (hpos : 0 < script)
    (hfit : FitsLen (ctrl + 1)) :
    ∃ b', Ecbs.marker_step b = .ok b' ∧
      b'.sudo_5Board_4home = b.sudo_5Board_4home ∧
      b'.sudo_5Board_4held = b.sudo_5Board_4held ∧
      b'.sudo_5Board_8bench_on = b.sudo_5Board_8bench_on ∧
      b'.sudo_5Board_8bench_to = b.sudo_5Board_8bench_to ∧
      b'.sudo_5Board_5bench = b.sudo_5Board_5bench ∧
      b'.sudo_5Board_1t = b.sudo_5Board_1t ∧
      b'.sudo_5Board_9marker_on = b.sudo_5Board_9marker_on ∧
      b'.sudo_5Board_3row = b.sudo_5Board_3row ∧
      b'.sudo_5Board_4cost.sudo_5Costs_5moves = b.sudo_5Board_4cost.sudo_5Costs_5moves ∧
      b'.sudo_5Board_4cost.sudo_5Costs_6slides = b.sudo_5Board_4cost.sudo_5Costs_6slides ∧
      b'.sudo_5Board_4cost.sudo_5Costs_4peak = b.sudo_5Board_4cost.sudo_5Costs_4peak ∧
      b'.sudo_5Board_4cost.sudo_5Costs_11peak_strict =
        b.sudo_5Board_4cost.sudo_5Costs_11peak_strict ∧
      b'.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
        b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole ∧
      b'.sudo_5Board_4cost.sudo_5Costs_3ops = b.sudo_5Board_4cost.sudo_5Costs_3ops ∧
      b'.sudo_5Board_6marker = 0 ∧
      b'.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (ctrl + 1) ∧
      b'.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat (max mx 1) := by
  refine ⟨_, marker_step_down b ctrl mx script hm hc hx hs hpos hfit,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Advancing a seated marker leaves the same card fields. -/
theorem marker_step_up_frame (b : Ecbs.Board) (m ctrl mx script : Nat)
    (hm : b.sudo_5Board_6marker = Int.ofNat m)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hs : b.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script)
    (hbound : m + 1 < script)
    (hfitM : FitsLen (m + 1))
    (hfitC : FitsLen (ctrl + 2))
    (hfit2 : FitsLen (m + 2)) :
    ∃ b', Ecbs.marker_step b = .ok b' ∧
      b'.sudo_5Board_4home = b.sudo_5Board_4home ∧
      b'.sudo_5Board_4held = b.sudo_5Board_4held ∧
      b'.sudo_5Board_8bench_on = b.sudo_5Board_8bench_on ∧
      b'.sudo_5Board_8bench_to = b.sudo_5Board_8bench_to ∧
      b'.sudo_5Board_5bench = b.sudo_5Board_5bench ∧
      b'.sudo_5Board_1t = b.sudo_5Board_1t ∧
      b'.sudo_5Board_9marker_on = b.sudo_5Board_9marker_on ∧
      b'.sudo_5Board_3row = b.sudo_5Board_3row ∧
      b'.sudo_5Board_4cost.sudo_5Costs_5moves = b.sudo_5Board_4cost.sudo_5Costs_5moves ∧
      b'.sudo_5Board_4cost.sudo_5Costs_6slides = b.sudo_5Board_4cost.sudo_5Costs_6slides ∧
      b'.sudo_5Board_4cost.sudo_5Costs_4peak = b.sudo_5Board_4cost.sudo_5Costs_4peak ∧
      b'.sudo_5Board_4cost.sudo_5Costs_11peak_strict =
        b.sudo_5Board_4cost.sudo_5Costs_11peak_strict ∧
      b'.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
        b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole ∧
      b'.sudo_5Board_4cost.sudo_5Costs_3ops = b.sudo_5Board_4cost.sudo_5Costs_3ops ∧
      b'.sudo_5Board_6marker = Int.ofNat (m + 1) ∧
      b'.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (ctrl + 2) ∧
      b'.sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
        Int.ofNat (max mx (m + 2)) := by
  refine ⟨_, marker_step_up b m ctrl mx script hm hc hx hs hbound hfitM hfitC hfit2,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `log_op` with the marker off is the identity. -/
theorem log_op_off (b : Ecbs.Board) (hmk : b.sudo_5Board_9marker_on = false) :
    Ecbs.log_op b = .ok b := by
  unfold Ecbs.log_op
  simp [hmk, pure_eq_ok]

/-- `log_op` with the marker on is `marker_step`. -/
theorem log_op_on (b : Ecbs.Board) (hmk : b.sudo_5Board_9marker_on = true) :
    Ecbs.log_op b = Ecbs.marker_step b := by
  unfold Ecbs.log_op
  simp [hmk]

end EcbsLink2.Link2
