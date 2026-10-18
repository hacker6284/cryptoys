/-
  One tail increment fits in one cell charge, on each shipped tier.
  The numerals are `rfl` / `simp` reductions. The comparison is the kernel's
  `Nat.ble`, not `decide` and not `native_decide`.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.WalkCharge
import EcbsLink2.Link2.FformPointDo
import EcbsLink2.Link2.FrobeniusRead

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

theorem demo_tierR : tierR demo = 2 := by
  simp [tierR, demo_rungs]

theorem toy_tierR : tierR toy = 4 := by
  simp [tierR, toy_rungs]

theorem hobby_tierR : tierR hobby = 5 := by
  simp [tierR, hobby_rungs]

theorem serious_tierR : tierR serious = 7 := by
  simp [tierR, serious_rungs]

private theorem ble_le (a b : Nat) (h : Nat.ble a b = true) : a ≤ b :=
  Nat.le_of_ble_eq_true h

theorem demo_step : stepBudget demo.n demo.benchlen = 109 := by
  simp [stepBudget, demo]

theorem toy_step : stepBudget toy.n toy.benchlen = 745 := by
  simp [stepBudget, toy]

theorem hobby_step : stepBudget hobby.n hobby.benchlen = 4021 := by
  simp [stepBudget, hobby]

theorem serious_step : stepBudget serious.n serious.benchlen = 33661 := by
  simp [stepBudget, serious]

theorem demo_walk : walkCharge demo = 2074 := by
  rw [walkCharge, cellMoveCharge, demo_tierR, demo_row_room]
  simp [rungCharge, pegCharge, mulCharge, tailMoveCap, demo]

theorem toy_walk : walkCharge toy = 28080 := by
  rw [walkCharge, cellMoveCharge, toy_tierR, toy_row_room]
  simp [rungCharge, pegCharge, mulCharge, tailMoveCap, toy]

theorem hobby_walk : walkCharge hobby = 232610 := by
  rw [walkCharge, cellMoveCharge, hobby_tierR, hobby_row_room]
  simp [rungCharge, pegCharge, mulCharge, tailMoveCap, hobby]

theorem serious_walk : walkCharge serious = 2830868 := by
  rw [walkCharge, cellMoveCharge, serious_tierR, serious_row_room]
  simp [rungCharge, pegCharge, mulCharge, tailMoveCap, serious]

theorem demo_slideCharge : cellSlideCharge demo + slideCharge demo.n = 364 := by
  rw [cellSlideCharge, demo_tierR, demo_row_room]
  simp [rungSlideCharge, tailSlideCap, slideCharge, demo]

theorem toy_slideCharge : cellSlideCharge toy + slideCharge toy.n = 4232 := by
  rw [cellSlideCharge, toy_tierR, toy_row_room]
  simp [rungSlideCharge, tailSlideCap, slideCharge, toy]

theorem hobby_slideCharge : cellSlideCharge hobby + slideCharge hobby.n = 36344 := by
  rw [cellSlideCharge, hobby_tierR, hobby_row_room]
  simp [rungSlideCharge, tailSlideCap, slideCharge, hobby]

theorem serious_slideCharge : cellSlideCharge serious + slideCharge serious.n = 448932 := by
  rw [cellSlideCharge, serious_tierR, serious_row_room]
  simp [rungSlideCharge, tailSlideCap, slideCharge, serious]

theorem demo_ctrlCharge : cellCtrlCharge demo + 4 = 80 := by
  rw [cellCtrlCharge, demo_tierR, demo_row_room]

theorem toy_ctrlCharge : cellCtrlCharge toy + 4 = 306 := by
  rw [cellCtrlCharge, toy_tierR, toy_row_room]

theorem hobby_ctrlCharge : cellCtrlCharge hobby + 4 = 1067 := by
  rw [cellCtrlCharge, hobby_tierR, hobby_row_room]

theorem serious_ctrlCharge : cellCtrlCharge serious + 4 = 4251 := by
  rw [cellCtrlCharge, serious_tierR, serious_row_room]

private theorem moves_demo : (872 : Nat) ≤ 2208 := ble_le _ _ rfl
private theorem moves_toy : (5960 : Nat) ≤ 28558 := ble_le _ _ rfl
private theorem moves_hobby : (32168 : Nat) ≤ 233808 := ble_le _ _ rfl
private theorem moves_serious : (269288 : Nat) ≤ 2834466 := ble_le _ _ rfl
private theorem slides_demo : (56 : Nat) ≤ 364 := ble_le _ _ rfl
private theorem slides_toy : (184 : Nat) ≤ 4232 := ble_le _ _ rfl
private theorem slides_hobby : (472 : Nat) ≤ 36344 := ble_le _ _ rfl
private theorem slides_serious : (1432 : Nat) ≤ 448932 := ble_le _ _ rfl
private theorem ctrl_demo : (8 : Nat) ≤ 80 := ble_le _ _ rfl
private theorem ctrl_toy : (8 : Nat) ≤ 306 := ble_le _ _ rfl
private theorem ctrl_hobby : (8 : Nat) ≤ 1067 := ble_le _ _ rfl
private theorem ctrl_serious : (8 : Nat) ≤ 4251 := ble_le _ _ rfl

theorem demo_tail_moves :
    8 * stepBudget demo.n demo.benchlen ≤
      walkCharge demo + (6 * demo.benchlen + 2 * demo.n) := by
  rw [demo_step, demo_walk]
  exact moves_demo

theorem toy_tail_moves :
    8 * stepBudget toy.n toy.benchlen ≤
      walkCharge toy + (6 * toy.benchlen + 2 * toy.n) := by
  rw [toy_step, toy_walk]
  exact moves_toy

theorem hobby_tail_moves :
    8 * stepBudget hobby.n hobby.benchlen ≤
      walkCharge hobby + (6 * hobby.benchlen + 2 * hobby.n) := by
  rw [hobby_step, hobby_walk]
  exact moves_hobby

theorem serious_tail_moves :
    8 * stepBudget serious.n serious.benchlen ≤
      walkCharge serious + (6 * serious.benchlen + 2 * serious.n) := by
  rw [serious_step, serious_walk]
  exact moves_serious

theorem demo_tail_slides :
    8 * demo.n ≤ cellSlideCharge demo + slideCharge demo.n := by
  rw [demo_slideCharge]
  exact slides_demo

theorem toy_tail_slides :
    8 * toy.n ≤ cellSlideCharge toy + slideCharge toy.n := by
  rw [toy_slideCharge]
  exact slides_toy

theorem hobby_tail_slides :
    8 * hobby.n ≤ cellSlideCharge hobby + slideCharge hobby.n := by
  rw [hobby_slideCharge]
  exact slides_hobby

theorem serious_tail_slides :
    8 * serious.n ≤ cellSlideCharge serious + slideCharge serious.n := by
  rw [serious_slideCharge]
  exact slides_serious

theorem demo_tail_ctrl : 8 ≤ cellCtrlCharge demo + 4 := by
  rw [demo_ctrlCharge]
  exact ctrl_demo

theorem toy_tail_ctrl : 8 ≤ cellCtrlCharge toy + 4 := by
  rw [toy_ctrlCharge]
  exact ctrl_toy

theorem hobby_tail_ctrl : 8 ≤ cellCtrlCharge hobby + 4 := by
  rw [hobby_ctrlCharge]
  exact ctrl_hobby

theorem serious_tail_ctrl : 8 ≤ cellCtrlCharge serious + 4 := by
  rw [serious_ctrlCharge]
  exact ctrl_serious

end EcbsLink2.Link2
