/-
  Room for the four cofactor cells after a search that spent its whole budget.
  The search's moves are at most `perHole · n`, and the same shape bounds
  slides, control, and the ops slots. Four cells add at most four chord
  charges. Each tier is a concrete `Nat.ble` comparison.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.WalkCharge
import EcbsLink2.Link2.SearchPlant

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- Cells in the cofactor walk `[1, 2, 1, 2]`. -/
def cofactorSpan : Nat := 4

private theorem fits_ble (n : Nat) (h : n ≤ 9223372036854775807) : FitsLen n := by
  simpa [FitsLen, i64MaxNat] using h

private theorem demo_cofactor_num :
    perHole demo.n demo.benchlen * demo.n + walkCharge demo * cofactorSpan
      ≤ 9223372036854775807 ∧
    perSlide demo.n * demo.n + cellSlideCharge demo * cofactorSpan
      ≤ 9223372036854775807 ∧
    tierR demo + perCtrl demo.n * demo.n + cellCtrlCharge demo * cofactorSpan
      ≤ 9223372036854775807 ∧
    perOp demo.n * demo.n + cellOpsCharge demo * cofactorSpan
      ≤ 9223372036854775807 := by
  unfold cofactorSpan perHole plantRoom perSlide perCtrl perOp
    walkCharge cellMoveCharge cellSlideCharge cellCtrlCharge cellOpsCharge
    tailMoveCap tailSlideCap pegCharge rungCharge mulCharge rungSlideCharge
  simp only [tierR, demo_rungs, rowRoom, tallyOrigin]
  rw [show demo.n = 7 from rfl, show demo.benchlen = 20 from rfl,
    show demo.control = 16 from rfl, show demo.script = 5 from rfl]
  exact ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl,
    Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩

/-- Demo's search budget plus four cofactor cells fits an i64. -/
theorem demo_cofactor_room :
    FitsLen (perHole demo.n demo.benchlen * demo.n + walkCharge demo * cofactorSpan) ∧
    FitsLen (perSlide demo.n * demo.n + cellSlideCharge demo * cofactorSpan) ∧
    FitsLen (tierR demo + perCtrl demo.n * demo.n + cellCtrlCharge demo * cofactorSpan) ∧
    FitsLen (perOp demo.n * demo.n + cellOpsCharge demo * cofactorSpan) := by
  exact ⟨fits_ble _ demo_cofactor_num.1, fits_ble _ demo_cofactor_num.2.1,
    fits_ble _ demo_cofactor_num.2.2.1, fits_ble _ demo_cofactor_num.2.2.2⟩

private theorem toy_cofactor_num :
    perHole toy.n toy.benchlen * toy.n + walkCharge toy * cofactorSpan
      ≤ 9223372036854775807 ∧
    perSlide toy.n * toy.n + cellSlideCharge toy * cofactorSpan
      ≤ 9223372036854775807 ∧
    tierR toy + perCtrl toy.n * toy.n + cellCtrlCharge toy * cofactorSpan
      ≤ 9223372036854775807 ∧
    perOp toy.n * toy.n + cellOpsCharge toy * cofactorSpan
      ≤ 9223372036854775807 := by
  unfold cofactorSpan perHole plantRoom perSlide perCtrl perOp
    walkCharge cellMoveCharge cellSlideCharge cellCtrlCharge cellOpsCharge
    tailMoveCap tailSlideCap pegCharge rungCharge mulCharge rungSlideCharge
  simp only [tierR, toy_rungs, rowRoom, tallyOrigin]
  rw [show toy.n = 23 from rfl, show toy.benchlen = 72 from rfl,
    show toy.control = 40 from rfl, show toy.script = 15 from rfl]
  exact ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl,
    Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩

/-- Toy's search budget plus four cofactor cells fits an i64. -/
theorem toy_cofactor_room :
    FitsLen (perHole toy.n toy.benchlen * toy.n + walkCharge toy * cofactorSpan) ∧
    FitsLen (perSlide toy.n * toy.n + cellSlideCharge toy * cofactorSpan) ∧
    FitsLen (tierR toy + perCtrl toy.n * toy.n + cellCtrlCharge toy * cofactorSpan) ∧
    FitsLen (perOp toy.n * toy.n + cellOpsCharge toy * cofactorSpan) := by
  exact ⟨fits_ble _ toy_cofactor_num.1, fits_ble _ toy_cofactor_num.2.1,
    fits_ble _ toy_cofactor_num.2.2.1, fits_ble _ toy_cofactor_num.2.2.2⟩

private theorem hobby_cofactor_num :
    perHole hobby.n hobby.benchlen * hobby.n + walkCharge hobby * cofactorSpan
      ≤ 9223372036854775807 ∧
    perSlide hobby.n * hobby.n + cellSlideCharge hobby * cofactorSpan
      ≤ 9223372036854775807 ∧
    tierR hobby + perCtrl hobby.n * hobby.n + cellCtrlCharge hobby * cofactorSpan
      ≤ 9223372036854775807 ∧
    perOp hobby.n * hobby.n + cellOpsCharge hobby * cofactorSpan
      ≤ 9223372036854775807 := by
  unfold cofactorSpan perHole plantRoom perSlide perCtrl perOp
    walkCharge cellMoveCharge cellSlideCharge cellCtrlCharge cellOpsCharge
    tailMoveCap tailSlideCap pegCharge rungCharge mulCharge rungSlideCharge
  simp only [tierR, hobby_rungs, rowRoom, tallyOrigin]
  rw [show hobby.n = 59 from rfl, show hobby.benchlen = 180 from rfl,
    show hobby.control = 80 from rfl, show hobby.script = 15 from rfl]
  exact ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl,
    Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩

/-- Hobby's search budget plus four cofactor cells fits an i64. -/
theorem hobby_cofactor_room :
    FitsLen (perHole hobby.n hobby.benchlen * hobby.n + walkCharge hobby * cofactorSpan) ∧
    FitsLen (perSlide hobby.n * hobby.n + cellSlideCharge hobby * cofactorSpan) ∧
    FitsLen (tierR hobby + perCtrl hobby.n * hobby.n + cellCtrlCharge hobby * cofactorSpan) ∧
    FitsLen (perOp hobby.n * hobby.n + cellOpsCharge hobby * cofactorSpan) := by
  exact ⟨fits_ble _ hobby_cofactor_num.1, fits_ble _ hobby_cofactor_num.2.1,
    fits_ble _ hobby_cofactor_num.2.2.1, fits_ble _ hobby_cofactor_num.2.2.2⟩

private theorem serious_cofactor_num :
    perHole serious.n serious.benchlen * serious.n + walkCharge serious * cofactorSpan
      ≤ 9223372036854775807 ∧
    perSlide serious.n * serious.n + cellSlideCharge serious * cofactorSpan
      ≤ 9223372036854775807 ∧
    tierR serious + perCtrl serious.n * serious.n + cellCtrlCharge serious * cofactorSpan
      ≤ 9223372036854775807 ∧
    perOp serious.n * serious.n + cellOpsCharge serious * cofactorSpan
      ≤ 9223372036854775807 := by
  unfold cofactorSpan perHole plantRoom perSlide perCtrl perOp
    walkCharge cellMoveCharge cellSlideCharge cellCtrlCharge cellOpsCharge
    tailMoveCap tailSlideCap pegCharge rungCharge mulCharge rungSlideCharge
  simp only [tierR, serious_rungs, rowRoom, tallyOrigin]
  rw [show serious.n = 179 from rfl, show serious.benchlen = 540 from rfl,
    show serious.control = 200 from rfl, show serious.script = 15 from rfl]
  exact ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl,
    Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩

/-- Serious's search budget plus four cofactor cells fits an i64. -/
theorem serious_cofactor_room :
    FitsLen (perHole serious.n serious.benchlen * serious.n +
        walkCharge serious * cofactorSpan) ∧
    FitsLen (perSlide serious.n * serious.n + cellSlideCharge serious * cofactorSpan) ∧
    FitsLen (tierR serious + perCtrl serious.n * serious.n +
        cellCtrlCharge serious * cofactorSpan) ∧
    FitsLen (perOp serious.n * serious.n + cellOpsCharge serious * cofactorSpan) := by
  exact ⟨fits_ble _ serious_cofactor_num.1, fits_ble _ serious_cofactor_num.2.1,
    fits_ble _ serious_cofactor_num.2.2.1, fits_ble _ serious_cofactor_num.2.2.2⟩

private theorem demo_after_seat :
    perHole demo.n demo.benchlen * demo.n + 5 * demo.n + walkCharge demo * cofactorSpan
      ≤ 9223372036854775807 ∧
    perSlide demo.n * demo.n + 2 * demo.n + cellSlideCharge demo * cofactorSpan
      ≤ 9223372036854775807 := by
  unfold cofactorSpan perHole plantRoom perSlide walkCharge cellMoveCharge cellSlideCharge
    tailMoveCap tailSlideCap pegCharge rungCharge mulCharge rungSlideCharge
  simp only [tierR, demo_rungs, rowRoom, tallyOrigin]
  rw [show demo.n = 7 from rfl, show demo.benchlen = 20 from rfl,
    show demo.control = 16 from rfl, show demo.script = 5 from rfl]
  exact ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩

private theorem toy_after_seat :
    perHole toy.n toy.benchlen * toy.n + 5 * toy.n + walkCharge toy * cofactorSpan
      ≤ 9223372036854775807 ∧
    perSlide toy.n * toy.n + 2 * toy.n + cellSlideCharge toy * cofactorSpan
      ≤ 9223372036854775807 := by
  unfold cofactorSpan perHole plantRoom perSlide walkCharge cellMoveCharge cellSlideCharge
    tailMoveCap tailSlideCap pegCharge rungCharge mulCharge rungSlideCharge
  simp only [tierR, toy_rungs, rowRoom, tallyOrigin]
  rw [show toy.n = 23 from rfl, show toy.benchlen = 72 from rfl,
    show toy.control = 40 from rfl, show toy.script = 15 from rfl]
  exact ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩

private theorem hobby_after_seat :
    perHole hobby.n hobby.benchlen * hobby.n + 5 * hobby.n + walkCharge hobby * cofactorSpan
      ≤ 9223372036854775807 ∧
    perSlide hobby.n * hobby.n + 2 * hobby.n + cellSlideCharge hobby * cofactorSpan
      ≤ 9223372036854775807 := by
  unfold cofactorSpan perHole plantRoom perSlide walkCharge cellMoveCharge cellSlideCharge
    tailMoveCap tailSlideCap pegCharge rungCharge mulCharge rungSlideCharge
  simp only [tierR, hobby_rungs, rowRoom, tallyOrigin]
  rw [show hobby.n = 59 from rfl, show hobby.benchlen = 180 from rfl,
    show hobby.control = 80 from rfl, show hobby.script = 15 from rfl]
  exact ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩

private theorem serious_after_seat :
    perHole serious.n serious.benchlen * serious.n + 5 * serious.n +
        walkCharge serious * cofactorSpan ≤ 9223372036854775807 ∧
    perSlide serious.n * serious.n + 2 * serious.n +
        cellSlideCharge serious * cofactorSpan ≤ 9223372036854775807 := by
  unfold cofactorSpan perHole plantRoom perSlide walkCharge cellMoveCharge cellSlideCharge
    tailMoveCap tailSlideCap pegCharge rungCharge mulCharge rungSlideCharge
  simp only [tierR, serious_rungs, rowRoom, tallyOrigin]
  rw [show serious.n = 179 from rfl, show serious.benchlen = 540 from rfl,
    show serious.control = 200 from rfl, show serious.script = 15 from rfl]
  exact ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩

/-- The search budget, the seat's extra pegs, and four cofactor cells. Control
    and ops are unchanged by the seat, so they are `cofactor_room`. -/
theorem cofactor_after_seat (t : Spec.Tier)
    (h : t = demo ∨ t = toy ∨ t = hobby ∨ t = serious) :
    FitsLen (perHole t.n t.benchlen * t.n + 5 * t.n + walkCharge t * cofactorSpan) ∧
    FitsLen (perSlide t.n * t.n + 2 * t.n + cellSlideCharge t * cofactorSpan) ∧
    FitsLen (tierR t + perCtrl t.n * t.n + cellCtrlCharge t * cofactorSpan) ∧
    FitsLen (perOp t.n * t.n + cellOpsCharge t * cofactorSpan) := by
  rcases h with rfl | rfl | rfl | rfl
  · exact ⟨fits_ble _ demo_after_seat.1, fits_ble _ demo_after_seat.2,
      demo_cofactor_room.2.2.1, demo_cofactor_room.2.2.2⟩
  · exact ⟨fits_ble _ toy_after_seat.1, fits_ble _ toy_after_seat.2,
      toy_cofactor_room.2.2.1, toy_cofactor_room.2.2.2⟩
  · exact ⟨fits_ble _ hobby_after_seat.1, fits_ble _ hobby_after_seat.2,
      hobby_cofactor_room.2.2.1, hobby_cofactor_room.2.2.2⟩
  · exact ⟨fits_ble _ serious_after_seat.1, fits_ble _ serious_after_seat.2,
      serious_cofactor_room.2.2.1, serious_cofactor_room.2.2.2⟩

private theorem demo_suffix_num :
    perHole demo.n demo.benchlen * demo.n + 5 * demo.n +
        walkCharge demo * (cofactorSpan + 1) ≤ 9223372036854775807 ∧
    perSlide demo.n * demo.n + 2 * demo.n +
        cellSlideCharge demo * (cofactorSpan + 1) ≤ 9223372036854775807 ∧
    tierR demo + perCtrl demo.n * demo.n +
        cellCtrlCharge demo * (cofactorSpan + 1) ≤ 9223372036854775807 ∧
    perOp demo.n * demo.n + cellOpsCharge demo * (cofactorSpan + 1)
        ≤ 9223372036854775807 ∧
    (6 * demo.benchlen + 2 * demo.n) * cofactorSpan ≤ walkCharge demo ∧
    4 * demo.n * cofactorSpan ≤ cellSlideCharge demo ∧
    4 * cofactorSpan ≤ cellCtrlCharge demo ∧
    2 * cofactorSpan + 2 ≤ cellOpsCharge demo := by
  unfold cofactorSpan perHole plantRoom perSlide perCtrl perOp
    walkCharge cellMoveCharge cellSlideCharge cellCtrlCharge cellOpsCharge
    tailMoveCap tailSlideCap pegCharge rungCharge mulCharge rungSlideCharge
  simp only [tierR, demo_rungs, rowRoom, tallyOrigin]
  rw [show demo.n = 7 from rfl, show demo.benchlen = 20 from rfl,
    show demo.control = 16 from rfl, show demo.script = 5 from rfl]
  exact ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl,
    Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl,
    Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl,
    Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩

private theorem toy_suffix_num :
    perHole toy.n toy.benchlen * toy.n + 5 * toy.n +
        walkCharge toy * (cofactorSpan + 1) ≤ 9223372036854775807 ∧
    perSlide toy.n * toy.n + 2 * toy.n +
        cellSlideCharge toy * (cofactorSpan + 1) ≤ 9223372036854775807 ∧
    tierR toy + perCtrl toy.n * toy.n +
        cellCtrlCharge toy * (cofactorSpan + 1) ≤ 9223372036854775807 ∧
    perOp toy.n * toy.n + cellOpsCharge toy * (cofactorSpan + 1)
        ≤ 9223372036854775807 ∧
    (6 * toy.benchlen + 2 * toy.n) * cofactorSpan ≤ walkCharge toy ∧
    4 * toy.n * cofactorSpan ≤ cellSlideCharge toy ∧
    4 * cofactorSpan ≤ cellCtrlCharge toy ∧
    2 * cofactorSpan + 2 ≤ cellOpsCharge toy := by
  unfold cofactorSpan perHole plantRoom perSlide perCtrl perOp
    walkCharge cellMoveCharge cellSlideCharge cellCtrlCharge cellOpsCharge
    tailMoveCap tailSlideCap pegCharge rungCharge mulCharge rungSlideCharge
  simp only [tierR, toy_rungs, rowRoom, tallyOrigin]
  rw [show toy.n = 23 from rfl, show toy.benchlen = 72 from rfl,
    show toy.control = 40 from rfl, show toy.script = 15 from rfl]
  exact ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl,
    Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl,
    Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl,
    Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩

private theorem hobby_suffix_num :
    perHole hobby.n hobby.benchlen * hobby.n + 5 * hobby.n +
        walkCharge hobby * (cofactorSpan + 1) ≤ 9223372036854775807 ∧
    perSlide hobby.n * hobby.n + 2 * hobby.n +
        cellSlideCharge hobby * (cofactorSpan + 1) ≤ 9223372036854775807 ∧
    tierR hobby + perCtrl hobby.n * hobby.n +
        cellCtrlCharge hobby * (cofactorSpan + 1) ≤ 9223372036854775807 ∧
    perOp hobby.n * hobby.n + cellOpsCharge hobby * (cofactorSpan + 1)
        ≤ 9223372036854775807 ∧
    (6 * hobby.benchlen + 2 * hobby.n) * cofactorSpan ≤ walkCharge hobby ∧
    4 * hobby.n * cofactorSpan ≤ cellSlideCharge hobby ∧
    4 * cofactorSpan ≤ cellCtrlCharge hobby ∧
    2 * cofactorSpan + 2 ≤ cellOpsCharge hobby := by
  unfold cofactorSpan perHole plantRoom perSlide perCtrl perOp
    walkCharge cellMoveCharge cellSlideCharge cellCtrlCharge cellOpsCharge
    tailMoveCap tailSlideCap pegCharge rungCharge mulCharge rungSlideCharge
  simp only [tierR, hobby_rungs, rowRoom, tallyOrigin]
  rw [show hobby.n = 59 from rfl, show hobby.benchlen = 180 from rfl,
    show hobby.control = 80 from rfl, show hobby.script = 15 from rfl]
  exact ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl,
    Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl,
    Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl,
    Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩

private theorem serious_suffix_num :
    perHole serious.n serious.benchlen * serious.n + 5 * serious.n +
        walkCharge serious * (cofactorSpan + 1) ≤ 9223372036854775807 ∧
    perSlide serious.n * serious.n + 2 * serious.n +
        cellSlideCharge serious * (cofactorSpan + 1) ≤ 9223372036854775807 ∧
    tierR serious + perCtrl serious.n * serious.n +
        cellCtrlCharge serious * (cofactorSpan + 1) ≤ 9223372036854775807 ∧
    perOp serious.n * serious.n + cellOpsCharge serious * (cofactorSpan + 1)
        ≤ 9223372036854775807 ∧
    (6 * serious.benchlen + 2 * serious.n) * cofactorSpan ≤ walkCharge serious ∧
    4 * serious.n * cofactorSpan ≤ cellSlideCharge serious ∧
    4 * cofactorSpan ≤ cellCtrlCharge serious ∧
    2 * cofactorSpan + 2 ≤ cellOpsCharge serious := by
  unfold cofactorSpan perHole plantRoom perSlide perCtrl perOp
    walkCharge cellMoveCharge cellSlideCharge cellCtrlCharge cellOpsCharge
    tailMoveCap tailSlideCap pegCharge rungCharge mulCharge rungSlideCharge
  simp only [tierR, serious_rungs, rowRoom, tallyOrigin]
  rw [show serious.n = 179 from rfl, show serious.benchlen = 540 from rfl,
    show serious.control = 200 from rfl, show serious.script = 15 from rfl]
  exact ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl,
    Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl,
    Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl,
    Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩

/-- Search, seat, four cofactor cells, and the spare charge `suffix_walk` uses
    so one `walkCharge` can cover every cube. -/
theorem cofactor_suffix_room (t : Spec.Tier)
    (h : t = demo ∨ t = toy ∨ t = hobby ∨ t = serious) :
    FitsLen (perHole t.n t.benchlen * t.n + 5 * t.n +
        walkCharge t * (cofactorSpan + 1)) ∧
    FitsLen (perSlide t.n * t.n + 2 * t.n +
        cellSlideCharge t * (cofactorSpan + 1)) ∧
    FitsLen (tierR t + perCtrl t.n * t.n +
        cellCtrlCharge t * (cofactorSpan + 1)) ∧
    FitsLen (perOp t.n * t.n + cellOpsCharge t * (cofactorSpan + 1)) ∧
    (6 * t.benchlen + 2 * t.n) * cofactorSpan ≤ walkCharge t ∧
    4 * t.n * cofactorSpan ≤ cellSlideCharge t ∧
    4 * cofactorSpan ≤ cellCtrlCharge t ∧
    2 * cofactorSpan + 2 ≤ cellOpsCharge t := by
  rcases h with rfl | rfl | rfl | rfl
  · exact ⟨fits_ble _ demo_suffix_num.1, fits_ble _ demo_suffix_num.2.1,
      fits_ble _ demo_suffix_num.2.2.1, fits_ble _ demo_suffix_num.2.2.2.1,
      demo_suffix_num.2.2.2.2.1, demo_suffix_num.2.2.2.2.2.1,
      demo_suffix_num.2.2.2.2.2.2.1, demo_suffix_num.2.2.2.2.2.2.2⟩
  · exact ⟨fits_ble _ toy_suffix_num.1, fits_ble _ toy_suffix_num.2.1,
      fits_ble _ toy_suffix_num.2.2.1, fits_ble _ toy_suffix_num.2.2.2.1,
      toy_suffix_num.2.2.2.2.1, toy_suffix_num.2.2.2.2.2.1,
      toy_suffix_num.2.2.2.2.2.2.1, toy_suffix_num.2.2.2.2.2.2.2⟩
  · exact ⟨fits_ble _ hobby_suffix_num.1, fits_ble _ hobby_suffix_num.2.1,
      fits_ble _ hobby_suffix_num.2.2.1, fits_ble _ hobby_suffix_num.2.2.2.1,
      hobby_suffix_num.2.2.2.2.1, hobby_suffix_num.2.2.2.2.2.1,
      hobby_suffix_num.2.2.2.2.2.2.1, hobby_suffix_num.2.2.2.2.2.2.2⟩
  · exact ⟨fits_ble _ serious_suffix_num.1, fits_ble _ serious_suffix_num.2.1,
      fits_ble _ serious_suffix_num.2.2.1, fits_ble _ serious_suffix_num.2.2.2.1,
      serious_suffix_num.2.2.2.2.1, serious_suffix_num.2.2.2.2.2.1,
      serious_suffix_num.2.2.2.2.2.2.1, serious_suffix_num.2.2.2.2.2.2.2⟩

private theorem demo_back_num :
    perHole demo.n demo.benchlen * demo.n + 5 * demo.n +
        walkCharge demo * (cofactorSpan + 1) + 6 * demo.n ≤ 9223372036854775807 ∧
    perSlide demo.n * demo.n + 2 * demo.n +
        cellSlideCharge demo * (cofactorSpan + 1) + 4 * demo.n ≤ 9223372036854775807 := by
  unfold cofactorSpan perHole plantRoom perSlide
    walkCharge cellMoveCharge cellSlideCharge
    tailMoveCap tailSlideCap pegCharge rungCharge mulCharge rungSlideCharge
  simp only [tierR, demo_rungs, rowRoom, tallyOrigin]
  rw [show demo.n = 7 from rfl, show demo.benchlen = 20 from rfl,
    show demo.control = 16 from rfl, show demo.script = 5 from rfl]
  exact ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩

private theorem toy_back_num :
    perHole toy.n toy.benchlen * toy.n + 5 * toy.n +
        walkCharge toy * (cofactorSpan + 1) + 6 * toy.n ≤ 9223372036854775807 ∧
    perSlide toy.n * toy.n + 2 * toy.n +
        cellSlideCharge toy * (cofactorSpan + 1) + 4 * toy.n ≤ 9223372036854775807 := by
  unfold cofactorSpan perHole plantRoom perSlide
    walkCharge cellMoveCharge cellSlideCharge
    tailMoveCap tailSlideCap pegCharge rungCharge mulCharge rungSlideCharge
  simp only [tierR, toy_rungs, rowRoom, tallyOrigin]
  rw [show toy.n = 23 from rfl, show toy.benchlen = 72 from rfl,
    show toy.control = 40 from rfl, show toy.script = 15 from rfl]
  exact ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩

private theorem hobby_back_num :
    perHole hobby.n hobby.benchlen * hobby.n + 5 * hobby.n +
        walkCharge hobby * (cofactorSpan + 1) + 6 * hobby.n ≤ 9223372036854775807 ∧
    perSlide hobby.n * hobby.n + 2 * hobby.n +
        cellSlideCharge hobby * (cofactorSpan + 1) + 4 * hobby.n ≤ 9223372036854775807 := by
  unfold cofactorSpan perHole plantRoom perSlide
    walkCharge cellMoveCharge cellSlideCharge
    tailMoveCap tailSlideCap pegCharge rungCharge mulCharge rungSlideCharge
  simp only [tierR, hobby_rungs, rowRoom, tallyOrigin]
  rw [show hobby.n = 59 from rfl, show hobby.benchlen = 180 from rfl,
    show hobby.control = 80 from rfl, show hobby.script = 15 from rfl]
  exact ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩

private theorem serious_back_num :
    perHole serious.n serious.benchlen * serious.n + 5 * serious.n +
        walkCharge serious * (cofactorSpan + 1) + 6 * serious.n ≤ 9223372036854775807 ∧
    perSlide serious.n * serious.n + 2 * serious.n +
        cellSlideCharge serious * (cofactorSpan + 1) + 4 * serious.n
        ≤ 9223372036854775807 := by
  unfold cofactorSpan perHole plantRoom perSlide
    walkCharge cellMoveCharge cellSlideCharge
    tailMoveCap tailSlideCap pegCharge rungCharge mulCharge rungSlideCharge
  simp only [tierR, serious_rungs, rowRoom, tallyOrigin]
  rw [show serious.n = 179 from rfl, show serious.benchlen = 540 from rfl,
    show serious.control = 200 from rfl, show serious.script = 15 from rfl]
  exact ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩

/-- The suffix room plus the four pegs of the move back: two clears (`≤ n`
    each) and two `move_band`s (`≤ 2 · n` each). That is `6 · n` moves and
    `4 · n` slides. Each tier is a `Nat.ble` comparison. -/
theorem cofactor_back_room (t : Spec.Tier)
    (h : t = demo ∨ t = toy ∨ t = hobby ∨ t = serious) :
    FitsLen (perHole t.n t.benchlen * t.n + 5 * t.n +
        walkCharge t * (cofactorSpan + 1) + 6 * t.n) ∧
    FitsLen (perSlide t.n * t.n + 2 * t.n +
        cellSlideCharge t * (cofactorSpan + 1) + 4 * t.n) := by
  rcases h with rfl | rfl | rfl | rfl
  · exact ⟨fits_ble _ demo_back_num.1, fits_ble _ demo_back_num.2⟩
  · exact ⟨fits_ble _ toy_back_num.1, fits_ble _ toy_back_num.2⟩
  · exact ⟨fits_ble _ hobby_back_num.1, fits_ble _ hobby_back_num.2⟩
  · exact ⟨fits_ble _ serious_back_num.1, fits_ble _ serious_back_num.2⟩

end EcbsLink2.Link2
