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
def cofactorCells : Nat := 4

private theorem fits_ble (n : Nat) (h : n ≤ 9223372036854775807) : FitsLen n := by
  simpa [FitsLen, i64MaxNat] using h

private theorem demo_cofactor_num :
    perHole demo.n demo.benchlen * demo.n + walkCharge demo * cofactorCells
      ≤ 9223372036854775807 ∧
    perSlide demo.n * demo.n + cellSlideCharge demo * cofactorCells
      ≤ 9223372036854775807 ∧
    tierR demo + perCtrl demo.n * demo.n + cellCtrlCharge demo * cofactorCells
      ≤ 9223372036854775807 ∧
    perOp demo.n * demo.n + cellOpsCharge demo * cofactorCells
      ≤ 9223372036854775807 := by
  unfold cofactorCells perHole plantRoom perSlide perCtrl perOp
    walkCharge cellMoveCharge cellSlideCharge cellCtrlCharge cellOpsCharge
    tailMoveCap tailSlideCap pegCharge rungCharge mulCharge rungSlideCharge
  simp only [tierR, demo_rungs, rowRoom, tallyOrigin]
  rw [show demo.n = 7 from rfl, show demo.benchlen = 20 from rfl,
    show demo.control = 16 from rfl, show demo.script = 5 from rfl]
  exact ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl,
    Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩

/-- Demo's search budget plus four cofactor cells fits an i64. -/
theorem demo_cofactor_room :
    FitsLen (perHole demo.n demo.benchlen * demo.n + walkCharge demo * cofactorCells) ∧
    FitsLen (perSlide demo.n * demo.n + cellSlideCharge demo * cofactorCells) ∧
    FitsLen (tierR demo + perCtrl demo.n * demo.n + cellCtrlCharge demo * cofactorCells) ∧
    FitsLen (perOp demo.n * demo.n + cellOpsCharge demo * cofactorCells) := by
  exact ⟨fits_ble _ demo_cofactor_num.1, fits_ble _ demo_cofactor_num.2.1,
    fits_ble _ demo_cofactor_num.2.2.1, fits_ble _ demo_cofactor_num.2.2.2⟩

private theorem toy_cofactor_num :
    perHole toy.n toy.benchlen * toy.n + walkCharge toy * cofactorCells
      ≤ 9223372036854775807 ∧
    perSlide toy.n * toy.n + cellSlideCharge toy * cofactorCells
      ≤ 9223372036854775807 ∧
    tierR toy + perCtrl toy.n * toy.n + cellCtrlCharge toy * cofactorCells
      ≤ 9223372036854775807 ∧
    perOp toy.n * toy.n + cellOpsCharge toy * cofactorCells
      ≤ 9223372036854775807 := by
  unfold cofactorCells perHole plantRoom perSlide perCtrl perOp
    walkCharge cellMoveCharge cellSlideCharge cellCtrlCharge cellOpsCharge
    tailMoveCap tailSlideCap pegCharge rungCharge mulCharge rungSlideCharge
  simp only [tierR, toy_rungs, rowRoom, tallyOrigin]
  rw [show toy.n = 23 from rfl, show toy.benchlen = 72 from rfl,
    show toy.control = 40 from rfl, show toy.script = 15 from rfl]
  exact ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl,
    Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩

/-- Toy's search budget plus four cofactor cells fits an i64. -/
theorem toy_cofactor_room :
    FitsLen (perHole toy.n toy.benchlen * toy.n + walkCharge toy * cofactorCells) ∧
    FitsLen (perSlide toy.n * toy.n + cellSlideCharge toy * cofactorCells) ∧
    FitsLen (tierR toy + perCtrl toy.n * toy.n + cellCtrlCharge toy * cofactorCells) ∧
    FitsLen (perOp toy.n * toy.n + cellOpsCharge toy * cofactorCells) := by
  exact ⟨fits_ble _ toy_cofactor_num.1, fits_ble _ toy_cofactor_num.2.1,
    fits_ble _ toy_cofactor_num.2.2.1, fits_ble _ toy_cofactor_num.2.2.2⟩

private theorem hobby_cofactor_num :
    perHole hobby.n hobby.benchlen * hobby.n + walkCharge hobby * cofactorCells
      ≤ 9223372036854775807 ∧
    perSlide hobby.n * hobby.n + cellSlideCharge hobby * cofactorCells
      ≤ 9223372036854775807 ∧
    tierR hobby + perCtrl hobby.n * hobby.n + cellCtrlCharge hobby * cofactorCells
      ≤ 9223372036854775807 ∧
    perOp hobby.n * hobby.n + cellOpsCharge hobby * cofactorCells
      ≤ 9223372036854775807 := by
  unfold cofactorCells perHole plantRoom perSlide perCtrl perOp
    walkCharge cellMoveCharge cellSlideCharge cellCtrlCharge cellOpsCharge
    tailMoveCap tailSlideCap pegCharge rungCharge mulCharge rungSlideCharge
  simp only [tierR, hobby_rungs, rowRoom, tallyOrigin]
  rw [show hobby.n = 59 from rfl, show hobby.benchlen = 180 from rfl,
    show hobby.control = 80 from rfl, show hobby.script = 15 from rfl]
  exact ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl,
    Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩

/-- Hobby's search budget plus four cofactor cells fits an i64. -/
theorem hobby_cofactor_room :
    FitsLen (perHole hobby.n hobby.benchlen * hobby.n + walkCharge hobby * cofactorCells) ∧
    FitsLen (perSlide hobby.n * hobby.n + cellSlideCharge hobby * cofactorCells) ∧
    FitsLen (tierR hobby + perCtrl hobby.n * hobby.n + cellCtrlCharge hobby * cofactorCells) ∧
    FitsLen (perOp hobby.n * hobby.n + cellOpsCharge hobby * cofactorCells) := by
  exact ⟨fits_ble _ hobby_cofactor_num.1, fits_ble _ hobby_cofactor_num.2.1,
    fits_ble _ hobby_cofactor_num.2.2.1, fits_ble _ hobby_cofactor_num.2.2.2⟩

private theorem serious_cofactor_num :
    perHole serious.n serious.benchlen * serious.n + walkCharge serious * cofactorCells
      ≤ 9223372036854775807 ∧
    perSlide serious.n * serious.n + cellSlideCharge serious * cofactorCells
      ≤ 9223372036854775807 ∧
    tierR serious + perCtrl serious.n * serious.n + cellCtrlCharge serious * cofactorCells
      ≤ 9223372036854775807 ∧
    perOp serious.n * serious.n + cellOpsCharge serious * cofactorCells
      ≤ 9223372036854775807 := by
  unfold cofactorCells perHole plantRoom perSlide perCtrl perOp
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
        walkCharge serious * cofactorCells) ∧
    FitsLen (perSlide serious.n * serious.n + cellSlideCharge serious * cofactorCells) ∧
    FitsLen (tierR serious + perCtrl serious.n * serious.n +
        cellCtrlCharge serious * cofactorCells) ∧
    FitsLen (perOp serious.n * serious.n + cellOpsCharge serious * cofactorCells) := by
  exact ⟨fits_ble _ serious_cofactor_num.1, fits_ble _ serious_cofactor_num.2.1,
    fits_ble _ serious_cofactor_num.2.2.1, fits_ble _ serious_cofactor_num.2.2.2⟩

end EcbsLink2.Link2
