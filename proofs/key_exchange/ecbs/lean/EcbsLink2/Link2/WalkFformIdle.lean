/-
  An empty key on the F-form walk. Every cell is `0`, so the walk never
  copies the base point. The homes stay, the result is not live, and
  `walkRun` keeps the accumulator. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.WalkFform
import EcbsLink2.Link2.WalkBound
import EcbsLink2.Link2.OpenBoard

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

private theorem base_marker (t : Spec.Tier) (x y : List Nat) :
    (baseBoard t x y).sudo_5Board_6marker = -1 := by
  simp [baseBoard, putAcross, built_marker_down]

private theorem cells_fit (t : Spec.Tier) (tw : TierWalk t) : FitsLen t.cells := by
  apply FitsLen.of_le tw.roomO
  have hpos : 0 < cellOpsCharge t := by
    unfold cellOpsCharge
    omega
  have hmul : t.cells ≤ t.cells * cellOpsCharge t :=
    Nat.le_mul_of_pos_right t.cells hpos
  calc
    t.cells ≤ t.cells * cellOpsCharge t := hmul
    _ ≤ t.cells * cellOpsCharge t + cellOpsCharge t := Nat.le_add_right _ _
    _ = (t.cells + 1) * cellOpsCharge t := by rw [Nat.succ_mul]

/-- Every cell empty. `Ecbs.walk_fform` on `baseBoard` is not live, the homes
    stay, and `walkRun` is `some (false, acc)`. -/
theorem walk_fform_idle (t : Spec.Tier) (x y : List Nat) (cells : List Nat)
    (tw : TierWalk t) (acc : List Nat × List Nat)
    (hlen : cells.length = t.cells) (hz : ∀ c ∈ cells, c = 0) :
    Ecbs.walk_fform (baseBoard t x y) (embed cells) =
        .ok ((false, true),
          { baseBoard t x y with sudo_5Board_9marker_on := false }) ∧
      walkRun t.n t.k t.benchlen (x, y) false acc cells = some (false, acc) := by
  have hfit : FitsLen cells.length := by rw [hlen]; exact cells_fit t tw
  obtain ⟨hch, hrun, _⟩ :=
    walk_fform_zeros (baseBoard t x y) cells t.n t.k t.benchlen (x, y) acc
      hz (base_marker t x y) hfit
  exact ⟨hch, hrun⟩

end EcbsLink2.Link2
