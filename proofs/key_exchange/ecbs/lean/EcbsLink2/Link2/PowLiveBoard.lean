/-
  The board a nonzero root digit's multiply returns: the lane fold with the
  marker flag put back on. The name is the record update, so the multiply
  closes by `rfl` against that syntax.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.OntoFoldProj

namespace EcbsLink2.Link2

open MegaDreifach.Link2

/-- `ontoFoldBoard` with the script-marker flag on. -/
def powLiveBoard (b : Ecbs.Board) (sch : List Nat) (n k mv peak : Nat) : Ecbs.Board :=
  { ontoFoldBoard b sch n k mv peak with sudo_5Board_9marker_on := true }

theorem powLiveBoard_def (b : Ecbs.Board) (sch : List Nat) (n k mv peak : Nat) :
    powLiveBoard b sch n k mv peak =
      { ontoFoldBoard b sch n k mv peak with sudo_5Board_9marker_on := true } := rfl

/-- Binding the flagged fold is `powLiveBoard`, as a record update. -/
theorem powLive_bind (b : Ecbs.Board) (sch : List Nat) (n k mv peak : Nat) :
    ((Except.ok (ontoFoldBoard b sch n k mv peak) : Except SudoRt.Trap Ecbs.Board) >>=
        fun r =>
          (pure { r with sudo_5Board_9marker_on := true } : Except SudoRt.Trap Ecbs.Board)) =
      (Except.ok (powLiveBoard b sch n k mv peak) : Except SudoRt.Trap Ecbs.Board) := by
  rw [ok_bind, pure_eq_ok, powLiveBoard]

end EcbsLink2.Link2
