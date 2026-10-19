/-
  One projection of `ontoFoldBoard` per declaration. The fold, the hole
  note, and the peak note stay folded; each lemma reads a single field.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.MarkerMul

namespace EcbsLink2.Link2

open MegaDreifach.Link2

@[simp] theorem ontoFoldBoard_home (b : Ecbs.Board) (sch : List Nat) (n k mv peak : Nat) :
    (ontoFoldBoard b sch n k mv peak).sudo_5Board_4home = b.sudo_5Board_4home := by
  unfold ontoFoldBoard peakBoard noteBench withMoves withHole
  split <;> rfl

@[simp] theorem ontoFoldBoard_held (b : Ecbs.Board) (sch : List Nat) (n k mv peak : Nat) :
    (ontoFoldBoard b sch n k mv peak).sudo_5Board_4held = b.sudo_5Board_4held := by
  unfold ontoFoldBoard peakBoard noteBench withMoves withHole
  split <;> rfl

@[simp] theorem ontoFoldBoard_marker (b : Ecbs.Board) (sch : List Nat) (n k mv peak : Nat) :
    (ontoFoldBoard b sch n k mv peak).sudo_5Board_9marker_on = b.sudo_5Board_9marker_on := by
  unfold ontoFoldBoard peakBoard noteBench withMoves withHole
  split <;> rfl

@[simp] theorem ontoFoldBoard_ops (b : Ecbs.Board) (sch : List Nat) (n k mv peak : Nat) :
    (ontoFoldBoard b sch n k mv peak).sudo_5Board_4cost.sudo_5Costs_3ops =
      b.sudo_5Board_4cost.sudo_5Costs_3ops := by
  unfold ontoFoldBoard peakBoard noteBench withMoves withHole
  split <;> rfl

@[simp] theorem ontoFoldBoard_tier (b : Ecbs.Board) (sch : List Nat) (n k mv peak : Nat) :
    (ontoFoldBoard b sch n k mv peak).sudo_5Board_1t = b.sudo_5Board_1t := by
  unfold ontoFoldBoard peakBoard noteBench withMoves withHole
  split <;> rfl

@[simp] theorem ontoFoldBoard_on (b : Ecbs.Board) (sch : List Nat) (n k mv peak : Nat) :
    (ontoFoldBoard b sch n k mv peak).sudo_5Board_8bench_on = b.sudo_5Board_8bench_on := by
  unfold ontoFoldBoard peakBoard noteBench withMoves withHole
  split <;> rfl

@[simp] theorem ontoFoldBoard_to (b : Ecbs.Board) (sch : List Nat) (n k mv peak : Nat) :
    (ontoFoldBoard b sch n k mv peak).sudo_5Board_8bench_to = b.sudo_5Board_8bench_to := by
  unfold ontoFoldBoard peakBoard noteBench withMoves withHole
  split <;> rfl

@[simp] theorem ontoFoldBoard_mark (b : Ecbs.Board) (sch : List Nat) (n k mv peak : Nat) :
    (ontoFoldBoard b sch n k mv peak).sudo_5Board_6marker = b.sudo_5Board_6marker := by
  unfold ontoFoldBoard peakBoard noteBench withMoves withHole
  split <;> rfl

@[simp] theorem ontoFoldBoard_ctrl (b : Ecbs.Board) (sch : List Nat) (n k mv peak : Nat) :
    (ontoFoldBoard b sch n k mv peak).sudo_5Board_4cost.sudo_5Costs_4ctrl =
      b.sudo_5Board_4cost.sudo_5Costs_4ctrl := by
  unfold ontoFoldBoard peakBoard noteBench withMoves withHole
  split <;> rfl

@[simp] theorem ontoFoldBoard_mx (b : Ecbs.Board) (sch : List Nat) (n k mv peak : Nat) :
    (ontoFoldBoard b sch n k mv peak).sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
      b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max := by
  unfold ontoFoldBoard peakBoard noteBench withMoves withHole
  split <;> rfl

@[simp] theorem ontoFoldBoard_strict (b : Ecbs.Board) (sch : List Nat) (n k mv peak : Nat) :
    (ontoFoldBoard b sch n k mv peak).sudo_5Board_4cost.sudo_5Costs_11peak_strict =
      b.sudo_5Board_4cost.sudo_5Costs_11peak_strict := by
  unfold ontoFoldBoard peakBoard noteBench withMoves withHole
  split <;> rfl

/-- The fold's hole is the note taken before the lane is written. -/
theorem ontoFoldBoard_hole (b : Ecbs.Board) (sch : List Nat) (n k mv peak : Nat) :
    (ontoFoldBoard b sch n k mv peak).sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      (noteBench b (Int.ofNat (EcbsLink2.Spec.topIdx sch))
        (Int.ofNat (mv + foldCharge n (n - k) sch))).sudo_5Board_4cost.sudo_5Costs_14max_bench_hole := by
  unfold ontoFoldBoard peakBoard
  rfl

end EcbsLink2.Link2
