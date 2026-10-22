/-
  The fields the next root step reads after a nonzero digit's multiply:
  the up home, the spare, the marker flag, and ops slot 0.
  Each one is a projection of `powLiveBoard`. The fold stays irreducible.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.PowLiveBoard

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

attribute [local irreducible] ontoFoldBoard peakBoard noteBench laneFold

/-- What clear-and-settle reads off the live multiply. -/
structure PowLiveAt (b : Ecbs.Board) (up spare : Nat) (cube : List Nat) (slot0 : Int) : Prop where
  homeUp : b.sudo_5Board_4home[up]? = some (embed cube)
  heldUp : b.sudo_5Board_4held[up]? = some true
  spareHome : b.sudo_5Board_4home[spare]? = some (#[] : Array Int)
  spareHeld : b.sudo_5Board_4held[spare]? = some false
  markerOn : b.sudo_5Board_9marker_on = true
  ops0 : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]? = some slot0

theorem powAt_board (b : Ecbs.Board) (sch : List Nat) (n k mv peak up spare : Nat)
    (cube : List Nat) (slot0 : Int)
    (hUp : b.sudo_5Board_4home[up]? = some (embed cube))
    (hHeld : b.sudo_5Board_4held[up]? = some true)
    (hSpH : b.sudo_5Board_4home[spare]? = some (#[] : Array Int))
    (hSpD : b.sudo_5Board_4held[spare]? = some false)
    (hOps : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]? = some slot0) :
    PowLiveAt (powLiveBoard b sch n k mv peak) up spare cube slot0 := by
  have hHome : (powLiveBoard b sch n k mv peak).sudo_5Board_4home = b.sudo_5Board_4home := by
    simp only [powLiveBoard, ontoFoldBoard_home]
  have hHeldA : (powLiveBoard b sch n k mv peak).sudo_5Board_4held = b.sudo_5Board_4held := by
    simp only [powLiveBoard, ontoFoldBoard_held]
  have hOpsA : (powLiveBoard b sch n k mv peak).sudo_5Board_4cost.sudo_5Costs_3ops =
      b.sudo_5Board_4cost.sudo_5Costs_3ops := by
    simp only [powLiveBoard, ontoFoldBoard_ops]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hHome]; exact hUp
  · rw [hHeldA]; exact hHeld
  · rw [hHome]; exact hSpH
  · rw [hHeldA]; exact hSpD
  · simp only [powLiveBoard]
  · rw [hOpsA]; exact hOps

end EcbsLink2.Link2
