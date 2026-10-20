/-
  One live cell's Frobenius, paid from the counters already on the board.
  `cellsLeft` is how many cells of this suffix remain, including this one.
  The fresh key spends `t.cells + 1` at the opening seat and `t.cells - i`
  here. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.CellRun
import EcbsLink2.Link2.WalkCharge

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

private theorem room_one (a c k : Nat) (hk : 0 < k) (h : FitsLen (a + c * k)) :
    FitsLen (a + c) := by
  apply FitsLen.of_le h
  have hc : c * 1 ≤ c * k := Nat.mul_le_mul_left c hk
  simpa using hc

private theorem cube_in_walk (t : Spec.Tier) :
    cubeCharge t.n t.benchlen + 3 * t.n ≤ walkCharge t := by
  unfold walkCharge cellMoveCharge cubeCharge pegCharge
  omega

private theorem slide_in_cell (t : Spec.Tier) : slideCharge t.n ≤ cellSlideCharge t := by
  unfold slideCharge cellSlideCharge tailSlideCap
  omega

private theorem ctrl_in_cell (t : Spec.Tier) : 5 ≤ cellCtrlCharge t := by
  unfold cellCtrlCharge
  omega

private theorem ops_in_cell (t : Spec.Tier) : 2 ≤ cellOpsCharge t := by
  unfold cellOpsCharge
  omega

private theorem spend_mul (moves moves' c rem : Nat) (hrem : 0 < rem)
    (hm : moves' ≤ moves + c) (h : FitsLen (moves + c * rem)) :
    FitsLen (moves' + c * (rem - 1)) := by
  have hcomm : FitsLen (moves + rem * c) := by simpa [Nat.mul_comm] using h
  have hsucc := ctrl_room_succ moves moves' rem c hrem hm hcomm
  simpa [Nat.mul_comm] using hsucc

/-- Frobenius of one live cell. The four rooms shrink by one charge. -/
theorem suffix_frob (t : Spec.Tier) (b : Ecbs.Board)
    (baseX accX baseY accY : List Nat) (fr : RunFrame b t baseX accX)
    (cellsLeft : Nat) (hOk : BoardOk t) (sat : TierSat t) (hsh : TierShape t)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hY : fr.y4 = baseY) (hA : fr.y1 = accY)
    (hf4 : fr.flag4 = true) (hf1 : fr.flag1 = true)
    (hyA : accY.length = t.n) (htriY : allTritList accY)
    (hleft : 0 < cellsLeft)
    (hst : fr.peakS ≤ 7) (hhole : fr.hole ≤ t.benchlen)
    (hM : FitsLen (fr.moves + walkCharge t * cellsLeft))
    (hS : FitsLen (fr.slides + cellSlideCharge t * cellsLeft))
    (hO : FitsLen (fr.opsCap + cellOpsCharge t * cellsLeft))
    (hC : FitsLen (fr.ctrl + cellCtrlCharge t * cellsLeft)) :
    ∃ bL bF, ∃ fr' : RunFrame bF t baseX (fieldCube t.n t.k t.benchlen accX),
      Ecbs.marker_lift b = .ok bL ∧
      Ecbs.frobenius_affine bL = .ok bF ∧
      bF.sudo_5Board_9marker_on = true ∧
      fr'.y1 = fieldCube t.n t.k t.benchlen accY ∧
      fr'.y4 = baseY ∧
      fr'.flag1 = true ∧
      fr'.flag4 = true ∧
      fr'.moves ≤ fr.moves + cubeCharge t.n t.benchlen ∧
      fr'.slides ≤ fr.slides + slideCharge t.n ∧
      fr'.ctrl = fr.ctrl + 4 ∧
      fr'.opsCap = fr.opsCap + 2 ∧
      fr'.peakS ≤ 7 ∧
      fr'.hole ≤ t.benchlen ∧
      FitsLen (fr'.moves + walkCharge t * (cellsLeft - 1)) ∧
      FitsLen (fr'.slides + cellSlideCharge t * (cellsLeft - 1)) ∧
      FitsLen (fr'.opsCap + cellOpsCharge t * (cellsLeft - 1)) ∧
      FitsLen (fr'.ctrl + cellCtrlCharge t * (cellsLeft - 1)) := by
  have hMove : FitsLen (fr.moves + cubeCharge t.n t.benchlen + 3 * t.n) := by
    have h1 := room_one fr.moves (walkCharge t) cellsLeft hleft hM
    apply FitsLen.of_le h1
    have hcu := cube_in_walk t
    omega
  have hSlide : FitsLen (fr.slides + slideCharge t.n) := by
    have h1 := room_one fr.slides (cellSlideCharge t) cellsLeft hleft hS
    apply FitsLen.of_le h1
    have hslC := slide_in_cell t
    omega
  have hCtrl : FitsLen (fr.ctrl + 5) := by
    have h1 := room_one fr.ctrl (cellCtrlCharge t) cellsLeft hleft hC
    apply FitsLen.of_le h1
    have hc5 := ctrl_in_cell t
    omega
  have hOps : FitsLen (fr.opsCap + 2) := by
    have h1 := room_one fr.opsCap (cellOpsCharge t) cellsLeft hleft hO
    apply FitsLen.of_le h1
    have hop := ops_in_cell t
    omega
  obtain ⟨bL, bF, fr', hml, hfrob, hmk', hy1, hy4, hf1', hf4', hctrl, _hmark,
      _hcOps, _hchord, hmv, hsl, hops, hheld, ⟨occU, hocc, hpeak⟩, hholeEq,
      htopX, htopY⟩ :=
    cell_run_frame b t baseX accX baseY accY fr hOk sat hsh hmk hY hA hf4 hf1
      hyA htriY hMove hSlide hCtrl hOps
  have hst' : fr'.peakS ≤ 7 := by
    rw [hpeak]
    exact strict_out_le fr.peakS (countHeld b.sudo_5Board_4held 7) occU hst hheld hocc
  have hho' : fr'.hole ≤ t.benchlen := by
    rw [hholeEq]
    exact hole_out_le fr.hole (topIdx (combStrip t.n t.benchlen accX))
      (topIdx (combStrip t.n t.benchlen accY)) t.benchlen hhole htopX htopY
  refine ⟨bL, bF, fr', hml, hfrob, hmk', hy1, hy4, hf1', hf4', hmv, hsl, hctrl, hops,
    hst', hho', ?_, ?_, ?_, ?_⟩
  · have hspend : fr'.moves ≤ fr.moves + walkCharge t := by
      calc
        fr'.moves ≤ fr.moves + cubeCharge t.n t.benchlen := hmv
        _ ≤ fr.moves + walkCharge t := by
          have hcu := cube_in_walk t
          omega
    exact spend_mul fr.moves fr'.moves (walkCharge t) cellsLeft hleft hspend hM
  · have hspend : fr'.slides ≤ fr.slides + cellSlideCharge t := by
      calc
        fr'.slides ≤ fr.slides + slideCharge t.n := hsl
        _ ≤ fr.slides + cellSlideCharge t := by
          have hslC := slide_in_cell t
          omega
    exact spend_mul fr.slides fr'.slides (cellSlideCharge t) cellsLeft hleft hspend hS
  · have hspend : fr'.opsCap ≤ fr.opsCap + cellOpsCharge t := by
      have hop := ops_in_cell t
      calc
        fr'.opsCap = fr.opsCap + 2 := hops
        _ ≤ fr.opsCap + cellOpsCharge t := by omega
    exact spend_mul fr.opsCap fr'.opsCap (cellOpsCharge t) cellsLeft hleft hspend hO
  · have hspend : fr'.ctrl ≤ fr.ctrl + cellCtrlCharge t := by
      rw [hctrl]
      have hc5 := ctrl_in_cell t
      omega
    exact spend_mul fr.ctrl fr'.ctrl (cellCtrlCharge t) cellsLeft hleft hspend hC

end EcbsLink2.Link2
