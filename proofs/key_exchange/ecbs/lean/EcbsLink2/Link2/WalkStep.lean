/-
  One live cell of the walk, with the fuel taken from the cells still left.
  `i < toN` leaves a later cell, and that later cell is the frame's extra
  fuel. `i = toN` is `chordStep_live_last`.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.ChordFrame
import EcbsLink2.Link2.WalkLast

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- A live cell that is not the last. `fuel = toN - i` is `cellsLeft - 1`. -/
theorem chordStep_live_later (cells : List Nat) (i toN c : Nat)
    (b0 b bF : Ecbs.Board) (t : Spec.Tier)
    (baseX accX baseY accY preX preY inv : List Nat)
    (fr : RunFrame bF t baseX accX)
    (hOk : BoardOk t) (sat : TierSat t) (hR : 0 < tierR t) (hsh : TierShape t)
    (hmk : bF.sudo_5Board_9marker_on = true)
    (hc : c = 1 ∨ c = 2)
    (hY : fr.y4 = baseY) (hA : fr.y1 = accY)
    (hf4 : fr.flag4 = true) (hf1 : fr.flag1 = true)
    (hyB : baseY.length = t.n) (hyA : accY.length = t.n)
    (htriY : allTritList baseY) (htriUp : allTritList accY)
    (hpreX : accX = fieldCube t.n t.k t.benchlen preX)
    (hpreY : accY = fieldCube t.n t.k t.benchlen preY)
    (hacc : fieldInv t.n t.k t.benchlen (fieldSub t.n baseX accX) = some inv)
    (hMove : FitsLen (fr.moves + cellsLeft i toN * walkCharge t))
    (hSlide : FitsLen (fr.slides + cellsLeft i toN * cellSlideCharge t))
    (hCtrl : FitsLen (fr.ctrl + cellsLeft i toN * cellCtrlCharge t))
    (hOps : FitsLen (fr.opsCap + cellsLeft i toN * cellOpsCharge t))
    (hst7 : fr.peakS ≤ 7)
    (hholeFr : fr.hole ≤ t.benchlen)
    (hMark : fr.mark + 3 < t.script) (hMarkF : FitsLen (fr.mark + 4))
    (hi : i < toN) (hlen : cells.length = toN + 1)
    (hcAt : cells[i]'(by omega) = c) (hc0 : c ≠ 0) (hc2 : c ≤ 2)
    (hml : Ecbs.marker_lift b0 = .ok b)
    (hfrob : Ecbs.frobenius_affine b = .ok bF)
    (hfiti : FitsLen (i + 1)) :
    ∃ bA, chordStep (embed cells) (Int.ofNat toN) (Int.ofNat i, (b0, true)) =
      .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), (bA, true))) := by
  have hleft : 2 ≤ cellsLeft i toN := by
    unfold cellsLeft
    omega
  obtain ⟨hfuel, hMf⟩ := frame_fuel_move t fr.moves (cellsLeft i toN) hleft hMove
  obtain ⟨_, hSf⟩ := frame_fuel_ctrl fr.slides (cellsLeft i toN) (cellSlideCharge t) hleft hSlide
  obtain ⟨_, hCf⟩ := frame_fuel_ctrl fr.ctrl (cellsLeft i toN) (cellCtrlCharge t) hleft hCtrl
  obtain ⟨_, hOf⟩ := frame_fuel_ctrl fr.opsCap (cellsLeft i toN) (cellOpsCharge t) hleft hOps
  have hfuelEq : toN - i = cellsLeft i toN - 1 := (fuel_of_later i toN hi).2
  obtain ⟨bA, hstep⟩ := chordStep_from_live cells i toN c (toN - i) b0 b bF t
      baseX accX baseY accY preX preY inv fr
      hOk sat hR hsh hmk hc hY hA hf4 hf1 hyB hyA htriY htriUp
      hpreX hpreY hacc (by simpa [hfuelEq] using hfuel)
      (by simpa [hfuelEq] using hMf) (by simpa [hfuelEq] using hSf)
      (by simpa [hfuelEq] using hCf) (by simpa [hfuelEq] using hOf)
      hst7 hholeFr hMark hMarkF (by omega) hlen hcAt hc0 hc2 hml hfrob hfiti
  have hne : ¬ i = toN := by
    intro heq
    exact absurd heq (by omega)
  rw [if_neg hne] at hstep
  exact ⟨bA, hstep⟩

/-- One live cell. The branch is the cells still left, not a separate fuel
    parameter. The last cell does not build a next frame. -/
theorem chordStep_live_cell (cells : List Nat) (i toN c : Nat)
    (b0 b bF : Ecbs.Board) (t : Spec.Tier)
    (baseX accX baseY accY preX preY inv : List Nat)
    (fr : RunFrame bF t baseX accX)
    (hOk : BoardOk t) (sat : TierSat t) (hR : 0 < tierR t) (hsh : TierShape t)
    (hmk : bF.sudo_5Board_9marker_on = true)
    (hc : c = 1 ∨ c = 2)
    (hY : fr.y4 = baseY) (hA : fr.y1 = accY)
    (hf4 : fr.flag4 = true) (hf1 : fr.flag1 = true)
    (hyB : baseY.length = t.n) (hyA : accY.length = t.n)
    (htriY : allTritList baseY) (htriUp : allTritList accY)
    (hpreX : accX = fieldCube t.n t.k t.benchlen preX)
    (hpreY : accY = fieldCube t.n t.k t.benchlen preY)
    (hacc : fieldInv t.n t.k t.benchlen (fieldSub t.n baseX accX) = some inv)
    (hMove : FitsLen (fr.moves + cellsLeft i toN * walkCharge t))
    (hSlide : FitsLen (fr.slides + cellsLeft i toN * cellSlideCharge t))
    (hCtrl : FitsLen (fr.ctrl + cellsLeft i toN * cellCtrlCharge t))
    (hOps : FitsLen (fr.opsCap + cellsLeft i toN * cellOpsCharge t))
    (hst7 : fr.peakS ≤ 7)
    (hholeFr : fr.hole ≤ t.benchlen)
    (hMark : fr.mark + 3 < t.script) (hMarkF : FitsLen (fr.mark + 4))
    (hi : i ≤ toN) (hlen : cells.length = toN + 1)
    (hcAt : cells[i]'(by omega) = c) (hc0 : c ≠ 0) (hc2 : c ≤ 2)
    (hml : Ecbs.marker_lift b0 = .ok b)
    (hfrob : Ecbs.frobenius_affine b = .ok bF)
    (hfiti : FitsLen (i + 1)) :
    ∃ bA, chordStep (embed cells) (Int.ofNat toN) (Int.ofNat i, (b0, true)) =
      if i = toN then .ok (SudoRt.Flow.brk (Int.ofNat i, (bA, true)))
      else .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), (bA, true))) := by
  by_cases hlast : i = toN
  · have hleft : cellsLeft i toN = 1 := cellsLeft_last i toN hlast
    obtain ⟨hM, hS, hC, hO⟩ := last_rooms_of_left t fr.moves fr.slides fr.ctrl fr.opsCap
      baseX accX fr.lenX fr.lenA
      (by simpa [hleft] using hMove) (by simpa [hleft] using hSlide)
      (by simpa [hleft] using hCtrl) (by simpa [hleft] using hOps)
    obtain ⟨bA, hstep⟩ := chordStep_live_last cells i toN c b0 b bF t
      baseX accX baseY accY preX preY inv fr
      hOk sat hR hsh hmk hc hY hA hf4 hf1 hyB hyA htriY htriUp
      hpreX hpreY hacc hM hS hC hO hMark hMarkF hholeFr hlast hlen hcAt hc0 hc2 hml hfrob hfiti
    exact ⟨bA, by simpa [hlast] using hstep⟩
  · have hlt : i < toN := by omega
    obtain ⟨bA, hstep⟩ := chordStep_live_later cells i toN c b0 b bF t
      baseX accX baseY accY preX preY inv fr
      hOk sat hR hsh hmk hc hY hA hf4 hf1 hyB hyA htriY htriUp
      hpreX hpreY hacc hMove hSlide hCtrl hOps hst7 hholeFr hMark hMarkF hlt hlen hcAt hc0 hc2
      hml hfrob hfiti
    refine ⟨bA, ?_⟩
    have hne : ¬ i = toN := by
      intro heq
      exact absurd heq (by omega)
    rw [if_neg hne]
    exact hstep

end EcbsLink2.Link2
