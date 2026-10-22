/-
  One live cell of `walk_chord`, for any tier that has a `TierWalk`.
  `tier_cell_frob` and `tier_cell_chord` are that cell for demo, toy, hobby,
  and serious: each shipped tier is a `TierWalk`. Frobenius asks for
  `FitsLen (opsCap + 2)` and writes strict and hole through `raisedPeak`
  and `raisedHole`. Those checks are `tier_frob_fits`. They are not
  hypotheses beyond the tier's proved room. The chord that follows is
  charged from the same room, and it keeps `peakS ≤ 7`.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.CellRun
import EcbsLink2.Link2.ChordFrame

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

theorem tier_cell_frob (t : Spec.Tier) (b : Ecbs.Board)
    (baseX accX baseY accY : List Nat) (fr : RunFrame b t baseX accX)
    (done left : Nat) (tw : TierWalk t)
    (hOk : BoardOk t) (sat : TierSat t) (hsh : TierShape t)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hY : fr.y4 = baseY) (hA : fr.y1 = accY)
    (hf4 : fr.flag4 = true) (hf1 : fr.flag1 = true)
    (hyA : accY.length = t.n) (htriY : allTritList accY)
    (hsum : done + left = t.cells) (hleft : 0 < left)
    (hm : fr.moves ≤ done * (walkCharge t + (6 * t.benchlen + 2 * t.n)))
    (hs : fr.slides ≤ done * (cellSlideCharge t + 4 * t.n))
    (hc : fr.ctrl ≤ done * (cellCtrlCharge t + 4))
    (ho : fr.opsCap ≤ done * (cellOpsCharge t + 2))
    (hst : fr.peakS ≤ 7) (hhole : fr.hole ≤ t.benchlen) :
    ∃ bL bF, ∃ fr' : RunFrame bF t baseX (fieldCube t.n t.k t.benchlen accX),
      Ecbs.marker_lift b = .ok bL ∧
      Ecbs.frobenius_affine bL = .ok bF ∧
      bF.sudo_5Board_9marker_on = true ∧
      fr'.y1 = fieldCube t.n t.k t.benchlen accY ∧
      fr'.y4 = baseY ∧
      fr'.ctrl = fr.ctrl + 4 ∧
      fr'.mark = 1 ∧
      fr'.opsCap = fr.opsCap + 2 ∧
      fr'.moves ≤ fr.moves + cubeCharge t.n t.benchlen ∧
      fr'.slides ≤ fr.slides + slideCharge t.n ∧
      fr'.peakS ≤ 7 ∧
      fr'.hole ≤ t.benchlen ∧
      FitsLen fr'.peakS ∧
      FitsLen fr'.hole ∧
      FitsLen (fr'.opsCap + left * cellOpsCharge t) ∧
      (∃ occU, occU ≤ 7 ∧
        fr'.peakS = raisedPeak
          (raisedPeak fr.peakS (countHeld b.sudo_5Board_4held 7)) occU) ∧
      fr'.hole = raisedHole
        (raisedHole fr.hole (topIdx (combStrip t.n t.benchlen accX)))
        (topIdx (combStrip t.n t.benchlen accY)) ∧
      fr'.flag1 = true ∧
      fr'.flag4 = true := by
  have hfit := tier_frob_fits t tw done left fr.moves fr.slides fr.ctrl fr.opsCap
    fr.peakS fr.hole hsum hleft hm hs hc ho hst hhole
  have hMove := hfit.1
  have hSlide := hfit.2.1
  have hCtrl := hfit.2.2.1
  have hOps := hfit.2.2.2.1
  have hOpsC := hfit.2.2.2.2.2.2.1
  obtain ⟨bL, bF, fr', hml, hfrob, hmk', hy1, hy4, hf1', hf4', hctrl, hmark,
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
  have hfitS : FitsLen fr'.peakS :=
    counter_fit fr'.peakS ((t.cells + 1) * cellOpsCharge t)
      (Nat.le_trans hst' tw.sevenLe) tw.roomO
  have hfitH : FitsLen fr'.hole :=
    counter_fit fr'.hole ((t.cells + 1) * cellOpsCharge t)
      (Nat.le_trans hho' tw.benchLe) tw.roomO
  have hopsNext : FitsLen (fr'.opsCap + left * cellOpsCharge t) := by
    rw [hops]
    exact hOpsC
  exact ⟨bL, bF, fr', hml, hfrob, hmk', hy1, hy4, hctrl, hmark, hops, hmv, hsl,
    hst', hho', hfitS, hfitH, hopsNext, ⟨occU, hocc, hpeak⟩, hholeEq, hf1', hf4'⟩

/-- Blank counters, `done = 0`. The tier room is `tw`. -/
theorem tier_cell_frob_zero (t : Spec.Tier) (b : Ecbs.Board)
    (baseX accX baseY accY : List Nat) (fr : RunFrame b t baseX accX)
    (tw : TierWalk t)
    (hOk : BoardOk t) (sat : TierSat t) (hsh : TierShape t)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hY : fr.y4 = baseY) (hA : fr.y1 = accY)
    (hf4 : fr.flag4 = true) (hf1 : fr.flag1 = true)
    (hyA : accY.length = t.n) (htriY : allTritList accY)
    (hcells : 0 < t.cells)
    (hm0 : fr.moves = 0) (hs0 : fr.slides = 0) (hc0 : fr.ctrl = 0)
    (ho0 : fr.opsCap = 0) (hst0 : fr.peakS = 0) (hho0 : fr.hole = 0) :
    ∃ bL bF, ∃ fr' : RunFrame bF t baseX (fieldCube t.n t.k t.benchlen accX),
      Ecbs.marker_lift b = .ok bL ∧
      Ecbs.frobenius_affine bL = .ok bF ∧
      fr'.opsCap = 2 ∧
      fr'.peakS ≤ 7 ∧
      fr'.hole ≤ t.benchlen ∧
      FitsLen fr'.peakS ∧
      FitsLen fr'.hole ∧
      FitsLen (fr'.opsCap + t.cells * cellOpsCharge t) := by
  obtain ⟨bL, bF, fr', hml, hfrob, _hmk', _hy1, _hy4, _hctrl, _hmark, hops, _hmv,
      _hsl, hst', hho', hfitS, hfitH, hopsNext, _, _⟩ :=
    tier_cell_frob t b baseX accX baseY accY fr 0 t.cells tw hOk sat hsh hmk hY hA
      hf4 hf1 hyA htriY (by omega) hcells
      (by simp [hm0]) (by simp [hs0]) (by simp [hc0]) (by simp [ho0])
      (by simp [hst0]) (by simp [hho0])
  refine ⟨bL, bF, fr', hml, hfrob, ?_, hst', hho', hfitS, hfitH, hopsNext⟩
  rw [hops, ho0]

/-- The chord's four rooms, from the counters Frobenius can leave. -/
theorem chord_rooms (t : Spec.Tier) (tw : TierWalk t)
    (moves slides ctrl ops moves' slides' ctrl' ops' done left : Nat)
    (hsum : done + left = t.cells) (hleft : 0 < left)
    (hm : moves ≤ done * (walkCharge t + (6 * t.benchlen + 2 * t.n)))
    (hs : slides ≤ done * (cellSlideCharge t + 4 * t.n))
    (hc : ctrl ≤ done * (cellCtrlCharge t + 4))
    (ho : ops ≤ done * (cellOpsCharge t + 2))
    (hmv : moves' ≤ moves + cubeCharge t.n t.benchlen)
    (hsl : slides' ≤ slides + slideCharge t.n)
    (hctrl : ctrl' ≤ ctrl + 4)
    (hops : ops' ≤ ops + 2) :
    FitsLen (moves' + left * cellMoveCharge t) ∧
      FitsLen (slides' + left * cellSlideCharge t) ∧
      FitsLen (ctrl' + left * cellCtrlCharge t) ∧
      FitsLen (ops' + left * cellOpsCharge t) := by
  have hfit := tier_frob_fits t tw done left moves slides ctrl ops 0 0 hsum hleft hm hs hc ho
    (by decide) (Nat.zero_le _)
  have hMoveC := hfit.2.2.2.2.2.2.2.1
  have hSlideC := hfit.2.2.2.2.2.2.2.2.1
  have hCtrlC := hfit.2.2.2.2.2.2.2.2.2
  have hOpsC := hfit.2.2.2.2.2.2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply FitsLen.of_le hMoveC
    omega
  · apply FitsLen.of_le hSlideC
    omega
  · apply FitsLen.of_le hCtrlC
    omega
  · apply FitsLen.of_le hOpsC
    omega

/-- A non-final live cell. `fuel + 1 = left`. The output ops cap is the
    Frobenius cap plus one `cellOpsCharge`. -/
theorem tier_cell_chord (t : Spec.Tier) (b : Ecbs.Board)
    (baseX accX baseY accY preX preY inv : List Nat) (c fuel : Nat)
    (fr : RunFrame b t baseX accX)
    (moves0 slides0 ctrl0 ops0 done left : Nat) (tw : TierWalk t)
    (hOk : BoardOk t) (sat : TierSat t) (hR : 0 < tierR t) (hsh : TierShape t)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hc : c = 1 ∨ c = 2)
    (hY : fr.y4 = baseY) (hA : fr.y1 = accY)
    (hf4 : fr.flag4 = true) (hf1 : fr.flag1 = true)
    (hyB : baseY.length = t.n) (hyA : accY.length = t.n)
    (htriY : allTritList baseY) (htriUp : allTritList accY)
    (hpreX : accX = fieldCube t.n t.k t.benchlen preX)
    (hpreY : accY = fieldCube t.n t.k t.benchlen preY)
    (hacc : fieldInv t.n t.k t.benchlen (fieldSub t.n baseX accX) = some inv)
    (hFuel : 1 ≤ fuel) (hleftEq : fuel + 1 = left)
    (hsum : done + left = t.cells) (hleft : 0 < left)
    (hm : moves0 ≤ done * (walkCharge t + (6 * t.benchlen + 2 * t.n)))
    (hs : slides0 ≤ done * (cellSlideCharge t + 4 * t.n))
    (hctrl0 : ctrl0 ≤ done * (cellCtrlCharge t + 4))
    (ho : ops0 ≤ done * (cellOpsCharge t + 2))
    (hmv : fr.moves ≤ moves0 + cubeCharge t.n t.benchlen)
    (hsl : fr.slides ≤ slides0 + slideCharge t.n)
    (hctrl : fr.ctrl ≤ ctrl0 + 4)
    (hops : fr.opsCap ≤ ops0 + 2)
    (hst : fr.peakS ≤ 7)
    (hhole : fr.hole ≤ t.benchlen)
    (hMark : fr.mark + 3 < t.script) (hMarkF : FitsLen (fr.mark + 4)) :
    ∃ b' x3 y3, ∃ fr' : RunFrame b' t baseX x3,
      Ecbs.chord_add_demo b (decide (c = 2)) = .ok (true, b') ∧
      walkStep t.n t.k t.benchlen (baseX, baseY) true (preX, preY) c =
        some (true, (x3, y3)) ∧
      fr'.opsCap = fr.opsCap + cellOpsCharge t ∧
      fr'.moves ≤ fr.moves + walkCharge t ∧
      fr'.ctrl ≤ fr.ctrl + cellCtrlCharge t ∧
      fr'.slides ≤ fr.slides + cellSlideCharge t ∧
      fr'.peakS ≤ 7 ∧
      fr'.hole ≤ t.benchlen ∧
      fr'.y1 = y3 ∧
      fr'.y4 = baseY ∧
      fr'.flag1 = true ∧
      fr'.flag4 = true ∧
      b'.sudo_5Board_9marker_on = true ∧
      fr'.opsCap ≤ (done + 1) * (cellOpsCharge t + 2) := by
  have hrooms := chord_rooms t tw moves0 slides0 ctrl0 ops0 fr.moves fr.slides fr.ctrl
    fr.opsCap done left hsum hleft hm hs hctrl0 ho hmv hsl hctrl hops
  have hMove : FitsLen (fr.moves + (fuel + 1) * cellMoveCharge t) := by
    rw [hleftEq]
    exact hrooms.1
  have hSlide : FitsLen (fr.slides + (fuel + 1) * cellSlideCharge t) := by
    rw [hleftEq]
    exact hrooms.2.1
  have hCtrl : FitsLen (fr.ctrl + (fuel + 1) * cellCtrlCharge t) := by
    rw [hleftEq]
    exact hrooms.2.2.1
  have hOps : FitsLen (fr.opsCap + (fuel + 1) * cellOpsCharge t) := by
    rw [hleftEq]
    exact hrooms.2.2.2
  obtain ⟨b', x3, y3, hdemo, _hx3, _hy3, hwalk,
      ⟨fr', hops', hmv', hctrl', hsl', hst', hho', hy1', hy4', hf1', hf4', hmk'⟩⟩ :=
    chord_add_live_frame b t baseX accX baseY accY preX preY inv c fuel fr
      hOk sat hR hsh hmk hc hY hA hf4 hf1 hyB hyA htriY htriUp hpreX hpreY hacc
      hFuel hMove hSlide hCtrl hOps hst hhole hMark hMarkF
  refine ⟨b', x3, y3, fr', hdemo, hwalk, hops', hmv', hctrl', hsl', hst', hho',
    hy1', hy4', hf1', hf4', hmk', ?_⟩
  · rw [hops']
    have hstep : fr.opsCap + cellOpsCharge t ≤ ops0 + 2 + cellOpsCharge t := by omega
    have hcomm : ops0 + 2 + cellOpsCharge t = ops0 + cellOpsCharge t + 2 := by omega
    rw [hcomm] at hstep
    exact ops_succ (cellOpsCharge t) done ops0 (fr.opsCap + cellOpsCharge t) ho hstep

end EcbsLink2.Link2
