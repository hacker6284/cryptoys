/-
  One live cell of `walk_chord`, for a shipped tier. Frobenius asks for
  `FitsLen (opsCap + 2)` and writes strict and hole through `raisedPeak` and
  `raisedHole`. Those checks are `demo_frob_fits` and its siblings, which read
  the proved `(cells + 1)` room. They are not hypotheses. The chord that
  follows is charged from the same room: its ops cap is the bumped cap plus
  one `cellOpsCharge`.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.CellRun
import EcbsLink2.Link2.ChordFrame

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

theorem demo_cell_frob (b : Ecbs.Board)
    (baseX accX baseY accY : List Nat) (fr : RunFrame b Spec.demo baseX accX)
    (done left : Nat)
    (hOk : BoardOk Spec.demo) (sat : TierSat Spec.demo) (hsh : TierShape Spec.demo)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hY : fr.y4 = baseY) (hA : fr.y1 = accY)
    (hf4 : fr.flag4 = true) (hf1 : fr.flag1 = true)
    (hyA : accY.length = Spec.demo.n) (htriY : allTritList accY)
    (hsum : done + left = Spec.demo.cells) (hleft : 0 < left)
    (hm : fr.moves ≤ done * (walkCharge Spec.demo +
      (6 * Spec.demo.benchlen + 2 * Spec.demo.n)))
    (hs : fr.slides ≤ done * (cellSlideCharge Spec.demo + 4 * Spec.demo.n))
    (hc : fr.ctrl ≤ done * (cellCtrlCharge Spec.demo + 4))
    (ho : fr.opsCap ≤ done * (cellOpsCharge Spec.demo + 2))
    (hst : fr.peakS ≤ 7) (hhole : fr.hole ≤ Spec.demo.benchlen) :
    ∃ bL bF, ∃ fr' : RunFrame bF Spec.demo baseX
        (fieldCube Spec.demo.n Spec.demo.k Spec.demo.benchlen accX),
      Ecbs.marker_lift b = .ok bL ∧
      Ecbs.frobenius_affine bL = .ok bF ∧
      bF.sudo_5Board_9marker_on = true ∧
      fr'.y1 = fieldCube Spec.demo.n Spec.demo.k Spec.demo.benchlen accY ∧
      fr'.y4 = baseY ∧
      fr'.ctrl = fr.ctrl + 4 ∧
      fr'.mark = 1 ∧
      fr'.opsCap = fr.opsCap + 2 ∧
      fr'.moves ≤ fr.moves + cubeCharge Spec.demo.n Spec.demo.benchlen ∧
      fr'.slides ≤ fr.slides + slideCharge Spec.demo.n ∧
      fr'.peakS ≤ 7 ∧
      fr'.hole ≤ Spec.demo.benchlen ∧
      FitsLen fr'.peakS ∧
      FitsLen fr'.hole ∧
      FitsLen (fr'.opsCap + left * cellOpsCharge Spec.demo) ∧
      (∃ occU, occU ≤ 7 ∧
        fr'.peakS = raisedPeak
          (raisedPeak fr.peakS (countHeld b.sudo_5Board_4held 7)) occU) ∧
      fr'.hole = raisedHole
        (raisedHole fr.hole (topIdx (combStrip Spec.demo.n Spec.demo.benchlen accX)))
        (topIdx (combStrip Spec.demo.n Spec.demo.benchlen accY)) := by
  have hfit := demo_frob_fits done left fr.moves fr.slides fr.ctrl fr.opsCap fr.peakS fr.hole
    hsum hleft hm hs hc ho hst hhole
  have hMove := hfit.1
  have hSlide := hfit.2.1
  have hCtrl := hfit.2.2.1
  have hOps := hfit.2.2.2.1
  have hOpsC := hfit.2.2.2.2.2.2.1
  have hMoveC := hfit.2.2.2.2.2.2.2.1
  obtain ⟨bL, bF, fr', hml, hfrob, hmk', hy1, hy4, hf1', hf4', hctrl, hmark, hcOps, hchord,
      hmv, hsl, hops, hheld, ⟨occU, hocc, hpeak⟩, hholeEq, htopX, htopY⟩ :=
    cell_run_frame b Spec.demo baseX accX baseY accY fr hOk sat hsh hmk hY hA hf4 hf1
      hyA htriY hMove hSlide hCtrl hOps
  have hst' : fr'.peakS ≤ 7 := by
    rw [hpeak]
    exact strict_out_le fr.peakS (countHeld b.sudo_5Board_4held 7) occU hst hheld hocc
  have hho' : fr'.hole ≤ Spec.demo.benchlen := by
    rw [hholeEq]
    exact hole_out_le fr.hole
      (topIdx (combStrip Spec.demo.n Spec.demo.benchlen accX))
      (topIdx (combStrip Spec.demo.n Spec.demo.benchlen accY))
      Spec.demo.benchlen hhole htopX htopY
  have hspan := demo_walk_span
  have hroom := demo_walk_room
  have hfitS : FitsLen fr'.peakS :=
    counter_fit fr'.peakS ((Spec.demo.cells + 1) * cellOpsCharge Spec.demo)
      (Nat.le_trans hst' hspan.2.2.2.2.1) hroom.2.2.2
  have hfitH : FitsLen fr'.hole :=
    counter_fit fr'.hole ((Spec.demo.cells + 1) * cellOpsCharge Spec.demo)
      (Nat.le_trans hho' hspan.2.2.2.2.2.1) hroom.2.2.2
  have hopsNext : FitsLen (fr'.opsCap + left * cellOpsCharge Spec.demo) := by
    rw [hops]
    exact hOpsC
  exact ⟨bL, bF, fr', hml, hfrob, hmk', hy1, hy4, hctrl, hmark, hops, hmv, hsl,
    hst', hho', hfitS, hfitH, hopsNext, ⟨occU, hocc, hpeak⟩, hholeEq⟩

/-- A blank counter block is the `done = 0` case. `0 ≤ 7` and `0 ≤ bench`
    are the only counter facts, and the rooms come from `demo_walk_room`. -/
theorem demo_cell_frob_zero (b : Ecbs.Board)
    (baseX accX baseY accY : List Nat) (fr : RunFrame b Spec.demo baseX accX)
    (hOk : BoardOk Spec.demo) (sat : TierSat Spec.demo) (hsh : TierShape Spec.demo)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hY : fr.y4 = baseY) (hA : fr.y1 = accY)
    (hf4 : fr.flag4 = true) (hf1 : fr.flag1 = true)
    (hyA : accY.length = Spec.demo.n) (htriY : allTritList accY)
    (hm0 : fr.moves = 0) (hs0 : fr.slides = 0) (hc0 : fr.ctrl = 0)
    (ho0 : fr.opsCap = 0) (hst0 : fr.peakS = 0) (hho0 : fr.hole = 0) :
    ∃ bL bF, ∃ fr' : RunFrame bF Spec.demo baseX
        (fieldCube Spec.demo.n Spec.demo.k Spec.demo.benchlen accX),
      Ecbs.marker_lift b = .ok bL ∧
      Ecbs.frobenius_affine bL = .ok bF ∧
      fr'.opsCap = 2 ∧
      fr'.peakS ≤ 7 ∧
      fr'.hole ≤ Spec.demo.benchlen ∧
      FitsLen fr'.peakS ∧
      FitsLen fr'.hole ∧
      FitsLen (fr'.opsCap + Spec.demo.cells * cellOpsCharge Spec.demo) := by
  have hcells : 0 < Spec.demo.cells := by simp [Spec.demo]
  obtain ⟨bL, bF, fr', hml, hfrob, hmk', hy1, hy4, hctrl, hmark, hops, hmv, hsl,
      hst', hho', hfitS, hfitH, hopsNext, _, _⟩ :=
    demo_cell_frob b baseX accX baseY accY fr 0 Spec.demo.cells hOk sat hsh hmk hY hA
      hf4 hf1 hyA htriY (by simp [Spec.demo]) hcells
      (by simp [hm0]) (by simp [hs0]) (by simp [hc0]) (by simp [ho0])
      (by simp [hst0]) (by simp [hho0])
  refine ⟨bL, bF, fr', hml, hfrob, ?_, hst', hho', hfitS, hfitH, ?_⟩
  · rw [hops, ho0]
  · simpa [Spec.demo] using hopsNext

/-- After Frobenius, the chord's four `FitsLen` checks are the same
    `(cells + 1)` products. `left` counts this chord. -/
theorem demo_chord_rooms (moves slides ctrl ops moves' slides' ctrl' ops' done left : Nat)
    (hsum : done + left = Spec.demo.cells) (hleft : 0 < left)
    (hm : moves ≤ done * (walkCharge Spec.demo +
      (6 * Spec.demo.benchlen + 2 * Spec.demo.n)))
    (hs : slides ≤ done * (cellSlideCharge Spec.demo + 4 * Spec.demo.n))
    (hc : ctrl ≤ done * (cellCtrlCharge Spec.demo + 4))
    (ho : ops ≤ done * (cellOpsCharge Spec.demo + 2))
    (hmv : moves' ≤ moves + cubeCharge Spec.demo.n Spec.demo.benchlen)
    (hsl : slides' ≤ slides + slideCharge Spec.demo.n)
    (hctrl : ctrl' ≤ ctrl + 4)
    (hops : ops' ≤ ops + 2) :
    FitsLen (moves' + left * cellMoveCharge Spec.demo) ∧
      FitsLen (slides' + left * cellSlideCharge Spec.demo) ∧
      FitsLen (ctrl' + left * cellCtrlCharge Spec.demo) ∧
      FitsLen (ops' + left * cellOpsCharge Spec.demo) := by
  have hfit := demo_frob_fits done left moves slides ctrl ops 0 0 hsum hleft hm hs hc ho
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

/-- A non-final Demo cell. `fuel + 1` is `left`, the cells still to run,
    including this chord. The four `FitsLen` arguments of `chord_add_live_frame`
    are `demo_chord_rooms`. The output ops cap is the Frobenius cap plus one
    `cellOpsCharge`, so from the counter before Frobenius it grew by
    `cellOpsCharge + 2`. -/
theorem demo_cell_chord (b : Ecbs.Board)
    (baseX accX baseY accY preX preY inv : List Nat) (c fuel : Nat)
    (fr : RunFrame b Spec.demo baseX accX)
    (moves0 slides0 ctrl0 ops0 done left : Nat)
    (hOk : BoardOk Spec.demo) (sat : TierSat Spec.demo) (hR : 0 < tierR Spec.demo)
    (hsh : TierShape Spec.demo)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hc : c = 1 ∨ c = 2)
    (hY : fr.y4 = baseY) (hA : fr.y1 = accY)
    (hf4 : fr.flag4 = true) (hf1 : fr.flag1 = true)
    (hyB : baseY.length = Spec.demo.n) (hyA : accY.length = Spec.demo.n)
    (htriY : allTritList baseY) (htriUp : allTritList accY)
    (hpreX : accX = fieldCube Spec.demo.n Spec.demo.k Spec.demo.benchlen preX)
    (hpreY : accY = fieldCube Spec.demo.n Spec.demo.k Spec.demo.benchlen preY)
    (hacc : fieldInv Spec.demo.n Spec.demo.k Spec.demo.benchlen
      (fieldSub Spec.demo.n baseX accX) = some inv)
    (hFuel : 1 ≤ fuel) (hleftEq : fuel + 1 = left)
    (hsum : done + left = Spec.demo.cells) (hleft : 0 < left)
    (hm : moves0 ≤ done * (walkCharge Spec.demo +
      (6 * Spec.demo.benchlen + 2 * Spec.demo.n)))
    (hs : slides0 ≤ done * (cellSlideCharge Spec.demo + 4 * Spec.demo.n))
    (hctrl0 : ctrl0 ≤ done * (cellCtrlCharge Spec.demo + 4))
    (ho : ops0 ≤ done * (cellOpsCharge Spec.demo + 2))
    (hmv : fr.moves ≤ moves0 + cubeCharge Spec.demo.n Spec.demo.benchlen)
    (hsl : fr.slides ≤ slides0 + slideCharge Spec.demo.n)
    (hctrl : fr.ctrl ≤ ctrl0 + 4)
    (hops : fr.opsCap ≤ ops0 + 2)
    (hMark : fr.mark + 3 < Spec.demo.script) (hMarkF : FitsLen (fr.mark + 4)) :
    ∃ b' x3 y3, ∃ fr' : RunFrame b' Spec.demo baseX x3,
      Ecbs.chord_add_demo b (decide (c = 2)) = .ok (true, b') ∧
      walkStep Spec.demo.n Spec.demo.k Spec.demo.benchlen (baseX, baseY) true
        (preX, preY) c = some (true, (x3, y3)) ∧
      fr'.opsCap = fr.opsCap + cellOpsCharge Spec.demo ∧
      fr'.moves ≤ fr.moves + walkCharge Spec.demo ∧
      fr'.ctrl ≤ fr.ctrl + cellCtrlCharge Spec.demo ∧
      fr'.opsCap ≤ (done + 1) * (cellOpsCharge Spec.demo + 2) := by
  have hrooms := demo_chord_rooms moves0 slides0 ctrl0 ops0 fr.moves fr.slides fr.ctrl
    fr.opsCap done left hsum hleft hm hs hctrl0 ho hmv hsl hctrl hops
  have hMove : FitsLen (fr.moves + (fuel + 1) * cellMoveCharge Spec.demo) := by
    rw [hleftEq]
    exact hrooms.1
  have hSlide : FitsLen (fr.slides + (fuel + 1) * cellSlideCharge Spec.demo) := by
    rw [hleftEq]
    exact hrooms.2.1
  have hCtrl : FitsLen (fr.ctrl + (fuel + 1) * cellCtrlCharge Spec.demo) := by
    rw [hleftEq]
    exact hrooms.2.2.1
  have hOps : FitsLen (fr.opsCap + (fuel + 1) * cellOpsCharge Spec.demo) := by
    rw [hleftEq]
    exact hrooms.2.2.2
  obtain ⟨b', x3, y3, hdemo, _hx3, _hy3, hwalk, ⟨fr', hops', hmv', hctrl'⟩⟩ :=
    chord_add_live_frame b Spec.demo baseX accX baseY accY preX preY inv c fuel fr
      hOk sat hR hsh hmk hc hY hA hf4 hf1 hyB hyA htriY htriUp hpreX hpreY hacc
      hFuel hMove hSlide hCtrl hOps hMark hMarkF
  refine ⟨b', x3, y3, fr', hdemo, hwalk, hops', hmv', hctrl', ?_⟩
  · rw [hops']
    have hstep : fr.opsCap + cellOpsCharge Spec.demo ≤ ops0 + 2 + cellOpsCharge Spec.demo := by
      omega
    have hcomm : ops0 + 2 + cellOpsCharge Spec.demo = ops0 + cellOpsCharge Spec.demo + 2 := by
      omega
    rw [hcomm] at hstep
    exact ops_succ (cellOpsCharge Spec.demo) done ops0
      (fr.opsCap + cellOpsCharge Spec.demo) ho hstep

end EcbsLink2.Link2
