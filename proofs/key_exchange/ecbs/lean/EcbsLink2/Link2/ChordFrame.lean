/-
  The board `chord_add_live` leaves is the next cell's `RunFrame`.
  A second cell of fuel pays for `fitRoom` and `fitCtrl`: one `liveMoveRoom`
  is tight once the rise's two homes are counted, and `fitCtrl` wants one
  more control step than the tail spends. `chordStep_from_live` obtains that
  frame and hands the demo equation to `chordStep_open`.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.ChordNext
import EcbsLink2.Link2.WalkLive

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

private theorem charge_head (a c fuel : Nat) (h : FitsLen (a + (fuel + 1) * c)) :
    FitsLen (a + c) := by
  apply FitsLen.of_le h
  have hc : c ≤ (fuel + 1) * c := Nat.le_mul_of_pos_left c (Nat.succ_pos fuel)
  omega

private theorem charge_ge (t : Spec.Tier) : 5 * t.n ≤ cellMoveCharge t := by
  unfold cellMoveCharge tailMoveCap
  omega

private theorem ctrl_ge (t : Spec.Tier) : 1 ≤ cellCtrlCharge t := by
  unfold cellCtrlCharge
  omega

/-- One live cell, with fuel for at least one cell after it. The output board
    is a `RunFrame` whose homes 0 and 1 are the new point and whose homes 3
    and 4 are still the base. -/
theorem chord_add_live_frame (b : Ecbs.Board) (t : Spec.Tier)
    (baseX accX baseY accY preX preY inv : List Nat) (c fuel : Nat)
    (fr : RunFrame b t baseX accX)
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
    (hFuel : 1 ≤ fuel)
    (hMove : FitsLen (fr.moves + (fuel + 1) * cellMoveCharge t))
    (hSlide : FitsLen (fr.slides + (fuel + 1) * cellSlideCharge t))
    (hCtrl : FitsLen (fr.ctrl + (fuel + 1) * cellCtrlCharge t))
    (hOps : FitsLen (fr.opsCap + (fuel + 1) * cellOpsCharge t))
    (hMark : fr.mark + 3 < t.script) (hMarkF : FitsLen (fr.mark + 4)) :
    ∃ b' x3 y3,
      Ecbs.chord_add_demo b (decide (c = 2)) = .ok (true, b') ∧
      x3 = chordX3 t.n t.k t.benchlen
        (fieldMul t.n t.k t.benchlen
          (fieldSub t.n (if decide (c = 2) then mirrorTrits baseY else baseY) accY) inv)
        accX (fieldSub t.n baseX accX) ∧
      y3 = chordY3 t.n t.k t.benchlen
        (fieldMul t.n t.k t.benchlen
          (fieldSub t.n (if decide (c = 2) then mirrorTrits baseY else baseY) accY) inv)
        (fieldSub t.n accX x3) accY ∧
      walkStep t.n t.k t.benchlen (baseX, baseY) true (preX, preY) c =
        some (true, (x3, y3)) ∧
      Nonempty (RunFrame b' t baseX x3) := by
  have hMove1 : FitsLen (liveMoveRoom t fr.moves baseX accX) := by
    apply FitsLen.of_le (charge_head fr.moves (cellMoveCharge t) fuel hMove)
    exact live_move_le t fr.moves baseX accX fr.lenX fr.lenA
  have hSlide1 : FitsLen (liveSlideRoom t fr.slides) := by
    rw [live_slide_eq]
    exact charge_head fr.slides (cellSlideCharge t) fuel hSlide
  have hCtrl1 : FitsLen (liveCtrlRoom t fr.ctrl) := by
    rw [live_ctrl_eq]
    exact charge_head fr.ctrl (cellCtrlCharge t) fuel hCtrl
  have hOps1 : FitsLen (liveOpsRoom t fr.opsCap) := by
    rw [live_ops_eq]
    exact charge_head fr.opsCap (cellOpsCharge t) fuel hOps
  obtain ⟨b', hdemo, hx0, hy1, hwalk, hhigh, hbud, hpackEx⟩ :=
    chord_add_live b t baseX accX baseY accY preX preY inv c fr
      hOk sat hR hsh hmk hc hY hA hf4 hf1 hyB hyA htriY htriUp
      hpreX hpreY hacc hMove1 hSlide1 hCtrl1 hOps1 hMark hMarkF
  obtain ⟨high, hhi, hge⟩ := hhigh
  obtain ⟨bud, hleft, hctrlEq, hmoveEq, hopsEq⟩ := hbud
  obtain ⟨_, _, hpack⟩ := hpackEx
  let red := decide (c = 2)
  let run := fieldSub t.n baseX accX
  let y := if red then mirrorTrits baseY else baseY
  let rise := fieldSub t.n y accY
  let slope := fieldMul t.n t.k t.benchlen rise inv
  let x3 := chordX3 t.n t.k t.benchlen slope accX run
  let y3 := chordY3 t.n t.k t.benchlen slope (fieldSub t.n accX x3) accY
  have hx3 : x3 = chordX3 t.n t.k t.benchlen
      (fieldMul t.n t.k t.benchlen
        (fieldSub t.n (if decide (c = 2) then mirrorTrits baseY else baseY) accY) inv)
      accX (fieldSub t.n baseX accX) := rfl
  have hy3 : y3 = chordY3 t.n t.k t.benchlen
      (fieldMul t.n t.k t.benchlen
        (fieldSub t.n (if decide (c = 2) then mirrorTrits baseY else baseY) accY) inv)
      (fieldSub t.n accX x3) accY := rfl
  have hwalk' : walkStep t.n t.k t.benchlen (baseX, baseY) true (preX, preY) c =
      some (true, (x3, y3)) := by
    simpa [red, run, y, rise, slope, x3, y3] using hwalk
  obtain ⟨c2, hc2, _hle2⟩ := hleft.ops 2 hleft.ops2lt
  obtain ⟨c3, hc3, _hle3⟩ := hleft.ops 3 hleft.ops3lt
  obtain ⟨mv, hmv, hmvLe⟩ := hleft.movesLe
  obtain ⟨sl, hsl⟩ := hpack.slides
  obtain ⟨pk, hpk⟩ := hpack.peak
  obtain ⟨st, hst⟩ := hpack.strict
  obtain ⟨ho, hho⟩ := hpack.hole
  obtain ⟨ctrl, hctrl, hctrlLe⟩ := hleft.ctrlLe
  obtain ⟨m0, _, hmark⟩ := hpack.mark
  obtain ⟨mMx, mx0, _, _, hmx⟩ := hpack.mx
  obtain ⟨tmax, htmax⟩ := hleft.tmax
  have hmvRoom : mv ≤ fr.moves + cellMoveCharge t + 2 * t.n := by
    have hlive : liveMoveRoom t fr.moves baseX accX ≤ fr.moves + cellMoveCharge t :=
      live_move_le t fr.moves baseX accX fr.lenX fr.lenA
    have htail : mv ≤ liveMoveRoom t fr.moves baseX accX + 2 * t.n := by
      have hstep : mv ≤ checkMoveCap bud + 2 * t.n + tailMoveCap t.n t.benchlen := hmvLe
      have hcomm : checkMoveCap bud + 2 * t.n + tailMoveCap t.n t.benchlen =
          checkMoveCap bud + tailMoveCap t.n t.benchlen + 2 * t.n := by omega
      rw [hcomm, hmoveEq] at hstep
      exact hstep
    omega
  have hfitRoom : FitsLen (mv + 3 * t.n) := by
    have htwo : FitsLen (fr.moves + 2 * cellMoveCharge t) := by
      apply FitsLen.of_le hMove
      have hmul : 2 * cellMoveCharge t ≤ (fuel + 1) * cellMoveCharge t := by
        have h2 : 2 ≤ fuel + 1 := by omega
        exact Nat.mul_le_mul_right _ h2
      omega
    have hle : mv + 3 * t.n ≤ fr.moves + 2 * cellMoveCharge t := by
      have h5 := charge_ge t
      omega
    exact FitsLen.of_le htwo hle
  have hfitCtrl : FitsLen (ctrl + 1) := by
    have htwo : FitsLen (fr.ctrl + 2 * cellCtrlCharge t) := by
      apply FitsLen.of_le hCtrl
      have hmul : 2 * cellCtrlCharge t ≤ (fuel + 1) * cellCtrlCharge t := by
        have h2 : 2 ≤ fuel + 1 := by omega
        exact Nat.mul_le_mul_right _ h2
      omega
    have hcap : ctrl ≤ liveCtrlRoom t fr.ctrl := Nat.le_trans hctrlLe hctrlEq
    rw [live_ctrl_eq] at hcap
    have hle : ctrl + 1 ≤ fr.ctrl + 2 * cellCtrlCharge t := by
      have h1 := ctrl_ge t
      omega
    exact FitsLen.of_le htwo hle
  have hfitOps : FitsLen (checkOpsCap bud + 3) := by
    rw [hopsEq, live_ops_eq]
    exact charge_head fr.opsCap (cellOpsCharge t) fuel hOps
  have hlenX : x3.length = t.n := by
    simp [x3, chordX3, fieldAdd, fieldMul, whiteHole0, mirrorTrits,
      List.length_map, List.length_range, List.length_replicate]
  have htriX : allTritList x3 := by
    simp only [x3, chordX3]
    exact fieldAdd_span_trits _ _ _
  refine ⟨b', x3, y3, hdemo, hx3, hy3, hwalk', ⟨{
    szH := hpack.szH
    szD := hpack.szD
    bench := hpack.benchOff
    held5 := hpack.off5 (by rw [hpack.szD]; decide)
    held6 := hpack.off6 (by rw [hpack.szD]; decide)
    held2 := hpack.off2 (by rw [hpack.szD]; decide)
    held0 := hpack.held0 (by rw [hpack.szD]; decide)
    home0 := hx0 (by rw [hpack.szH]; decide)
    held3 := hleft.held3 (by rw [hpack.szD]; decide)
    home3 := hleft.home3 (by rw [hpack.szH]; decide)
    y1 := y3
    y4 := baseY
    flag1 := true
    flag4 := true
    home1 := hy1 (by rw [hpack.szH]; decide)
    held1 := hpack.held1 (by rw [hpack.szD]; decide)
    home4 := hleft.home4 (by rw [hpack.szH]; decide)
    held4 := hleft.held4 (by rw [hpack.szD]; decide)
    mark := m0 + 3
    mx := max (max (max mx0 (mMx + 2)) (mMx + 3)) (mMx + 4)
    hmark := hmark
    hmx := hmx
    lenX := fr.lenX
    lenA := hlenX
    triX := fr.triX
    triA := htriX
    tier := hleft.tier
    moves := mv
    slides := sl
    peak := pk
    ctrl := ctrl
    high := high
    cOps := c2
    chordOps := c3
    opsCap := checkOpsCap bud + 3
    peakS := st
    hole := ho
    hmoves := hmv
    hslides := hsl
    hpeak := hpk
    hctrl := hctrl
    hhigh := hhi
    tmax := tmax
    htally := hleft.tlen
    ht0 := hleft.t0
    hrow := hleft.row
    htmax := htmax
    hStart := Or.inr hge
    hlad := hleft.ladder
    hl0 := hleft.l0
    hnr := hleft.nr
    hpark := hleft.park
    hfrom := hleft.fromH
    hridx := hleft.ridx
    hstrict := hst
    hhole := hho
    ops2 := hleft.ops2lt
    ops3 := hleft.ops3lt
    hop2 := hc2
    hop3 := hc3
    fitInv := by
      have hle := _hle2
      simp only [if_pos rfl] at hle
      exact FitsLen.of_le hfitOps hle
    fitChord := by
      have hle := _hle3
      simp only [if_neg (by decide : (3 : Nat) ≠ 2), if_pos rfl] at hle
      exact FitsLen.of_le hfitOps hle
    fitCtrl := hfitCtrl
    fitRoom := hfitRoom
    opsRoom := hleft.ops
  }⟩⟩

/-- A live cell with fuel left. The emitted step is `chordStep_open` on the
    board the frame just built. -/
theorem chordStep_from_live (cells : List Nat) (i toN c fuel : Nat)
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
    (hFuel : 1 ≤ fuel)
    (hMove : FitsLen (fr.moves + (fuel + 1) * cellMoveCharge t))
    (hSlide : FitsLen (fr.slides + (fuel + 1) * cellSlideCharge t))
    (hCtrl : FitsLen (fr.ctrl + (fuel + 1) * cellCtrlCharge t))
    (hOps : FitsLen (fr.opsCap + (fuel + 1) * cellOpsCharge t))
    (hMark : fr.mark + 3 < t.script) (hMarkF : FitsLen (fr.mark + 4))
    (hi : i ≤ toN) (hlen : cells.length = toN + 1)
    (hcAt : cells[i]'(by omega) = c) (hc0 : c ≠ 0) (hc2 : c ≤ 2)
    (hml : Ecbs.marker_lift b0 = .ok b)
    (hfrob : Ecbs.frobenius_affine b = .ok bF)
    (hfiti : FitsLen (i + 1)) :
    ∃ bA, chordStep (embed cells) (Int.ofNat toN) (Int.ofNat i, (b0, true)) =
      if i = toN then .ok (SudoRt.Flow.brk (Int.ofNat i, (bA, true)))
      else .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), (bA, true))) := by
  obtain ⟨bA, _, _, hdemo, _, _, _, _⟩ :=
    chord_add_live_frame bF t baseX accX baseY accY preX preY inv c fuel fr
      hOk sat hR hsh hmk hc hY hA hf4 hf1 hyB hyA htriY htriUp
      hpreX hpreY hacc hFuel hMove hSlide hCtrl hOps hMark hMarkF
  have hadd : Ecbs.chord_add_demo bF (SudoRt.SEq.beq (Int.ofNat c) (2 : Int)) =
      .ok (true, bA) := by
    have hflag : SudoRt.SEq.beq (Int.ofNat c) (2 : Int) = decide (c = 2) := by
      rcases hc with rfl | rfl <;> decide
    rw [hflag]
    exact hdemo
  exact ⟨bA, chordStep_open cells i toN c b0 b bF bA hi hlen hcAt hc0 hc2 hml hfrob hadd hfiti⟩

end EcbsLink2.Link2
