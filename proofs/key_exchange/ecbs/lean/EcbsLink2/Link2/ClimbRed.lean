/-
  The final rung of the emitted climb: cube the gap product onto the spare
  and multiply by the held input, then the white scan while rungs remain.
  Split out of `ClimbEmit` so that file stays under the per-file memory line.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.ClimbEmit

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

attribute [local irreducible] bumpOp

private theorem replicate_trits (k : Nat) : allTritList (List.replicate k 0) := by
  intro x hx
  simp [List.mem_replicate] at hx
  rcases hx with ⟨_, rfl⟩
  decide

/-- Final rung. After the gap mul and the clear, the emitter cubes that product
    onto the spare and multiplies the cube by the held input. This rung does not
    double the tally. Both results are the named live boards, and the same live
    results hold for any board that agrees on the fields the cube and the mul
    read: replacing the row, tally length, control counter, recorded high, and
    `tally_max` copies those fields onto the result. The input's length and trits
    are the per-call reads of that mul; the core does not store them. Moves
    and slides stay `2 · n` under one `rungCharge` of this rung. -/
theorem red_cube_mul {done rest : List Nat} {r : Nat} {b : Ecbs.Board}
    {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvKCore done (r :: rest) b s base)
    (hM : MoveHeadroom b base.n base.bench base.mMax)
    (hS : SlideHeadroom b base.n base.mMax)
    (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax)
    (hhome : s.onBench = false)
    (hxLen : base.x.length = base.n) (hxT : allTritList base.x) :
    ∃ (bLoop bMul bClear bCube bRed : Ecbs.Board),
      Ecbs.mul bLoop ((5 : Nat) : Int) ((5 : Nat) : Int) ((6 : Nat) : Int)
          false false false = .ok bMul ∧
      Ecbs.clear bMul ((5 : Nat) : Int) = .ok bClear ∧
      Ecbs.cube bClear ((6 : Nat) : Int) ((5 : Nat) : Int) = .ok bCube ∧
      Ecbs.mul bCube ((5 : Nat) : Int) (base.xHome : Int) ((6 : Nat) : Int)
          false false false = .ok bRed ∧
      (∃ (mvE mvR slE slR : Nat),
        b.sudo_5Board_4cost.sudo_5Costs_5moves = (mvE : Int) ∧
        bRed.sudo_5Board_4cost.sudo_5Costs_5moves = (mvR : Int) ∧
        mvR + 2 * base.n ≤ mvE + rungCharge base.n base.bench s.tally ∧
        b.sudo_5Board_4cost.sudo_5Costs_6slides = (slE : Int) ∧
        bRed.sudo_5Board_4cost.sudo_5Costs_6slides = (slR : Int) ∧
        slR + 2 * base.n ≤ slE + rungSlideCharge base.n s.tally) ∧
      bClear.sudo_5Board_9tally_len = (s.tally : Int) ∧
      bClear.sudo_5Board_6tally0 = (s.t0 : Int) ∧
      bClear.sudo_5Board_3row = embed (paintRed s.row s.t0 s.tally) ∧
      bClear.sudo_5Board_1t.sudo_4Tier_7control = (base.control : Int) ∧
      bClear.sudo_5Board_4cost.sudo_5Costs_15control_highest = (s.high : Int) ∧
      bClear.sudo_5Board_4cost.sudo_5Costs_4ctrl = ((s.ctrl + s.tally : Nat) : Int) ∧
      bClear.sudo_5Board_4cost.sudo_5Costs_9tally_max =
        b.sudo_5Board_4cost.sudo_5Costs_9tally_max ∧
      bCube.sudo_5Board_6tally0 = (s.t0 : Int) ∧
      bRed.sudo_5Board_6tally0 = (s.t0 : Int) ∧
      bCube.sudo_5Board_1t = bClear.sudo_5Board_1t ∧
      bRed.sudo_5Board_1t = bClear.sudo_5Board_1t ∧
      (∀ (row : Array Int) (len ctrl high tmax : Int),
        Ecbs.cube (withTally bClear row len ctrl high tmax)
            ((6 : Nat) : Int) ((5 : Nat) : Int) =
          .ok (withTally bCube row len ctrl high tmax)) ∧
      (∀ (row : Array Int) (len ctrl high tmax : Int),
        Ecbs.mul (withTally bCube row len ctrl high tmax)
            ((5 : Nat) : Int) (base.xHome : Int) ((6 : Nat) : Int)
            false false false =
          .ok (withTally bRed row len ctrl high tmax)) ∧
      bRed.sudo_5Board_8bench_on = true ∧
      bRed.sudo_5Board_8bench_to = (5 : Int) ∧
      bRed.sudo_5Board_9tally_len = (s.tally : Int) ∧
      bRed.sudo_5Board_5bench =
        embed (fieldMul s.n s.k s.benchlen base.x
          (fieldCube s.n s.k s.benchlen
            (fieldMul s.n s.k s.benchlen s.gap
              (cubeTimes s.n s.k s.benchlen s.gap s.tally))) ++
          List.replicate (s.benchlen - s.n) 0) ∧
      (∀ (row : Array Int) (ctrl fromHole ridx : Int),
        Ecbs.clear (withPark bMul row ctrl fromHole ridx) ((5 : Nat) : Int) =
          .ok (withPark bClear row ctrl fromHole ridx)) ∧
      (∀ (row : Array Int) (ctrl fromHole ridx : Int),
        Ecbs.cube (withPark bClear row ctrl fromHole ridx)
            ((6 : Nat) : Int) ((5 : Nat) : Int) =
          .ok (withPark bCube row ctrl fromHole ridx)) ∧
      (∀ (row : Array Int) (ctrl fromHole ridx : Int),
        Ecbs.mul (withPark bCube row ctrl fromHole ridx)
            ((5 : Nat) : Int) (base.xHome : Int) ((6 : Nat) : Int)
            false false false =
          .ok (withPark bRed row ctrl fromHole ridx)) ∧
      (∀ (rowD rowP : Array Int) (len high tmax : Int) (ctrlD ctrlP fromHole ridx : Int),
        Ecbs.cube (withPark (withTally bClear rowD len ctrlD high tmax) rowP ctrlP fromHole ridx)
            ((6 : Nat) : Int) ((5 : Nat) : Int) =
          .ok (withPark (withTally bCube rowD len ctrlD high tmax) rowP ctrlP fromHole ridx)) ∧
      (∀ (rowD rowP : Array Int) (len high tmax : Int) (ctrlD ctrlP fromHole ridx : Int),
        Ecbs.mul (withPark (withTally bCube rowD len ctrlD high tmax) rowP ctrlP fromHole ridx)
            ((5 : Nat) : Int) (base.xHome : Int) ((6 : Nat) : Int)
            false false false =
          .ok (withPark (withTally bRed rowD len ctrlD high tmax) rowP ctrlP fromHole ridx)) ∧
      (∃ (cU : PegCtx) (ys : List Nat) (moves slides hole peak peakS cOps : Nat)
        (hH : 6 < bLoop.sudo_5Board_4home.size)
        (hD : 6 < bLoop.sudo_5Board_4held.size)
        (hops : 0 < bLoop.sudo_5Board_4cost.sudo_5Costs_3ops.size),
        bLoop = pegBoard cU cU.m ∧
        cU.row0 = s.row ∧ cU.ctrl0 = s.ctrl ∧ cU.g = s.gap ∧ cU.m = s.tally ∧
        cU.n = s.n ∧ cU.k = s.k ∧ cU.bench = s.benchlen ∧ cU.src = 6 ∧
        cU.t0 = s.t0 ∧
        bMul = mulNoLiveBoard bLoop 5 6 cU.g ys ⟨cU.n, cU.k, moves, slides, hole, cU.bench, peak, peakS, cOps, hops⟩ ⟨hH, hD⟩ ∧
        ys = cubeBenchIter cU.n cU.k cU.bench cU.g cU.m ∧
        moves = (pegPack cU cU.m cU.hm (Nat.le_refl _)).moves ∧
        slides = (pegPack cU cU.m cU.hm (Nat.le_refl _)).slides ∧
        hole = (pegPack cU cU.m cU.hm (Nat.le_refl _)).hole ∧
        peak = (pegPack cU cU.m cU.hm (Nat.le_refl _)).peak ∧
        peakS = (pegPack cU cU.m cU.hm (Nat.le_refl _)).peakS ∧
        Ecbs.copy_band b ((6 : Nat) : Int) ((5 : Nat) : Int) false = .ok cU.b0) ∧
      (∃ (mvE mvR slE slR : Nat),
        b.sudo_5Board_4cost.sudo_5Costs_5moves = (mvE : Int) ∧
        bRed.sudo_5Board_4cost.sudo_5Costs_5moves = (mvR : Int) ∧
        mvR + 2 * base.n ≤ mvE + rungCharge base.n base.bench s.tally ∧
        b.sudo_5Board_4cost.sudo_5Costs_6slides = (slE : Int) ∧
        bRed.sudo_5Board_4cost.sudo_5Costs_6slides = (slR : Int) ∧
        slR + 2 * base.n ≤ slE + rungSlideCharge base.n s.tally) ∧
      bRed.sudo_5Board_4cost.sudo_5Costs_15control_highest = (s.high : Int) ∧
      bRed.sudo_5Board_4cost.sudo_5Costs_9tally_max =
        b.sudo_5Board_4cost.sudo_5Costs_9tally_max := by
  obtain ⟨c, bLoop, ys, moves, slides, hole, peak, peakS, cMul, hH, hD, hops,
      hcopy, hsrc, hg, hmEq, hn, hkN, hbch, hpegB, hysEq, hGap, hX,
      hOp, hRow, htier, _hmk, h7, _hop0, hOpsLe, hctrl0, hhighS,
      hcontrol, hlen0, hmax0, ht0, hmulG, hrow0, hmvB, hslB, hhoB, hpkB, hpsB,
      ⟨mvE, hmvE, hmovRel⟩, ⟨slE, hslE, hsldRel⟩, _hmulW⟩ :=
    mul_of_shape h hM hS hm hT hhome
  have hloopM : moves + 2 * base.n ≤
      mvE + base.n + s.tally * pegCharge base.n base.bench := hmovRel
  have hloopS : slides + 2 * base.n ≤ slE + s.tally * (2 * base.n) := hsldRel
  let bMul := mulNoLiveBoard bLoop 5 6 c.g ys ⟨c.n, c.k, moves, slides, hole, c.bench, peak, peakS, cMul, hops⟩ ⟨hH, hD⟩
  have hKeep := mulLive_keep bLoop 5 6 5 c.g ys ⟨c.n, c.k, moves, slides, hole, c.bench, peak, peakS, cMul, hops⟩ c.g ⟨hH, hD⟩ (by decide) hGap.heldLt hGap.homeLt hGap.held hGap.arr
  have hXMul := mulLive_keep bLoop 5 6 base.xHome c.g ys ⟨c.n, c.k, moves, slides, hole, c.bench, peak, peakS, cMul, hops⟩ base.x ⟨hH, hD⟩ h.shape.xNe6 hX.heldLt hX.homeLt hX.held hX.arr
  let mvC := mulMovesNo (moves + 2 * pegCount (ys.take c.n)) c.g (ys.take c.n)
    c.n c.k c.bench
  have hmvC : bMul.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mvC := by
    simpa [bMul, mvC] using
      mul_live_moves bLoop 5 6 c.g ys ⟨c.n, c.k, moves, slides, hole, c.bench, peak, peakS, cMul, hops⟩ ⟨hH, hD⟩
  have hlenG : c.g.length = c.n := c.hlenx
  have hfitN : FitsLen c.g.length := by rw [hlenG]; exact c.hf
  have hpegN : pegCount c.g ≤ c.n := by rw [← hlenG]; exact pegCount_le c.g
  have hmvC_le : mvC ≤ moves + mulCharge c.n c.bench := by
    have hstep := mulMovesNo_bound moves c.n c.k c.bench c.g ys c.n_le
    have hrest : 2 * pegCount (ys.take c.n) + c.n * (c.n + 1) + 3 * (c.bench - c.n) ≤
        mulCharge c.n c.bench := by
      unfold mulCharge
      have hp := pegCount_take_le ys c.n
      omega
    omega
  have hcn : c.n = base.n := hn.trans h.hn
  have hcb : c.bench = base.bench := hbch.trans h.hbench
  have hk : done.length + 1 ≤ base.R := by
    have hlen := h.kLe
    rw [List.length_append, List.length_cons] at hlen
    omega
  let L := laneFold c.n (c.n - c.k)
    (school c.n c.g (ys.take c.n) (List.replicate c.bench 0) false)
  have hschLen : (school c.n c.g (ys.take c.n) (List.replicate c.bench 0) false).length =
      c.bench := by
    simpa [List.length_replicate] using
      school_length c.g (ys.take c.n) (List.replicate c.bench 0) false c.n
  have hlenL : L.length = c.bench := by
    simpa [L, hschLen] using
      laneFold_length c.n (c.n - c.k)
        (school c.n c.g (ys.take c.n) (List.replicate c.bench 0) false)
        (by rw [hschLen]; exact c.n_le)
  have hzeroL : ∀ i, c.n ≤ i → ∀ hi : i < L.length, L[i] = 0 := by
    intro i hlo hi
    have hcoeff := mul_no_high c.g (ys.take c.n) c.n c.k c.bench c.hn0 c.gap_pos i hlo
      (hlenL ▸ hi)
    exact (coeff_eq_get L i hi).symm.trans hcoeff
  have hposL : 0 < L.length := by
    rw [hlenL]; exact Nat.lt_of_lt_of_le c.hn0 c.n_le
  have hnleL : c.n ≤ L.length := by rw [hlenL]; exact c.n_le
  have hfitL : FitsLen L.length := by rw [hlenL]; exact c.hfitB
  have htriL : allTritList (L.take c.n) := by
    have hrep : allTritList (List.replicate c.bench 0) := replicate_trits c.bench
    have hwide : ∀ i, i < c.n → i + (c.n - 1) < (List.replicate c.bench 0).length := by
      intro i hi
      rw [List.length_replicate]
      have h2 : 2 * (c.n - 1) < c.bench := by
        have hs := c.hspan
        omega
      omega
    have hschT := school_trits c.g (ys.take c.n) (List.replicate c.bench 0) false c.n hrep hwide
    have hfoldT := laneFold_trits c.n (c.n - c.k)
      (school c.n c.g (ys.take c.n) (List.replicate c.bench 0) false)
      hschT (Nat.sub_le _ _) (by rw [hschLen]; exact c.n_le)
    exact allTritList_take hfoldT c.n
  let pegL := pegCount (L.take c.n)
  have hpegL : 2 * pegL ≤ 2 * c.n := by
    have hp := pegCount_take_le L c.n
    simp only [pegL] at hp
    omega
  have hcubeLe : 2 * pegL + 2 * c.n + 3 * (c.bench - c.n) ≤ pegCharge c.n c.bench := by
    unfold pegCharge
    omega
  have hpegY : 2 * pegCount (ys.take c.n) ≤ 2 * c.n := by
    have hp := pegCount_take_le ys c.n
    omega
  have hmvN : mvC ≤ moves + mulCharge base.n base.bench := by
    rw [← show mulCharge c.n c.bench = mulCharge base.n base.bench by rw [hcn, hcb]]
    exact hmvC_le
  have hpegBase : pegCount c.g ≤ base.n := by rw [← hcn]; exact hpegN
  have hcubeBase : 2 * pegL + 2 * base.n + 3 * (base.bench - base.n) ≤
      pegCharge base.n base.bench := by
    rw [← hcn, ← hcb]; exact hcubeLe
  let movesC := mvC + pegCount c.g
  let slidesC := slides + 2 * pegCount (ys.take c.n)
  let bSettle := settleBoard bLoop 6 hH hD ys c.n moves slides peak
  let peakC := raisedPeak
    (raisedPeak peak (countHeld (bLoop.sudo_5Board_4held.set ⟨6, hD⟩ true) 7))
    (countHeld (bSettle.sudo_5Board_4held.set
      ⟨6, settle_held_lt bLoop 6 ⟨hH, hD⟩ ys c.n moves slides peak⟩ false) 7)
  let holeC := raisedHole hole
    (topIdx (school c.n c.g (ys.take c.n) (List.replicate c.bench 0) false))
  let peakSC := raisedPeak peakS (countHeld bSettle.sudo_5Board_4held 7)
  have hpeakM : bMul.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peakC := by
    simpa [bMul, peakC, bSettle] using
      mul_live_peak bLoop 5 6 c.g ys ⟨c.n, c.k, moves, slides, hole, c.bench, peak, peakS, cMul, hops⟩ ⟨hH, hD⟩
  have hslidesM : bMul.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slidesC := by
    simpa [bMul, slidesC] using
      mul_live_slides bLoop 5 6 c.g ys ⟨c.n, c.k, moves, slides, hole, c.bench, peak, peakS, cMul, hops⟩ ⟨hH, hD⟩
  have hholeM : bMul.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat holeC := by
    simpa [bMul, holeC] using
      mul_live_hole bLoop 5 6 c.g ys ⟨c.n, c.k, moves, slides, hole, c.bench, peak, peakS, cMul, hops⟩ ⟨hH, hD⟩
  have hstrictM : bMul.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat peakSC := by
    simpa [bMul, peakSC, bSettle] using
      mul_live_strict bLoop 5 6 c.g ys ⟨c.n, c.k, moves, slides, hole, c.bench, peak, peakS, cMul, hops⟩ ⟨hH, hD⟩
  have hbenchM : bMul.sudo_5Board_5bench = embed L := by
    simpa [bMul, L] using
      mul_live_bench bLoop 5 6 c.g ys ⟨c.n, c.k, moves, slides, hole, c.bench, peak, peakS, cMul, hops⟩ ⟨hH, hD⟩
  have hmkM : bMul.sudo_5Board_9marker_on = false := by
    simpa [bMul] using
      mul_live_marker bLoop 5 6 c.g ys ⟨c.n, c.k, moves, slides, hole, c.bench, peak, peakS, cMul, hops⟩ ⟨hH, hD⟩
  have haim := mul_live_aimed bLoop 5 6 c.g ys ⟨c.n, c.k, moves, slides, hole, c.bench, peak, peakS, cMul, hops⟩ ⟨hH, hD⟩
  have htierM : bMul.sudo_5Board_1t = bLoop.sudo_5Board_1t := by
    simpa [bMul] using
      mul_live_tier bLoop 5 6 c.g ys ⟨c.n, c.k, moves, slides, hole, c.bench, peak, peakS, cMul, hops⟩ ⟨hH, hD⟩
  have hfitC : FitsLen (mvC + pegCount c.g) := by
    apply FitsLen.of_le (MoveHeadroom.at hM hmvE)
    have hpiece : mvC + pegCount c.g ≤
        mvE + base.n + s.tally * pegCharge base.n base.bench +
          mulCharge base.n base.bench + base.n := by
      omega
    have hbody := white_piece_in_room base.n base.bench s.tally mvE
      (mvC + pegCount c.g) hpiece
    exact Nat.le_trans hbody (Nat.add_le_add_left
      (Nat.sub_le_sub_right
        (rungCharge_mono base.n base.bench s.tally base.mMax hT) _) mvE)
  have hclear := clear_held_refines bMul 5 c.g mvC hKeep.homeLt hKeep.heldLt
    hKeep.held hKeep.arr hmvC hfitN hfitC
  let bClear := clearHeldBoard bMul 5 c.g mvC hKeep.homeLt hKeep.heldLt
  have hclearEq : Ecbs.clear bMul ((5 : Nat) : Int) = .ok bClear := by
    simpa [bClear, clearHeldBoard] using hclear
  have hXClear : CellKeep bClear base.xHome base.x :=
    clearCell_keep bMul 5 base.xHome c.g mvC base.x ⟨hKeep.homeLt, hKeep.heldLt⟩ (Ne.symm h.shape.xNe5) hXMul
  have hH5 : 5 < bClear.sudo_5Board_4home.size := by
    simp [bClear, clearHeldBoard, Array.size_set]
    exact hKeep.homeLt
  have hD5 : 5 < bClear.sudo_5Board_4held.size := by
    simp [bClear, clearHeldBoard, Array.size_set]
    exact hKeep.heldLt
  have hemptyC : bClear.sudo_5Board_4held[5]'hD5 = false := by
    have hEq : bClear.sudo_5Board_4held =
        bMul.sudo_5Board_4held.set ⟨5, hKeep.heldLt⟩ false := by
      simp [bClear, clearHeldBoard]
    rw [show bClear.sudo_5Board_4held[5] =
        (bMul.sudo_5Board_4held.set ⟨5, hKeep.heldLt⟩ false)[5]'(hEq ▸ hD5) from
      idx_get hEq 5 hD5]
    simp [Array.getElem_set]
  have h7C : 7 ≤ bClear.sudo_5Board_4held.size := by
    have hszC : bClear.sudo_5Board_4held.size = bMul.sudo_5Board_4held.size := by
      simp [bClear, clearHeldBoard, Array.size_set]
    rw [hszC]
    have hHeld := mul_live_held bLoop 5 6 c.g ys ⟨c.n, c.k, moves, slides, hole, c.bench, peak, peakS, cMul, hops⟩ ⟨hH, hD⟩
    have hS := settle_held_eq bLoop 6 ⟨hH, hD⟩ ys c.n moves slides peak
    have hsz : bMul.sudo_5Board_4held.size = bLoop.sudo_5Board_4held.size := by
      rw [hHeld]
      simp only [Array.size_set]
      rw [hS]
      simp only [Array.size_set]
    rw [hsz]
    exact h7
  have hmkC : bClear.sudo_5Board_9marker_on = false := by
    simp [bClear, clearHeldBoard, hmkM]
  have honC : bClear.sudo_5Board_8bench_on = true := by
    simp [bClear, clearHeldBoard]
    exact haim.1
  have htoC : bClear.sudo_5Board_8bench_to = (5 : Int) := by
    simp [bClear, clearHeldBoard]
    exact haim.2
  have hbenchC : bClear.sudo_5Board_5bench = embed L := by
    simp [bClear, clearHeldBoard, hbenchM]
  have hmovesC : bClear.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat movesC := by
    simp [bClear, clearHeldBoard, movesC]
  have hslidesC : bClear.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slidesC := by
    simp [bClear, clearHeldBoard, hslidesM]
  have hpeakC : bClear.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peakC := by
    simp [bClear, clearHeldBoard, hpeakM]
  have hholeC : bClear.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat holeC := by
    simp [bClear, clearHeldBoard, hholeM]
  have hstrictC : bClear.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakSC : Int) := by
    simpa [bClear, clearHeldBoard, ofNat_eq_natCast] using hstrictM
  have htierC : bClear.sudo_5Board_1t = c.b0.sudo_5Board_1t := by
    have h1 : bClear.sudo_5Board_1t = bMul.sudo_5Board_1t := by
      simp [bClear, clearHeldBoard]
    rw [h1, htierM, htier]
  have hnC : bClear.sudo_5Board_1t.sudo_4Tier_1n = (c.n : Int) := by rw [htierC]; exact c.hn
  have hblC : bClear.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat c.bench := by
    rw [htierC]; exact c.hbl
  have hcgC : bClear.sudo_5Board_1t.sudo_4Tier_7combgap = Int.ofNat c.cg := by
    rw [htierC]; exact c.hcg
  have hwC : bClear.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat c.w := by rw [htierC]; exact c.hwF
  have hhC : bClear.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat c.h := by rw [htierC]; exact c.hhF
  have hrC : bClear.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat c.r := by rw [htierC]; exact c.hrF
  have hkC : bClear.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat c.k := by rw [htierC]; exact c.hkF
  obtain ⟨cCube, h1Loop, hop1Loop, hCubeFit⟩ := hOp
  have hMulOps := mul_live_ops bLoop 5 6 c.g ys ⟨c.n, c.k, moves, slides, hole, c.bench, peak, peakS, cMul, hops⟩ ⟨hH, hD⟩
  have hSettleOps := settle_ops bLoop 6 ⟨hH, hD⟩ ys c.n moves slides peak
  have hop1M : ∀ (h1 : 1 < bMul.sudo_5Board_4cost.sudo_5Costs_3ops.size),
      bMul.sudo_5Board_4cost.sudo_5Costs_3ops[1] = (cCube : Int) := by
    intro h1
    have hget := idx_get hMulOps 1 h1
    rw [hget, Array.getElem_set, if_neg (by decide : (0 : Nat) ≠ 1)]
    have hsz : 1 < (settleBoard bLoop 6 hH hD ys c.n moves slides peak).sudo_5Board_4cost.sudo_5Costs_3ops.size := by
      rw [hSettleOps]; exact h1Loop
    exact (idx_get hSettleOps 1 hsz).trans hop1Loop
  have hOpsEq : bClear.sudo_5Board_4cost.sudo_5Costs_3ops =
      bMul.sudo_5Board_4cost.sudo_5Costs_3ops := by
    simp [bClear, clearHeldBoard]
  have hopsC : 1 < bClear.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    have hsz : bClear.sudo_5Board_4cost.sudo_5Costs_3ops.size =
        bLoop.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
      rw [hOpsEq, hMulOps, Array.size_set, hSettleOps]
    rw [hsz]; exact h1Loop
  have hop1C : bClear.sudo_5Board_4cost.sudo_5Costs_3ops[1]'hopsC = (cCube : Int) :=
    (idx_get hOpsEq 1 hopsC).trans (hop1M _)
  have hClearLoose : movesC ≤ mvE + base.n + s.tally * pegCharge base.n base.bench +
      mulCharge base.n base.bench + base.n := by
    omega
  have hpegLn0 : pegL ≤ base.n := by
    have h2 := hpegL
    rw [hcn] at h2
    omega
  have hfoldC : FitsLen (movesC + 2 * pegL + 2 * c.n + 3 * (c.bench - c.n)) := by
    apply FitsLen.of_le (MoveHeadroom.at hM hmvE)
    have hroom := clear_fold_room base.n base.bench s.tally mvE movesC pegL
      hClearLoose hpegLn0
    have hmono := Nat.sub_le_sub_right
      (rungCharge_mono base.n base.bench s.tally base.mMax hT) (2 * base.n)
    have hle : movesC + 2 * pegL + 2 * base.n + 3 * (base.bench - base.n) ≤
        mvE + (rungCharge base.n base.bench base.mMax - 2 * base.n) :=
      Nat.le_trans hroom (Nat.add_le_add_left hmono mvE)
    rw [hcn, hcb]
    exact hle
  have hfmC : FitsLen (movesC + 2 * pegL + 2 * c.n) := FitsLen.of_le hfoldC (by omega)
  have hfitMC : FitsLen (movesC + 2 * pegL) := FitsLen.of_le hfmC (by omega)
  have hpegF : FitsLen (2 * pegL) := FitsLen.of_le hfitMC (by omega)
  have hfitSC : FitsLen (slidesC + 2 * pegL) := by
    apply FitsLen.of_le (SlideHeadroom.at hS hslE)
    have hextra : slidesC + 2 * pegL ≤
        slE + s.tally * (2 * base.n) + 2 * base.n := by
      have hpeg : 2 * pegCount (ys.take c.n) ≤ 2 * base.n := by
        rw [← hcn]; exact hpegY
      have hL : 2 * pegL ≤ 2 * base.n := by rw [← hcn]; exact hpegL
      omega
    exact loose_slide_in_room base.n s.tally base.mMax slE _ hT hextra
  have hcube := cube_eq_live bClear 6 5 L c.w c.h c.r c.n c.k movesC slidesC holeC c.bench peakC peakSC cCube c.cg hmkC honC htoC hH5 hD5 h7C hemptyC hbenchC hnC c.hn0 hposL hnleL hzeroL c.hf hfitL hmovesC hslidesC hpeakC (by simpa [pegL] using hpegF) (by simpa [pegL] using hfitMC) (by simpa [pegL] using hfitSC) hopsC hop1C hCubeFit hblC hcgC c.hspan htriL c.h3 hfmC ⟨c.hw0, c.hh0, c.hrR, c.hrP, c.hnE, c.hkLe, c.hgap⟩ hwC hhC hrC hkC hholeC hstrictC c.hsm c.hnsm c.hfitB (by simpa [pegL] using hfoldC)
  let bCube := cubeLiveBoard bClear 6 5 L ⟨c.n, c.k, movesC, slidesC, holeC, c.bench, peakC, peakSC, cCube, hopsC⟩ ⟨hH5, hD5⟩
  have hcubeEq : Ecbs.cube bClear ((6 : Nat) : Int) ((5 : Nat) : Int) = .ok bCube := by
    simpa [bCube] using hcube
  let mvCube := cubeMoves (movesC + 2 * pegL) (L.take c.n) c.n c.k c.bench
  have hmvCube : bCube.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mvCube := by
    rw [show bCube = cubeLiveBoard bClear 6 5 L ⟨c.n, c.k, movesC, slidesC, holeC, c.bench, peakC, peakSC, cCube, hopsC⟩ ⟨hH5, hD5⟩ from rfl,
      cube_live_moves bClear 6 5 L ⟨c.n, c.k, movesC, slidesC, holeC, c.bench, peakC, peakSC, cCube, hopsC⟩ ⟨hH5, hD5⟩]
  let slidesCube := slidesC + 2 * pegL
  have hslidesCube : bCube.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slidesCube := by
    rw [show bCube = cubeLiveBoard bClear 6 5 L ⟨c.n, c.k, movesC, slidesC, holeC, c.bench, peakC, peakSC, cCube, hopsC⟩ ⟨hH5, hD5⟩ from rfl,
      cube_live_slides bClear 6 5 L ⟨c.n, c.k, movesC, slidesC, holeC, c.bench, peakC, peakSC, cCube, hopsC⟩ ⟨hH5, hD5⟩]
  let ysC := laneFold c.n (c.n - c.k) (combStrip c.n c.bench (L.take c.n))
  have hbenchR : bCube.sudo_5Board_5bench = embed ysC := by
    rw [show bCube = cubeLiveBoard bClear 6 5 L ⟨c.n, c.k, movesC, slidesC, holeC, c.bench, peakC, peakSC, cCube, hopsC⟩ ⟨hH5, hD5⟩ from rfl,
      cube_live_bench bClear 6 5 L ⟨c.n, c.k, movesC, slidesC, holeC, c.bench, peakC, peakSC, cCube, hopsC⟩ ⟨hH5, hD5⟩]
  have hlenY : ysC.length = c.bench := by
    have hcomb : (combStrip c.n c.bench (L.take c.n)).length = c.bench :=
      combStrip_length c.n c.bench (L.take c.n)
    simpa [ysC, hcomb] using
      laneFold_length c.n (c.n - c.k) (combStrip c.n c.bench (L.take c.n))
        (by rw [hcomb]; exact c.n_le)
  have hzeroY : ∀ i, c.n ≤ i → ∀ hi : i < ysC.length, ysC[i] = 0 := by
    intro i hlo hi
    have hcoeff := cube_live_high L c.n c.k c.bench c.hn0 c.gap_pos i hlo (hlenY ▸ hi)
    exact (coeff_eq_get ysC i hi).symm.trans hcoeff
  have hposY : 0 < ysC.length := by
    rw [hlenY]; exact Nat.lt_of_lt_of_le c.hn0 c.n_le
  have hnleY : c.n ≤ ysC.length := by rw [hlenY]; exact c.n_le
  have hfitY : FitsLen ysC.length := by rw [hlenY]; exact c.hfitB
  have htriY : allTritList (ysC.take c.n) := by
    have hcomb := combStrip_trits (L.take c.n) c.n c.bench htriL c.span3
    have hlenC : (combStrip c.n c.bench (L.take c.n)).length = c.bench :=
      combStrip_length c.n c.bench (L.take c.n)
    have hfold := laneFold_trits c.n (c.n - c.k) (combStrip c.n c.bench (L.take c.n))
      hcomb (Nat.sub_le _ _) (by rw [hlenC]; exact c.n_le)
    simpa [ysC] using allTritList_take hfold c.n
  let bSCube := settleBoard bClear 5 hH5 hD5 L c.n movesC slidesC peakC
  let peakCube := raisedPeak
    (raisedPeak peakC (countHeld (bClear.sudo_5Board_4held.set ⟨5, hD5⟩ true) 7))
    (countHeld (bSCube.sudo_5Board_4held.set
      ⟨5, settle_held_lt bClear 5 ⟨hH5, hD5⟩ L c.n movesC slidesC peakC⟩ false) 7)
  let peakSRed := raisedPeak peakSC (countHeld bSCube.sudo_5Board_4held 7)
  let holeRed := raisedHole holeC (topIdx (combStrip c.n c.bench (L.take c.n)))
  have hpeakR : bCube.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peakCube := by
    simpa [bCube, peakCube, bSCube] using
      cube_live_peak bClear 6 5 L ⟨c.n, c.k, movesC, slidesC, holeC, c.bench, peakC, peakSC, cCube, hopsC⟩ ⟨hH5, hD5⟩
  have hstrictR : bCube.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakSRed : Int) := by
    simpa [bCube, peakSRed, bSCube, ofNat_eq_natCast] using
      cube_live_strict bClear 6 5 L ⟨c.n, c.k, movesC, slidesC, holeC, c.bench, peakC, peakSC, cCube, hopsC⟩ ⟨hH5, hD5⟩
  have hholeR : bCube.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat holeRed := by
    simpa [bCube, holeRed] using
      cube_live_hole bClear 6 5 L ⟨c.n, c.k, movesC, slidesC, holeC, c.bench, peakC, peakSC, cCube, hopsC⟩ ⟨hH5, hD5⟩
  have hmkR : bCube.sudo_5Board_9marker_on = false := by
    simpa [bCube] using
      cube_live_marker bClear 6 5 L ⟨c.n, c.k, movesC, slidesC, holeC, c.bench, peakC, peakSC, cCube, hopsC⟩ ⟨hH5, hD5⟩
  have honR : bCube.sudo_5Board_8bench_on = true := by
    simpa [bCube] using
      cube_live_on bClear 6 5 L ⟨c.n, c.k, movesC, slidesC, holeC, c.bench, peakC, peakSC, cCube, hopsC⟩ ⟨hH5, hD5⟩
  have htoR : bCube.sudo_5Board_8bench_to = (6 : Int) := by
    simpa [bCube] using
      cube_live_to bClear 6 5 L ⟨c.n, c.k, movesC, slidesC, holeC, c.bench, peakC, peakSC, cCube, hopsC⟩ ⟨hH5, hD5⟩
  have htierR : bCube.sudo_5Board_1t = bClear.sudo_5Board_1t := by
    simpa [bCube] using
      cube_live_tier bClear 6 5 L ⟨c.n, c.k, movesC, slidesC, holeC, c.bench, peakC, peakSC, cCube, hopsC⟩ ⟨hH5, hD5⟩
  have hXCube : CellKeep bCube base.xHome base.x :=
    cubeLive_keep bClear 6 5 base.xHome L ⟨c.n, c.k, movesC, slidesC, holeC, c.bench, peakC, peakSC, cCube, hopsC⟩ base.x ⟨hH5, hD5⟩ h.shape.xNe5 hXClear.heldLt hXClear.homeLt hXClear.held hXClear.arr
  have hH6C : 6 < bClear.sudo_5Board_4home.size := by
    have hHomeM := mul_live_home bLoop 5 6 c.g ys ⟨c.n, c.k, moves, slides, hole, c.bench, peak, peakS, cMul, hops⟩ ⟨hH, hD⟩
    have hszM : bMul.sudo_5Board_4home.size = bLoop.sudo_5Board_4home.size := by
      rw [hHomeM, Array.size_set]
    have hszC : bClear.sudo_5Board_4home.size = bMul.sudo_5Board_4home.size := by
      simp [bClear, clearHeldBoard, Array.size_set]
    rw [hszC, hszM]; exact hH
  have hD6C : 6 < bClear.sudo_5Board_4held.size := by
    rw [show bClear.sudo_5Board_4held.size = bMul.sudo_5Board_4held.size by
      simp [bClear, clearHeldBoard, Array.size_set]]
    have hHeld := mul_live_held bLoop 5 6 c.g ys ⟨c.n, c.k, moves, slides, hole, c.bench, peak, peakS, cMul, hops⟩ ⟨hH, hD⟩
    have hS := settle_held_eq bLoop 6 ⟨hH, hD⟩ ys c.n moves slides peak
    have hsz : bMul.sudo_5Board_4held.size = bLoop.sudo_5Board_4held.size := by
      rw [hHeld]; simp only [Array.size_set]; rw [hS]; simp only [Array.size_set]
    rw [hsz]; exact hD
  have hempty6C : bClear.sudo_5Board_4held[6]'hD6C = false := by
    have hHeld := mul_live_held bLoop 5 6 c.g ys ⟨c.n, c.k, moves, slides, hole, c.bench, peak, peakS, cMul, hops⟩ ⟨hH, hD⟩
    have h6M : 6 < bMul.sudo_5Board_4held.size := by
      rw [show bClear.sudo_5Board_4held.size = bMul.sudo_5Board_4held.size by
        simp [bClear, clearHeldBoard, Array.size_set]] at hD6C
      exact hD6C
    have hget := idx_get hHeld 6 h6M
    have hfalse : bMul.sudo_5Board_4held[6] = false := by
      rw [hget, Array.getElem_set, if_pos rfl]
    have hEq : bClear.sudo_5Board_4held =
        bMul.sudo_5Board_4held.set ⟨5, hKeep.heldLt⟩ false := by
      simp [bClear, clearHeldBoard]
    rw [show bClear.sudo_5Board_4held[6] =
        (bMul.sudo_5Board_4held.set ⟨5, hKeep.heldLt⟩ false)[6]'(hEq ▸ hD6C) from
      idx_get hEq 6 hD6C]
    rw [Array.getElem_set, if_neg (by decide : (5 : Nat) ≠ 6)]
    exact hfalse
  have hH6R : 6 < bCube.sudo_5Board_4home.size := by
    rw [show bCube.sudo_5Board_4home =
        bClear.sudo_5Board_4home.set ⟨5, hH5⟩ #[] by
      simpa [bCube] using
        cube_live_home bClear 6 5 L ⟨c.n, c.k, movesC, slidesC, holeC, c.bench, peakC, peakSC, cCube, hopsC⟩ ⟨hH5, hD5⟩]
    simp [Array.size_set]
    exact hH6C
  have hD6R : 6 < bCube.sudo_5Board_4held.size := by
    have hHeld := cube_live_held bClear 6 5 L ⟨c.n, c.k, movesC, slidesC, holeC, c.bench, peakC, peakSC, cCube, hopsC⟩ ⟨hH5, hD5⟩
    have hsz : bCube.sudo_5Board_4held.size = bClear.sudo_5Board_4held.size := by
      rw [hHeld]
      simp only [Array.size_set]
      rw [settle_held_eq bClear 5 ⟨hH5, hD5⟩ L c.n movesC slidesC peakC]
      simp only [Array.size_set]
    rw [hsz]; exact hD6C
  have hother6 := cube_live_held_other bClear bCube 6 5 6 L ⟨c.n, c.k, movesC, slidesC, holeC, c.bench, peakC, peakSC, cCube, hopsC⟩ ⟨hH5, hD5⟩ rfl (by decide) hD6C hD6R
  have hempty6R := hother6.trans hempty6C
  have h7R : 7 ≤ bCube.sudo_5Board_4held.size := by
    have hHeld := cube_live_held bClear 6 5 L ⟨c.n, c.k, movesC, slidesC, holeC, c.bench, peakC, peakSC, cCube, hopsC⟩ ⟨hH5, hD5⟩
    have hsz : bCube.sudo_5Board_4held.size = bClear.sudo_5Board_4held.size := by
      rw [hHeld]
      simp only [Array.size_set]
      rw [settle_held_eq bClear 5 ⟨hH5, hD5⟩ L c.n movesC slidesC peakC]
      simp only [Array.size_set]
    rw [hsz]
    exact h7C
  have hCubeOps := cube_live_ops bClear 6 5 L ⟨c.n, c.k, movesC, slidesC, holeC, c.bench, peakC, peakSC, cCube, hopsC⟩ ⟨hH5, hD5⟩
  have hops0R : 0 < bCube.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [hCubeOps, Array.size_set]
    exact Nat.lt_trans (by decide : (0 : Nat) < 1) hopsC
  have h0C : 0 < bClear.sudo_5Board_4cost.sudo_5Costs_3ops.size :=
    Nat.lt_trans (by decide : (0 : Nat) < 1) hopsC
  have hopMul : ∀ (h0 : 0 < bMul.sudo_5Board_4cost.sudo_5Costs_3ops.size),
      bMul.sudo_5Board_4cost.sudo_5Costs_3ops[0] = ((cMul + 1 : Nat) : Int) := by
    intro h0
    have hg := idx_get hMulOps 0 h0
    rw [hg, Array.getElem_set]
    simp [ofNat_eq_natCast]
  have hopClear := (idx_get hOpsEq 0 h0C).trans (hopMul _)
  have hop0FromCube := cube_live_op0 bClear bCube 6 5 L ⟨c.n, c.k, movesC, slidesC, holeC, c.bench, peakC, peakSC, cCube, hopsC⟩ ⟨hH5, hD5⟩ rfl hops0R
  have hop0R := hop0FromCube.trans hopClear
  have hfopsR : FitsLen ((cMul + 1) + 1) := by
    apply FitsLen.of_le base.fitO
    have hstep : cMul + 2 ≤ base.ops0 + (done.length + 1) * (base.mMax + 3) := by
      have hsucc : (done.length + 1) * (base.mMax + 3) =
          done.length * (base.mMax + 3) + (base.mMax + 3) := by rw [Nat.succ_mul]
      omega
    have hR : (done.length + 1) * (base.mMax + 3) ≤ base.R * (base.mMax + 3) :=
      Nat.mul_le_mul_right _ hk
    omega
  let pegY := pegCount (ysC.take c.n)
  have hpegZ : 2 * pegY ≤ 2 * c.n := by
    have hp := pegCount_take_le ysC c.n
    simp only [pegY] at hp
    omega
  have hmvCubeLe : mvCube ≤ movesC + 2 * pegL + 2 * c.n + 3 * (c.bench - c.n) := by
    have hle := cubeMoves_le (movesC + 2 * pegL) (L.take c.n) c.n c.k c.bench
    simpa [mvCube, Nat.add_assoc] using hle
  have hShortC : movesC + 2 * base.n ≤
      mvE + base.n + s.tally * pegCharge base.n base.bench +
        mulCharge base.n base.bench + base.n := by
    omega
  have hCubeLe0 : mvCube ≤ movesC + pegCharge base.n base.bench := by
    have h1 := hmvCubeLe
    rw [hcn, hcb] at h1
    have hgroup : movesC + 2 * pegL + 2 * base.n + 3 * (base.bench - base.n) =
        movesC + (2 * pegL + 2 * base.n + 3 * (base.bench - base.n)) := by
      rw [Nat.add_assoc movesC (2 * pegL) (2 * base.n)]
      rw [Nat.add_assoc movesC (2 * pegL + 2 * base.n) (3 * (base.bench - base.n))]
    rw [hgroup] at h1
    exact Nat.le_trans h1 (Nat.add_le_add_left hcubeBase movesC)
  have hpegYn0 : pegY ≤ base.n := by
    have h2 := hpegZ
    rw [hcn] at h2
    omega
  have hfoldR : FitsLen (mvCube + 2 * pegY + c.n * (c.n + 1) + 3 * (c.bench - c.n)) := by
    apply FitsLen.of_le (MoveHeadroom.at hM hmvE)
    have hroom := red_fold_headroom base.n base.bench s.tally mvE movesC mvCube pegY
      hShortC hCubeLe0 hpegYn0
    have hmono := Nat.sub_le_sub_right
      (rungCharge_mono base.n base.bench s.tally base.mMax hT) (2 * base.n)
    have hle : mvCube + 2 * pegY + base.n * (base.n + 1) + 3 * (base.bench - base.n) ≤
        mvE + (rungCharge base.n base.bench base.mMax - 2 * base.n) :=
      Nat.le_trans hroom (Nat.add_le_add_left hmono mvE)
    rw [hcn, hcb]
    exact hle
  have hfmR : FitsLen (mvCube + 2 * pegY + c.n * (c.n + 1)) :=
    FitsLen.of_le hfoldR (by omega)
  have hfitMR : FitsLen (mvCube + 2 * pegY) := FitsLen.of_le hfmR (by omega)
  have hpegFR : FitsLen (2 * pegY) := FitsLen.of_le hfitMR (by omega)
  have hfitSR : FitsLen (slidesCube + 2 * pegY) := by
    apply FitsLen.of_le (SlideHeadroom.at hS hslE)
    have hextra : slidesCube + 2 * pegY ≤
        slE + s.tally * (2 * base.n) + 2 * base.n + 2 * base.n := by
      have hpeg : 2 * pegCount (ys.take c.n) ≤ 2 * base.n := by
        rw [← hcn]; exact hpegY
      have hL : 2 * pegL ≤ 2 * base.n := by rw [← hcn]; exact hpegL
      have hY : 2 * pegY ≤ 2 * base.n := by rw [← hcn]; exact hpegZ
      omega
    exact red_slide_headroom base.n s.tally base.mMax slE _ hT hextra
  have hlenx : base.x.length = c.n := by rw [hxLen, ← hcn]
  have hspan2 : 2 * (c.n - 1) < c.bench := by
    have hs := c.hspan
    omega
  have hfi : FitsLen (2 * (c.n - 1)) := FitsLen.of_le c.h3 (by omega)
  have hmulR := mul_eq_live bCube 5 base.xHome 6 base.x ysC c.w c.h c.r c.n c.k mvCube slidesCube holeRed c.bench peakCube peakSRed (cMul + 1) hmkR honR htoR hH6R hD6R h7R hempty6R hbenchR (by rw [htierR]; exact hnC) c.hn0 hposY hnleY hzeroY c.hf hfitY hmvCube hslidesCube hpeakR hpegFR hfitMR hfitSR hops0R hop0R hfopsR (by rw [htierR]; exact hblC) hXCube.heldLt hXCube.homeLt hXCube.held hXCube.arr h.shape.xNe6 hlenx hspan2 hxT hfi hfmR ⟨c.hw0, c.hh0, c.hrR, c.hrP, c.hnE, c.hkLe, c.hgap⟩ (by rw [htierR]; exact hwC) (by rw [htierR]; exact hhC) (by rw [htierR]; exact hrC) (by rw [htierR]; exact hkC) hholeR hstrictR c.hsm c.hnsm c.hfitB hfoldR
  let bRed := mulNoLiveBoard bCube 5 6 base.x ysC ⟨c.n, c.k, mvCube, slidesCube, holeRed, c.bench, peakCube, peakSRed, (cMul + 1), hops0R⟩ ⟨hH6R, hD6R⟩
  have hmulEq : Ecbs.mul bCube ((5 : Nat) : Int) (base.xHome : Int) ((6 : Nat) : Int)
      false false false = .ok bRed := by
    simpa [bRed] using hmulR
  let mvRed := mulMovesNo (mvCube + 2 * pegY) base.x (ysC.take c.n) c.n c.k c.bench
  have hmvRed : bRed.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mvRed := by
    simpa [bRed, mvRed, pegY] using
      mul_live_moves bCube 5 6 base.x ysC ⟨c.n, c.k, mvCube, slidesCube, holeRed, c.bench, peakCube, peakSRed, (cMul + 1), hops0R⟩ ⟨hH6R, hD6R⟩
  let slRed := slidesCube + 2 * pegY
  have hslRed : bRed.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slRed := by
    simpa [bRed, slRed, pegY] using
      mul_live_slides bCube 5 6 base.x ysC ⟨c.n, c.k, mvCube, slidesCube, holeRed, c.bench, peakCube, peakSRed, (cMul + 1), hops0R⟩ ⟨hH6R, hD6R⟩
  have hcubeAny : ∀ (row : Array Int) (len ctrl high tmax : Int),
      Ecbs.cube (withTally bClear row len ctrl high tmax)
          ((6 : Nat) : Int) ((5 : Nat) : Int) =
        .ok (withTally bCube row len ctrl high tmax) := by
    intro row len ctrl high tmax
    simpa [bCube] using
      cube_eq_live_withTally bClear 6 5 L c.w c.h c.r c.n c.k movesC slidesC holeC c.bench peakC peakSC cCube c.cg hmkC honC htoC hH5 hD5 h7C hemptyC hbenchC hnC c.hn0 hposL hnleL hzeroL c.hf hfitL hmovesC hslidesC hpeakC (by simpa [pegL] using hpegF) (by simpa [pegL] using hfitMC) (by simpa [pegL] using hfitSC) hopsC hop1C hCubeFit hblC hcgC c.hspan htriL c.h3 hfmC ⟨c.hw0, c.hh0, c.hrR, c.hrP, c.hnE, c.hkLe, c.hgap⟩ hwC hhC hrC hkC hholeC hstrictC c.hsm c.hnsm c.hfitB (by simpa [pegL] using hfoldC) row len ctrl high tmax
  have hmulAny : ∀ (row : Array Int) (len ctrl high tmax : Int),
      Ecbs.mul (withTally bCube row len ctrl high tmax)
          ((5 : Nat) : Int) (base.xHome : Int) ((6 : Nat) : Int)
          false false false =
        .ok (withTally bRed row len ctrl high tmax) := by
    intro row len ctrl high tmax
    simpa [bRed] using
      mul_eq_live_withTally bCube 5 base.xHome 6 base.x ysC c.w c.h c.r c.n c.k mvCube slidesCube holeRed c.bench peakCube peakSRed (cMul + 1) hmkR honR htoR hH6R hD6R h7R hempty6R hbenchR (by rw [htierR]; exact hnC) c.hn0 hposY hnleY hzeroY c.hf hfitY hmvCube hslidesCube hpeakR hpegFR hfitMR hfitSR hops0R hop0R hfopsR (by rw [htierR]; exact hblC) hXCube.heldLt hXCube.homeLt hXCube.held hXCube.arr h.shape.xNe6 hlenx hspan2 hxT hfi hfmR ⟨c.hw0, c.hh0, c.hrR, c.hrP, c.hnE, c.hkLe, c.hgap⟩ (by rw [htierR]; exact hwC) (by rw [htierR]; exact hhC) (by rw [htierR]; exact hrC) (by rw [htierR]; exact hkC) hholeR hstrictR c.hsm c.hnsm c.hfitB hfoldR row len ctrl high tmax
  have hbookM := mulLive_book bLoop 5 6 c.g ys ⟨c.n, c.k, moves, slides, hole, c.bench, peak, peakS, cMul, hops⟩ ⟨hH, hD⟩
  have hbookC := clearHeld_book bMul 5 c.g mvC ⟨hKeep.homeLt, hKeep.heldLt⟩
  let dp := pegPack c c.m c.hm (Nat.le_refl _)
  have hpb := pegPack_board c c.m c.hm (Nat.le_refl _)
  have hbPack : dp.b = bLoop := hpb.1.trans hpegB.symm
  have hlenC : bClear.sudo_5Board_9tally_len = (s.tally : Int) := by
    rw [hbookC.2.2.2.1, hbookM.2.2.1, ← hbPack, hpb.2.2.2.1, hlen0]
  have hhighC : bClear.sudo_5Board_4cost.sudo_5Costs_15control_highest = (s.high : Int) := by
    rw [hbookC.2.2.2.2.2.2.1, hbookM.2.2.2.2.2.1, ← hbPack, hpb.2.2.2.2.2.2.1,
      c.hHigh, hhighS]
  have hctrlC : bClear.sudo_5Board_4cost.sudo_5Costs_4ctrl =
      ((s.ctrl + s.tally : Nat) : Int) := by
    have hpack : dp.b.sudo_5Board_4cost.sudo_5Costs_4ctrl =
        ((s.ctrl + s.tally : Nat) : Int) := by
      rw [dp.hctrl, dp.hctrlN, hctrl0, hmEq]
    rw [hbookC.2.2.2.2.2.2.2.1, hbookM.2.2.2.2.2.2.1, ← hbPack, hpack]
  have ht0C : bClear.sudo_5Board_6tally0 = (s.t0 : Int) := by
    rw [hbookC.2.2.2.2.1, hbookM.2.2.2.1, ← hbPack, hpb.2.2.2.2.1, c.hT0, ht0]
  have hrowC : bClear.sudo_5Board_3row = embed (paintRed s.row s.t0 s.tally) := by
    rw [hbookC.1, hbookM.2.2.2.2.2.2.2, hRow]
  have hctrlN : bClear.sudo_5Board_1t.sudo_4Tier_7control = (base.control : Int) := by
    have htM : bMul.sudo_5Board_1t = bLoop.sudo_5Board_1t := by
      simpa [bMul] using
        mul_live_tier bLoop 5 6 c.g ys ⟨c.n, c.k, moves, slides, hole, c.bench, peak, peakS, cMul, hops⟩ ⟨hH, hD⟩
    have htC : bClear.sudo_5Board_1t = bMul.sudo_5Board_1t := by
      simp [bClear, clearHeldBoard]
    rw [htC, htM, htier, c.hCtrlN, hcontrol]
  have hmaxC : bClear.sudo_5Board_4cost.sudo_5Costs_9tally_max =
      b.sudo_5Board_4cost.sudo_5Costs_9tally_max := by
    rw [clear_tmax bMul 5 c.g mvC ⟨hKeep.homeLt, hKeep.heldLt⟩,
      mulLive_tmax bLoop 5 6 c.g ys
        ⟨c.n, c.k, moves, slides, hole, c.bench, peak, peakS, cMul, hops⟩ ⟨hH, hD⟩,
      ← hbPack, pegPack_tmax c c.m c.hm (Nat.le_refl _), hmax0]
  have ht0Cube : bCube.sudo_5Board_6tally0 = (s.t0 : Int) := by
    have h1 := cube_live_tally bClear 6 5 L ⟨c.n, c.k, movesC, slidesC, holeC, c.bench, peakC, peakSC, cCube, hopsC⟩ ⟨hH5, hD5⟩
    exact h1.trans ht0C
  have ht0Red : bRed.sudo_5Board_6tally0 = (s.t0 : Int) := by
    have h1 := mul_live_tally bCube 5 6 base.x ysC ⟨c.n, c.k, mvCube, slidesCube, holeRed, c.bench, peakCube, peakSRed, (cMul + 1), hops0R⟩ ⟨hH6R, hD6R⟩
    exact h1.trans ht0Cube
  have htierCube : bCube.sudo_5Board_1t = bClear.sudo_5Board_1t := by
    simpa [bCube] using
      cube_live_tier bClear 6 5 L ⟨c.n, c.k, movesC, slidesC, holeC, c.bench, peakC, peakSC, cCube, hopsC⟩ ⟨hH5, hD5⟩
  have htierRed : bRed.sudo_5Board_1t = bClear.sudo_5Board_1t := by
    have h1 := mul_live_tier bCube 5 6 base.x ysC ⟨c.n, c.k, mvCube, slidesCube, holeRed, c.bench, peakCube, peakSRed, (cMul + 1), hops0R⟩ ⟨hH6R, hD6R⟩
    exact h1.trans htierCube
  have hAimR := mul_live_aimed bCube 5 6 base.x ysC ⟨c.n, c.k, mvCube, slidesCube, holeRed, c.bench, peakCube, peakSRed, (cMul + 1), hops0R⟩ ⟨hH6R, hD6R⟩
  have hlenRed : bRed.sudo_5Board_9tally_len = (s.tally : Int) := by
    have hMul := mulLive_carries bCube 5 6 base.x ysC ⟨c.n, c.k, mvCube, slidesCube, holeRed, c.bench, peakCube, peakSRed, (cMul + 1), hops0R⟩ ⟨hH6R, hD6R⟩
    have hCubeK := cubeLive_carries bClear 6 5 L ⟨c.n, c.k, movesC, slidesC, holeC, c.bench, peakC, peakSC, cCube, hopsC⟩ ⟨hH5, hD5⟩
    rw [hMul.2.2.1, hCubeK.2.2, hlenC]
  have hBenchRed : bRed.sudo_5Board_5bench =
      embed (fieldMul s.n s.k s.benchlen base.x
        (fieldCube s.n s.k s.benchlen
          (fieldMul s.n s.k s.benchlen s.gap
            (cubeTimes s.n s.k s.benchlen s.gap s.tally))) ++
        List.replicate (s.benchlen - s.n) 0) := by
    have hpre : ys.take c.n = cubeTimes c.n c.k c.bench c.g c.m := by
      rw [hysEq]
      exact cubeBenchIter_prefix c.n c.k c.bench c.g c.hlenx c.m
    have hLtake : L.take c.n =
        fieldMul c.n c.k c.bench c.g (cubeTimes c.n c.k c.bench c.g c.m) := by
      have hpre2 : L.take c.n = fieldMul c.n c.k c.bench c.g (ys.take c.n) := by
        simpa [L] using mul_live_prefix c.n c.k c.bench c.g ys
      rw [hpre2, hpre]
    have hysTake : ysC.take c.n = fieldCube c.n c.k c.bench (L.take c.n) := by
      simpa [ysC] using cube_live_prefix c.n c.k c.bench L
    have hraw := mul_live_bench_gap bCube 5 6 base.x ysC ⟨c.n, c.k, mvCube, slidesCube, holeRed, c.bench, peakCube, peakSRed, (cMul + 1), hops0R⟩ ⟨hH6R, hD6R⟩ c.hn0 c.gap_pos c.n_le
    rw [show bRed.sudo_5Board_5bench =
        (mulNoLiveBoard bCube 5 6 base.x ysC ⟨c.n, c.k, mvCube, slidesCube, holeRed, c.bench, peakCube, peakSRed, (cMul + 1), hops0R⟩ ⟨hH6R, hD6R⟩).sudo_5Board_5bench from rfl,
      hraw, hysTake, hLtake, hn, hkN, hbch, hg, hmEq]
  have hclearPark : ∀ (row : Array Int) (ctrl fromHole ridx : Int),
      Ecbs.clear (withPark bMul row ctrl fromHole ridx) ((5 : Nat) : Int) =
        .ok (withPark bClear row ctrl fromHole ridx) := by
    intro row ctrl fromHole ridx
    let hHp := withPark_home bMul row ctrl fromHole ridx ▸ hKeep.homeLt
    let hDp := withPark_held bMul row ctrl fromHole ridx ▸ hKeep.heldLt
    have hC := clear_held_refines (withPark bMul row ctrl fromHole ridx) 5 c.g mvC hHp hDp
      (by simpa [withPark] using hKeep.held)
      (by simpa [withPark] using hKeep.arr)
      (by simpa [withPark] using hmvC)
      hfitN hfitC
    have hcomm := clearHeld_withPark bMul row ctrl fromHole ridx 5 c.g mvC ⟨hKeep.homeLt, hKeep.heldLt⟩
    have hir := clearHeld_irrel (withPark bMul row ctrl fromHole ridx) 5 c.g mvC
      hHp (withPark_home bMul row ctrl fromHole ridx ▸ hKeep.homeLt)
      hDp (withPark_held bMul row ctrl fromHole ridx ▸ hKeep.heldLt)
    simpa [bClear, hcomm, hir, clearHeldBoard] using hC
  have hcubePark : ∀ (row : Array Int) (ctrl fromHole ridx : Int),
      Ecbs.cube (withPark bClear row ctrl fromHole ridx)
          ((6 : Nat) : Int) ((5 : Nat) : Int) =
        .ok (withPark bCube row ctrl fromHole ridx) := by
    intro row ctrl fromHole ridx
    simpa [bCube] using
      cube_eq_live_withPark bClear 6 5 L c.w c.h c.r c.n c.k movesC slidesC holeC c.bench peakC peakSC cCube c.cg hmkC honC htoC hH5 hD5 h7C hemptyC hbenchC hnC c.hn0 hposL hnleL hzeroL c.hf hfitL hmovesC hslidesC hpeakC (by simpa [pegL] using hpegF) (by simpa [pegL] using hfitMC) (by simpa [pegL] using hfitSC) hopsC hop1C hCubeFit hblC hcgC c.hspan htriL c.h3 hfmC ⟨c.hw0, c.hh0, c.hrR, c.hrP, c.hnE, c.hkLe, c.hgap⟩ hwC hhC hrC hkC hholeC hstrictC c.hsm c.hnsm c.hfitB (by simpa [pegL] using hfoldC) row ctrl fromHole ridx
  have hmulPark : ∀ (row : Array Int) (ctrl fromHole ridx : Int),
      Ecbs.mul (withPark bCube row ctrl fromHole ridx)
          ((5 : Nat) : Int) (base.xHome : Int) ((6 : Nat) : Int)
          false false false =
        .ok (withPark bRed row ctrl fromHole ridx) := by
    intro row ctrl fromHole ridx
    simpa [bRed] using
      mul_eq_live_withPark bCube 5 base.xHome 6 base.x ysC c.w c.h c.r c.n c.k mvCube slidesCube holeRed c.bench peakCube peakSRed (cMul + 1) hmkR honR htoR hH6R hD6R h7R hempty6R hbenchR (by rw [htierR]; exact hnC) c.hn0 hposY hnleY hzeroY c.hf hfitY hmvCube hslidesCube hpeakR hpegFR hfitMR hfitSR hops0R hop0R hfopsR (by rw [htierR]; exact hblC) hXCube.heldLt hXCube.homeLt hXCube.held hXCube.arr h.shape.xNe6 hlenx hspan2 hxT hfi hfmR ⟨c.hw0, c.hh0, c.hrR, c.hrP, c.hnE, c.hkLe, c.hgap⟩ (by rw [htierR]; exact hwC) (by rw [htierR]; exact hhC) (by rw [htierR]; exact hrC) (by rw [htierR]; exact hkC) hholeR hstrictR c.hsm c.hnsm c.hfitB hfoldR row ctrl fromHole ridx
  have hcubeBoth : ∀ (rowD rowP : Array Int) (len high tmax : Int)
      (ctrlD ctrlP fromHole ridx : Int),
      Ecbs.cube (withPark (withTally bClear rowD len ctrlD high tmax) rowP ctrlP fromHole ridx)
          ((6 : Nat) : Int) ((5 : Nat) : Int) =
        .ok (withPark (withTally bCube rowD len ctrlD high tmax) rowP ctrlP fromHole ridx) := by
    intro rowD rowP len high tmax ctrlD ctrlP fromHole ridx
    simpa [bCube] using
      cube_eq_live_withPark_withTally bClear 6 5 L c.w c.h c.r c.n c.k movesC slidesC holeC c.bench peakC peakSC cCube c.cg hmkC honC htoC hH5 hD5 h7C hemptyC hbenchC hnC c.hn0 hposL hnleL hzeroL c.hf hfitL hmovesC hslidesC hpeakC (by simpa [pegL] using hpegF) (by simpa [pegL] using hfitMC) (by simpa [pegL] using hfitSC) hopsC hop1C hCubeFit hblC hcgC c.hspan htriL c.h3 hfmC ⟨c.hw0, c.hh0, c.hrR, c.hrP, c.hnE, c.hkLe, c.hgap⟩ hwC hhC hrC hkC hholeC hstrictC c.hsm c.hnsm c.hfitB (by simpa [pegL] using hfoldC) rowD rowP len high tmax ctrlD ctrlP fromHole ridx
  have hmulBoth : ∀ (rowD rowP : Array Int) (len high tmax : Int)
      (ctrlD ctrlP fromHole ridx : Int),
      Ecbs.mul (withPark (withTally bCube rowD len ctrlD high tmax) rowP ctrlP fromHole ridx)
          ((5 : Nat) : Int) (base.xHome : Int) ((6 : Nat) : Int)
          false false false =
        .ok (withPark (withTally bRed rowD len ctrlD high tmax) rowP ctrlP fromHole ridx) := by
    intro rowD rowP len high tmax ctrlD ctrlP fromHole ridx
    simpa [bRed] using
      mul_eq_live_withPark_withTally bCube 5 base.xHome 6 base.x ysC c.w c.h c.r c.n c.k mvCube slidesCube holeRed c.bench peakCube peakSRed (cMul + 1) hmkR honR htoR hH6R hD6R h7R hempty6R hbenchR (by rw [htierR]; exact hnC) c.hn0 hposY hnleY hzeroY c.hf hfitY hmvCube hslidesCube hpeakR hpegFR hfitMR hfitSR hops0R hop0R hfopsR (by rw [htierR]; exact hblC) hXCube.heldLt hXCube.homeLt hXCube.held hXCube.arr h.shape.xNe6 hlenx hspan2 hxT hfi hfmR ⟨c.hw0, c.hh0, c.hrR, c.hrP, c.hnE, c.hkLe, c.hgap⟩ (by rw [htierR]; exact hwC) (by rw [htierR]; exact hhC) (by rw [htierR]; exact hrC) (by rw [htierR]; exact hkC) hholeR hstrictR c.hsm c.hnsm c.hfitB hfoldR rowD rowP len high tmax ctrlD ctrlP fromHole ridx
  have hRedLe : mvRed ≤ mvCube + mulCharge base.n base.bench := by
    have hstep := mulMovesNo_bound mvCube c.n c.k c.bench base.x ysC c.n_le
    have hrest : 2 * pegY + c.n * (c.n + 1) + 3 * (c.bench - c.n) ≤
        mulCharge c.n c.bench := by
      unfold mulCharge
      exact Nat.add_le_add (Nat.add_le_add hpegZ (Nat.le_refl _)) (Nat.le_refl _)
    have hbound : mvRed ≤ mvCube + (2 * pegY + c.n * (c.n + 1) + 3 * (c.bench - c.n)) := by
      simpa [mvRed, pegY, Nat.add_assoc] using hstep
    have h1 : mvRed ≤ mvCube + mulCharge c.n c.bench :=
      Nat.le_trans hbound (Nat.add_le_add_left hrest mvCube)
    rw [show mulCharge c.n c.bench = mulCharge base.n base.bench by rw [hcn, hcb]] at h1
    exact h1
  have hMovTight : mvRed + 2 * base.n ≤ mvE + rungCharge base.n base.bench s.tally :=
    red_mul_tight base.n base.bench s.tally mvE movesC mvRed hShortC
      (Nat.le_trans hRedLe (Nat.add_le_add hCubeLe0 (Nat.le_refl _)))
  have hSlideShort : slidesC ≤ slE + s.tally * (2 * base.n) := by
    have hpeg : 2 * pegCount (ys.take c.n) ≤ 2 * base.n := by
      rw [← hcn]
      exact hpegY
    have h1 : slidesC ≤ slides + 2 * base.n := by
      simpa [slidesC] using Nat.add_le_add_left hpeg slides
    exact Nat.le_trans h1 hloopS
  have hSldTight : slRed + 2 * base.n ≤ slE + rungSlideCharge base.n s.tally := by
    have h2L : 2 * pegL ≤ 2 * base.n := by rw [← hcn]; exact hpegL
    have h2Y : 2 * pegY ≤ 2 * base.n := by rw [← hcn]; exact hpegZ
    have hR : slRed ≤ slidesC + 2 * base.n + 2 * base.n := by
      simp [slRed, slidesCube]
      omega
    exact red_slide_tight base.n s.tally slE slidesC slRed hSlideShort hR
  have hhighRed : bRed.sudo_5Board_4cost.sudo_5Costs_15control_highest = (s.high : Int) := by
    rw [mul_live_highest bCube 5 6 base.x ysC ⟨c.n, c.k, mvCube, slidesCube, holeRed, c.bench, peakCube, peakSRed, (cMul + 1), hops0R⟩ ⟨hH6R, hD6R⟩,
      cube_live_highest bClear 6 5 L ⟨c.n, c.k, movesC, slidesC, holeC, c.bench, peakC, peakSC, cCube, hopsC⟩ ⟨hH5, hD5⟩,
      hhighC]
  have htmaxRed : bRed.sudo_5Board_4cost.sudo_5Costs_9tally_max =
      b.sudo_5Board_4cost.sudo_5Costs_9tally_max := by
    rw [mulLive_tmax bCube 5 6 base.x ysC ⟨c.n, c.k, mvCube, slidesCube, holeRed, c.bench, peakCube, peakSRed, (cMul + 1), hops0R⟩ ⟨hH6R, hD6R⟩,
      cubeLive_tmax bClear 6 5 L ⟨c.n, c.k, movesC, slidesC, holeC, c.bench, peakC, peakSC, cCube, hopsC⟩ ⟨hH5, hD5⟩,
      hmaxC]
  have hRel : ∃ (mvE' mvR slE' slR : Nat),
      b.sudo_5Board_4cost.sudo_5Costs_5moves = (mvE' : Int) ∧
      bRed.sudo_5Board_4cost.sudo_5Costs_5moves = (mvR : Int) ∧
      mvR + 2 * base.n ≤ mvE' + rungCharge base.n base.bench s.tally ∧
      b.sudo_5Board_4cost.sudo_5Costs_6slides = (slE' : Int) ∧
      bRed.sudo_5Board_4cost.sudo_5Costs_6slides = (slR : Int) ∧
      slR + 2 * base.n ≤ slE' + rungSlideCharge base.n s.tally :=
    ⟨mvE, mvRed, slE, slRed, hmvE, by simpa [ofNat_eq_natCast] using hmvRed, hMovTight,
      hslE, by simpa [ofNat_eq_natCast] using hslRed, hSldTight⟩
  refine ⟨bLoop, bMul, bClear, bCube, bRed, hmulG, hclearEq, hcubeEq, hmulEq,
    hRel,
    hlenC, ht0C, hrowC, hctrlN, hhighC, hctrlC, hmaxC,
    ht0Cube, ht0Red, htierCube, htierRed, hcubeAny, hmulAny,
    hAimR.1, hAimR.2, hlenRed, hBenchRed, hclearPark, hcubePark, hmulPark,
    hcubeBoth, hmulBoth,
    ⟨c, ys, moves, slides, hole, peak, peakS, cMul, hH, hD, hops,
      hpegB, hrow0, hctrl0, hg, hmEq, hn, hkN, hbch, hsrc, ht0,
      rfl, hysEq,
      (by
        apply ofNat_inj_nat
        have hP := (pegPack c c.m c.hm (Nat.le_refl _)).hmoves
        have hB : (pegPack c c.m c.hm (Nat.le_refl _)).b = bLoop :=
          (pegPack_board c c.m c.hm (Nat.le_refl _)).1.trans hpegB.symm
        rw [hB] at hP
        exact (hP.symm.trans hmvB).symm),
      (by
        apply ofNat_inj_nat
        have hP := (pegPack c c.m c.hm (Nat.le_refl _)).hslides
        have hB : (pegPack c c.m c.hm (Nat.le_refl _)).b = bLoop :=
          (pegPack_board c c.m c.hm (Nat.le_refl _)).1.trans hpegB.symm
        rw [hB] at hP
        exact (hP.symm.trans hslB).symm),
      (by
        apply ofNat_inj_nat
        have hP := (pegPack c c.m c.hm (Nat.le_refl _)).hHole
        have hB : (pegPack c c.m c.hm (Nat.le_refl _)).b = bLoop :=
          (pegPack_board c c.m c.hm (Nat.le_refl _)).1.trans hpegB.symm
        rw [hB] at hP
        exact (hP.symm.trans hhoB).symm),
      (by
        apply ofNat_inj_nat
        have hP := (pegPack c c.m c.hm (Nat.le_refl _)).hpeak
        have hB : (pegPack c c.m c.hm (Nat.le_refl _)).b = bLoop :=
          (pegPack_board c c.m c.hm (Nat.le_refl _)).1.trans hpegB.symm
        rw [hB] at hP
        exact (hP.symm.trans hpkB).symm),
      (by
        apply ofNat_inj_nat
        have hP := (pegPack c c.m c.hm (Nat.le_refl _)).hpeakS
        have hB : (pegPack c c.m c.hm (Nat.le_refl _)).b = bLoop :=
          (pegPack_board c c.m c.hm (Nat.le_refl _)).1.trans hpegB.symm
        rw [hB] at hP
        exact (hP.symm.trans hpsB).symm), hcopy⟩, hRel, hhighRed, htmaxRed⟩



/-- `ClimbInvK` supplies the core and one charge of tight headroom. -/
noncomputable def red_cube_mul_ofK {done rest : List Nat} {r : Nat} {b : Ecbs.Board}
    {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvK done (r :: rest) b s base)
    (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax)
    (hhome : s.onBench = false)
    (hxLen : base.x.length = base.n) (hxT : allTritList base.x) :=
  red_cube_mul h.toCore (moveHeadroom_of_cons h) (slideHeadroom_of_cons h)
    hm hT hhome hxLen hxT

/-- Non-final rung, before `cube spare gap`. Doubles the red tally on the cleared
    gap board. The recorded high, the empty tail, and `tally_max` are read from
    `ClimbInvK`. The spare cube and the mul by the input on that doubled board
    are the corollary `red_doubled_cube_mul`; this theorem stops at the double.
    The i64 fits on the counter, the index, and the new length follow from
    `fitCtrl`, `fitControl`, and the running `rungCharge` bound. -/
theorem red_open_double {done rest : List Nat} {r : Nat} {b : Ecbs.Board}
    {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvK done (r :: rest) b s base)
    (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax)
    (hhome : s.onBench = false) (hrest : rest ≠ []) :
    ∃ (bLoop bMul bClear bD : Ecbs.Board),
      Ecbs.mul bLoop ((5 : Nat) : Int) ((5 : Nat) : Int) ((6 : Nat) : Int)
          false false false = .ok bMul ∧
      Ecbs.clear bMul ((5 : Nat) : Int) = .ok bClear ∧
      Ecbs.tally_double bClear = .ok bD := by
  have hge : 2 ≤ (r :: rest).length := by
    cases rest with
    | nil => exact absurd rfl hrest
    | cons _ _ => simp
  have hRoom : s.t0 + 2 * s.tally ≤ base.control := h.openRoom hge
  have hHighEq : s.t0 + s.tally - 1 ≤ s.high := by
    rw [h.highTop]
    exact Nat.le_max_right _ _
  obtain ⟨tmax, hMax⟩ := h.tmaxLt
  have hRpos : 0 < base.R := by
    have hk := h.kLe
    rw [List.length_append, List.length_cons] at hk
    omega
  have hn0 : 0 < base.n := by rw [← h.hn]; exact h.shape.peg.n_pos
  have hFitL1 : FitsLen (2 * s.tally + 1) :=
    double_len_fit hn0 hRpos hT base.fitM
  have hFitM : FitsLen (2 * s.tally) := FitsLen.of_le hFitL1 (by omega)
  have hFitI : FitsLen (s.t0 + 2 * s.tally) :=
    (double_index_fit_le hRoom base.fitControl).1
  have hdone : done.length ≤ base.R := by
    have hk := h.kLe
    rw [List.length_append] at hk
    omega
  have hCtrlPair := double_ctrl_fit h.ctrlLe hT hdone base.fitCtrl
  have hFitC : FitsLen (s.ctrl + 3 * s.tally) := hCtrlPair.1
  obtain ⟨c, bLoop, ys, moves, slides, hole, peak, peakS, cMul, hH, hD, hops,
      _hcopy, _hsrc, _hg, hmEq, hn, _hkN, hbch, hpegB, _hys, hGap, _hX,
      _hOp, hRow, _htier, _hmk, _h7, _hop0, _hOpsLe, hctrl0, hhighS,
      hcontrol, hlen0, hmax0, ht0, hmul, _hrow0, _hmvB, _hslB, _hhoB, _hpkB, _hpsB,
      ⟨mvE, hmvE, hmovRel⟩, ⟨_, _, _⟩, _hmulW⟩ :=
    mul_of_shape_ofK h hm hT hhome
  obtain ⟨mvAbs, hmvAbs, hmvAbsLe⟩ := h.moves_loose
  have hmvEeq : mvE = mvAbs := ofNat_inj_nat (hmvE.symm.trans hmvAbs)
  have hMov : moves ≤ base.moves0 + done.length * rungCharge base.n base.bench base.mMax +
      base.n + s.tally * pegCharge base.n base.bench := by
    have hloose : moves ≤ mvE + base.n + s.tally * pegCharge base.n base.bench := by
      omega
    have hrel := hloose
    rw [hmvEeq] at hrel
    have hflat : mvAbs + base.n + s.tally * pegCharge base.n base.bench =
        mvAbs + (base.n + s.tally * pegCharge base.n base.bench) := by
      rw [← Nat.add_assoc]
    rw [hflat] at hrel
    have hstep := Nat.add_le_add_right hmvAbsLe
      (base.n + s.tally * pegCharge base.n base.bench)
    have hright := (Nat.add_assoc
      (base.moves0 + done.length * rungCharge base.n base.bench base.mMax)
      base.n (s.tally * pegCharge base.n base.bench)).symm
    exact Nat.le_trans (Nat.le_trans hrel hstep) (Nat.le_of_eq hright)
  let bMul := mulNoLiveBoard bLoop 5 6 c.g ys ⟨c.n, c.k, moves, slides, hole, c.bench, peak, peakS, cMul, hops⟩ ⟨hH, hD⟩
  have hKeep := mulLive_keep bLoop 5 6 5 c.g ys ⟨c.n, c.k, moves, slides, hole, c.bench, peak, peakS, cMul, hops⟩ c.g ⟨hH, hD⟩ (by decide) hGap.heldLt hGap.homeLt hGap.held hGap.arr
  let mvC := mulMovesNo (moves + 2 * pegCount (ys.take c.n)) c.g (ys.take c.n)
    c.n c.k c.bench
  have hmvC : bMul.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mvC := by
    simpa [bMul, mvC] using
      mul_live_moves bLoop 5 6 c.g ys ⟨c.n, c.k, moves, slides, hole, c.bench, peak, peakS, cMul, hops⟩ ⟨hH, hD⟩
  have hfitN : FitsLen c.g.length := by rw [c.hlenx]; exact c.hf
  have hpegN : pegCount c.g ≤ c.n := by rw [← c.hlenx]; exact pegCount_le c.g
  have hmvC_le : mvC ≤ moves + mulCharge c.n c.bench := by
    have hstep := mulMovesNo_bound moves c.n c.k c.bench c.g ys c.n_le
    have hrest : 2 * pegCount (ys.take c.n) + c.n * (c.n + 1) + 3 * (c.bench - c.n) ≤
        mulCharge c.n c.bench := by
      unfold mulCharge
      have hp := pegCount_take_le ys c.n
      omega
    omega
  have hk : done.length + 1 ≤ base.R := by
    have hlen := h.kLe
    rw [List.length_append, List.length_cons] at hlen
    omega
  have hbudget : mvC + pegCount c.g ≤
      base.moves0 + base.R * rungCharge base.n base.bench base.mMax := by
    have hmulC : mulCharge c.n c.bench = mulCharge base.n base.bench := by
      rw [hn, hbch, h.hn, h.hbench]
    have hcn : c.n = base.n := by rw [hn, h.hn]
    have h1 : mvC + pegCount c.g ≤ moves + mulCharge base.n base.bench + base.n := by
      have hadd := Nat.add_le_add hmvC_le hpegN
      rw [hmulC, hcn] at hadd
      exact hadd
    have h2 : moves + mulCharge base.n base.bench + base.n ≤
        base.moves0 + done.length * rungCharge base.n base.bench base.mMax +
          (base.n + s.tally * pegCharge base.n base.bench) +
          (mulCharge base.n base.bench + base.n) := by
      have hadd := Nat.add_le_add_right hMov (mulCharge base.n base.bench + base.n)
      simpa [Nat.add_assoc] using hadd
    have hpiece : base.n + s.tally * pegCharge base.n base.bench +
        (mulCharge base.n base.bench + base.n) ≤
        rungCharge base.n base.bench base.mMax := by
      unfold rungCharge
      have hpeg : s.tally * pegCharge base.n base.bench ≤
          (base.mMax + 1) * pegCharge base.n base.bench :=
        Nat.mul_le_mul_right _ (Nat.le_succ_of_le hT)
      have hnn : base.n + base.n = 2 * base.n := by rw [Nat.two_mul]
      have htwo : mulCharge base.n base.bench + mulCharge base.n base.bench =
          2 * mulCharge base.n base.bench := by rw [Nat.two_mul]
      omega
    have h3 : base.moves0 + done.length * rungCharge base.n base.bench base.mMax +
        (base.n + s.tally * pegCharge base.n base.bench) +
        (mulCharge base.n base.bench + base.n) ≤
        base.moves0 + done.length * rungCharge base.n base.bench base.mMax +
          rungCharge base.n base.bench base.mMax := by
      have hadd := Nat.add_le_add_left hpiece
        (base.moves0 + done.length * rungCharge base.n base.bench base.mMax)
      simpa [Nat.add_assoc] using hadd
    have hsucc : base.moves0 + done.length * rungCharge base.n base.bench base.mMax +
        rungCharge base.n base.bench base.mMax =
        base.moves0 + (done.length + 1) * rungCharge base.n base.bench base.mMax := by
      rw [Nat.add_assoc, ← Nat.succ_mul]
    have hR : base.moves0 + (done.length + 1) * rungCharge base.n base.bench base.mMax ≤
        base.moves0 + base.R * rungCharge base.n base.bench base.mMax :=
      Nat.add_le_add_left (Nat.mul_le_mul_right _ hk) _
    exact Nat.le_trans h1 (Nat.le_trans h2 (Nat.le_trans h3
      (Nat.le_trans (Nat.le_of_eq hsucc) hR)))
  have hfitC : FitsLen (mvC + pegCount c.g) := FitsLen.of_le base.fitM hbudget
  have hclear := clear_held_refines bMul 5 c.g mvC hKeep.homeLt hKeep.heldLt
    hKeep.held hKeep.arr hmvC hfitN hfitC
  let bClear := clearHeldBoard bMul 5 c.g mvC hKeep.homeLt hKeep.heldLt
  have hclearEq : Ecbs.clear bMul ((5 : Nat) : Int) = .ok bClear := by
    simpa [bClear, clearHeldBoard] using hclear
  have hbookM := mulLive_book bLoop 5 6 c.g ys ⟨c.n, c.k, moves, slides, hole, c.bench, peak, peakS, cMul, hops⟩ ⟨hH, hD⟩
  have hbookC := clearHeld_book bMul 5 c.g mvC ⟨hKeep.homeLt, hKeep.heldLt⟩
  let dp := pegPack c c.m c.hm (Nat.le_refl _)
  have hpb := pegPack_board c c.m c.hm (Nat.le_refl _)
  have hbPack : dp.b = bLoop := hpb.1.trans hpegB.symm
  have hlenC : bClear.sudo_5Board_9tally_len = (s.tally : Int) := by
    rw [hbookC.2.2.2.1, hbookM.2.2.1, ← hbPack, hpb.2.2.2.1, hlen0]
  have hhighC : bClear.sudo_5Board_4cost.sudo_5Costs_15control_highest = (s.high : Int) := by
    rw [hbookC.2.2.2.2.2.2.1, hbookM.2.2.2.2.2.1, ← hbPack, hpb.2.2.2.2.2.2.1,
      c.hHigh, hhighS]
  have hctrlC : bClear.sudo_5Board_4cost.sudo_5Costs_4ctrl =
      ((s.ctrl + s.tally : Nat) : Int) := by
    have hpack : dp.b.sudo_5Board_4cost.sudo_5Costs_4ctrl = ((s.ctrl + s.tally : Nat) : Int) := by
      rw [dp.hctrl, dp.hctrlN, hctrl0, hmEq]
    rw [hbookC.2.2.2.2.2.2.2.1, hbookM.2.2.2.2.2.2.1, ← hbPack, hpack]
  have ht0C : bClear.sudo_5Board_6tally0 = (s.t0 : Int) := by
    rw [hbookC.2.2.2.2.1, hbookM.2.2.2.1, ← hbPack, hpb.2.2.2.2.1, c.hT0, ht0]
  have hrowC : bClear.sudo_5Board_3row = embed (paintRed s.row s.t0 s.tally) := by
    rw [hbookC.1, hbookM.2.2.2.2.2.2.2, hRow]
  have hctrlN : bClear.sudo_5Board_1t.sudo_4Tier_7control = (base.control : Int) := by
    have htM : bMul.sudo_5Board_1t = bLoop.sudo_5Board_1t := by
      simpa [bMul] using
        mul_live_tier bLoop 5 6 c.g ys ⟨c.n, c.k, moves, slides, hole, c.bench, peak, peakS, cMul, hops⟩ ⟨hH, hD⟩
    have htC : bClear.sudo_5Board_1t = bMul.sudo_5Board_1t := by
      simp [bClear, clearHeldBoard]
    rw [htC, htM, _htier, c.hCtrlN, hcontrol]
  have hmaxC : bClear.sudo_5Board_4cost.sudo_5Costs_9tally_max = (tmax : Int) := by
    rw [clear_tmax bMul 5 c.g mvC ⟨hKeep.homeLt, hKeep.heldLt⟩,
      mulLive_tmax bLoop 5 6 c.g ys
        ⟨c.n, c.k, moves, slides, hole, c.bench, peak, peakS, cMul, hops⟩ ⟨hH, hD⟩,
      ← hbPack, pegPack_tmax c c.m c.hm (Nat.le_refl _),
      hmax0, hMax]
  have hopen : rest ≠ [] := hrest
  let xs := paintRed s.row s.t0 s.tally
  have hRed : ∀ j (hj : j < s.tally),
      xs[s.t0 + j]'(by
        simp [xs, paintRed_length]
        exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj s.t0) h.shape.seg.room) = 2 := by
    intro j hj
    simpa [xs] using paintRed_get_lo s.row s.t0 s.tally j hj h.shape.seg.room
  have hZero : ∀ k (hk : k < s.tally),
      xs[s.t0 + s.tally + k]'(by
        simp [xs, paintRed_length, h.shape.rowLen]
        omega) = 0 := by
    intro k hk
    have hlen : s.row.length = base.control := h.shape.rowLen
    have hix : s.t0 + (s.tally + k) < s.row.length := by
      rw [hlen]
      omega
    have hsrc := h.openZero hge k hk
      (by simpa [Nat.add_assoc] using hix)
    have hsrc' : s.row[s.t0 + s.tally + k]'(by omega) = 0 := hsrc
    have hget := paintRed_get_hi s.row s.t0 s.tally (s.t0 + s.tally + k)
      (by omega) (by omega)
    simpa [xs] using hget.trans hsrc'
  have hfitC0 : FitsLen (s.ctrl + s.tally + 2 * s.tally) :=
    FitsLen.of_le hFitC (by omega)
  have htally := tally_double_refines bClear xs s.t0 s.tally (s.ctrl + s.tally)
    s.high base.control tmax hm hlenC ht0C hrowC
    (by
      change s.t0 + 2 * s.tally ≤ (paintRed s.row s.t0 s.tally).length
      rw [paintRed_length, h.shape.rowLen]
      exact hRoom)
    hRed hZero hctrlN hhighC hHighEq hctrlC hRoom hFitI
    hfitC0 hFitM hmaxC
  exact ⟨bLoop, bMul, bClear, _, hmul, hclearEq, htally⟩

/-- Non-final rung. `tally_double` changes only the row, the tally length, the
    control counter, the recorded high, and `tally_max`. The live spare cube and
    the live mul by the input on that doubled board are the final-rung results
    with those fields copied across. `tally_add_one` then lays the extra white
    peg at `t0 + 2 · tally`, which was empty, and the recorded high becomes
    that hole. -/
theorem red_doubled_cube_mul {done rest : List Nat} {r : Nat} {b : Ecbs.Board}
    {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvK done (r :: rest) b s base)
    (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax)
    (hhome : s.onBench = false) (hrest : rest ≠ []) (hr : r = 2)
    (hxLen : base.x.length = base.n) (hxT : allTritList base.x) :
    ∃ (bClear bD bCube bRed bAdd : Ecbs.Board),
      Ecbs.tally_double bClear = .ok bD ∧
      Ecbs.cube bD ((6 : Nat) : Int) ((5 : Nat) : Int) = .ok bCube ∧
      Ecbs.mul bCube ((5 : Nat) : Int) (base.xHome : Int) ((6 : Nat) : Int)
          false false false = .ok bRed ∧
      Ecbs.tally_add_one bRed = .ok bAdd ∧
      bAdd.sudo_5Board_4cost.sudo_5Costs_15control_highest =
        ((max s.high (s.t0 + 2 * s.tally) : Nat) : Int) ∧
      ∃ (hix : s.t0 + 2 * s.tally < bRed.sudo_5Board_3row.size),
        bRed.sudo_5Board_3row[s.t0 + 2 * s.tally] = 0 := by
  have hge : 2 ≤ (r :: rest).length := by
    cases rest with
    | nil => exact absurd rfl hrest
    | cons _ _ => simp
  have hRoom : s.t0 + 2 * s.tally ≤ base.control := h.openRoom hge
  have hHighEq : s.t0 + s.tally - 1 ≤ s.high := by
    rw [h.highTop]
    exact Nat.le_max_right _ _
  obtain ⟨tmax, hMax⟩ := h.tmaxLt
  have hRpos : 0 < base.R := by
    have hk := h.kLe
    rw [List.length_append, List.length_cons] at hk
    omega
  have hn0 : 0 < base.n := by rw [← h.hn]; exact h.shape.peg.n_pos
  have hFitL1 : FitsLen (2 * s.tally + 1) :=
    double_len_fit hn0 hRpos hT base.fitM
  have hFitM : FitsLen (2 * s.tally) := FitsLen.of_le hFitL1 (by omega)
  have hFitI : FitsLen (s.t0 + 2 * s.tally) :=
    (double_index_fit_le hRoom base.fitControl).1
  have hdone : done.length ≤ base.R := by
    have hk := h.kLe
    rw [List.length_append] at hk
    omega
  have hCtrlPair := double_ctrl_fit h.ctrlLe hT hdone base.fitCtrl
  have hFitC : FitsLen (s.ctrl + 3 * s.tally) := hCtrlPair.1
  have hFitC1 : FitsLen (s.ctrl + s.tally + 2 * s.tally + 1) := hCtrlPair.2
  obtain ⟨_bLoop, _bMul, bClear, bCube0, bRed0, _hmul, _hclear, _hcube, _hred,
      _hbounds, hlenC, ht0C, hrowC, hctrlN, hhighC, hctrlC, hmaxC,
      ht0Cube, ht0Red, htierCube, htierRed, hcubeF, hmulF,
      _honR, _htoR, _hlenR, _hbenchR, _hclearP, _hcubeP, _hmulP,
      _hcubeBoth, _hmulBoth, _hcU⟩ :=
    red_cube_mul_ofK h hm hT hhome hxLen hxT
  let xs := paintRed s.row s.t0 s.tally
  have hRed : ∀ j (hj : j < s.tally),
      xs[s.t0 + j]'(by
        simp [xs, paintRed_length]
        exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj s.t0) h.shape.seg.room) = 2 := by
    intro j hj
    simpa [xs] using paintRed_get_lo s.row s.t0 s.tally j hj h.shape.seg.room
  have hZero : ∀ k (hk : k < s.tally),
      xs[s.t0 + s.tally + k]'(by
        simp [xs, paintRed_length, h.shape.rowLen]
        omega) = 0 := by
    intro k hk
    have hlen : s.row.length = base.control := h.shape.rowLen
    have hix : s.t0 + (s.tally + k) < s.row.length := by
      rw [hlen]
      omega
    have hsrc := h.openZero hge k hk
      (by simpa [Nat.add_assoc] using hix)
    have hsrc' : s.row[s.t0 + s.tally + k]'(by omega) = 0 := hsrc
    have hget := paintRed_get_hi s.row s.t0 s.tally (s.t0 + s.tally + k)
      (by omega) (by omega)
    simpa [xs] using hget.trans hsrc'
  have hhighTop : bClear.sudo_5Board_4cost.sudo_5Costs_15control_highest =
      (s.high : Int) := by
    exact hhighC
  have hmaxNat : bClear.sudo_5Board_4cost.sudo_5Costs_9tally_max = (tmax : Int) :=
    hmaxC.trans hMax
  have hfitC0 : FitsLen (s.ctrl + s.tally + 2 * s.tally) :=
    FitsLen.of_le hFitC (by omega)
  have htally := tally_double_refines bClear xs s.t0 s.tally (s.ctrl + s.tally)
    s.high base.control tmax hm hlenC ht0C hrowC
    (by
      change s.t0 + 2 * s.tally ≤ (paintRed s.row s.t0 s.tally).length
      rw [paintRed_length, h.shape.rowLen]
      exact hRoom)
    hRed hZero hctrlN hhighTop hHighEq hctrlC hRoom hFitI
    hfitC0 hFitM hmaxNat
  let rowD := embed (paintOnes (paintOnes xs s.t0 s.tally) (s.t0 + s.tally) s.tally)
  let lenD : Int := Int.ofNat (2 * s.tally)
  let ctrlD : Int := Int.ofNat (s.ctrl + s.tally + 2 * s.tally)
  let highD : Int := ((max s.high (s.t0 + 2 * s.tally - 1) : Nat) : Int)
  let maxD : Int := ((max tmax (2 * s.tally) : Nat) : Int)
  have htallyW : Ecbs.tally_double bClear =
      .ok (withTally bClear rowD lenD ctrlD highD maxD) := by
    simpa [rowD, lenD, ctrlD, highD, maxD, withTally] using htally
  let bD := withTally bClear rowD lenD ctrlD highD maxD
  let bCube := withTally bCube0 rowD lenD ctrlD highD maxD
  let bRed := withTally bRed0 rowD lenD ctrlD highD maxD
  let wide := paintOnes (paintOnes xs s.t0 s.tally) (s.t0 + s.tally) s.tally
  have hlenW : wide.length = base.control := by
    simp [wide, xs, paintOnes_length, paintRed_length, h.shape.rowLen]
  have hGrow := red_final_gt s.tally r rest hr hrest
  have hWhole : climbTally s.tally (r :: rest) =
      climbTally base.tally0 (done ++ (r :: rest)) := by
    rw [h.htally0]
    exact climbTally_prefix_rest base.tally0 done (r :: rest)
  have hOff : 2 * s.tally < climbTally base.tally0 (done ++ (r :: rest)) := by
    rw [← hWhole]
    exact hGrow
  have hPast : s.t0 + 2 * s.tally < base.control := by
    have hfit := h.tailFit
    rw [h.shape.rowLen] at hfit
    omega
  have hroom2 : s.t0 + s.tally + s.tally < base.control := by
    simpa [Nat.two_mul, Nat.add_assoc] using hPast
  have hixW : s.t0 + s.tally + s.tally < wide.length := by
    rw [hlenW]; exact hroom2
  have hcell : wide[s.t0 + s.tally + s.tally]'hixW = 0 := by
    have hmid : (paintOnes xs s.t0 s.tally).length = base.control := by
      simp [xs, paintOnes_length, paintRed_length, h.shape.rowLen]
    have h1 := paintOnes_get_hi (paintOnes xs s.t0 s.tally) (s.t0 + s.tally) s.tally
      (s.t0 + s.tally + s.tally) (by omega) (by rw [hmid]; exact hroom2)
    have h2 := paintOnes_get_hi xs s.t0 s.tally (s.t0 + s.tally + s.tally)
      (by omega) (by simp [xs, paintRed_length, h.shape.rowLen]; exact hroom2)
    have h3 := paintRed_get_hi s.row s.t0 s.tally (s.t0 + s.tally + s.tally)
      (by omega) (by rw [h.shape.rowLen]; exact hroom2)
    have h4 := h.tailZero (s.tally + s.tally) (Nat.le_add_left _ _)
      (by
        rw [← Nat.two_mul]
        exact hOff)
      (by
        rw [h.shape.rowLen, ← Nat.add_assoc]
        exact hroom2)
    have h4' : s.row[s.t0 + s.tally + s.tally]'(by rw [h.shape.rowLen]; exact hroom2) = 0 :=
      (getElem_congr (Nat.add_assoc s.t0 s.tally s.tally)).trans h4
    rw [h1, h2, h3]
    exact h4'
  have hrowR : bRed.sudo_5Board_3row = embed wide := by
    simp [bRed, withTally, rowD, wide]
  have hixR : s.t0 + 2 * s.tally < bRed.sudo_5Board_3row.size := by
    have hEq : s.t0 + 2 * s.tally = s.t0 + s.tally + s.tally := by
      rw [Nat.two_mul, Nat.add_assoc]
    rw [hEq, hrowR, size_embed]; exact hixW
  have hzeroR : bRed.sudo_5Board_3row[s.t0 + 2 * s.tally]'hixR = 0 := by
    have hEq : s.t0 + 2 * s.tally = s.t0 + s.tally + s.tally := by
      rw [Nat.two_mul, Nat.add_assoc]
    have hixA : s.t0 + s.tally + s.tally < bRed.sudo_5Board_3row.size := by
      rw [← hEq]; exact hixR
    have hget := get_embed wide (s.t0 + s.tally + s.tally) (hrowR ▸ hixA)
    have hidx := idx_get hrowR (s.t0 + s.tally + s.tally) hixA
    have hA : bRed.sudo_5Board_3row[s.t0 + s.tally + s.tally] = 0 := by
      rw [hidx, hget, hcell]
      rfl
    simpa [hEq] using hA
  have ht0R : bRed.sudo_5Board_6tally0 = (s.t0 : Int) := by
    simp [bRed, withTally, ht0Red]
  have hctrlR : bRed.sudo_5Board_1t.sudo_4Tier_7control = (base.control : Int) := by
    have h1 : bRed.sudo_5Board_1t = bRed0.sudo_5Board_1t := by
      simp [bRed, withTally]
    rw [h1, htierRed, hctrlN]
  have hlenR : bRed.sudo_5Board_9tally_len = ((2 * s.tally : Nat) : Int) := by
    simp [bRed, withTally, lenD]
  have hhighR : bRed.sudo_5Board_4cost.sudo_5Costs_15control_highest =
      ((max s.high (s.t0 + 2 * s.tally - 1) : Nat) : Int) := by
    simp [bRed, withTally, highD]
  have hctrlNum : bRed.sudo_5Board_4cost.sudo_5Costs_4ctrl =
      ((s.ctrl + s.tally + 2 * s.tally : Nat) : Int) := by
    simp [bRed, withTally, ctrlD]
  have hmaxR : bRed.sudo_5Board_4cost.sudo_5Costs_9tally_max =
      ((max tmax (2 * s.tally) : Nat) : Int) := by
    simp [bRed, withTally, maxD]
  have hadd := tally_add_one_mark bRed s.t0 (2 * s.tally)
      (max s.high (s.t0 + 2 * s.tally - 1)) base.control
      (s.ctrl + s.tally + 2 * s.tally) (max tmax (2 * s.tally))
      hlenR ht0R hixR hzeroR hctrlR hPast hhighR hFitI
      hctrlNum hFitC1 hFitL1 hmaxR
  have hflat : max (max s.high (s.t0 + 2 * s.tally - 1)) (s.t0 + 2 * s.tally) =
      max s.high (s.t0 + 2 * s.tally) := by
    rw [Nat.max_assoc]
    exact congrArg (max s.high) (Nat.max_eq_right (Nat.sub_le _ _))
  rw [hflat] at hadd
  have hflatM : max (max tmax (2 * s.tally)) (2 * s.tally + 1) =
      max tmax (2 * s.tally + 1) := by
    rw [Nat.max_assoc]
    exact congrArg (max tmax) (Nat.max_eq_right (Nat.le_succ _))
  rw [hflatM] at hadd
  let bAdd := { bRed with
    sudo_5Board_3row := bRed.sudo_5Board_3row.set ⟨s.t0 + 2 * s.tally, hixR⟩ (1 : Int)
    sudo_5Board_9tally_len := Int.ofNat (2 * s.tally + 1)
    sudo_5Board_4cost := { bRed.sudo_5Board_4cost with
      sudo_5Costs_15control_highest :=
        ((max s.high (s.t0 + 2 * s.tally) : Nat) : Int)
      sudo_5Costs_4ctrl := Int.ofNat (s.ctrl + s.tally + 2 * s.tally + 1)
      sudo_5Costs_9tally_max := ((max tmax (2 * s.tally + 1) : Nat) : Int) } }
  refine ⟨bClear, bD, bCube, bRed, bAdd, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [bD] using htallyW
  · simpa [bD, bCube] using hcubeF rowD lenD ctrlD highD maxD
  · simpa [bCube, bRed] using hmulF rowD lenD ctrlD highD maxD
  · simpa [bAdd] using hadd
  · simp [bAdd]
  · exact ⟨hixR, hzeroR⟩

theorem withPark_id (b : Ecbs.Board) :
    withPark b b.sudo_5Board_3row b.sudo_5Board_4cost.sudo_5Costs_4ctrl
        b.sudo_5Board_11parked_from b.sudo_5Board_8rung_idx = b := by
  apply board_ext
  case hcost =>
    apply cost_ext
    all_goals rfl
  all_goals rfl

theorem parkKeep_withPark (b : Ecbs.Board) (xs : List Nat)
    (hole park rung i ctrl : Nat)
    (hRowP : park < b.sudo_5Board_3row.size) (hRowH : hole < b.sudo_5Board_3row.size)
    (hrow : b.sudo_5Board_3row = embed xs) (hp : park < xs.length) (hh : hole < xs.length) :
    parkKeepBoard b hole park rung i ctrl hRowP hRowH =
      withPark b (embed (afterPark xs (-1) park hole rung))
        (Int.ofNat (ctrl + 2)) ((hole : Nat) : Int) (Int.ofNat (i + 1)) := by
  have hR := parkKeep_row b xs hole park rung i ctrl hRowP hRowH hrow hp hh
  apply board_ext
  case hrow =>
    rw [hR]
    simp [afterPark, withPark]
  case hcost =>
    apply cost_ext
    all_goals rfl
  all_goals rfl

@[simp] private theorem embed_set_any (xs : List Nat) (i v : Nat) (h : i < (embed xs).size) :
    (embed xs).set ⟨i, h⟩ (Int.ofNat v) = embed (xs.set i v) := by
  apply Array.ext
  · simp [embed, size_embed, List.length_set]
  · intro j hj hj'
    simp [embed, Array.getElem_set, List.getElem_set]

private theorem embed_paint_step (xs : List Nat) (t0 j : Nat) (h : t0 + j < xs.length) :
    (embed (paintRed xs t0 j)).set
        ⟨t0 + j, by rw [size_embed, paintRed_length]; exact h⟩ ((2 : Nat) : Int) =
      embed (paintRed xs t0 (j + 1)) := by
  rw [(ofNat_eq_natCast 2).symm]
  rw [embed_set (paintRed xs t0 j) (t0 + j) 2 (by rw [paintRed_length]; exact h), paintRed_succ]

private theorem pegStep_rowPr (b : Ecbs.Board) (row : Array Int) (ctrl fromHole ridx : Int)
    (t0 j : Nat)
    (h1 h2 : t0 + j < (withPark b row ctrl fromHole ridx).sudo_5Board_3row.size)
    (ctrlN : Nat) :
    pegStep (withPark b row ctrl fromHole ridx) t0 j h1 ctrlN =
      pegStep (withPark b row ctrl fromHole ridx) t0 j h2 ctrlN := by
  unfold pegStep
  have hf : (⟨t0 + j, h1⟩ : Fin _) = ⟨t0 + j, h2⟩ := Fin.ext rfl
  rw [hf]

private theorem pegStep_board {b b' : Ecbs.Board} (hbb : b = b')
    (t0 j : Nat) (hrow : t0 + j < b.sudo_5Board_3row.size) (ctrl : Nat) :
    pegStep b t0 j hrow ctrl = pegStep b' t0 j (hbb ▸ hrow) ctrl := by
  cases hbb
  rfl

private theorem pegStep_overwrite (b : Ecbs.Board) (row : Array Int)
    (ctrl fromHole ridx : Int) (t0 j ctrlN ctrlN' : Nat)
    (hrow : t0 + j < b.sudo_5Board_3row.size) (hrow' : t0 + j < row.size) :
    pegStep (withPark b row ctrl fromHole ridx) t0 j hrow' ctrlN =
      withPark (pegStep b t0 j hrow ctrlN')
        (row.set ⟨t0 + j, hrow'⟩ ((2 : Nat) : Int))
        (Int.ofNat (ctrlN + 1)) fromHole ridx := by
  apply board_ext
  case hrow => rfl
  case hcost =>
    apply cost_ext
    all_goals rfl
  all_goals rfl

/-- Two peg contexts that agree on every value the cube loop reads. The second
    board is the first with a replacement row, counter, parked-from hole, and
    rung index. -/
structure PegTwin (c d : PegCtx) where
  src : d.src = c.src
  g : d.g = c.g
  n : d.n = c.n
  k : d.k = c.k
  bench : d.bench = c.bench
  moves0 : d.moves0 = c.moves0
  slides0 : d.slides0 = c.slides0
  hole0 : d.hole0 = c.hole0
  peak0 : d.peak0 = c.peak0
  peakS0 : d.peakS0 = c.peakS0
  cOps0 : d.cOps0 = c.cOps0
  t0 : d.t0 = c.t0
  m : d.m = c.m
  fromHole : Int
  ridx : Int
  b0 : d.b0 =
    withPark c.b0 (embed d.row0) ((d.ctrl0 : Nat) : Int) fromHole ridx

private theorem cubeOff_twin (c d : PegCtx) (t : PegTwin c d) :
    cubeOffBoard d.b0 d.src d.src d.g d.n d.k d.moves0 d.hole0 d.bench d.peak0 d.peakS0
        d.cOps0 d.hops0 d.hF d.hHome =
      withPark
        (cubeOffBoard c.b0 c.src c.src c.g c.n c.k c.moves0 c.hole0 c.bench c.peak0
          c.peakS0 c.cOps0 c.hops0 c.hF c.hHome)
        (embed d.row0) ((d.ctrl0 : Nat) : Int) t.fromHole t.ridx := by
  have hs : d.src = c.src := t.src
  have hg : d.g = c.g := t.g
  have hn : d.n = c.n := t.n
  have hk : d.k = c.k := t.k
  have hb : d.bench = c.bench := t.bench
  have hm : d.moves0 = c.moves0 := t.moves0
  have hho : d.hole0 = c.hole0 := t.hole0
  have hpk : d.peak0 = c.peak0 := t.peak0
  have hps : d.peakS0 = c.peakS0 := t.peakS0
  have hop : d.cOps0 = c.cOps0 := t.cOps0
  have hF' : c.src < d.b0.sudo_5Board_4held.size := hs ▸ d.hF
  have hH' : c.src < d.b0.sudo_5Board_4home.size := hs ▸ d.hHome
  simp only [hs, hg, hn, hk, hb, hm, hho, hpk, hps, hop]
  have htr := cubeOffBoard_transport t.b0 c.src c.src c.g c.n c.k c.moves0 c.hole0 c.bench
    c.peak0 c.peakS0 c.cOps0 d.hops0 hF' hH'
  rw [htr]
  have hir := cubeOffBoard_irrel (withPark c.b0 (embed d.row0) ((d.ctrl0 : Nat) : Int)
      t.fromHole t.ridx) c.src c.src c.g c.n c.k c.moves0 c.hole0 c.bench c.peak0 c.peakS0
    c.cOps0 (t.b0 ▸ d.hops0) (withPark_ops c.b0 (embed d.row0) ((d.ctrl0 : Nat) : Int)
      t.fromHole t.ridx ▸ c.hops0)
    (t.b0 ▸ hF') (withPark_held c.b0 (embed d.row0) ((d.ctrl0 : Nat) : Int)
      t.fromHole t.ridx ▸ c.hF)
    (t.b0 ▸ hH') (withPark_home c.b0 (embed d.row0) ((d.ctrl0 : Nat) : Int)
      t.fromHole t.ridx ▸ c.hHome)
  rw [hir]
  exact cubeOffBoard_withPark c.b0 (embed d.row0) ((d.ctrl0 : Nat) : Int) t.fromHole t.ridx
    c.src c.src c.g c.n c.k c.moves0 c.hole0 c.bench c.peak0 c.peakS0 c.cOps0
    c.hops0 c.hF c.hHome

private theorem offPeg_twin (c d : PegCtx) (t : PegTwin c d) :
    offPeg d = withPark (offPeg c) (embed (paintRed d.row0 d.t0 1))
      (Int.ofNat (d.ctrl0 + 1)) t.fromHole t.ridx := by
  have hc := cubeOff_twin c d t
  have hrowD : d.t0 + 0 <
      (cubeOffBoard d.b0 d.src d.src d.g d.n d.k d.moves0 d.hole0 d.bench d.peak0 d.peakS0
        d.cOps0 d.hops0 d.hF d.hHome).sudo_5Board_3row.size := by
    simpa using offRowPr d
  have hpb := pegStep_board hc d.t0 0 hrowD d.ctrl0
  have hlen : d.t0 < (embed d.row0).size := by
    rw [size_embed]
    exact Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right d.hm) d.hRoom
  have hbase : d.t0 <
      (cubeOffBoard c.b0 c.src c.src c.g c.n c.k c.moves0 c.hole0 c.bench c.peak0 c.peakS0
        c.cOps0 c.hops0 c.hF c.hHome).sudo_5Board_3row.size := by
    rw [cube_off_row, c.hRow, size_embed]
    exact t.t0.symm ▸ Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right c.hm) c.hRoom
  unfold offPeg
  rw [hpb]
  have hlen0 : d.t0 + 0 < (embed d.row0).size := hlen
  have hstep := pegStep_overwrite
    (cubeOffBoard c.b0 c.src c.src c.g c.n c.k c.moves0 c.hole0 c.bench c.peak0 c.peakS0
      c.cOps0 c.hops0 c.hF c.hHome)
    (embed d.row0) ((d.ctrl0 : Nat) : Int) t.fromHole t.ridx d.t0 0 d.ctrl0 c.ctrl0
    (by simpa using hbase) hlen0
  rw [hstep]
  have hzero : paintRed d.row0 d.t0 0 = d.row0 := by simp [paintRed]
  have hpaint := embed_paint_step d.row0 d.t0 0
    (Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right d.hm) d.hRoom)
  dsimp [withPark]
  simp [hzero, hpaint, t.t0, paintRed]
  apply Array.ext
  · simp [embed, size_embed, List.length_set]
  · intro j _ _
    simp [embed, Array.getElem_set, List.getElem_set, ofNat_eq_natCast]

private theorem pack_moves_eq {c d : PegCtx} {i : Nat} {h0 : 0 < i} {hle : i ≤ c.m}
    {hleD : i ≤ d.m}
    (hB : (pegPack d i h0 hleD).b =
      withPark (pegPack c i h0 hle).b
        (embed (paintRed d.row0 d.t0 i)) (Int.ofNat (d.ctrl0 + i))
        (pegPack d i h0 hleD).b.sudo_5Board_11parked_from
        (pegPack d i h0 hleD).b.sudo_5Board_8rung_idx) :
    (pegPack d i h0 hleD).moves = (pegPack c i h0 hle).moves := by
  apply ofNat_inj_nat
  have hd := (pegPack d i h0 hleD).hmoves
  have hc := (pegPack c i h0 hle).hmoves
  have hm : (pegPack d i h0 hleD).b.sudo_5Board_4cost.sudo_5Costs_5moves =
      (pegPack c i h0 hle).b.sudo_5Board_4cost.sudo_5Costs_5moves := by
    rw [hB, withPark_moves]
  exact hd.symm.trans (hm.trans hc)

/-- After the same number of cube-pegs, the parked context's board is the
    unparked board with the painted park row, the parked counter, and the park's
    hole and rung index. -/
theorem pegPack_twin (c d : PegCtx) (t : PegTwin c d) (i : Nat)
    (h0 : 0 < i) (hle : i ≤ c.m) :
    (pegPack d i h0 (by rw [t.m]; exact hle)).b =
      withPark (pegPack c i h0 hle).b
        (embed (paintRed d.row0 d.t0 i))
        (Int.ofNat (d.ctrl0 + i)) t.fromHole t.ridx := by
  match i with
  | 0 => exact absurd h0 (Nat.not_lt_zero 0)
  | 1 =>
    simp only [pegPack]
    have h := offPeg_twin c d t
    simpa [pegFromOff] using h
  | n + 2 =>
    have hle1 : n + 1 ≤ c.m := Nat.le_of_succ_le hle
    have h0' : 0 < n + 1 := Nat.succ_pos n
    have ih := pegPack_twin c d t (n + 1) h0' hle1
    have hleD1 : n + 1 ≤ d.m := by rw [t.m]; exact hle1
    let pc := pegPack c (n + 1) h0' hle1
    let pd := pegPack d (n + 1) h0' (by rw [t.m]; exact hle1)
    have hib : pd.b = withPark pc.b (embed (paintRed d.row0 d.t0 (n + 1)))
        (Int.ofNat (d.ctrl0 + (n + 1))) t.fromHole t.ridx := by
      simpa [pc, pd] using ih
    have hxs : pd.xs = pc.xs := by rw [pd.hxs, pc.hxs, t.n, t.k, t.bench, t.g]
    have hmoves : pd.moves = pc.moves := by
      apply ofNat_inj_nat
      have hd := pd.hmoves
      rw [hib, withPark_moves] at hd
      exact hd.symm.trans pc.hmoves
    have hslides : pd.slides = pc.slides := by
      apply ofNat_inj_nat
      have hd := pd.hslides
      rw [hib, withPark_slides] at hd
      exact hd.symm.trans pc.hslides
    have hhole : pd.hole = pc.hole := by
      apply ofNat_inj_nat
      have hd := pd.hHole
      rw [hib, withPark_hole] at hd
      exact hd.symm.trans pc.hHole
    have hpeak : pd.peak = pc.peak := by
      apply ofNat_inj_nat
      have hd := pd.hpeak
      rw [hib, withPark_peak] at hd
      exact hd.symm.trans pc.hpeak
    have hpeakS : pd.peakS = pc.peakS := by
      apply ofNat_inj_nat
      have hd := pd.hpeakS
      rw [hib, withPark_strict] at hd
      exact hd.symm.trans pc.hpeakS
    have hcOps : pd.cOps = pc.cOps := by
      apply ofNat_inj_nat
      have hopsEq : pd.b.sudo_5Board_4cost.sudo_5Costs_3ops =
          pc.b.sudo_5Board_4cost.sudo_5Costs_3ops := by rw [hib, withPark_ops]
      have hget := idx_get hopsEq 1 pd.hops
      exact (pd.hop1.symm.trans (hget.trans pc.hop1))
    have hsrc : d.src = c.src := t.src
    have hn : d.n = c.n := t.n
    have hk : d.k = c.k := t.k
    have hbch : d.bench = c.bench := t.bench
    have ht0 : d.t0 = c.t0 := t.t0
    simp only [pegPack]
    unfold pegNext
    show livePegBoard d pd (Nat.lt_of_succ_le (by rw [t.m]; exact hle : n + 2 ≤ d.m)) =
      withPark (livePegBoard c pc (Nat.lt_of_succ_le hle))
        (embed (paintRed d.row0 d.t0 (n + 2)))
        (Int.ofNat (d.ctrl0 + (n + 2))) t.fromHole t.ridx
    unfold livePegBoard
    simp only [hsrc, hn, hk, hbch, hxs, hmoves, hslides, hhole, hpeak, hpeakS, hcOps, ht0]
    have hHd : c.src < pd.b.sudo_5Board_4home.size := hsrc ▸ pd.hH
    have hDd : c.src < pd.b.sudo_5Board_4held.size := hsrc ▸ pd.hD
    have hcube := cubeLiveBoard_withPark pc.b (embed (paintRed d.row0 d.t0 (n + 1))) (Int.ofNat (d.ctrl0 + (n + 1))) t.fromHole t.ridx c.src c.src pc.xs ⟨c.n, c.k, pc.moves, pc.slides, pc.hole, c.bench, pc.peak, pc.peakS, pc.cOps, pc.hops⟩ ⟨pc.hH, pc.hD⟩
    have hir := cubeLiveBoard_irrel (withPark pc.b (embed (paintRed d.row0 d.t0 (n + 1)))
        (Int.ofNat (d.ctrl0 + (n + 1))) t.fromHole t.ridx) c.src c.src pc.xs c.n c.k pc.moves
      pc.slides pc.hole c.bench pc.peak pc.peakS pc.cOps
      (hib ▸ hHd) (withPark_home pc.b _ _ _ _ ▸ pc.hH)
      (hib ▸ hDd) (withPark_held pc.b _ _ _ _ ▸ pc.hD)
      (hib ▸ pd.hops) (withPark_ops pc.b _ _ _ _ ▸ pc.hops)
    have hb : pd.b = withPark pc.b (embed (paintRed d.row0 d.t0 (n + 1)))
        (Int.ofNat (d.ctrl0 + (n + 1))) t.fromHole t.ridx := hib
    have htr := cubeLiveBoard_transport hb c.src c.src pc.xs ⟨c.n, c.k, pc.moves, pc.slides, pc.hole, c.bench, pc.peak, pc.peakS, pc.cOps, pd.hops⟩ ⟨hHd, hDd⟩
    rw [pegStep_board (htr.trans (hir.trans hcube))]
    have hrow' : c.t0 + (n + 1) < (embed (paintRed d.row0 d.t0 (n + 1))).size := by
      rw [size_embed, paintRed_length, ← ht0]
      exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left (Nat.lt_of_succ_le hle) d.t0)
        (t.m ▸ d.hRoom)
    have hrowB : c.t0 + (n + 1) <
        (cubeLiveBoard pc.b c.src c.src pc.xs ⟨c.n, c.k, pc.moves, pc.slides, pc.hole, c.bench, pc.peak, pc.peakS, pc.cOps, pc.hops⟩ ⟨pc.hH, pc.hD⟩).sudo_5Board_3row.size :=
      liveRowPr c pc (Nat.lt_of_succ_le hle)
    have hov := pegStep_overwrite
      (cubeLiveBoard pc.b c.src c.src pc.xs ⟨c.n, c.k, pc.moves, pc.slides, pc.hole, c.bench, pc.peak, pc.peakS, pc.cOps, pc.hops⟩ ⟨pc.hH, pc.hD⟩)
      (embed (paintRed d.row0 d.t0 (n + 1))) (Int.ofNat (d.ctrl0 + (n + 1))) t.fromHole t.ridx
      c.t0 (n + 1) pd.ctrl pc.ctrl hrowB hrow'
    have hctrlD : pd.ctrl = d.ctrl0 + (n + 1) := pd.hctrlN
    have hctrlC : pc.ctrl = c.ctrl0 + (n + 1) := pc.hctrlN
    have hpaint := embed_paint_step d.row0 c.t0 (n + 1) (by
      rw [size_embed] at hrow'
      rw [paintRed_length] at hrow'
      exact hrow')
    -- The live step uses `liveRowPr`, not `hrow'`.
    have hrowW : c.t0 + (n + 1) <
        (withPark
          (cubeLiveBoard pc.b c.src c.src pc.xs ⟨c.n, c.k, pc.moves, pc.slides, pc.hole, c.bench, pc.peak, pc.peakS, pc.cOps, pc.hops⟩ ⟨pc.hH, pc.hD⟩)
          (embed (paintRed d.row0 d.t0 (n + 1))) (Int.ofNat (d.ctrl0 + (n + 1)))
          t.fromHole t.ridx).sudo_5Board_3row.size := by
      rw [withPark_row]; exact hrow'
    have hswap : pegStep (withPark
          (cubeLiveBoard pc.b c.src c.src pc.xs ⟨c.n, c.k, pc.moves, pc.slides, pc.hole, c.bench, pc.peak, pc.peakS, pc.cOps, pc.hops⟩ ⟨pc.hH, pc.hD⟩)
          (embed (paintRed d.row0 d.t0 (n + 1))) (Int.ofNat (d.ctrl0 + (n + 1)))
          t.fromHole t.ridx) c.t0 (n + 1) hrowW pd.ctrl =
      pegStep (withPark
          (cubeLiveBoard pc.b c.src c.src pc.xs ⟨c.n, c.k, pc.moves, pc.slides, pc.hole, c.bench, pc.peak, pc.peakS, pc.cOps, pc.hops⟩ ⟨pc.hH, pc.hD⟩)
          (embed (paintRed d.row0 d.t0 (n + 1))) (Int.ofNat (d.ctrl0 + (n + 1)))
          t.fromHole t.ridx) c.t0 (n + 1) hrow' pd.ctrl := by
      unfold pegStep
      have : (⟨c.t0 + (n + 1), hrowW⟩ : Fin _) = ⟨c.t0 + (n + 1), hrow'⟩ := Fin.ext rfl
      rw [this]
    rw [hswap, hov]
    simp only [ht0, hctrlD, embed_set, paintRed_succ, paintRed]
    have hsum : d.ctrl0 + (n + 1) + 1 = d.ctrl0 + (n + 2) := by omega
    dsimp [withPark]
    simp only [hsum]
    apply board_ext
    case hrow =>
      apply Array.ext
      · simp [embed, size_embed, List.length_set, paintRed_length]
      · intro j _ _
        simp [ht0, embed, Array.getElem_set, List.getElem_set, ofNat_eq_natCast, paintRed]
    case hcost =>
      apply cost_ext <;> simp [ht0]
    all_goals rfl

/-- The live nocopy mul does not depend on which proof of the index bounds is used. -/
private theorem mulNoLiveBoard_irrel (b : Ecbs.Board) (dst second : Nat) (xs ys : List Nat)
    (n k moves slides hole bench peak peakS cOps : Nat)
    (hH hH' : second < b.sudo_5Board_4home.size)
    (hD hD' : second < b.sudo_5Board_4held.size)
    (hops hops' : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size) :
    mulNoLiveBoard b dst second xs ys ⟨n, k, moves, slides, hole, bench, peak, peakS, cOps, hops⟩ ⟨hH, hD⟩ =
      mulNoLiveBoard b dst second xs ys ⟨n, k, moves, slides, hole, bench, peak, peakS, cOps, hops'⟩ ⟨hH', hD'⟩ := by
  cases Subsingleton.elim hH hH'
  cases Subsingleton.elim hD hD'
  cases Subsingleton.elim hops hops'
  rfl

/-- `pegPack`'s board is `pegBoard`, for whichever bound proof the pack used. -/
theorem packEqBoard (c : PegCtx) (i : Nat) (h0 : 0 < i) (hle : i ≤ c.m)
    {b : Ecbs.Board} (h : (pegPack c i h0 hle).b = b) : pegBoard c i = b :=
  ((pegPack_board c i h0 hle).1).symm.trans h

/-- A peg loop whose start is `withPark` of another, and whose painted row and
    counter are already the base loop's own row and counter, ends on the same
    board. The bound proof inside `pegPack_twin` is read off the loop equality. -/
theorem twin_boards_eq (base other : PegCtx) (t : PegTwin base other)
    (hfrom : t.fromHole = base.b0.sudo_5Board_11parked_from)
    (hridx : t.ridx = base.b0.sudo_5Board_8rung_idx)
    (hrow0 : other.row0 = base.row0) (ht0 : other.t0 = base.t0)
    (hctrl0 : other.ctrl0 = base.ctrl0) :
    pegBoard other other.m = pegBoard base base.m := by
  have hloop := pegPack_twin base other t base.m base.hm (Nat.le_refl _)
  let pc := pegPack base base.m base.hm (Nat.le_refl _)
  have hPcB := (pegPack_board base base.m base.hm (Nat.le_refl _)).1
  have hrow : pc.b.sudo_5Board_3row =
      embed (paintRed other.row0 other.t0 base.m) := by
    rw [pc.hrow, ← hrow0, ← ht0]
  have hctrl : pc.b.sudo_5Board_4cost.sudo_5Costs_4ctrl =
      Int.ofNat (other.ctrl0 + base.m) := by
    rw [pc.hctrl, pc.hctrlN, ← hctrl0]
    exact (ofNat_eq_natCast _).symm
  have hfr : pc.b.sudo_5Board_11parked_from = t.fromHole :=
    ((pegPack_board base base.m base.hm (Nat.le_refl _)).2.1).trans hfrom.symm
  have hri : pc.b.sudo_5Board_8rung_idx = t.ridx :=
    ((pegPack_board base base.m base.hm (Nat.le_refl _)).2.2.1).trans hridx.symm
  have hself : withPark pc.b (embed (paintRed other.row0 other.t0 base.m))
      (Int.ofNat (other.ctrl0 + base.m)) t.fromHole t.ridx = pc.b := by
    rw [← hrow, ← hctrl, ← hfr, ← hri]
    exact withPark_id pc.b
  have hOb := packEqBoard other base.m base.hm _ (hloop.trans hself)
  have hidx : pegBoard other other.m = pegBoard other base.m := by rw [t.m]
  exact hidx.trans (hOb.trans hPcB)

/-- After the same number of cube-pegs, the parked peg board is the unparked
    peg board with the painted park row, the parked counter, and the park hole
    and rung index. -/
private theorem pegBoard_withPark (c d : PegCtx) (t : PegTwin c d) :
    pegBoard d c.m =
      withPark (pegBoard c c.m)
        (embed (paintRed d.row0 d.t0 c.m))
        (Int.ofNat (d.ctrl0 + c.m)) t.fromHole t.ridx := by
  have hloop := pegPack_twin c d t c.m c.hm (Nat.le_refl _)
  have hPc := (pegPack_board c c.m c.hm (Nat.le_refl _)).1
  have hD := packEqBoard d c.m c.hm _ hloop
  rw [hPc] at hD
  exact hD

private theorem pack_moves_board (c : PegCtx) :
    (pegBoard c c.m).sudo_5Board_4cost.sudo_5Costs_5moves =
      Int.ofNat (pegPack c c.m c.hm (Nat.le_refl _)).moves := by
  have hm := (pegPack c c.m c.hm (Nat.le_refl _)).hmoves
  rwa [(pegPack_board c c.m c.hm (Nat.le_refl _)).1] at hm

private theorem pack_slides_board (c : PegCtx) :
    (pegBoard c c.m).sudo_5Board_4cost.sudo_5Costs_6slides =
      Int.ofNat (pegPack c c.m c.hm (Nat.le_refl _)).slides := by
  have hm := (pegPack c c.m c.hm (Nat.le_refl _)).hslides
  rwa [(pegPack_board c c.m c.hm (Nat.le_refl _)).1] at hm

private theorem pack_hole_board (c : PegCtx) :
    (pegBoard c c.m).sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      Int.ofNat (pegPack c c.m c.hm (Nat.le_refl _)).hole := by
  have hm := (pegPack c c.m c.hm (Nat.le_refl _)).hHole
  rwa [(pegPack_board c c.m c.hm (Nat.le_refl _)).1] at hm

private theorem pack_peak_board (c : PegCtx) :
    (pegBoard c c.m).sudo_5Board_4cost.sudo_5Costs_4peak =
      Int.ofNat (pegPack c c.m c.hm (Nat.le_refl _)).peak := by
  have hm := (pegPack c c.m c.hm (Nat.le_refl _)).hpeak
  rwa [(pegPack_board c c.m c.hm (Nat.le_refl _)).1] at hm

private theorem pack_peakS_board (c : PegCtx) :
    (pegBoard c c.m).sudo_5Board_4cost.sudo_5Costs_11peak_strict =
      ((pegPack c c.m c.hm (Nat.le_refl _)).peakS : Int) := by
  have hm := (pegPack c c.m c.hm (Nat.le_refl _)).hpeakS
  rwa [(pegPack_board c c.m c.hm (Nat.le_refl _)).1] at hm

/-- Rewrite the polynomial arguments of a live nocopy mul. The index proofs stay. -/
private theorem mulNoLive_eq_args (b : Ecbs.Board) (dst second : Nat)
    (xs xs' ys ys' : List Nat)
    (n n' k k' moves moves' slides slides' hole hole' bench bench' peak peak' peakS peakS'
      cOps cOps' : Nat)
    (hxs : xs = xs') (hys : ys = ys') (hn : n = n') (hk : k = k')
    (hmv : moves = moves') (hsl : slides = slides') (hho : hole = hole')
    (hbn : bench = bench') (hpk : peak = peak') (hps : peakS = peakS')
    (hop : cOps = cOps')
    (hH : second < b.sudo_5Board_4home.size) (hD : second < b.sudo_5Board_4held.size)
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size) :
    mulNoLiveBoard b dst second xs ys ⟨n, k, moves, slides, hole, bench, peak, peakS, cOps, hops⟩ ⟨hH, hD⟩ =
      mulNoLiveBoard b dst second xs' ys' ⟨n', k', moves', slides', hole', bench', peak', peakS', cOps', hops⟩ ⟨hH, hD⟩ := by
  cases hxs
  cases hys
  cases hn
  cases hk
  cases hmv
  cases hsl
  cases hho
  cases hbn
  cases hpk
  cases hps
  cases hop
  rfl

/-- Two peg contexts with the same start board and the same scalars the loop
    reads end on the same peg board. -/
theorem pegBoard_same_copy (c d : PegCtx)
    (hb0 : c.b0 = d.b0)
    (hsrc : d.src = c.src) (hg : d.g = c.g) (hn : d.n = c.n)
    (hk : d.k = c.k) (hbench : d.bench = c.bench)
    (hrow0 : d.row0 = c.row0) (ht0 : d.t0 = c.t0)
    (hctrl0 : d.ctrl0 = c.ctrl0) (hm : d.m = c.m) :
    pegBoard d d.m = pegBoard c c.m := by
  have hmov : d.moves0 = c.moves0 := by
    apply ofNat_inj_nat
    have hd := d.hmoves0
    rw [← hb0] at hd
    exact hd.symm.trans c.hmoves0
  have hslide : d.slides0 = c.slides0 := by
    apply ofNat_inj_nat
    have hd := d.hslides0
    rw [← hb0] at hd
    have h := hd.symm.trans c.hslides0
    exact ((ofNat_eq_natCast _).symm).trans (h.trans (ofNat_eq_natCast _))
  have hhole : d.hole0 = c.hole0 := by
    apply ofNat_inj_nat
    have hd := d.hHole0
    rw [← hb0] at hd
    have h := hd.symm.trans c.hHole0
    exact ((ofNat_eq_natCast _).symm).trans (h.trans (ofNat_eq_natCast _))
  have hpeak : d.peak0 = c.peak0 := by
    apply ofNat_inj_nat
    have hd := d.hpeak0
    rw [← hb0] at hd
    exact hd.symm.trans c.hpeak0
  have hps : d.peakS0 = c.peakS0 := by
    apply ofNat_inj_nat
    have hd := d.hpeakS0
    rw [← hb0] at hd
    exact hd.symm.trans c.hpeakS0
  have hcops : d.cOps0 = c.cOps0 := by
    apply ofNat_inj_nat
    have hopsEq : d.b0.sudo_5Board_4cost.sudo_5Costs_3ops =
        c.b0.sudo_5Board_4cost.sudo_5Costs_3ops := by rw [← hb0]
    have hget := idx_get hopsEq 1 d.hops0
    have hopC : c.b0.sudo_5Board_4cost.sudo_5Costs_3ops[1]'(hopsEq ▸ d.hops0) =
        (c.cOps0 : Int) := by
      cases Subsingleton.elim (hopsEq ▸ d.hops0) c.hops0
      exact c.hop10
    exact d.hop10.symm.trans (hget.trans hopC)
  have hb0w : d.b0 = withPark c.b0 (embed d.row0) ((d.ctrl0 : Nat) : Int)
      c.b0.sudo_5Board_11parked_from c.b0.sudo_5Board_8rung_idx := by
    rw [← hb0]
    have hrowE : c.b0.sudo_5Board_3row = embed d.row0 := by
      rw [c.hRow, ← hrow0]
    have hctrlE : c.b0.sudo_5Board_4cost.sudo_5Costs_4ctrl =
        ((d.ctrl0 : Nat) : Int) := by
      rw [c.hCtrl0, ← hctrl0]
    have hid := (withPark_id c.b0).symm
    rw [hrowE, hctrlE] at hid
    exact hid
  let t : PegTwin c d := {
    src := hsrc
    g := hg
    n := hn
    k := hk
    bench := hbench
    moves0 := hmov
    slides0 := hslide
    hole0 := hhole
    peak0 := hpeak
    peakS0 := hps
    cOps0 := hcops
    t0 := ht0
    m := hm
    fromHole := c.b0.sudo_5Board_11parked_from
    ridx := c.b0.sudo_5Board_8rung_idx
    b0 := hb0w
  }
  exact twin_boards_eq c d t rfl rfl hrow0 ht0 hctrl0

/-- The emitted gap mul on the idle park is the unparked gap mul with the park
    row, the parked counter, the climb hole, and the advanced rung index. -/
theorem parked_gap_is_withPark
    {done rest : List Nat} {r : Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvKCore done (r :: rest) b s base)
    (hM : MoveHeadroom b base.n base.bench base.mMax)
    (hS : SlideHeadroom b base.n base.mMax)
    (hF : s.fromHole < 0) (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax)
    (hhome : s.onBench = false) :
    ∃ (bMulU bMulP : Ecbs.Board),
      (∃ (c : PegCtx) (bLoop : Ecbs.Board),
        Ecbs.mul bLoop ((5 : Nat) : Int) ((5 : Nat) : Int) ((6 : Nat) : Int)
            false false false = .ok bMulU ∧
        bLoop = pegBoard c c.m ∧
        Ecbs.copy_band b ((6 : Nat) : Int) ((5 : Nat) : Int) false = .ok c.b0 ∧
        c.row0 = s.row ∧ c.ctrl0 = s.ctrl ∧ c.g = s.gap ∧ c.m = s.tally ∧
        c.n = s.n ∧ c.k = s.k ∧ c.bench = s.benchlen ∧ c.src = 6 ∧ c.t0 = s.t0) ∧
      (∃ (c : PegCtx),
        Ecbs.mul (pegBoard c c.m) ((5 : Nat) : Int) ((5 : Nat) : Int)
            ((6 : Nat) : Int) false false false = .ok bMulP ∧
        c.row0 = afterPark s.row (-1) s.parkAt
          (climbAt base.ladder0 base.R s.ridx) r ∧
        c.ctrl0 = s.ctrl + 2 ∧
        c.m = s.tally ∧ c.t0 = s.t0 ∧
        c.g = s.gap ∧ c.n = s.n ∧ c.k = s.k ∧ c.bench = s.benchlen ∧ c.src = 6 ∧
        ∃ bPark, Ecbs.park_rung b (r : Int) = .ok bPark ∧
          Ecbs.copy_band bPark ((6 : Nat) : Int) ((5 : Nat) : Int) false = .ok c.b0) ∧
      bMulP = withPark bMulU
        (embed (paintRed (afterPark s.row (-1) s.parkAt
          (climbAt base.ladder0 base.R s.ridx) r) s.t0 s.tally))
        (((s.ctrl + 2 + s.tally : Nat) : Int))
        ((climbAt base.ladder0 base.R s.ridx : Nat) : Int)
        (Int.ofNat (s.ridx + 1)) := by
  obtain ⟨mv, pk, sl, c, hmv, hpk, hsl, hb0, hcopyC, hsrc, hg, hmE, hrow0, hn, hk, hbch,
      hmv0, hsl0, ht0, hctrl0, _, _, _, _⟩ := peg_of_shape h hM hS hm hT hhome
  obtain ⟨bPark, d, hpark, hcopyD, hrowD, hctrlD, hmD, ht0D, hgD, hnD, hkD, hbD, hsrcD, hfrom, hridx,
      _, hpack⟩ := parked_peg_ctx h hM hS hF hm hT hhome
  obtain ⟨mvP, pkP, slP, h6H, h6D, hmvP, hpkP, hslP, hmovD, hslD, hb0D⟩ := hpack
  have hmvE : mv = mvP := ofNat_inj_nat (hmv.symm.trans hmvP)
  have hpkE : pk = pkP := ofNat_inj_nat (hpk.symm.trans hpkP)
  let hole := climbAt base.ladder0 base.R s.ridx
  obtain ⟨bP0, hpark0, _, _, hkeep⟩ := park_of_shape h
  obtain ⟨hRowP, hRowH, hEq⟩ := hkeep hF
  have hPK : bPark = parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH := by
    have hboard : bPark = bP0 := by injection hpark.symm.trans hpark0
    exact hboard.trans hEq
  have hParkW := parkKeep_withPark b s.row hole s.parkAt r s.ridx s.ctrl hRowP hRowH
    h.inv.row h.shape.park.parkLt h.shape.park.holeLt
  have hbDrel : d.b0 = withPark c.b0 (embed d.row0) ((d.ctrl0 : Nat) : Int)
      ((hole : Nat) : Int) (Int.ofNat (s.ridx + 1)) := by
    have hplacePK : placeBoard bPark 6 h6H h6D s.gap mvP pkP =
        placeBoard (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH)
          6 (hPK ▸ h6H) (hPK ▸ h6D) s.gap mvP pkP := by
      cases hPK
      rfl
    have hmvpk : placeBoard (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH)
          6 (hPK ▸ h6H) (hPK ▸ h6D) s.gap mvP pkP =
        placeBoard (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH)
          6 (hPK ▸ h6H) (hPK ▸ h6D) s.gap mv pk := by
      rw [hmvE, hpkE]
    let rowW := embed (afterPark s.row (-1) s.parkAt hole r)
    let ctrlW := Int.ofNat (s.ctrl + 2)
    let fromW := ((hole : Nat) : Int)
    let ridxW := Int.ofNat (s.ridx + 1)
    let wp := withPark b rowW ctrlW fromW ridxW
    have hplSame : placeBoard (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH)
          6 (hPK ▸ h6H) (hPK ▸ h6D) s.gap mv pk =
        placeBoard wp 6 (withPark_home b rowW ctrlW fromW ridxW ▸ h.shape.spareH)
          (withPark_held b rowW ctrlW fromW ridxW ▸ h.shape.spareD) s.gap mv pk := by
      unfold placeBoard
      have hcount :
          countHeld ((parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH).sudo_5Board_4held.set
              ⟨6, hPK ▸ h6D⟩ true) 7 =
            countHeld (wp.sudo_5Board_4held.set
              ⟨6, withPark_held b rowW ctrlW fromW ridxW ▸ h.shape.spareD⟩ true) 7 := by
        simp [wp, parkKeepBoard, withPark, ridxW, fromW, ctrlW]
      by_cases hlt : pk < countHeld (wp.sudo_5Board_4held.set
          ⟨6, withPark_held b rowW ctrlW fromW ridxW ▸ h.shape.spareD⟩ true) 7
      · have hltK : pk < countHeld
            ((parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH).sudo_5Board_4held.set
              ⟨6, hPK ▸ h6D⟩ true) 7 := by
          simpa [hcount] using hlt
        simp only [hlt, hltK]
        apply board_ext
        all_goals first
          | simpa [wp, withPark, rowW] using
              congrArg (fun bd => bd.sudo_5Board_3row) hParkW
          | (apply cost_ext
             all_goals first
               | simp [wp, parkKeepBoard, withPark, ctrlW]
               | simp [wp, parkKeepBoard, withPark, ridxW, fromW, ctrlW])
          | simp [wp, parkKeepBoard, withPark, ridxW, fromW, ctrlW]
      · have hltK : ¬ pk < countHeld
            ((parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH).sudo_5Board_4held.set
              ⟨6, hPK ▸ h6D⟩ true) 7 := by
          simpa [hcount] using hlt
        simp only [hlt, hltK]
        apply board_ext
        all_goals first
          | simpa [wp, withPark, rowW] using
              congrArg (fun bd => bd.sudo_5Board_3row) hParkW
          | (apply cost_ext
             all_goals first
               | simp [wp, parkKeepBoard, withPark, ctrlW]
               | simp [wp, parkKeepBoard, withPark, ridxW, fromW, ctrlW])
          | simp [wp, parkKeepBoard, withPark, ridxW, fromW, ctrlW]
    have hpl := placeBoard_withPark b rowW ctrlW fromW ridxW 6 ⟨h.shape.spareH, h.shape.spareD⟩ s.gap mv pk
    have hstep : d.b0 = withPark c.b0 rowW ctrlW fromW ridxW := by
      have h1 := hb0D.trans (hplacePK.trans (hmvpk.trans (hplSame.trans hpl)))
      simpa [wp, ← hb0] using h1
    have hrowR : rowW = embed d.row0 := by
      show embed (afterPark s.row (-1) s.parkAt hole r) = embed d.row0
      rw [← hrowD]
    have hctrlR : ctrlW = ((d.ctrl0 : Nat) : Int) := by
      show Int.ofNat (s.ctrl + 2) = ((d.ctrl0 : Nat) : Int)
      rw [← hctrlD]
      exact ofNat_eq_natCast _
    rw [hrowR, hctrlR] at hstep
    exact hstep
  have hhole0 : d.hole0 = c.hole0 := by
    apply ofNat_inj_nat
    have hd := d.hHole0
    rw [hbDrel, withPark_hole] at hd
    exact hd.symm.trans c.hHole0
  have hpeak0 : d.peak0 = c.peak0 := by
    apply ofNat_inj_nat
    have hd := d.hpeak0
    rw [hbDrel, withPark_peak] at hd
    exact hd.symm.trans c.hpeak0
  have hps0 : d.peakS0 = c.peakS0 := by
    apply ofNat_inj_nat
    have hd := d.hpeakS0
    rw [hbDrel, withPark_strict] at hd
    exact hd.symm.trans c.hpeakS0
  have hcops0 : d.cOps0 = c.cOps0 := by
    apply ofNat_inj_nat
    have hopsEq : d.b0.sudo_5Board_4cost.sudo_5Costs_3ops =
        c.b0.sudo_5Board_4cost.sudo_5Costs_3ops := by rw [hbDrel, withPark_ops]
    have hget := idx_get hopsEq 1 d.hops0
    exact d.hop10.symm.trans (hget.trans c.hop10)
  let t : PegTwin c d := {
    src := hsrcD.trans hsrc.symm
    g := hgD.trans hg.symm
    n := hnD.trans hn.symm
    k := hkD.trans hk.symm
    bench := hbD.trans hbch.symm
    moves0 := by rw [hmovD, hmv0, hmvE]
    slides0 := by
      have hslE : sl = slP := ofNat_inj_nat (hsl.symm.trans hslP)
      rw [hslD, hsl0, hslE]
    hole0 := hhole0
    peak0 := hpeak0
    peakS0 := hps0
    cOps0 := hcops0
    t0 := ht0D.trans ht0.symm
    m := hmD.trans hmE.symm
    fromHole := ((hole : Nat) : Int)
    ridx := Int.ofNat (s.ridx + 1)
    b0 := hbDrel
  }
  obtain ⟨cu, bLoop, ys, moves, slides, holeM, peak, peakS, cOps, hHu, hDu, hopsu,
      hcopyU, hsrcU, hgU, hmU, hnU, hkU, hbU, hpegB, hys, _hGap, _hX,
      _hOp, _hRow, _htier, _hmk, _h7, hopU, _hOpsLe, hctrlU, _hhighU,
      _hcontrolU, _hlenU, _hmaxU, ht0U, hmul, hrow0U, hmvB, hslB, hhoB, hpkB, hpsB,
      ⟨_, _, _⟩, ⟨_, _, _⟩, _hmulW⟩ :=
    mul_of_shape h hM hS hm hT hhome
  obtain ⟨dp, bMulP, hmulP, _, _, _, _, _, hrow0P, hctrl0P, hmP, ht0P, _, _, _, hlive⟩ :=
    parked_gap_mul h hM hS hF hm hT hhome
  obtain ⟨ysP, movesP, slidesP, holeP, peakP, peakSP, cOpsP, hHP, hDP, hopsP, hnamed, hysP,
      hmovP, hslP, hhoP, hpkP, hpsP, hopP, hsrcP, hgP, hnP, hkP, hbP, hparkE, _h5⟩ := hlive
  obtain ⟨bParkP, hparkP, hcopyP⟩ := hparkE
  have hbU0 : c.b0 = cu.b0 := by
    injection hcopyC.symm.trans hcopyU
  have hmovSame : cu.moves0 = c.moves0 := by
    apply ofNat_inj_nat
    have hu := cu.hmoves0
    rw [← hbU0] at hu
    exact hu.symm.trans c.hmoves0
  have hslideSame : cu.slides0 = c.slides0 := by
    apply ofNat_inj_nat
    have hu := cu.hslides0
    rw [← hbU0] at hu
    have h := hu.symm.trans c.hslides0
    exact ((ofNat_eq_natCast _).symm).trans (h.trans (ofNat_eq_natCast _))
  have hholeSame : cu.hole0 = c.hole0 := by
    apply ofNat_inj_nat
    have hu := cu.hHole0
    rw [← hbU0] at hu
    have h := hu.symm.trans c.hHole0
    exact ((ofNat_eq_natCast _).symm).trans (h.trans (ofNat_eq_natCast _))
  have hpeakSame : cu.peak0 = c.peak0 := by
    apply ofNat_inj_nat
    have hu := cu.hpeak0
    rw [← hbU0] at hu
    exact hu.symm.trans c.hpeak0
  have hpsSame : cu.peakS0 = c.peakS0 := by
    apply ofNat_inj_nat
    have hu := cu.hpeakS0
    rw [← hbU0] at hu
    exact hu.symm.trans c.hpeakS0
  have hcopsSame : cu.cOps0 = c.cOps0 := by
    apply ofNat_inj_nat
    have hopsEq : cu.b0.sudo_5Board_4cost.sudo_5Costs_3ops =
        c.b0.sudo_5Board_4cost.sudo_5Costs_3ops := by rw [← hbU0]
    have hget := idx_get hopsEq 1 cu.hops0
    have hopC : c.b0.sudo_5Board_4cost.sudo_5Costs_3ops[1]'(hopsEq ▸ cu.hops0) =
        (c.cOps0 : Int) := by
      cases Subsingleton.elim (hopsEq ▸ cu.hops0) c.hops0
      exact c.hop10
    exact cu.hop10.symm.trans (hget.trans hopC)
  have hb0w : cu.b0 = withPark c.b0 (embed cu.row0) ((cu.ctrl0 : Nat) : Int)
      c.b0.sudo_5Board_11parked_from c.b0.sudo_5Board_8rung_idx := by
    rw [← hbU0]
    have hrowE : c.b0.sudo_5Board_3row = embed cu.row0 := by
      rw [c.hRow, hrow0, ← hrow0U]
    have hctrlE : c.b0.sudo_5Board_4cost.sudo_5Costs_4ctrl = ((cu.ctrl0 : Nat) : Int) := by
      rw [c.hCtrl0, hctrl0, ← hctrlU]
    have hid := (withPark_id c.b0).symm
    rw [hrowE, hctrlE] at hid
    exact hid
  let tU : PegTwin c cu := {
    src := hsrcU.trans hsrc.symm
    g := hgU.trans hg.symm
    n := hnU.trans hn.symm
    k := hkU.trans hk.symm
    bench := hbU.trans hbch.symm
    moves0 := hmovSame
    slides0 := hslideSame
    hole0 := hholeSame
    peak0 := hpeakSame
    peakS0 := hpsSame
    cOps0 := hcopsSame
    t0 := ht0U.trans ht0.symm
    m := hmU.trans hmE.symm
    fromHole := c.b0.sudo_5Board_11parked_from
    ridx := c.b0.sudo_5Board_8rung_idx
    b0 := hb0w
  }
  have hUeq := twin_boards_eq c cu tU rfl rfl (hrow0U.trans hrow0.symm)
    (ht0U.trans ht0.symm) (hctrlU.trans hctrl0.symm)
  have hBPark : bPark = bParkP := by
    injection hpark.symm.trans hparkP
  have hbP0 : d.b0 = dp.b0 := by
    injection hcopyD.symm.trans (hBPark ▸ hcopyP)
  have hmovP0 : dp.moves0 = d.moves0 := by
    apply ofNat_inj_nat
    have hu := dp.hmoves0
    rw [← hbP0] at hu
    exact hu.symm.trans d.hmoves0
  have hslideP0 : dp.slides0 = d.slides0 := by
    apply ofNat_inj_nat
    have hu := dp.hslides0
    rw [← hbP0] at hu
    have h := hu.symm.trans d.hslides0
    exact ((ofNat_eq_natCast _).symm).trans (h.trans (ofNat_eq_natCast _))
  have hholeP0 : dp.hole0 = d.hole0 := by
    apply ofNat_inj_nat
    have hu := dp.hHole0
    rw [← hbP0] at hu
    have h := hu.symm.trans d.hHole0
    exact ((ofNat_eq_natCast _).symm).trans (h.trans (ofNat_eq_natCast _))
  have hpeakP0 : dp.peak0 = d.peak0 := by
    apply ofNat_inj_nat
    have hu := dp.hpeak0
    rw [← hbP0] at hu
    exact hu.symm.trans d.hpeak0
  have hpsP0 : dp.peakS0 = d.peakS0 := by
    apply ofNat_inj_nat
    have hu := dp.hpeakS0
    rw [← hbP0] at hu
    exact hu.symm.trans d.hpeakS0
  have hcopsP0 : dp.cOps0 = d.cOps0 := by
    apply ofNat_inj_nat
    have hopsEq : dp.b0.sudo_5Board_4cost.sudo_5Costs_3ops =
        d.b0.sudo_5Board_4cost.sudo_5Costs_3ops := by rw [← hbP0]
    have hget := idx_get hopsEq 1 dp.hops0
    have hopD : d.b0.sudo_5Board_4cost.sudo_5Costs_3ops[1]'(hopsEq ▸ dp.hops0) =
        (d.cOps0 : Int) := by
      cases Subsingleton.elim (hopsEq ▸ dp.hops0) d.hops0
      exact d.hop10
    exact dp.hop10.symm.trans (hget.trans hopD)
  have hb0wP : dp.b0 = withPark d.b0 (embed dp.row0) ((dp.ctrl0 : Nat) : Int)
      d.b0.sudo_5Board_11parked_from d.b0.sudo_5Board_8rung_idx := by
    rw [← hbP0]
    have hrowE : d.b0.sudo_5Board_3row = embed dp.row0 := by
      rw [d.hRow, hrowD, ← hrow0P]
    have hctrlE : d.b0.sudo_5Board_4cost.sudo_5Costs_4ctrl = ((dp.ctrl0 : Nat) : Int) := by
      rw [d.hCtrl0, hctrlD, ← hctrl0P]
    have hid := (withPark_id d.b0).symm
    rw [hrowE, hctrlE] at hid
    exact hid
  let tP : PegTwin d dp := {
    src := hsrcP.trans hsrcD.symm
    g := hgP.trans hgD.symm
    n := hnP.trans hnD.symm
    k := hkP.trans hkD.symm
    bench := hbP.trans hbD.symm
    moves0 := hmovP0
    slides0 := hslideP0
    hole0 := hholeP0
    peak0 := hpeakP0
    peakS0 := hpsP0
    cOps0 := hcopsP0
    t0 := ht0P.trans ht0D.symm
    m := hmP.trans hmD.symm
    fromHole := d.b0.sudo_5Board_11parked_from
    ridx := d.b0.sudo_5Board_8rung_idx
    b0 := hb0wP
  }
  have hPeq := twin_boards_eq d dp tP rfl rfl (hrow0P.trans hrowD.symm)
    (ht0P.trans ht0D.symm) (hctrl0P.trans hctrlD.symm)
  let bC := pegBoard c c.m
  have hBU : bLoop = bC := hpegB.trans hUeq
  let hHc : 6 < bC.sudo_5Board_4home.size := hBU ▸ hHu
  let hDc : 6 < bC.sudo_5Board_4held.size := hBU ▸ hDu
  let hopsC : 0 < bC.sudo_5Board_4cost.sudo_5Costs_3ops.size := hBU ▸ hopsu
  let bMulU := mulNoLiveBoard bLoop 5 6 cu.g ys ⟨cu.n, cu.k, moves, slides, holeM, cu.bench, peak, peakS, cOps, hopsu⟩ ⟨hHu, hDu⟩
  let rowP := embed (paintRed d.row0 d.t0 c.m)
  let ctrlP := Int.ofNat (d.ctrl0 + c.m)
  let fromP := ((hole : Nat) : Int)
  let ridxP := Int.ofNat (s.ridx + 1)
  have hPdW := pegBoard_withPark c d t
  have hDidx : pegBoard d d.m = pegBoard d c.m := by rw [t.m]
  have hBoardP : pegBoard dp dp.m = withPark bC rowP ctrlP fromP ridxP := by
    rw [hPeq, hDidx, hPdW]
  have hmovPU : movesP = moves := by
    apply ofNat_inj_nat
    have hP := pack_moves_board dp
    rw [← hmovP] at hP
    have hU : bC.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves := by
      rw [← hBU, hmvB]
    have hW : (pegBoard dp dp.m).sudo_5Board_4cost.sudo_5Costs_5moves =
        bC.sudo_5Board_4cost.sudo_5Costs_5moves := by
      rw [hBoardP, withPark_moves]
    have h := hP.symm.trans (hW.trans hU)
    exact ((ofNat_eq_natCast _).symm).trans (h.trans (ofNat_eq_natCast _))
  have hslPU : slidesP = slides := by
    apply ofNat_inj_nat
    have hP := pack_slides_board dp
    rw [← hslP] at hP
    have hU : bC.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides := by
      rw [← hBU, hslB]
    have hW : (pegBoard dp dp.m).sudo_5Board_4cost.sudo_5Costs_6slides =
        bC.sudo_5Board_4cost.sudo_5Costs_6slides := by
      rw [hBoardP, withPark_slides]
    have h := hP.symm.trans (hW.trans hU)
    exact ((ofNat_eq_natCast _).symm).trans (h.trans (ofNat_eq_natCast _))
  have hhoPU : holeP = holeM := by
    apply ofNat_inj_nat
    have hP := pack_hole_board dp
    rw [← hhoP] at hP
    have hU : bC.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat holeM := by
      rw [← hBU, hhoB]
    have hW : (pegBoard dp dp.m).sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
        bC.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole := by
      rw [hBoardP, withPark_hole]
    have h := hP.symm.trans (hW.trans hU)
    exact ((ofNat_eq_natCast _).symm).trans (h.trans (ofNat_eq_natCast _))
  have hpkPU : peakP = peak := by
    apply ofNat_inj_nat
    have hP := pack_peak_board dp
    rw [← hpkP] at hP
    have hU : bC.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak := by
      rw [← hBU, hpkB]
    have hW : (pegBoard dp dp.m).sudo_5Board_4cost.sudo_5Costs_4peak =
        bC.sudo_5Board_4cost.sudo_5Costs_4peak := by
      rw [hBoardP, withPark_peak]
    have h := hP.symm.trans (hW.trans hU)
    exact ((ofNat_eq_natCast _).symm).trans (h.trans (ofNat_eq_natCast _))
  have hpsPU : peakSP = peakS := by
    apply ofNat_inj_nat
    have hP := pack_peakS_board dp
    rw [← hpsP] at hP
    have hU : bC.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int) := by
      rw [← hBU, hpsB]
    have hW : (pegBoard dp dp.m).sudo_5Board_4cost.sudo_5Costs_11peak_strict =
        bC.sudo_5Board_4cost.sudo_5Costs_11peak_strict := by
      rw [hBoardP, withPark_strict]
    exact hP.symm.trans (hW.trans hU)
  have hcopsPU : cOpsP = cOps := by
    apply ofNat_inj_nat
    have hOps : (pegBoard dp dp.m).sudo_5Board_4cost.sudo_5Costs_3ops = bLoop.sudo_5Board_4cost.sudo_5Costs_3ops := by
      rw [hBoardP, withPark_ops, hBU]
    have hget := idx_get hOps 0 hopsP
    have hopC : bLoop.sudo_5Board_4cost.sudo_5Costs_3ops[0]'(hOps ▸ hopsP) = (cOps : Int) := by
      cases Subsingleton.elim (hOps ▸ hopsP) hopsu
      exact hopU
    exact hopP.symm.trans (hget.trans hopC)
  have hysPU : ysP = ys := by
    rw [hysP, hys, hnP, hnU, hkP, hkU, hbP, hbU, hgP, hgU, hmP, hmU]
  have hUform : bMulU =
      mulNoLiveBoard bC 5 6 c.g ys ⟨c.n, c.k, moves, slides, holeM, c.bench, peak, peakS, cOps, hopsC⟩ ⟨hHc, hDc⟩ := by
    have htr := mulNoLiveBoard_transport hBU 5 6 cu.g ys ⟨cu.n, cu.k, moves, slides, holeM, cu.bench, peak, peakS, cOps, hopsu⟩ ⟨hHu, hDu⟩
    exact htr.trans (mulNoLive_eq_args bC 5 6 cu.g c.g ys ys cu.n c.n cu.k c.k
      moves moves slides slides holeM holeM cu.bench c.bench peak peak peakS peakS cOps cOps
      (hgU.trans hg.symm) rfl (hnU.trans hn.symm) (hkU.trans hk.symm) rfl rfl rfl
      (hbU.trans hbch.symm) rfl rfl rfl hHc hDc hopsC)
  have hPform : bMulP =
      mulNoLiveBoard (withPark bC rowP ctrlP fromP ridxP) 5 6 c.g ys ⟨c.n, c.k, moves, slides, holeM, c.bench, peak, peakS, cOps, (withPark_ops bC rowP ctrlP fromP ridxP ▸ hopsC)⟩ ⟨(withPark_home bC rowP ctrlP fromP ridxP ▸ hHc), (withPark_held bC rowP ctrlP fromP ridxP ▸ hDc)⟩ := by
    have htr := mulNoLiveBoard_transport hBoardP 5 6 dp.g ysP ⟨dp.n, dp.k, movesP, slidesP, holeP, dp.bench, peakP, peakSP, cOpsP, hopsP⟩ ⟨hHP, hDP⟩
    have hargs := mulNoLive_eq_args (withPark bC rowP ctrlP fromP ridxP) 5 6
      dp.g c.g ysP ys dp.n c.n dp.k c.k movesP moves slidesP slides holeP holeM
      dp.bench c.bench peakP peak peakSP peakS cOpsP cOps
      (hgP.trans hg.symm) hysPU (hnP.trans hn.symm) (hkP.trans hk.symm) hmovPU hslPU hhoPU
      (hbP.trans hbch.symm) hpkPU hpsPU hcopsPU
      (hBoardP ▸ hHP) (hBoardP ▸ hDP) (hBoardP ▸ hopsP)
    have hir := mulNoLiveBoard_irrel (withPark bC rowP ctrlP fromP ridxP) 5 6 c.g ys c.n c.k
      moves slides holeM c.bench peak peakS cOps
      (hBoardP ▸ hHP) (withPark_home bC rowP ctrlP fromP ridxP ▸ hHc)
      (hBoardP ▸ hDP) (withPark_held bC rowP ctrlP fromP ridxP ▸ hDc)
      (hBoardP ▸ hopsP) (withPark_ops bC rowP ctrlP fromP ridxP ▸ hopsC)
    exact hnamed.trans (htr.trans (hargs.trans hir))
  have hliveW := mulNoLiveBoard_withPark bC rowP ctrlP fromP ridxP 5 6 c.g ys ⟨c.n, c.k, moves, slides, holeM, c.bench, peak, peakS, cOps, hopsC⟩ ⟨hHc, hDc⟩
  have hfin0 : bMulP = withPark bMulU rowP ctrlP fromP ridxP := by
    exact hPform.trans (hliveW.trans
      (congrArg (fun b => withPark b rowP ctrlP fromP ridxP) hUform.symm))
  have hrowA : rowP =
      embed (paintRed (afterPark s.row (-1) s.parkAt hole r) s.t0 s.tally) := by
    show embed (paintRed d.row0 d.t0 c.m) = embed (paintRed (afterPark s.row (-1) s.parkAt hole r) s.t0 s.tally)
    rw [hrowD, ht0D, hmE]
  have hctrlA : ctrlP = ((s.ctrl + 2 + s.tally : Nat) : Int) := by
    show Int.ofNat (d.ctrl0 + c.m) = ((s.ctrl + 2 + s.tally : Nat) : Int)
    rw [hctrlD, hmE]
    exact ofNat_eq_natCast _
  rw [hrowA, hctrlA] at hfin0
  exact ⟨bMulU, bMulP,
    ⟨cu, bLoop, by simpa [bMulU] using hmul, hpegB, hcopyU, hrow0U, hctrlU, hgU, hmU,
      hnU, hkU, hbU, hsrcU, ht0U⟩,
    ⟨dp, hmulP, hrow0P, hctrl0P, hmP, ht0P, hgP, hnP, hkP, hbP, hsrcP,
      ⟨bParkP, hparkP, hcopyP⟩⟩,
    hfin0⟩

/-- `ClimbInvK` supplies the core and one charge of tight headroom. -/
noncomputable def parked_gap_is_withPark_ofK
    {done rest : List Nat} {r : Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvK done (r :: rest) b s base)
    (hF : s.fromHole < 0) (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax)
    (hhome : s.onBench = false) :=
  parked_gap_is_withPark h.toCore (moveHeadroom_of_cons h) (slideHeadroom_of_cons h)
    hF hm hT hhome

/-- On a final red rung, clear of the parked gap, the cube spare→gap, and the mul
    by the input are the unparked results with the park row, counter, hole, and
    rung index. The bench is the product list the unparked mul leaves. -/
theorem final_red_emit
    {done : List Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvK done [2] b s base)
    (hF : s.fromHole < 0) (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax)
    (hhome : s.onBench = false)
    (hxLen : base.x.length = base.n) (hxT : allTritList base.x) :
    ∃ (bMul bClear bCube bRed : Ecbs.Board),
      Ecbs.clear bMul ((5 : Nat) : Int) = .ok bClear ∧
      Ecbs.cube bClear ((6 : Nat) : Int) ((5 : Nat) : Int) = .ok bCube ∧
      Ecbs.mul bCube ((5 : Nat) : Int) (base.xHome : Int) ((6 : Nat) : Int)
          false false false = .ok bRed ∧
      bRed.sudo_5Board_3row =
        embed (paintRed (afterPark s.row (-1) s.parkAt
          (climbAt base.ladder0 base.R s.ridx) 2) s.t0 s.tally) ∧
      bRed.sudo_5Board_4cost.sudo_5Costs_4ctrl =
        ((s.ctrl + 2 + s.tally : Nat) : Int) ∧
      bRed.sudo_5Board_11parked_from =
        ((climbAt base.ladder0 base.R s.ridx : Nat) : Int) ∧
      bRed.sudo_5Board_8rung_idx = Int.ofNat (s.ridx + 1) ∧
      bRed.sudo_5Board_9tally_len = (s.tally : Int) ∧
      bRed.sudo_5Board_8bench_on = true ∧
      bRed.sudo_5Board_8bench_to = (5 : Int) ∧
      bRed.sudo_5Board_5bench =
        embed (fieldMul s.n s.k s.benchlen base.x
          (fieldCube s.n s.k s.benchlen
            (fieldMul s.n s.k s.benchlen s.gap
              (cubeTimes s.n s.k s.benchlen s.gap s.tally))) ++
          List.replicate (s.benchlen - s.n) 0) := by
  obtain ⟨bLoopR, bMulR, bClearR, bCubeR, bRedR, hmulR, _hclearR, _hcubeR, _hredR,
      _bud, _lenC, _t0C, _rowC, _tierC, _highC, _ctrlC, _maxC, _t0Cu, _t0R,
      _tierCu, _tierR, _fCube, _fMul, hon, hto, hlenR, hbench, hclearF, hcubeF,
      hmulF, _hcubeBoth, _hmulBoth, hpack, _hrel⟩ := red_cube_mul_ofK h hm hT hhome hxLen hxT
  obtain ⟨cU, _ys, _moves, _slides, _holeM, _peak, _peakS, _cOps, _hH, _hD, _hops,
      hloopR, hrowU, hctrlU, hgU, hmU, hnU, hkU, hbU, hsrcU, ht0U, _hnamed,
      _hys, _hmv, _hsl, _hho, _hpk, _hps, hcopyU⟩ := hpack
  obtain ⟨bMulU, bMulP, ⟨cP, bLoopP, hmulP, hloopP, hcopyP, hrowP, hctrlP, hgP,
      hmP, hnP, hkP, hbP, hsrcP, ht0P⟩, _parked, hrel⟩ :=
    parked_gap_is_withPark_ofK h hF hm hT hhome
  have hb0 : cP.b0 = cU.b0 := by
    injection hcopyP.symm.trans hcopyU
  have hboards := pegBoard_same_copy cP cU hb0
    (hsrcU.trans hsrcP.symm) (hgU.trans hgP.symm) (hnU.trans hnP.symm)
    (hkU.trans hkP.symm) (hbU.trans hbP.symm) (hrowU.trans hrowP.symm)
    (ht0U.trans ht0P.symm) (hctrlU.trans hctrlP.symm) (hmU.trans hmP.symm)
  have hloops : bLoopR = bLoopP := by
    rw [hloopR, hloopP, hboards]
  have hmulSame : bMulR = bMulU := by
    have hmulR' := hmulR
    rw [hloops] at hmulR'
    injection hmulR'.symm.trans hmulP
  have hpark : bMulP = withPark bMulR
      (embed (paintRed (afterPark s.row (-1) s.parkAt
        (climbAt base.ladder0 base.R s.ridx) 2) s.t0 s.tally))
      (((s.ctrl + 2 + s.tally : Nat) : Int))
      ((climbAt base.ladder0 base.R s.ridx : Nat) : Int)
      (Int.ofNat (s.ridx + 1)) := by
    simpa [hmulSame] using hrel
  let row := embed (paintRed (afterPark s.row (-1) s.parkAt
    (climbAt base.ladder0 base.R s.ridx) 2) s.t0 s.tally)
  let ctrl := ((s.ctrl + 2 + s.tally : Nat) : Int)
  let fromHole := ((climbAt base.ladder0 base.R s.ridx : Nat) : Int)
  let ridx := Int.ofNat (s.ridx + 1)
  have hclear := hclearF row ctrl fromHole ridx
  have hcube := hcubeF row ctrl fromHole ridx
  have hmul := hmulF row ctrl fromHole ridx
  rw [← hpark] at hclear
  have hcube' : Ecbs.cube (withPark bClearR row ctrl fromHole ridx)
      ((6 : Nat) : Int) ((5 : Nat) : Int) =
      .ok (withPark bCubeR row ctrl fromHole ridx) := hcube
  have hmul' : Ecbs.mul (withPark bCubeR row ctrl fromHole ridx)
      ((5 : Nat) : Int) (base.xHome : Int) ((6 : Nat) : Int) false false false =
      .ok (withPark bRedR row ctrl fromHole ridx) := hmul
  refine ⟨bMulP, withPark bClearR row ctrl fromHole ridx,
      withPark bCubeR row ctrl fromHole ridx, withPark bRedR row ctrl fromHole ridx,
      hclear, hcube', hmul', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [withPark, row]
  · simp [withPark, ctrl]
  · simp [withPark, fromHole]
  · simp [withPark, ridx]
  · simp [withPark, hlenR]
  · simp [withPark, hon]
  · simp [withPark, hto]
  · simp [withPark, hbench]

/-- While rungs remain, the tally segment is white, so the scan in the next rung
    leaves the board unchanged. -/
theorem white_of_shape (b : Ecbs.Board) (s : ClimbModel) (rest : List Nat)
    (base : ClimbBudget) (hinv : ClimbInv b s) (hshape : ClimbShape b s rest base)
    (hrest : rest ≠ []) (hm : 0 < s.tally)
    (hfit : FitsLen (s.t0 + s.tally)) (hfitM : FitsLen s.tally) :
    SudoRt.runLoopOn (Int.ofNat 0) (fuelRange (Int.ofNat 0) (Int.ofNat (s.tally - 1)))
      (whiteStep b (Int.ofNat (s.tally - 1)))
      (fun j => .ok (b, j))
      (fun _ => .ok (b, (0 : Int))) =
    .ok (b, Int.ofNat (s.tally - 1)) := by
  have hfin : rest.isEmpty = false := by
    cases rest with
    | nil => exact absurd rfl hrest
    | cons _ _ => rfl
  have hwhite : ∀ j (hj : j < s.tally), s.row[s.t0 + j]'(by
      exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj s.t0) hshape.seg.room) = 1 := by
    intro j hj
    have hc := hshape.seg.colour j hj
    simpa [hfin] using hc
  exact white_scan_loop_refines b s.row s.t0 s.tally hm hinv.t0 hinv.row hshape.seg.room
    hwhite hfit hfitM


end EcbsLink2.Link2
