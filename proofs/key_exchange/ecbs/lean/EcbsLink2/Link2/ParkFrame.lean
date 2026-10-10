/-
  Park-frame transport for a climb rung, and the parked final red successor.
  `withPark` overwrites the row, the control counter, the parked-from hole, and
  the rung index. Cost counters and the slides are copied, so a rung delta
  survives the frame (`rungDelta_withPark`). A climb invariant survives it when
  the model agrees on every field the frame does not write.
-/
import EcbsLink2.Link2.InvertStep

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- `cubeTimes` keeps the length of its input when that length is `n`. -/
theorem cubeTimes_length (n k bench : Nat) (x : List Nat) (t : Nat)
    (hx : x.length = n) (hn : n ≤ bench) :
    (cubeTimes n k bench x t).length = n := by
  induction t with
  | zero => simpa [cubeTimes] using hx
  | succ t ih =>
    rw [cubeTimes, fieldCube, List.length_take]
    have hcomb : (combStrip n bench (cubeTimes n k bench x t)).length = bench :=
      combStrip_length n bench _
    have hred : (reduceStrip n (n - k) (combStrip n bench (cubeTimes n k bench x t))).length =
        (combStrip n bench (cubeTimes n k bench x t)).length := by
      simpa [laneFold] using
        laneFold_length n (n - k) (combStrip n bench (cubeTimes n k bench x t))
          (by rw [hcomb]; exact hn)
    rw [hred, hcomb]
    exact Nat.min_eq_left hn

/-- `ClimbInv` of a parked frame, read off the fields `withPark` copies plus the
    four fields it writes. The written fields are the model's row, counter,
    parked-from hole, and rung index. -/
theorem climbInv_atPark (b : Ecbs.Board) (s : ClimbModel)
    (row : Array Int) (ctrl fromHole ridx : Int)
    (hG : 5 < b.sudo_5Board_4home.size)
    (hGs : 5 < b.sudo_5Board_4held.size)
    (hmark : b.sudo_5Board_9marker_on = false)
    (hlen : b.sudo_5Board_9tally_len = (s.tally : Int))
    (hhigh : b.sudo_5Board_4cost.sudo_5Costs_15control_highest = (s.high : Int))
    (ht0 : b.sudo_5Board_6tally0 = (s.t0 : Int))
    (hpark : b.sudo_5Board_9park_hole = (s.parkAt : Int))
    (hrow : row = embed s.row)
    (hctrl : ctrl = (s.ctrl : Int))
    (hfrom : fromHole = s.fromHole)
    (hridx : ridx = (s.ridx : Int))
    (hHome : s.onBench = false →
      b.sudo_5Board_4held[5]'(hGs) = true ∧
        b.sudo_5Board_4home[5]'(hG) = embed s.gap)
    (hBench : s.onBench = true →
      b.sudo_5Board_8bench_on = true ∧
        b.sudo_5Board_8bench_to = (5 : Int) ∧
        b.sudo_5Board_5bench =
          embed (s.gap.take s.n ++ List.replicate (s.benchlen - s.n) 0) ∧
        s.work = s.gap) :
    ClimbInv (withPark b row ctrl fromHole ridx) s := by
  refine
    { hG := by rw [withPark_home]; exact hG
      hGs := by rw [withPark_held]; exact hGs
      marker := by rw [withPark_marker]; exact hmark
      len := by rw [withPark_len]; exact hlen
      ctrl := by rw [withPark_ctrl]; exact hctrl
      high := by rw [withPark_high]; exact hhigh
      t0 := by rw [withPark_tally0]; exact ht0
      row := by rw [withPark_row]; exact hrow
      park := by rw [withPark_park]; exact hpark
      fromP := by rw [withPark_from]; exact hfrom
      ridx := by rw [withPark_ridx]; exact hridx
      gapHome := ?_
      gapBench := ?_ }
  · intro hOff
    obtain ⟨hh, hg⟩ := hHome hOff
    exact ⟨cell_eq_of (withPark_held b row ctrl fromHole ridx) hh,
      cell_eq_of (withPark_home b row ctrl fromHole ridx) hg⟩
  · intro hOn
    obtain ⟨hon, hto, hbench, hwork⟩ := hBench hOn
    refine ⟨?_, ?_, ?_, hwork⟩
    · rw [withPark_on]; exact hon
    · rw [withPark_to]; exact hto
    · rw [withPark_bench]; exact hbench

/-- A board that already satisfies `ClimbInv` still does after `withPark`, once
    the model keeps every field the frame does not write and the four written
    fields are the new model's row, counter, parked-from hole, and rung index.
    Move and slide deltas are `rungDelta_withPark`: those counters are copied,
    and the peak bound stays `max(prev, 7)`. -/
theorem climbInv_withPark {b : Ecbs.Board} {s s' : ClimbModel}
    (h : ClimbInv b s)
    (row : Array Int) (ctrl fromHole ridx : Int)
    (htally : s'.tally = s.tally)
    (hhigh : s'.high = s.high)
    (ht0 : s'.t0 = s.t0)
    (hparkAt : s'.parkAt = s.parkAt)
    (hgap : s'.gap = s.gap)
    (hwork : s'.work = s.work)
    (hon : s'.onBench = s.onBench)
    (hn : s'.n = s.n)
    (hb : s'.benchlen = s.benchlen)
    (hrow : row = embed s'.row)
    (hctrl : ctrl = (s'.ctrl : Int))
    (hfrom : fromHole = s'.fromHole)
    (hridx : ridx = (s'.ridx : Int)) :
    ClimbInv (withPark b row ctrl fromHole ridx) s' := by
  refine climbInv_atPark b s' row ctrl fromHole ridx h.hG h.hGs h.marker
    (by rw [h.len, htally]) (by rw [h.high, hhigh]) (by rw [h.t0, ht0])
    (by rw [h.park, hparkAt]) hrow hctrl hfrom hridx ?_ ?_
  · intro hOff
    have hOffS : s.onBench = false := by rwa [hon] at hOff
    obtain ⟨hh, hg⟩ := h.gapHome hOffS
    exact ⟨hh, hgap.symm ▸ hg⟩
  · intro hOn
    have hOnS : s.onBench = true := by rwa [hon] at hOn
    obtain ⟨honB, hto, hbench, hworkS⟩ := h.gapBench hOnS
    refine ⟨honB, hto, ?_, ?_⟩
    · rw [hbench, hgap, hn, hb]
    · rw [hwork, hgap]
      exact hworkS

/-- Parked final red rung. The clear, the spare cube, and the mul by the input
    are each `withPark` of the unparked boards at the real park frame. The rung
    delta is the unparked red delta (`rungDelta_withPark`): the frame copies
    moves, slides, ops, and peak. The climb invariant is that frame of the
    unparked red board (`climbInv_atPark`). -/
theorem red_final_ge
    {done : List Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvK done [2] b s base)
    (hge : 0 ≤ s.fromHole) (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax)
    (hhome : s.onBench = false)
    (hParkAt : s.parkAt = base.ladder0 + base.R)
    (hCap : climbTallyPrefix base.tally0 done [2] ≤ base.mMax)
    (hxLen : base.x.length = base.n) (hxT : allTritList base.x) :
    ∃ b',
      (do
          let b ← (do
              let b ← Ecbs.park_rung b ((2 : Nat) : Int)
              let b ← Ecbs.copy_band b ((6 : Nat) : Int) ((5 : Nat) : Int) false
              let _ ← SudoRt.runLoopOn (Int.ofNat 0)
                  (fuelRange (Int.ofNat 0) (Int.ofNat (s.tally - 1)))
                  (whiteStep b (Int.ofNat (s.tally - 1)))
                  (fun j => .ok (b, j))
                  (fun _ => .ok (b, (0 : Int)))
              let out ← SudoRt.runLoopOn (Int.ofNat 0, b)
                  (fuelRange (Int.ofNat 0) (Int.ofNat (s.tally - 1)))
                  (cubePegStep 6 (Int.ofNat (s.tally - 1)))
                  (fun σ => .ok σ)
                  (fun r => .ok ((0 : Int), r))
              let b := out.2
              let b ← Ecbs.mul b (5 : Int) (5 : Int) (6 : Int) false false false
              Ecbs.clear b (5 : Int))
          let b ← Ecbs.cube b ((6 : Nat) : Int) ((5 : Nat) : Int)
          Ecbs.mul b ((5 : Nat) : Int) (base.xHome : Int) ((6 : Nat) : Int)
            false false false) = .ok b' ∧
      ClimbInvK (done ++ [2]) [] b'
        (modelRung s base.x 2 (climbAt base.ladder0 base.R s.ridx) true) base := by
  let hole := climbAt base.ladder0 base.R s.ridx
  let rowP := embed (paintRed (afterPark s.row s.fromHole s.parkAt hole 2) s.t0 s.tally)
  let ctrlP := Int.ofNat (s.ctrl + 4 + s.tally)
  let fromH := ((hole : Nat) : Int)
  let ridxH := Int.ofNat (s.ridx + 1)
  let s' := modelRung s base.x 2 hole true
  obtain ⟨bClearU, bCube, bRed, hclearProg, hcubeF, hmulF, hcubeU, hredU, hrel,
      honR, htoR, hlenR, hbenchR, hhighR, htmaxR⟩ :=
    parked_clear_unparked h hge hm hT hhome hxLen hxT
  obtain ⟨bClear, bIdle, hrunI, hframe, hbenchE, hbonE, htoE, hmarkE, _hlenE, ht0E,
      hparkE, _hhighE, htierE, hladE, hnrE, _htmaxE, h5H, h5D, h6H, h6D, h7E, h5f, h6f,
      hkeep, ⟨ps, hps⟩, ⟨hnat, hhn⟩, _hrowIdle, _hctrlIdle, hδ, hslots, hpieceM, hpieceS⟩ :=
    parked_clear_ge h hge hm hT hhome
  have hboards : withPark bClearU rowP ctrlP fromH ridxH = bClear := by
    have hjoin := hclearProg.symm.trans hrunI
    injection hjoin
  let bClearP := withPark bClearU rowP ctrlP fromH ridxH
  have hP : bClearP = bClear := hboards
  have hδP : RungDelta b bClearP base s.tally := by
    simpa [hP] using hδ
  have hslotsP : ClearSlots b.sudo_5Board_4cost.sudo_5Costs_3ops
      bClearP.sudo_5Board_4cost.sudo_5Costs_3ops s.tally := by
    simpa [hP] using hslots
  have hmarkP : bClearP.sudo_5Board_9marker_on = false := by
    rw [hP, hframe, withPark_marker]; exact hmarkE
  have htierP : bClearP.sudo_5Board_1t = b.sudo_5Board_1t := by
    rw [hP, hframe, withPark_tier]; exact htierE
  have hbonP : bClearP.sudo_5Board_8bench_on = true := by
    rw [hP, hframe, withPark_on]; exact hbonE
  have htoP : bClearP.sudo_5Board_8bench_to = (5 : Int) := by
    rw [hP, hframe, withPark_to]; exact htoE
  have hbenchP : bClearP.sudo_5Board_5bench =
      embed (fieldMul s.n s.k s.benchlen s.gap
        (cubeTimes s.n s.k s.benchlen s.gap s.tally) ++
        List.replicate (s.benchlen - s.n) 0) := by
    rw [hP, hframe, withPark_bench]; exact hbenchE
  have h5HP : 5 < bClearP.sudo_5Board_4home.size := by
    rw [hP, hframe, withPark_home]; exact h5H
  have h5DP : 5 < bClearP.sudo_5Board_4held.size := by
    rw [hP, hframe, withPark_held]; exact h5D
  have h6HP : 6 < bClearP.sudo_5Board_4home.size := by
    rw [hP, hframe, withPark_home]; exact h6H
  have h6DP : 6 < bClearP.sudo_5Board_4held.size := by
    rw [hP, hframe, withPark_held]; exact h6D
  have h7P : 7 ≤ bClearP.sudo_5Board_4held.size := by
    rw [hP, hframe, withPark_held]; exact h7E
  have h5fP : ∀ h5 : 5 < bClearP.sudo_5Board_4held.size,
      bClearP.sudo_5Board_4held[5]'h5 = false := by
    intro h5
    have hheld : bClearP.sudo_5Board_4held = bIdle.sudo_5Board_4held := by
      rw [hP, hframe, withPark_held]
    have h5I : 5 < bIdle.sudo_5Board_4held.size := by
      rw [← congrArg Array.size hheld]; exact h5
    exact (arr_get hheld 5 h5).trans (h5f h5I)
  have h6fP : ∀ h6 : 6 < bClearP.sudo_5Board_4held.size,
      bClearP.sudo_5Board_4held[6]'h6 = false := by
    intro h6
    have hheld : bClearP.sudo_5Board_4held = bIdle.sudo_5Board_4held := by
      rw [hP, hframe, withPark_held]
    have h6I : 6 < bIdle.sudo_5Board_4held.size := by
      rw [← congrArg Array.size hheld]; exact h6
    exact (arr_get hheld 6 h6).trans (h6f h6I)
  have hkeepP : CellKeep bClearP base.xHome base.x := by
    have hheld : bClearP.sudo_5Board_4held = bIdle.sudo_5Board_4held := by
      rw [hP, hframe, withPark_held]
    have hhomeA : bClearP.sudo_5Board_4home = bIdle.sudo_5Board_4home := by
      rw [hP, hframe, withPark_home]
    refine
      { heldLt := by rw [hheld]; exact hkeep.heldLt
        held := (arr_get hheld base.xHome (by rw [hheld]; exact hkeep.heldLt)).trans hkeep.held
        homeLt := by rw [hhomeA]; exact hkeep.homeLt
        arr := (arr_get hhomeA base.xHome (by rw [hhomeA]; exact hkeep.homeLt)).trans hkeep.arr }
  have hopsP : 1 < bClearP.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [hslotsP.size]
    exact h.shape.peg.opsGt
  have hc1P : ∃ c1 : Nat, ∀ h1 : 1 < bClearP.sudo_5Board_4cost.sudo_5Costs_3ops.size,
      bClearP.sudo_5Board_4cost.sudo_5Costs_3ops[1]'h1 = (c1 : Int) := by
    have h1e : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size := h.shape.peg.opsGt
    obtain ⟨_cE, cC, _hcE, hcC, _h0, _h1, _hr⟩ := hslotsP.slots 1 h1e
    refine ⟨cC, ?_⟩
    intro h1
    exact (array_get_irrel (h1 := h1) (h2 := hslotsP.size ▸ h1e)).trans hcC
  have hpkP : ∃ p : Nat, bClearP.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (p : Int) := by
    refine ⟨ps, ?_⟩
    rw [hP, hframe, withPark_strict]; exact hps
  have hholeP : ∃ holeN : Nat,
      bClearP.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = (holeN : Int) := by
    refine ⟨hnat, ?_⟩
    rw [hP, hframe, withPark_hole]; exact hhn
  have hspan3 : 3 * (s.n - 1) < s.benchlen := by
    have hs := h.shape.peg.span
    omega
  have hnleB : s.n ≤ s.benchlen := by
    have hs := h.shape.peg.span
    omega
  have hctLen := cubeTimes_length s.n s.k s.benchlen s.gap s.tally h.shape.gapLen hnleB
  have htrits : allTritList (fieldMul s.n s.k s.benchlen s.gap
      (cubeTimes s.n s.k s.benchlen s.gap s.tally)) := by
    have hraw := fieldMul_trits s.n s.k s.benchlen s.gap
      (cubeTimes s.n s.k s.benchlen s.gap s.tally) hspan3 hnleB
    have htake := List.take_length (cubeTimes s.n s.k s.benchlen s.gap s.tally)
    rw [hctLen] at htake
    simpa [htake] using hraw
  have hpieceMP : ∃ mv mvC : Nat,
      b.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int) ∧
      bClearP.sudo_5Board_4cost.sudo_5Costs_5moves = (mvC : Int) ∧
      mvC ≤ mv + base.n + s.tally * pegCharge base.n base.bench +
        mulCharge base.n base.bench + base.n := by
    obtain ⟨mv, mvC, hmv, hmvC, hle⟩ := hpieceM
    refine ⟨mv, mvC, hmv, ?_, hle⟩
    simpa [hP] using hmvC
  have hpieceSP : ∃ sl slC : Nat,
      b.sudo_5Board_4cost.sudo_5Costs_6slides = (sl : Int) ∧
      bClearP.sudo_5Board_4cost.sudo_5Costs_6slides = (slC : Int) ∧
      slC ≤ sl + s.tally * (2 * base.n) + 2 * base.n := by
    obtain ⟨sl, slC, hsl, hslC, hle⟩ := hpieceS
    refine ⟨sl, slC, hsl, ?_, hle⟩
    simpa [hP] using hslC
  have hpack :=
    red_unparked_delta h hm hT hhome hxLen hxT
      bClearP bClearU bCube bRed rowP ctrlP fromH ridxH rfl
      hδP hslotsP hmarkP htierP hcubeU hredU hrel
      hbonP htoP hbenchP h5HP h5DP h6HP h6DP h7P h5fP h6fP hkeepP hopsP hc1P
      hpkP hholeP htrits hpieceMP hpieceSP
  let b' := withPark bRed rowP ctrlP fromH ridxH
  have hprog :
      (do
          let b ← (do
              let b ← Ecbs.park_rung b ((2 : Nat) : Int)
              let b ← Ecbs.copy_band b ((6 : Nat) : Int) ((5 : Nat) : Int) false
              let _ ← SudoRt.runLoopOn (Int.ofNat 0)
                  (fuelRange (Int.ofNat 0) (Int.ofNat (s.tally - 1)))
                  (whiteStep b (Int.ofNat (s.tally - 1)))
                  (fun j => .ok (b, j))
                  (fun _ => .ok (b, (0 : Int)))
              let out ← SudoRt.runLoopOn (Int.ofNat 0, b)
                  (fuelRange (Int.ofNat 0) (Int.ofNat (s.tally - 1)))
                  (cubePegStep 6 (Int.ofNat (s.tally - 1)))
                  (fun σ => .ok σ)
                  (fun r => .ok ((0 : Int), r))
              let b := out.2
              let b ← Ecbs.mul b (5 : Int) (5 : Int) (6 : Int) false false false
              Ecbs.clear b (5 : Int))
          let b ← Ecbs.cube b ((6 : Nat) : Int) ((5 : Nat) : Int)
          Ecbs.mul b ((5 : Nat) : Int) (base.xHome : Int) ((6 : Nat) : Int)
            false false false) = .ok b' := by
    rw [hclearProg, ok_bind, hcubeF, ok_bind]
    simpa [b', rowP, ctrlP, fromH, ridxH, hole] using hmulF
  have hδR : RungDelta b b' base s.tally :=
    rungDelta_withPark hpack.delta rowP ctrlP fromH ridxH
  obtain ⟨hgap, htall, honM, hwork, hctrlM, hhighM, hrowM, hfromM, hridxM, ht0M,
      hparkM, _hnM, _hkM, _hbM⟩ := model_final_red_ge s base.x hole hge
  have hidx : s.ridx < base.R := by
    rw [h.idx]
    have hk := h.kLe
    simp [List.length_append] at hk
    omega
  have hlenRow : s'.row.length = s.row.length := by
    rw [hrowM, paintRed_length, afterPark_length]
  have hStep := successor_hole base.ladder0 base.R s.ridx s.parkAt s.row.length
    h.shape.park.l0pos hidx hParkAt h.shape.park.holeLt
  have hnle : s.n ≤ s.benchlen := hnleB
  have hinv : ClimbInv b' s' :=
    climbInv_atPark bRed s' rowP ctrlP fromH ridxH
      (Nat.lt_trans (by decide : (5 : Nat) < 6) hpack.home6)
      (Nat.lt_trans (by decide : (5 : Nat) < 6) hpack.held6)
      hpack.marker
      (by rw [hlenR, htall])
      (by rw [hhighR, hhighM])
      (by
        rw [hpack.tally0, hP, hframe, withPark_tally0, ht0E, ht0M])
      (by
        rw [hpack.park, hP, hframe, withPark_park, hparkE, hparkM])
      (by rw [hrowM])
      (by rw [hctrlM]; exact (ofNat_eq_natCast _).symm)
      (by rw [hfromM])
      (by rw [hridxM]; exact (ofNat_eq_natCast _).symm)
      (by
        intro hOff
        rw [honM] at hOff
        cases hOff)
      (by
        intro _
        have hprod := fieldMul_len s.n s.k s.benchlen base.x
          (fieldCube s.n s.k s.benchlen
            (fieldMul s.n s.k s.benchlen s.gap
              (cubeTimes s.n s.k s.benchlen s.gap s.tally))) hnle
        have htake : (fieldMul s.n s.k s.benchlen base.x
            (fieldCube s.n s.k s.benchlen
              (fieldMul s.n s.k s.benchlen s.gap
                (cubeTimes s.n s.k s.benchlen s.gap s.tally)))).take s.n =
            fieldMul s.n s.k s.benchlen base.x
              (fieldCube s.n s.k s.benchlen
                (fieldMul s.n s.k s.benchlen s.gap
                  (cubeTimes s.n s.k s.benchlen s.gap s.tally))) :=
          List.take_of_length_le (Nat.le_of_eq hprod)
        refine ⟨honR, htoR, ?_, ?_⟩
        · rw [hbenchR, hgap, show s'.n = s.n from rfl, show s'.benchlen = s.benchlen from rfl,
            htake]
        · rw [hwork, hgap])
  have hseg : RowSeg s'.row s'.t0 s'.tally true := by
    have hred := rungRow_final_seg s.row s.fromHole s.parkAt hole s.t0 s.tally 2
      h.shape.seg h.parkBelow h.holeBelow (Or.inr (h.fromBelow hge))
    have hEq : s'.row =
        rungRow s.row s.fromHole s.parkAt hole s.t0 s.tally 2 true := by
      rw [hrowM, rungRow, afterTally]
      simp
    simpa [hEq, s'] using hred
  have hdone : done.length + 1 ≤ base.R := by
    have hk := h.kLe
    simp [List.length_append] at hk
    exact hk
  have hfits := final_white_ctrl_fit_ge s.ctrl s.tally base.ctrl0 done.length base.R
    base.mMax h.ctrlLe hT hdone base.fitCtrl
  have hhomeB : b'.sudo_5Board_4home = bRed.sudo_5Board_4home := by rw [withPark_home]
  have hheldB : b'.sudo_5Board_4held = bRed.sudo_5Board_4held := by rw [withPark_held]
  have hladB : b'.sudo_5Board_7ladder0 = b.sudo_5Board_7ladder0 := by
    rw [withPark_ladder, hpack.ladder, hP, hframe, withPark_ladder, hladE]
  have hnrB : b'.sudo_5Board_6nrungs = b.sudo_5Board_6nrungs := by
    rw [withPark_nrungs, hpack.nrungs, hP, hframe, withPark_nrungs, hnrE]
  have htierB : b'.sudo_5Board_1t = b.sudo_5Board_1t := by
    rw [withPark_tier, hpack.tier, htierP]
  have hpark' : ParkRead b' s' [] base := by
    refine
      { ladder0B := by rw [hladB]; exact h.shape.park.ladder0B
        nrungsB := by rw [hnrB]; exact h.shape.park.nrungsB
        climbH := ?_
        holeLt := ?_
        parkLt := ?_
        parkNe := ?_
        parkLe := ?_
        parkIn := ?_
        parkCell := ?_
        fromIdle := ?_
        fromNat := ?_
        srcOk := ?_
        parkHeld := ?_
        nextRung := ?_
        ladderTail := ?_
        fit2 := ?_
        fit4 := ?_
        fitI := ?_
        l0pos := h.shape.park.l0pos
        fitL0 := h.shape.park.fitL0
        fitLR := h.shape.park.fitLR }
    · have hL : b'.sudo_5Board_7ladder0 = Int.ofNat base.ladder0 := by
        rw [hladB, h.shape.park.ladder0B, ← ofNat_eq_natCast]
      have hN : b'.sudo_5Board_6nrungs = Int.ofNat base.R := by
        rw [hnrB, h.shape.park.nrungsB, ← ofNat_eq_natCast]
      exact climb_holes_refines b' base.ladder0 base.R hL hN h.shape.park.l0pos
        h.shape.park.fitL0 h.shape.park.fitLR
    · have hlt : climbAt base.ladder0 base.R (s.ridx + 1) < s.row.length := hStep.1
      rw [← hridxM, ← hlenRow] at hlt
      exact hlt
    · have hlt : s.parkAt < s.row.length := h.shape.park.parkLt
      rw [← hparkM, ← hlenRow] at hlt
      exact hlt
    · have hne : climbAt base.ladder0 base.R (s.ridx + 1) ≠ s.parkAt := hStep.2.1
      rw [← hridxM, ← hparkM] at hne
      exact hne
    · rw [hparkM, hhighM]
      exact h.shape.park.parkLe
    · rw [hparkM]
      exact h.shape.park.parkIn
    · intro hneg
      rw [hfromM] at hneg
      exact absurd hneg (by
        have hnn : 0 ≤ ((hole : Nat) : Int) := Int.ofNat_nonneg hole
        omega)
    · intro hneg
      rw [hfromM] at hneg
      exact absurd hneg (by
        have hnn : 0 ≤ ((hole : Nat) : Int) := Int.ofNat_nonneg hole
        omega)
    · intro _
      rw [hfromM]
      rfl
    · intro _
      rw [hfromM]
      refine ⟨?_, ?_, ?_, ?_⟩
      · have hlt : hole < s.row.length := h.shape.park.holeLt
        rw [← hlenRow] at hlt
        simpa [Int.toNat_ofNat] using hlt
      · have hlt : hole < s.row.length := h.shape.park.holeLt
        rw [h.shape.rowLen] at hlt
        simpa [Int.toNat_ofNat] using hlt
      · have hle : hole ≤ s.high := by
          have hhi : hole < s.t0 := h.holeBelow
          have htop : s.high = s.t0 + s.tally - 1 := h.highTop hm
          omega
        rw [hhighM]
        simpa [Int.toNat_ofNat] using hle
      · have hne : hole ≠ climbAt base.ladder0 base.R (s.ridx + 1) := hStep.2.2
        rw [← hridxM] at hne
        simpa [Int.toNat_ofNat] using hne
    · intro _
      have hlt : s'.parkAt < s'.row.length := by
        have h0 : s.parkAt < s.row.length := h.shape.park.parkLt
        rw [← hparkM, ← hlenRow] at h0
        exact h0
      exact ⟨s'.row[s'.parkAt]'hlt, rfl⟩
    · intro _ _ hrs
      cases hrs
    · intro _ hk _hlt
      simp at hk
    · rw [hctrlM]
      exact hfits.1
    · rw [hctrlM]
      exact hfits.2.1
    · have hri : s.ridx + 2 ≤ base.R + 1 := by
        rw [h.idx]
        omega
      have hfitR : FitsLen (base.R + 1) := by
        have hmul : base.R + 1 ≤ (base.R + 1) * (3 * base.mMax + 5) := by
          apply Nat.le_mul_of_pos_right
          omega
        exact FitsLen.of_le base.fitCtrl (by omega)
      have hle : s'.ridx + 1 ≤ base.R + 1 := by
        rw [hridxM, h.idx]
        omega
      exact FitsLen.of_le hfitR hle
  have hopsB : 1 < b'.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [withPark_ops, hpack.delta.opsSize, ← hδP.opsSize]
    exact hopsP
  have hpeg' : PegRead b' s' base := by
    refine
      { opsGt := hopsB
        cOps := ?_
        peakS := ?_
        holeM := ?_
        trits := ?_
        top := ?_
        fitRow := ?_
        fitTall := ?_
        fitCtrl := ?_
        n_pos := h.shape.peg.n_pos
        span := h.shape.peg.span
        small := h.shape.peg.small
        n_small := h.shape.peg.n_small
        fitN := h.shape.peg.fitN
        fitBn := h.shape.peg.fitBn
        fit3 := h.shape.peg.fit3 }
    · have hi : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
        rw [← hδP.opsSize]
        exact hopsP
      obtain ⟨_, c', _, hc', _⟩ := hpack.delta.ops 1 hi
      refine ⟨c', ?_⟩
      have hOpsEq : b'.sudo_5Board_4cost.sudo_5Costs_3ops =
          bRed.sudo_5Board_4cost.sudo_5Costs_3ops := by
        rw [withPark_ops]
      exact (arr_get hOpsEq 1 hopsB).trans hc'
    · obtain ⟨p, hp⟩ := hpack.strict
      refine ⟨p, ?_⟩
      rw [withPark_strict]
      exact hp
    · obtain ⟨hn0, hh⟩ := hpack.hole
      refine ⟨hn0, ?_⟩
      rw [withPark_hole]
      exact hh
    · have hspanG : 3 * (s.n - 1) < s.benchlen := hspan3
      have htri := fieldMul_trits s.n s.k s.benchlen base.x
        (fieldCube s.n s.k s.benchlen
          (fieldMul s.n s.k s.benchlen s.gap
            (cubeTimes s.n s.k s.benchlen s.gap s.tally))) hspanG hnle
      simpa [hgap, fieldCube, List.take_take] using htri
    · intro hpos
      rw [ht0M, htall, hhighM]
      exact Nat.le_of_eq (h.highTop (htall.symm ▸ hpos)).symm
    · rw [htall]
      exact h.shape.peg.fitRow
    · rw [htall]
      exact h.shape.peg.fitTall
    · rw [hctrlM, htall]
      exact hfits.2.2
  have hshape : ClimbShape b' s' [] base :=
    shape_refresh h.shape b' s' [] rfl rfl rfl
      (by
        rw [hgap]
        exact fieldMul_len s.n s.k s.benchlen base.x
          (fieldCube s.n s.k s.benchlen
            (fieldMul s.n s.k s.benchlen s.gap
              (cubeTimes s.n s.k s.benchlen s.gap s.tally))) hnle)
      hseg
      (by rw [hheldB]; exact hpack.held6)
      (by rw [hhomeB]; exact hpack.home6)
      (by
        have h6 : 6 < b'.sudo_5Board_4held.size := by
          rw [hheldB]; exact hpack.held6
        exact cell_eq_of hheldB hpack.empty6)
      (by rw [hheldB]; exact hpack.held7)
      (by
        intro _
        exact cell_eq_of hheldB hpack.empty5)
      (by
        intro hOff
        rw [honM] at hOff
        cases hOff)
      (by rw [hheldB]; exact hpack.keep.heldLt)
      (by rw [hhomeB]; exact hpack.keep.homeLt)
      (by exact cell_eq_of hheldB hpack.keep.held)
      (by exact cell_eq_of hhomeB hpack.keep.arr)
      (by rw [htierB]; exact h.shape.tierN)
      (by rw [htierB]; exact h.shape.tierK)
      (by rw [htierB]; exact h.shape.tierB)
      (by rw [htierB]; exact h.shape.tierW)
      (by rw [htierB]; exact h.shape.tierH)
      (by rw [htierB]; exact h.shape.tierR)
      (by rw [htierB]; exact h.shape.tierCg)
      (by rw [htierB]; exact h.shape.tierC)
      (by rw [hlenRow]; exact h.shape.rowLen)
      hpark' hpeg'
  have htmax : ∃ tmax : Nat,
      b'.sudo_5Board_4cost.sudo_5Costs_9tally_max = (tmax : Int) ∧
        (0 < s'.tally → tmax < 2 * s'.tally) := by
    obtain ⟨tmax, htm, hnote⟩ := h.tmaxLt
    refine ⟨tmax, ?_, ?_⟩
    · rw [withPark_tmax, htmaxR, htm]
    · intro hpos
      have hlt := hnote (by rw [← htall]; exact hpos)
      rw [htall]
      exact hlt
  have hK := climbInvK_succ h hinv hδR hCap hshape h.holeBelow htmax rfl
  exact ⟨b', hprog, hK⟩

end EcbsLink2.Link2
