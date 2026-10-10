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
      honR, htoR, hlenR, hbenchR, hhighR, htmaxR, _bLoop, _bMul, _hmulU, _hclearU,
      _hpackU⟩ :=
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

/-- A projection `withPark` leaves alone is the same on any two frames. -/
private theorem park_kept {α : Type} (f : Ecbs.Board → α)
    (hf : ∀ (b : Ecbs.Board) (row : Array Int) (ctrl fromHole ridx : Int),
      f (withPark b row ctrl fromHole ridx) = f b)
    {b1 b2 : Ecbs.Board} {r1 r2 : Array Int} {c1 c2 f1 f2 i1 i2 : Int}
    (h : withPark b1 r1 c1 f1 i1 = withPark b2 r1 c1 f1 i1) :
    f (withPark b1 r2 c2 f2 i2) = f (withPark b2 r2 c2 f2 i2) := by
  rw [hf, hf, ← hf b1 r1 c1 f1 i1, ← hf b2 r1 c1 f1 i1]
  exact congrArg f h

/-- `withPark` writes the frame and copies every other field, so boards that
    agree under one frame agree under any frame. -/
theorem withPark_transfer {b1 b2 : Ecbs.Board}
    {r1 r2 : Array Int} {c1 c2 f1 f2 i1 i2 : Int}
    (h : withPark b1 r1 c1 f1 i1 = withPark b2 r1 c1 f1 i1) :
    withPark b1 r2 c2 f2 i2 = withPark b2 r2 c2 f2 i2 := by
  apply board_ext
  · exact park_kept (fun bd => bd.sudo_5Board_1t)
      (fun b row ctrl fromHole ridx => withPark_tier b row ctrl fromHole ridx) h
  · exact park_kept (fun bd => bd.sudo_5Board_4home)
      (fun b row ctrl fromHole ridx => withPark_home b row ctrl fromHole ridx) h
  · exact park_kept (fun bd => bd.sudo_5Board_4held)
      (fun b row ctrl fromHole ridx => withPark_held b row ctrl fromHole ridx) h
  · exact park_kept (fun bd => bd.sudo_5Board_8bench_on)
      (fun b row ctrl fromHole ridx => withPark_on b row ctrl fromHole ridx) h
  · exact park_kept (fun bd => bd.sudo_5Board_8bench_to)
      (fun b row ctrl fromHole ridx => withPark_to b row ctrl fromHole ridx) h
  · exact park_kept (fun bd => bd.sudo_5Board_5bench)
      (fun b row ctrl fromHole ridx => withPark_bench b row ctrl fromHole ridx) h
  · apply cost_ext
    · exact park_kept (fun bd => bd.sudo_5Board_4cost.sudo_5Costs_5moves)
        (fun b row ctrl fromHole ridx => withPark_moves b row ctrl fromHole ridx) h
    · exact park_kept (fun bd => bd.sudo_5Board_4cost.sudo_5Costs_6slides)
        (fun b row ctrl fromHole ridx => withPark_slides b row ctrl fromHole ridx) h
    · rw [withPark_ctrl, withPark_ctrl]
    · exact park_kept (fun bd => bd.sudo_5Board_4cost.sudo_5Costs_5calls)
        (fun _ _ _ _ _ => rfl) h
    · exact park_kept (fun bd => bd.sudo_5Board_4cost.sudo_5Costs_13stale_cleared)
        (fun _ _ _ _ _ => rfl) h
    · exact park_kept (fun bd => bd.sudo_5Board_4cost.sudo_5Costs_14key_grid_moves)
        (fun _ _ _ _ _ => rfl) h
    · exact park_kept (fun bd => bd.sudo_5Board_4cost.sudo_5Costs_12ladder_moves)
        (fun _ _ _ _ _ => rfl) h
    · exact park_kept (fun bd => bd.sudo_5Board_4cost.sudo_5Costs_4peak)
        (fun b row ctrl fromHole ridx => withPark_peak b row ctrl fromHole ridx) h
    · exact park_kept (fun bd => bd.sudo_5Board_4cost.sudo_5Costs_11peak_strict)
        (fun b row ctrl fromHole ridx => withPark_strict b row ctrl fromHole ridx) h
    · exact park_kept (fun bd => bd.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole)
        (fun b row ctrl fromHole ridx => withPark_hole b row ctrl fromHole ridx) h
    · exact park_kept (fun bd => bd.sudo_5Board_4cost.sudo_5Costs_15control_highest)
        (fun b row ctrl fromHole ridx => withPark_high b row ctrl fromHole ridx) h
    · exact park_kept (fun bd => bd.sudo_5Board_4cost.sudo_5Costs_17script_marker_max)
        (fun _ _ _ _ _ => rfl) h
    · exact park_kept (fun bd => bd.sudo_5Board_4cost.sudo_5Costs_9tally_max)
        (fun b row ctrl fromHole ridx => withPark_tmax b row ctrl fromHole ridx) h
    · exact park_kept (fun bd => bd.sudo_5Board_4cost.sudo_5Costs_14moves_by_phase)
        (fun _ _ _ _ _ => rfl) h
    · exact park_kept (fun bd => bd.sudo_5Board_4cost.sudo_5Costs_13peak_by_phase)
        (fun _ _ _ _ _ => rfl) h
    · exact park_kept (fun bd => bd.sudo_5Board_4cost.sudo_5Costs_3ops)
        (fun b row ctrl fromHole ridx => withPark_ops b row ctrl fromHole ridx) h
  · exact park_kept (fun bd => bd.sudo_5Board_5phase) (fun _ _ _ _ _ => rfl) h
  · exact park_kept (fun bd => bd.sudo_5Board_8phase_m0) (fun _ _ _ _ _ => rfl) h
  · exact park_kept (fun bd => bd.sudo_5Board_8phase_pk) (fun _ _ _ _ _ => rfl) h
  · rw [withPark_row, withPark_row]
  · exact park_kept (fun bd => bd.sudo_5Board_10phase_hole) (fun _ _ _ _ _ => rfl) h
  · exact park_kept (fun bd => bd.sudo_5Board_12calling_hole) (fun _ _ _ _ _ => rfl) h
  · exact park_kept (fun bd => bd.sudo_5Board_7ladder0)
      (fun b row ctrl fromHole ridx => withPark_ladder b row ctrl fromHole ridx) h
  · exact park_kept (fun bd => bd.sudo_5Board_6nrungs)
      (fun b row ctrl fromHole ridx => withPark_nrungs b row ctrl fromHole ridx) h
  · exact park_kept (fun bd => bd.sudo_5Board_9park_hole)
      (fun b row ctrl fromHole ridx => withPark_park b row ctrl fromHole ridx) h
  · exact park_kept (fun bd => bd.sudo_5Board_6tally0)
      (fun b row ctrl fromHole ridx => withPark_tally0 b row ctrl fromHole ridx) h
  · exact park_kept (fun bd => bd.sudo_5Board_6marker) (fun _ _ _ _ _ => rfl) h
  · rw [withPark_from, withPark_from]
  · exact park_kept (fun bd => bd.sudo_5Board_9tally_len)
      (fun b row ctrl fromHole ridx => withPark_len b row ctrl fromHole ridx) h
  · exact park_kept (fun bd => bd.sudo_5Board_9marker_on)
      (fun b row ctrl fromHole ridx => withPark_marker b row ctrl fromHole ridx) h
  · rw [withPark_ridx, withPark_ridx]
  · exact park_kept (fun bd => bd.sudo_5Board_6ladder) (fun _ _ _ _ _ => rfl) h
  · exact park_kept (fun bd => bd.sudo_5Board_3log) (fun _ _ _ _ _ => rfl) h

/-- Two runs of copy, the peg loop, the gap mul, and clear on the same entry
    board are the same clear. The copies agree by `Except.ok.inj`; the peg
    boards agree by `pegBoard_same_copy`; mul and clear follow. -/
theorem unparked_clear_eq
    {b : Ecbs.Board} {s : ClimbModel}
    {bLoop bMul bClear bLoop' bMul' bClear' : Ecbs.Board}
    {c c' : PegCtx}
    (hcopy : Ecbs.copy_band b ((6 : Nat) : Int) ((5 : Nat) : Int) false = .ok c.b0)
    (hcopy' : Ecbs.copy_band b ((6 : Nat) : Int) ((5 : Nat) : Int) false = .ok c'.b0)
    (hloop : bLoop = pegBoard c c.m) (hloop' : bLoop' = pegBoard c' c'.m)
    (hsrc : c.src = 6) (hsrc' : c'.src = 6)
    (hg : c.g = s.gap) (hg' : c'.g = s.gap)
    (hn : c.n = s.n) (hn' : c'.n = s.n)
    (hk : c.k = s.k) (hk' : c'.k = s.k)
    (hbench : c.bench = s.benchlen) (hbench' : c'.bench = s.benchlen)
    (hrow : c.row0 = s.row) (hrow' : c'.row0 = s.row)
    (ht0 : c.t0 = s.t0) (ht0' : c'.t0 = s.t0)
    (hctrl : c.ctrl0 = s.ctrl) (hctrl' : c'.ctrl0 = s.ctrl)
    (hm : c.m = s.tally) (hm' : c'.m = s.tally)
    (hmul : Ecbs.mul bLoop ((5 : Nat) : Int) ((5 : Nat) : Int) ((6 : Nat) : Int)
        false false false = .ok bMul)
    (hmul' : Ecbs.mul bLoop' ((5 : Nat) : Int) ((5 : Nat) : Int) ((6 : Nat) : Int)
        false false false = .ok bMul')
    (hclear : Ecbs.clear bMul ((5 : Nat) : Int) = .ok bClear)
    (hclear' : Ecbs.clear bMul' ((5 : Nat) : Int) = .ok bClear') :
    bClear = bClear' := by
  have hb0 : c.b0 = c'.b0 := Except.ok.inj (hcopy.symm.trans hcopy')
  have hpeg : pegBoard c' c'.m = pegBoard c c.m :=
    pegBoard_same_copy c c' hb0
      (hsrc'.trans hsrc.symm) (hg'.trans hg.symm) (hn'.trans hn.symm)
      (hk'.trans hk.symm) (hbench'.trans hbench.symm) (hrow'.trans hrow.symm)
      (ht0'.trans ht0.symm) (hctrl'.trans hctrl.symm) (hm'.trans hm.symm)
  have hloops : bLoop' = bLoop := by rw [hloop', hloop, hpeg]
  have hmulSame : bMul' = bMul := by
    have hmulRun : Ecbs.mul bLoop ((5 : Nat) : Int) ((5 : Nat) : Int) ((6 : Nat) : Int)
        false false false = .ok bMul' := by
      rw [← hloops]
      exact hmul'
    exact Except.ok.inj (hmulRun.symm.trans hmul)
  have hclearRun : Ecbs.clear bMul ((5 : Nat) : Int) = .ok bClear' := by
    rw [← hmulSame]
    exact hclear'
  exact Except.ok.inj (hclear.symm.trans hclearRun)

/-- A non-final red counter, plus the two later park steps and the doubled
    tally, still fits inside the control budget. -/
theorem open_red_ctrl_fit_ge (ctrl tally ctrl0 done R mMax : Nat)
    (hctrl : ctrl ≤ ctrl0 + done * (3 * mMax + 5))
    (ht : tally ≤ mMax) (hd : done + 2 ≤ R)
    (hf : FitsLen (ctrl0 + (R + 1) * (3 * mMax + 5))) :
    FitsLen (ctrl + 4 + 3 * tally + 1) ∧
    FitsLen ((ctrl + 4 + 3 * tally + 1) + 2) ∧
    FitsLen ((ctrl + 4 + 3 * tally + 1) + 4) ∧
    FitsLen ((ctrl + 4 + 3 * tally + 1) + (2 * tally + 1)) := by
  have hmul : (done + 2) * (3 * mMax + 5) =
      done * (3 * mMax + 5) + (6 * mMax + 10) := by
    rw [Nat.add_mul]
    omega
  have hbody : ctrl + 6 * mMax + 10 ≤ ctrl0 + (done + 2) * (3 * mMax + 5) := by
    omega
  have hcap : ctrl0 + (done + 2) * (3 * mMax + 5) ≤
      ctrl0 + (R + 1) * (3 * mMax + 5) :=
    Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _
  refine ⟨FitsLen.of_le hf (by omega), FitsLen.of_le hf (by omega),
    FitsLen.of_le hf (by omega), FitsLen.of_le hf (by omega)⟩

theorem open_cons_tail (r : Nat) (rest : List Nat) (k : Nat) (hk : k < rest.length) :
    (r :: rest)[1 + k]'(by simp; omega) = rest[k] := by
  have hcomm : 1 + k = k + 1 := Nat.add_comm 1 k
  have hk1 : k + 1 < (r :: rest).length := by
    simpa [hcomm] using (by simp; omega : 1 + k < (r :: rest).length)
  exact (getElem_congr (c := r :: rest) (i := 1 + k) (j := k + 1)
    (h := by simp; omega) hcomm).trans (List.getElem_cons_succ r rest k hk1)

/-- The cell a non-final red rung later paints, read on the doubled row, is
    still the empty tail cell. -/
theorem open_red_peg_zero (row : List Nat) (fromHole : Int) (park hole t0 tally : Nat)
    (hpark : park < t0) (hhole : hole < t0)
    (hfrom : fromHole < 0 ∨ fromHole.toNat < t0)
    (hix : t0 + 2 * tally < row.length)
    (hzero : row[t0 + 2 * tally]'hix = 0) :
    (paintOnes (paintOnes (paintRed (afterPark row fromHole park hole 2) t0 tally)
        t0 tally) (t0 + tally) tally)[t0 + 2 * tally]'(by
          rw [paintOnes_length, paintOnes_length, paintRed_length, afterPark_length]
          exact hix) = 0 := by
  have hfromJ : fromHole < 0 ∨ fromHole.toNat < t0 + 2 * tally := by
    cases hfrom with
    | inl h => exact Or.inl h
    | inr h => exact Or.inr (Nat.lt_of_lt_of_le h (by omega))
  have hAp := afterPark_get row fromHole park hole 2 (t0 + 2 * tally)
    (Nat.lt_of_lt_of_le hpark (by omega))
    (Nat.lt_of_lt_of_le hhole (by omega)) hfromJ hix
  have hred := paintRed_get_hi (afterPark row fromHole park hole 2) t0 tally
    (t0 + 2 * tally) (by omega) (by rw [afterPark_length]; exact hix)
  have hone := paintOnes_get_hi (paintRed (afterPark row fromHole park hole 2) t0 tally)
    t0 tally (t0 + 2 * tally) (by omega)
    (by rw [paintRed_length, afterPark_length]; exact hix)
  have htwo := paintOnes_get_hi
    (paintOnes (paintRed (afterPark row fromHole park hole 2) t0 tally) t0 tally)
    (t0 + tally) tally (t0 + 2 * tally) (by omega)
    (by rw [paintOnes_length, paintRed_length, afterPark_length]; exact hix)
  exact htwo.trans (hone.trans (hred.trans (hAp.trans hzero)))

/-- A parked non-final red rung. The clear is the unparked clear in the resume
    frame. Doubling that frame, cubing the spare into the gap, multiplying by
    the input, and laying one more peg is the `ClimbInvK` successor. -/

theorem red_open_finish
    {done rs : List Nat} {r : Nat} {b b' bRed bClear : Ecbs.Board}
    {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvK done (r :: rs) b s base)
    (hge : 0 ≤ s.fromHole) (hr : r = 2) (hrest : rs ≠ [])
    (hParkAt : s.parkAt = base.ladder0 + base.R)
    (hCap : climbTallyPrefix base.tally0 done (r :: rs) ≤ base.mMax)
    (hT : s.tally ≤ base.mMax)
    (hinv : ClimbInv b' (modelRung s base.x r (climbAt base.ladder0 base.R s.ridx) false))
    (hδ' : RungDelta b b' base s.tally)
    (hladB : b'.sudo_5Board_7ladder0 = b.sudo_5Board_7ladder0)
    (hnrB : b'.sudo_5Board_6nrungs = b.sudo_5Board_6nrungs)
    (htierB : b'.sudo_5Board_1t = b.sudo_5Board_1t)
    (hhomeB : b'.sudo_5Board_4home = bRed.sudo_5Board_4home)
    (hheldB : b'.sudo_5Board_4held = bRed.sudo_5Board_4held)
    (hcarry : RedCarry b bRed bClear base s.tally base.xHome base.x)
    (hopsB : 1 < b'.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hopsF : b'.sudo_5Board_4cost.sudo_5Costs_3ops = bRed.sudo_5Board_4cost.sudo_5Costs_3ops)
    (hstrictF : b'.sudo_5Board_4cost.sudo_5Costs_11peak_strict =
      bRed.sudo_5Board_4cost.sudo_5Costs_11peak_strict)
    (hholeF : b'.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      bRed.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole)
    (htmaxEq : b'.sudo_5Board_4cost.sudo_5Costs_9tally_max =
      ((2 * s.tally + 1 : Nat) : Int))
    (hprog :
      (do
          let b ← (do
              let b ← Ecbs.park_rung b (r : Int)
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
          let b ← Ecbs.tally_double b
          let b ← Ecbs.cube b ((6 : Nat) : Int) ((5 : Nat) : Int)
          let b ← Ecbs.mul b ((5 : Nat) : Int) (base.xHome : Int) ((6 : Nat) : Int)
              false false false
          Ecbs.tally_add_one b) = .ok b') :
    ClimbInvK (done ++ [r]) rs b'
      (modelRung s base.x r (climbAt base.ladder0 base.R s.ridx) false) base := by
  let hole := climbAt base.ladder0 base.R s.ridx
  obtain ⟨hgap, htall, honM, _hwork, hctrlM, hhighM, hrowM, hfromM, hridxM, ht0M,
      hparkM, hnM, hkM, hbM⟩ :=
    model_open_red_ge s base.x r hole hr hge
  let s' := modelRung s base.x r hole false
  have hlenRow : s'.row.length = s.row.length := by
    rw [hrowM, List.length_set, paintOnes_length, paintOnes_length, paintRed_length,
      afterPark_length]
  have hidx : s.ridx < base.R := by
    rw [h.idx]
    have hk := h.kLe
    simp [List.length_append, List.length_cons] at hk
    omega
  have hStep := successor_hole base.ladder0 base.R s.ridx s.parkAt s.row.length
    h.shape.park.l0pos hidx hParkAt h.shape.park.holeLt
  have hempty : rs.isEmpty = false := by
    cases rs with
    | nil => exact absurd rfl hrest
    | cons _ _ => rfl
  have hrowRung : s'.row =
      rungRow s.row s.fromHole s.parkAt hole s.t0 s.tally 2 false := by
    rw [hrowM, hr]
    simp [rungRow, afterTally]
  have hgeLen : 2 ≤ (r :: rs).length := by
    cases rs with
    | nil => exact absurd rfl hrest
    | cons _ _ => simp
  have hPast : s.t0 + 2 * s.tally < s.row.length := by
    have hgt := red_final_gt s.tally r rs hr hrest
    have hwhole : climbTally s.tally (r :: rs) =
        climbTally base.tally0 (done ++ (r :: rs)) := by
      rw [h.htally0]
      exact climbTally_prefix_rest base.tally0 done (r :: rs)
    have hfit := h.tailFit
    rw [← hwhole] at hfit
    omega
  have hPastC : s.t0 + 2 * s.tally < base.control := by
    rw [← h.shape.rowLen]
    exact hPast
  have hdone2 : done.length + 2 ≤ base.R := by
    have hk := h.kLe
    simp [h.idx, List.length_append, List.length_cons] at hk
    cases rs with
    | nil => exact absurd rfl hrest
    | cons _ _ =>
      simp at hk
      omega
  have hfits := open_red_ctrl_fit_ge s.ctrl s.tally base.ctrl0 done.length base.R
    base.mMax h.ctrlLe hT hdone2 base.fitCtrl
  have hspan3 : 3 * (s.n - 1) < s.benchlen := by
    have hs := h.shape.peg.span
    omega
  have hnleB : s.n ≤ s.benchlen := by
    have hs := h.shape.peg.span
    omega
  have hseg : RowSeg s'.row s'.t0 s'.tally false := by
    have hsegR := rungRow_open_red_seg s.row s.fromHole s.parkAt hole s.t0 s.tally
      h.shape.seg h.parkBelow h.holeBelow (Or.inr (h.fromBelow hge)) hPast
    rw [hrowRung, ht0M, htall]
    exact hsegR
  have hpark' : ParkRead b' s' rs base := by
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
        rw [hladB, h.shape.park.ladder0B, ← Int.ofNat_eq_coe]
      have hN : b'.sudo_5Board_6nrungs = Int.ofNat base.R := by
        rw [hnrB, h.shape.park.nrungsB, ← Int.ofNat_eq_coe]
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
      have hhi : s.parkAt < s.t0 := h.parkBelow
      omega
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
      · rw [Int.toNat_ofNat, hlenRow]
        exact h.shape.park.holeLt
      · rw [Int.toNat_ofNat, ← h.shape.rowLen]
        exact h.shape.park.holeLt
      · rw [hhighM, Int.toNat_ofNat]
        have hhi : hole < s.t0 := h.holeBelow
        omega
      · rw [Int.toNat_ofNat, hridxM]
        exact hStep.2.2
    · intro _
      have hlt : s'.parkAt < s'.row.length := by
        have h0 : s.parkAt < s.row.length := h.shape.park.parkLt
        rw [← hparkM, ← hlenRow] at h0
        exact h0
      exact ⟨s'.row[s'.parkAt]'hlt, rfl⟩
    · intro r2 rss hrs
      have hlt0 : climbAt base.ladder0 base.R (s.ridx + 1) < s.row.length := hStep.1
      have ⟨hcol, hnz⟩ := h.shape.park.ladderTail 1 (by simp [hrs]) hlt0
      have hbelow : climbAt base.ladder0 base.R (s.ridx + 1) < s.t0 :=
        climb_below base.ladder0 base.R s.ridx 1 s.t0 h.shape.park.l0pos
          (by omega) h.holeBelow
      have hneP : s.parkAt ≠ climbAt base.ladder0 base.R (s.ridx + 1) :=
        (climbAt_ne_sum base.ladder0 base.R (s.ridx + 1) s.parkAt
          h.shape.park.l0pos (by omega) hParkAt).symm
      have hneH : hole ≠ climbAt base.ladder0 base.R (s.ridx + 1) := hStep.2.2
      have hneS : s.fromHole.toNat ≠ climbAt base.ladder0 base.R (s.ridx + 1) := by
        have hL : 0 < base.ladder0 := h.shape.park.l0pos
        have hi : s.ridx + 1 ≤ base.R := by
          rw [h.idx]
          omega
        have hltC : climbAt base.ladder0 base.R (s.ridx + 1) <
            climbAt base.ladder0 base.R s.ridx := by
          unfold climbAt
          omega
        have habove := h.srcAbove hge
        omega
      have hget := rungRow_red_below_ge s.row s.fromHole s.parkAt hole s.t0 s.tally
        (climbAt base.ladder0 base.R (s.ridx + 1)) hneP hneH
        (Or.inr hneS) hbelow hlt0
      have hrowR : s'.row = rungRow s.row s.fromHole s.parkAt hole s.t0 s.tally 2 false :=
        hrowRung
      have hhead : (r :: rs)[1]'(by simp [hrs]) = r2 := by simp [hrs]
      refine ⟨?_, ?_⟩
      · simpa [hrowR, hridxM, hhead] using hget.trans hcol
      · simpa [hhead] using hnz
    · intro k hk hlt
      have hoff : s.ridx + (1 + k) ≤ base.R := by
        rw [h.idx]
        have hlenK := h.kLe
        simp [List.length_append, List.length_cons] at hlenK
        omega
      have hlt0 : climbAt base.ladder0 base.R (s.ridx + 1 + k) < s.row.length := by
        rw [← hlenRow, ← hridxM]
        exact hlt
      have ⟨hcol, hnz⟩ := h.shape.park.ladderTail (1 + k) (by simp; omega)
        (by simpa [Nat.add_assoc] using hlt0)
      have hbelow : climbAt base.ladder0 base.R (s.ridx + 1 + k) < s.t0 := by
        simpa [Nat.add_assoc] using
          climb_below base.ladder0 base.R s.ridx (1 + k) s.t0 h.shape.park.l0pos hoff
            h.holeBelow
      have hneP : s.parkAt ≠ climbAt base.ladder0 base.R (s.ridx + 1 + k) :=
        (climbAt_ne_sum base.ladder0 base.R (s.ridx + 1 + k) s.parkAt
          h.shape.park.l0pos (by omega) hParkAt).symm
      have hneH : hole ≠ climbAt base.ladder0 base.R (s.ridx + 1 + k) := by
        intro heq
        have hL : 0 < base.ladder0 := h.shape.park.l0pos
        simp [hole, climbAt] at heq
        omega
      have hneS : s.fromHole.toNat ≠ climbAt base.ladder0 base.R (s.ridx + 1 + k) := by
        have hL : 0 < base.ladder0 := h.shape.park.l0pos
        have hi : s.ridx + 1 + k ≤ base.R := by
          simpa [Nat.add_assoc] using hoff
        have hltC : climbAt base.ladder0 base.R (s.ridx + 1 + k) <
            climbAt base.ladder0 base.R s.ridx := by
          unfold climbAt
          omega
        have habove := h.srcAbove hge
        omega
      have hclimb : climbAt base.ladder0 base.R (s.ridx + 1 + k) =
          climbAt base.ladder0 base.R (s.ridx + (1 + k)) := by
        simp [Nat.add_assoc]
      have hcol' :=
        (getElem_congr (c := s.row)
          (i := climbAt base.ladder0 base.R (s.ridx + 1 + k))
          (j := climbAt base.ladder0 base.R (s.ridx + (1 + k)))
          (h := hlt0) hclimb).trans hcol
      have hget := rungRow_red_below_ge s.row s.fromHole s.parkAt hole s.t0 s.tally
        (climbAt base.ladder0 base.R (s.ridx + 1 + k)) hneP hneH
        (Or.inr hneS) hbelow hlt0
      have hrowR : s'.row = rungRow s.row s.fromHole s.parkAt hole s.t0 s.tally 2 false :=
        hrowRung
      have hixEq : climbAt base.ladder0 base.R (s'.ridx + k) =
          climbAt base.ladder0 base.R (s.ridx + 1 + k) := by rw [hridxM]
      have hmoveG := getElem_congr (c := s'.row)
        (i := climbAt base.ladder0 base.R (s'.ridx + k))
        (j := climbAt base.ladder0 base.R (s.ridx + 1 + k))
        (h := hlt) hixEq
      have hcoll := getElem_congr_coll (c := s'.row)
        (d := rungRow s.row s.fromHole s.parkAt hole s.t0 s.tally 2 false)
        (i := climbAt base.ladder0 base.R (s.ridx + 1 + k))
        (h := by rw [← hixEq]; exact hlt) hrowR
      have hlist := open_cons_tail r rs k hk
      refine ⟨?_, ?_⟩
      · exact hmoveG.trans (hcoll.trans ((hget.trans hcol').trans hlist))
      · exact fun hz => hnz ((open_cons_tail r rs k hk).trans hz)
    · rw [hctrlM]
      exact hfits.2.1
    · rw [hctrlM]
      exact hfits.2.2.1
    · have hfitR : FitsLen (base.R + 1) := by
        have hmul : base.R + 1 ≤ (base.R + 1) * (3 * base.mMax + 5) := by
          apply Nat.le_mul_of_pos_right
          omega
        exact FitsLen.of_le base.fitCtrl (by omega)
      have hle : s'.ridx + 1 ≤ base.R + 1 := by
        rw [hridxM, h.idx]
        omega
      exact FitsLen.of_le hfitR hle
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
        n_pos := by rw [hnM]; exact h.shape.peg.n_pos
        span := by rw [hnM, hbM]; exact h.shape.peg.span
        small := by rw [hbM]; exact h.shape.peg.small
        n_small := by rw [hnM]; exact h.shape.peg.n_small
        fitN := by rw [hnM]; exact h.shape.peg.fitN
        fitBn := by rw [hbM]; exact h.shape.peg.fitBn
        fit3 := h.shape.peg.fit3 }
    · have hi : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
        rw [← hδ'.opsSize]
        exact hopsB
      obtain ⟨_, c', _, hc', _⟩ := hcarry.delta.ops 1 hi
      refine ⟨c', ?_⟩
      exact (arr_get hopsF 1 hopsB).trans hc'
    · obtain ⟨p, hp⟩ := hcarry.strict
      exact ⟨p, hstrictF.trans hp⟩
    · obtain ⟨hn0, hh⟩ := hcarry.hole
      exact ⟨hn0, hholeF.trans hh⟩
    · rw [hgap]
      have htri := fieldMul_trits s.n s.k s.benchlen base.x
        (fieldCube s.n s.k s.benchlen
          (fieldMul s.n s.k s.benchlen s.gap
            (cubeTimes s.n s.k s.benchlen s.gap s.tally))) hspan3 hnleB
      simpa [fieldCube, List.take_take] using htri
    · intro hpos
      rw [ht0M, htall, hhighM]
      omega
    · rw [ht0M, htall]
      exact FitsLen.of_le base.fitControl (by omega)
    · rw [htall]
      exact (double_index_fit hPastC base.fitControl).2.2
    · rw [hctrlM, htall]
      exact hfits.2.2.2
  have hshape : ClimbShape b' s' rs base :=
    shape_refresh h.shape b' s' rs hnM hkM hbM
      (by
        rw [hgap, hnM]
        exact fieldMul_len s.n s.k s.benchlen base.x
          (fieldCube s.n s.k s.benchlen
            (fieldMul s.n s.k s.benchlen s.gap
              (cubeTimes s.n s.k s.benchlen s.gap s.tally))) hnleB)
      (by simpa [hempty] using hseg)
      (by rw [hheldB]; exact hcarry.held6)
      (by rw [hhomeB]; exact hcarry.home6)
      (by
        have h6 : 6 < b'.sudo_5Board_4held.size := by
          rw [hheldB]
          exact hcarry.held6
        exact cell_eq_of hheldB hcarry.empty6)
      (by rw [hheldB]; exact hcarry.held7)
      (by
        intro _
        exact cell_eq_of hheldB hcarry.empty5)
      (by
        intro hOff
        rw [honM] at hOff
        cases hOff)
      (by rw [hheldB]; exact hcarry.keep.heldLt)
      (by rw [hhomeB]; exact hcarry.keep.homeLt)
      (by exact cell_eq_of hheldB hcarry.keep.held)
      (by exact cell_eq_of hhomeB hcarry.keep.arr)
      (by rw [htierB, hnM]; exact h.shape.tierN)
      (by rw [htierB, hkM]; exact h.shape.tierK)
      (by rw [htierB, hbM]; exact h.shape.tierB)
      (by rw [htierB]; exact h.shape.tierW)
      (by rw [htierB]; exact h.shape.tierH)
      (by rw [htierB]; exact h.shape.tierR)
      (by rw [htierB]; exact h.shape.tierCg)
      (by rw [htierB]; exact h.shape.tierC)
      (by rw [hlenRow]; exact h.shape.rowLen)
      hpark' hpeg'
  have htmaxS : ∃ tmax : Nat,
      b'.sudo_5Board_4cost.sudo_5Costs_9tally_max = (tmax : Int) ∧
        (0 < s'.tally → tmax < 2 * s'.tally) := by
    refine ⟨2 * s.tally + 1, ?_, ?_⟩
    · simpa [Int.ofNat_eq_coe] using htmaxEq
    · intro hpos
      rw [htall]
      omega
  have hK := climbInvK_succ h (by simpa [hempty] using hinv) hδ' hCap
    (by simpa [hempty] using hshape) h.holeBelow (by simpa [hempty] using htmaxS) rfl
  simpa [hempty] using hK

theorem red_open_ge
    {done rs : List Nat} {r : Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvK done (r :: rs) b s base)
    (hge : 0 ≤ s.fromHole) (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax)
    (hhome : s.onBench = false) (hr : r = 2) (hrest : rs ≠ [])
    (hParkAt : s.parkAt = base.ladder0 + base.R)
    (hCap : climbTallyPrefix base.tally0 done (r :: rs) ≤ base.mMax)
    (hxLen : base.x.length = base.n) (hxT : allTritList base.x) :
    ∃ b',
      (do
          let b ← (do
              let b ← Ecbs.park_rung b (r : Int)
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
          let b ← Ecbs.tally_double b
          let b ← Ecbs.cube b ((6 : Nat) : Int) ((5 : Nat) : Int)
          let b ← Ecbs.mul b ((5 : Nat) : Int) (base.xHome : Int) ((6 : Nat) : Int)
              false false false
          Ecbs.tally_add_one b) = .ok b' ∧
      ClimbInvK (done ++ [r]) rs b'
        (modelRung s base.x r (climbAt base.ladder0 base.R s.ridx) false) base := by
  let hole := climbAt base.ladder0 base.R s.ridx
  let c0 := s.ctrl + 2 + s.tally
  let xs := paintRed (afterPark s.row (-1) s.parkAt hole 2) s.t0 s.tally
  let xsP := paintRed (afterPark s.row s.fromHole s.parkAt hole r) s.t0 s.tally
  let fromH := ((hole : Nat) : Int)
  let ridxH := Int.ofNat (s.ridx + 1)
  let rowIn := embed (paintOnes (paintOnes xs s.t0 s.tally) (s.t0 + s.tally) s.tally)
  let rowOut := embed (paintOnes (paintOnes xsP s.t0 s.tally) (s.t0 + s.tally) s.tally)
  let lenD := Int.ofNat (2 * s.tally)
  let ctrlIn := Int.ofNat (c0 + 2 * s.tally)
  let highD := ((s.t0 + 2 * s.tally - 1 : Nat) : Int)
  let maxD := Int.ofNat (2 * s.tally)
  let ctrlOut := Int.ofNat (c0 + 2 + 2 * s.tally)
  obtain ⟨bClearU, bCubeP, bRedP, hclearProg, _hcubeF, _hmulF, hcubeU, hredU, hrelP,
      _honP, _htoP, _hlenP, _hbenchP, _hhighP, _htmaxP, bLoopP, bMulP, hmulP, hclearP,
      hpackP⟩ :=
    parked_clear_unparked h hge hm hT hhome hxLen hxT
  obtain ⟨cP, _ysP, _mvPk, _slPk, _hoPk, _pkPk, _psPk, _opsPk, _hHP, _hDP, _hopsP,
      hloopP, hrowP0, hctrlP0, hgP, hmP, hnP, hkP, hbP, hsrcP, ht0P, _hnamedP,
      _hysP, _hmvP, _hslP, _hhoP, _hpkP, _hpsP, hcopyP⟩ := hpackP
  obtain ⟨bClearG, bIdle, hrun, hframe, hbenchE, hbonE, htoE, hmarkE, hlenE, ht0E,
      hparkE, hhighE, htierE, hladE, hnrE, htmaxE, h5H, h5D, h6H, h6D, h7E, h5f, h6f,
      hkeep, ⟨ps, hps⟩, ⟨hnat, hhn⟩, hrowIdle, hctrlIdle, hδ, hslots, hpieceM, hpieceS⟩ :=
    parked_clear_ge h hge hm hT hhome
  obtain ⟨bLoopC, bMulC, bClearC, bCubeC, bRedC, hmulC, hclearC, hcubeC, hredC,
      _bounds, _lenC, _t0C, _rowC, hctrlN, _highC, _ctrlC, _maxC, _t0Cu, ht0Red,
      _tierCu, htierRed, _fCube, _fMul, honC, htoC, _lenRed, hbenchC, _clearF, _cubeF,
      _mulF, hcubeBoth, hmulBoth, hpackC, _hrelC, _highRed, _tmaxRed⟩ :=
    red_cube_mul h hm hT hhome hxLen hxT
  obtain ⟨cC, _ysC, _mvC, _slC, _hoC, _pkC, _psC, _opsC, _hHC, _hDC, _hopsC,
      hloopC, hrowC0, hctrlC0, hgC, hmC, hnC, hkC, hbC, hsrcC, ht0C0, _hnamedC,
      _hysC, _hmvC, _hslC, _hhoC, _hpkC, _hpsC, hcopyC⟩ := hpackC
  have hclearSame : bClearC = bClearU :=
    unparked_clear_eq hcopyC hcopyP hloopC hloopP hsrcC hsrcP hgC hgP hnC hnP
      hkC hkP hbC hbP hrowC0 hrowP0 ht0C0 ht0P hctrlC0 hctrlP0 hmC hmP
      hmulC hmulP hclearC hclearP
  have hcubeSame : bCubeC = bCubeP := by
    have hrunC : Ecbs.cube bClearU ((6 : Nat) : Int) ((5 : Nat) : Int) = .ok bCubeC := by
      rw [← hclearSame]
      exact hcubeC
    exact Except.ok.inj (hrunC.symm.trans hcubeU)
  have hredSame : bRedC = bRedP := by
    have hrunR : Ecbs.mul bCubeP ((5 : Nat) : Int) (base.xHome : Int) ((6 : Nat) : Int)
        false false false = .ok bRedC := by
      rw [← hcubeSame]
      exact hredC
    exact Except.ok.inj (hrunR.symm.trans hredU)
  have hcoe : Int.ofNat (s.ctrl + 4 + s.tally) =
      ((s.ctrl + 4 + s.tally : Nat) : Int) := by
    simp only [Int.ofNat_eq_coe]
  have hctr : ((c0 + 2 : Nat) : Int) = ((s.ctrl + 4 + s.tally : Nat) : Int) := by
    unfold c0
    exact congrArg (fun n : Nat => (n : Int)) (by omega)
  have hpayload : withPark bClearU (embed xsP) (Int.ofNat (s.ctrl + 4 + s.tally))
      fromH ridxH = bClearG := by
    have hjoin := hclearProg.symm.trans hrun
    injection hjoin
  have hmatch : withPark bClearU (embed xsP) (((c0 + 2 : Nat) : Int)) fromH ridxH =
      withPark bIdle (embed xsP) (((c0 + 2 : Nat) : Int)) fromH ridxH := by
    rw [hctr, ← hcoe, hpayload, hframe, hcoe]
  have hbase : withPark bIdle (embed xsP) (((c0 + 2 : Nat) : Int)) fromH ridxH =
      withPark bClearC (embed xsP) (((c0 + 2 : Nat) : Int)) fromH ridxH := by
    rw [← hmatch, hclearSame]
  have hmove : withPark bIdle rowOut ctrlOut fromH ridxH =
      withPark bClearC rowOut ctrlOut fromH ridxH :=
    withPark_transfer hbase
  have hgeLen : 2 ≤ (r :: rs).length := by
    cases rs with
    | nil => exact absurd rfl hrest
    | cons _ _ => simp
  have hRoom : s.t0 + 2 * s.tally ≤ base.control := h.openRoom hgeLen
  have hHighEq : s.high = s.t0 + s.tally - 1 := h.highTop hm
  obtain ⟨tmax0, hMax0, hNote0⟩ := h.tmaxLt
  have hNote : tmax0 < 2 * s.tally := hNote0 hm
  have hdone2 : done.length + 2 ≤ base.R := by
    have hk := h.kLe
    simp [h.idx, List.length_append, List.length_cons] at hk
    cases rs with
    | nil => exact absurd rfl hrest
    | cons _ _ =>
      simp at hk
      omega
  have hfits := open_red_ctrl_fit_ge s.ctrl s.tally base.ctrl0 done.length base.R
    base.mMax h.ctrlLe hT hdone2 base.fitCtrl
  have hwhole : climbTally s.tally (r :: rs) =
      climbTally base.tally0 (done ++ (r :: rs)) := by
    rw [h.htally0]
    exact climbTally_prefix_rest base.tally0 done (r :: rs)
  have hPast : s.t0 + 2 * s.tally < s.row.length := by
    have hgt := red_final_gt s.tally r rs hr hrest
    have hfit := h.tailFit
    rw [← hwhole] at hfit
    omega
  have hPastC : s.t0 + 2 * s.tally < base.control := by
    rw [← h.shape.rowLen]
    exact hPast
  have hRowLen : s.t0 + 2 * s.tally ≤ s.row.length := Nat.le_of_lt hPast
  have hrowI : bIdle.sudo_5Board_3row = embed xs := by
    rw [hrowIdle, hr]
  have hRedIdle : ∀ j (hj : j < s.tally),
      xs[s.t0 + j]'(by
        simp [xs, paintRed_length, afterPark_length]
        exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj s.t0) h.shape.seg.room) = 2 := by
    intro j hj
    simpa [xs] using paintRed_get_lo (afterPark s.row (-1) s.parkAt hole 2) s.t0 s.tally j hj
      (by rw [afterPark_length]; exact h.shape.seg.room)
  have hRedPark : ∀ j (hj : j < s.tally),
      xsP[s.t0 + j]'(by
        simp [xsP, paintRed_length, afterPark_length]
        exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj s.t0) h.shape.seg.room) = 2 := by
    intro j hj
    simpa [xsP] using
      paintRed_get_lo (afterPark s.row s.fromHole s.parkAt hole r) s.t0 s.tally j hj
        (by rw [afterPark_length]; exact h.shape.seg.room)
  have hZeroIdle : ∀ k (hk : k < s.tally),
      xs[s.t0 + s.tally + k]'(by
        simp [xs, paintRed_length, afterPark_length]
        exact Nat.lt_of_lt_of_le (by omega) hRowLen) = 0 := by
    intro k hk
    have hjLen : s.t0 + s.tally + k < s.row.length := by
      exact Nat.lt_of_lt_of_le (by omega) hRowLen
    have hsrc := h.openZero hgeLen k hk (by simpa [Nat.add_assoc] using hjLen)
    have hAp := afterPark_get s.row (-1) s.parkAt hole 2 (s.t0 + s.tally + k)
      (Nat.lt_of_lt_of_le h.parkBelow (by omega))
      (Nat.lt_of_lt_of_le h.holeBelow (by omega))
      (Or.inl (by decide : (-1 : Int) < 0)) hjLen
    have hget := paintRed_get_hi (afterPark s.row (-1) s.parkAt hole 2) s.t0 s.tally
      (s.t0 + s.tally + k) (by omega) (by rw [afterPark_length]; exact hjLen)
    simpa [xs] using hget.trans (hAp.trans hsrc)
  have hZeroPark : ∀ k (hk : k < s.tally),
      xsP[s.t0 + s.tally + k]'(by
        simp [xsP, paintRed_length, afterPark_length]
        exact Nat.lt_of_lt_of_le (by omega) hRowLen) = 0 := by
    intro k hk
    have hjLen : s.t0 + s.tally + k < s.row.length := by
      exact Nat.lt_of_lt_of_le (by omega) hRowLen
    have hsrc := h.openZero hgeLen k hk (by simpa [Nat.add_assoc] using hjLen)
    have hAp := afterPark_get s.row s.fromHole s.parkAt hole r (s.t0 + s.tally + k)
      (Nat.lt_of_lt_of_le h.parkBelow (by omega))
      (Nat.lt_of_lt_of_le h.holeBelow (by omega))
      (Or.inr (Nat.lt_of_lt_of_le (h.fromBelow hge) (by omega))) hjLen
    have hget := paintRed_get_hi (afterPark s.row s.fromHole s.parkAt hole r) s.t0 s.tally
      (s.t0 + s.tally + k) (by omega) (by rw [afterPark_length]; exact hjLen)
    simpa [xsP] using hget.trans (hAp.trans hsrc)
  have hctrlB : bIdle.sudo_5Board_1t.sudo_4Tier_7control = (base.control : Int) := by
    rw [htierE, h.shape.tierC]
  have htallD := tally_double_withPark bIdle xs xsP s.t0 s.tally c0
    (s.t0 + s.tally - 1) base.control tmax0 fromH ridxH
    hm hlenE ht0E hrowI
    (by simp [xs, paintRed_length, afterPark_length]; exact hRowLen)
    (by simp [xsP, paintRed_length, afterPark_length]; exact hRowLen)
    hRedIdle hRedPark hZeroIdle hZeroPark hctrlB
    (by rw [hhighE, hHighEq]) rfl hctrlIdle hRoom
    (double_index_fit_le hRoom base.fitControl).1
    (FitsLen.of_le hfits.1 (by omega))
    (FitsLen.of_le hfits.2.1 (by omega))
    (double_index_fit_le hRoom base.fitControl).2.1
    (htmaxE.trans hMax0) hNote
  have htallRun : Ecbs.tally_double
      (withPark bIdle (embed xsP) (((c0 + 2 : Nat) : Int)) fromH ridxH) =
      .ok (withPark (withTally bIdle rowIn lenD ctrlIn highD maxD)
        rowOut ctrlOut fromH ridxH) := by
    simpa [rowIn, rowOut, lenD, ctrlIn, highD, maxD, ctrlOut, withTally] using htallD
  have hInEq : withPark (withTally bIdle rowIn lenD ctrlIn highD maxD) rowOut ctrlOut fromH ridxH =
      withPark (withTally bClearC rowIn lenD ctrlIn highD maxD) rowOut ctrlOut fromH ridxH := by
    rw [withPark_withTally, withPark_withTally, hmove]
  have hcubeRun := hcubeBoth rowIn rowOut lenD highD maxD ctrlIn ctrlOut fromH ridxH
  rw [← hInEq] at hcubeRun
  have hmulRun := hmulBoth rowIn rowOut lenD highD maxD ctrlIn ctrlOut fromH ridxH
  let bTall := withTally bRedC rowIn lenD ctrlIn highD maxD
  have hmulBoard : withPark (withTally bRedC rowIn lenD ctrlIn highD maxD)
      rowOut ctrlOut fromH ridxH = withPark bTall rowOut ctrlOut fromH ridxH := rfl
  have hixTall : s.t0 + 2 * s.tally < bTall.sudo_5Board_3row.size := by
    unfold bTall rowIn
    rw [withTally_row, size_embed, paintOnes_length, paintOnes_length,
      paintRed_length, afterPark_length]
    exact hPast
  have hixOut : s.t0 + 2 * s.tally < rowOut.size := by
    unfold rowOut
    rw [size_embed, paintOnes_length, paintOnes_length, paintRed_length, afterPark_length]
    exact hPast
  have hzeroTall : bTall.sudo_5Board_3row[s.t0 + 2 * s.tally] = 0 := by
    have hlist := open_red_peg_zero s.row (-1) s.parkAt hole s.t0 s.tally
      h.parkBelow h.holeBelow (Or.inl (by decide : (-1 : Int) < 0)) hPast
      (h.tailZero (2 * s.tally) (by omega) (by
        have hgt := red_final_gt s.tally r rs hr hrest
        rw [← hwhole]
        exact hgt) hPast)
    have hrow : bTall.sudo_5Board_3row = rowIn := by
      unfold bTall
      exact withTally_row bRedC rowIn lenD ctrlIn highD maxD
    refine (arr_get hrow (s.t0 + 2 * s.tally) hixTall).trans ?_
    unfold rowIn
    simpa [embed, Array.getElem_mk, Int.ofNat_eq_coe] using
      congrArg (fun n : Nat => (n : Int)) hlist
  have hzeroOut : rowOut[s.t0 + 2 * s.tally] = 0 := by
    have hlist := open_red_peg_zero s.row s.fromHole s.parkAt hole s.t0 s.tally
      h.parkBelow h.holeBelow (Or.inr (h.fromBelow hge)) hPast
      (h.tailZero (2 * s.tally) (by omega) (by
        have hgt := red_final_gt s.tally r rs hr hrest
        rw [← hwhole]
        exact hgt) hPast)
    simpa [rowOut, xsP, hr, embed, Array.getElem_mk, Int.ofNat_eq_coe] using
      congrArg (fun n : Nat => (n : Int)) hlist
  have hctrlTall : bTall.sudo_5Board_4cost.sudo_5Costs_4ctrl =
      ((c0 + 2 * s.tally : Nat) : Int) := by
    unfold bTall ctrlIn
    rw [withTally_ctrl]
    simp only [Int.ofNat_eq_coe]
  have hframeAdd : ctrlOut = (((c0 + 2 * s.tally) + 2 : Nat) : Int) := by
    simp only [ctrlOut, Int.ofNat_eq_coe]
    exact congrArg (fun n : Nat => (n : Int)) (by omega)
  have hadd := tally_add_one_withPark bTall s.t0 (2 * s.tally)
    (s.t0 + 2 * s.tally - 1) base.control (c0 + 2 * s.tally) (2 * s.tally)
    rowOut fromH ridxH
    (by
      unfold bTall lenD
      rw [withTally_len]
      simp only [Int.ofNat_eq_coe])
    (by
      have ht : bTall.sudo_5Board_6tally0 = bRedC.sudo_5Board_6tally0 := by
        unfold bTall withTally
        rfl
      rw [ht, ht0Red])
    hixTall hixOut hzeroTall hzeroOut
    (by unfold bTall; rw [ withTally_tier, htierRed, hctrlN])
    hPastC
    (by
      unfold bTall highD
      rw [withTally_high])
    (by omega)
    (double_index_fit hPastC base.fitControl).1
    hctrlTall
    (FitsLen.of_le hfits.1 (by omega))
    (by
      have hEq : (c0 + 2 * s.tally) + 2 + 1 = s.ctrl + 4 + 3 * s.tally + 1 := by
        unfold c0
        omega
      simpa [hEq] using hfits.1)
    (double_index_fit hPastC base.fitControl).2.2
    (by
      unfold bTall maxD
      rw [withTally_max]
      simp only [Int.ofNat_eq_coe])
    (by omega)
  rw [← hframeAdd] at hadd
  let bRec :=
    { bTall with
        sudo_5Board_3row := bTall.sudo_5Board_3row.set ⟨s.t0 + 2 * s.tally, hixTall⟩ (1 : Int)
        sudo_5Board_9tally_len := Int.ofNat (2 * s.tally + 1)
        sudo_5Board_4cost := { bTall.sudo_5Board_4cost with
          sudo_5Costs_15control_highest := ((s.t0 + 2 * s.tally : Nat) : Int)
          sudo_5Costs_4ctrl := Int.ofNat (c0 + 2 * s.tally + 1)
          sudo_5Costs_9tally_max := Int.ofNat (2 * s.tally + 1) } }
  let rowF := rowOut.set ⟨s.t0 + 2 * s.tally, hixOut⟩ (1 : Int)
  let ctrlF := Int.ofNat ((c0 + 2 * s.tally) + 2 + 1)
  let b' := withPark bRec rowF ctrlF fromH ridxH
  have haddBoard : Ecbs.tally_add_one (withPark bTall rowOut ctrlOut fromH ridxH) = .ok b' := by
    simpa [b', bRec, rowF, ctrlF] using hadd
  have hprog :
      (do
          let b ← (do
              let b ← Ecbs.park_rung b (r : Int)
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
          let b ← Ecbs.tally_double b
          let b ← Ecbs.cube b ((6 : Nat) : Int) ((5 : Nat) : Int)
          let b ← Ecbs.mul b ((5 : Nat) : Int) (base.xHome : Int) ((6 : Nat) : Int)
              false false false
          Ecbs.tally_add_one b) = .ok b' := by
    have hcastFrame : withPark bClearU (embed xsP) (Int.ofNat (s.ctrl + 4 + s.tally))
        fromH ridxH =
        withPark bClearU (embed xsP) (((c0 + 2 : Nat) : Int)) fromH ridxH := by
      rw [hcoe, ← hctr]
    rw [hclearProg, ok_bind, hcastFrame, hmatch, htallRun, ok_bind, hcubeRun, ok_bind,
      hmulRun, ok_bind, hmulBoard, haddBoard]
  let rowP := embed xsP
  let ctrlP := Int.ofNat (s.ctrl + 4 + s.tally)
  let bClearP := withPark bClearU rowP ctrlP fromH ridxH
  have hP : bClearP = bClearG := hpayload
  have hδP : RungDelta b bClearP base s.tally := by
    simpa [hP] using hδ
  have hslotsP : ClearSlots b.sudo_5Board_4cost.sudo_5Costs_3ops
      bClearP.sudo_5Board_4cost.sudo_5Costs_3ops s.tally := by
    simpa [hP] using hslots
  have hmarkP : bClearP.sudo_5Board_9marker_on = false := by
    rw [hP, hframe, withPark_marker]
    exact hmarkE
  have htierP : bClearP.sudo_5Board_1t = b.sudo_5Board_1t := by
    rw [hP, hframe, withPark_tier]
    exact htierE
  have hbonP : bClearP.sudo_5Board_8bench_on = true := by
    rw [hP, hframe, withPark_on]
    exact hbonE
  have htoP : bClearP.sudo_5Board_8bench_to = (5 : Int) := by
    rw [hP, hframe, withPark_to]
    exact htoE
  have hbenchP : bClearP.sudo_5Board_5bench =
      embed (fieldMul s.n s.k s.benchlen s.gap
        (cubeTimes s.n s.k s.benchlen s.gap s.tally) ++
        List.replicate (s.benchlen - s.n) 0) := by
    rw [hP, hframe, withPark_bench]
    exact hbenchE
  have h5HP : 5 < bClearP.sudo_5Board_4home.size := by
    rw [hP, hframe, withPark_home]
    exact h5H
  have h5DP : 5 < bClearP.sudo_5Board_4held.size := by
    rw [hP, hframe, withPark_held]
    exact h5D
  have h6HP : 6 < bClearP.sudo_5Board_4home.size := by
    rw [hP, hframe, withPark_home]
    exact h6H
  have h6DP : 6 < bClearP.sudo_5Board_4held.size := by
    rw [hP, hframe, withPark_held]
    exact h6D
  have h7P : 7 ≤ bClearP.sudo_5Board_4held.size := by
    rw [hP, hframe, withPark_held]
    exact h7E
  have h5fP : ∀ h5 : 5 < bClearP.sudo_5Board_4held.size,
      bClearP.sudo_5Board_4held[5]'h5 = false := by
    intro h5
    have hheld : bClearP.sudo_5Board_4held = bIdle.sudo_5Board_4held := by
      rw [hP, hframe, withPark_held]
    have h5I : 5 < bIdle.sudo_5Board_4held.size := by
      rw [← congrArg Array.size hheld]
      exact h5
    exact (arr_get hheld 5 h5).trans (h5f h5I)
  have h6fP : ∀ h6 : 6 < bClearP.sudo_5Board_4held.size,
      bClearP.sudo_5Board_4held[6]'h6 = false := by
    intro h6
    have hheld : bClearP.sudo_5Board_4held = bIdle.sudo_5Board_4held := by
      rw [hP, hframe, withPark_held]
    have h6I : 6 < bIdle.sudo_5Board_4held.size := by
      rw [← congrArg Array.size hheld]
      exact h6
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
    rw [hP, hframe, withPark_strict]
    exact hps
  have hholeP : ∃ holeN : Nat,
      bClearP.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = (holeN : Int) := by
    refine ⟨hnat, ?_⟩
    rw [hP, hframe, withPark_hole]
    exact hhn
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
  have hcarry :=
    red_unparked_delta h hm hT hhome hxLen hxT
      bClearP bClearU bCubeP bRedP rowP ctrlP fromH ridxH rfl
      hδP hslotsP hmarkP htierP hcubeU hredU hrelP
      hbonP htoP hbenchP h5HP h5DP h6HP h6DP h7P h5fP h6fP hkeepP hopsP hc1P
      hpkP hholeP htrits hpieceMP hpieceSP
  obtain ⟨hgap, htall, honM, hwork, hctrlM, hhighM, hrowM, hfromM, hridxM, ht0M,
      hparkM, hnM, hkM, hbM⟩ := model_open_red_ge s base.x r hole hr hge
  let s' := modelRung s base.x r hole false
  have hmvF : b'.sudo_5Board_4cost.sudo_5Costs_5moves =
      bRedP.sudo_5Board_4cost.sudo_5Costs_5moves := by
    unfold b' bRec bTall withTally withPark
    simp [hredSame]
  have hslF : b'.sudo_5Board_4cost.sudo_5Costs_6slides =
      bRedP.sudo_5Board_4cost.sudo_5Costs_6slides := by
    unfold b' bRec bTall withTally withPark
    simp [hredSame]
  have hopsF : b'.sudo_5Board_4cost.sudo_5Costs_3ops =
      bRedP.sudo_5Board_4cost.sudo_5Costs_3ops := by
    unfold b' bRec bTall withTally withPark
    simp [hredSame]
  have hpkF : b'.sudo_5Board_4cost.sudo_5Costs_4peak =
      bRedP.sudo_5Board_4cost.sudo_5Costs_4peak := by
    unfold b' bRec bTall withTally withPark
    simp [hredSame]
  have hδ' : RungDelta b b' base s.tally :=
    rungDelta_cost hcarry.delta hmvF hslF hopsF hpkF
  have hhomeB : b'.sudo_5Board_4home = bRedP.sudo_5Board_4home := by
    unfold b' bRec bTall withTally withPark
    simp [hredSame]
  have hheldB : b'.sudo_5Board_4held = bRedP.sudo_5Board_4held := by
    unfold b' bRec bTall withTally withPark
    simp [hredSame]
  have hladRec : bRec.sudo_5Board_7ladder0 = bRedC.sudo_5Board_7ladder0 := by
    unfold bRec bTall withTally
    rfl
  have hnrRec : bRec.sudo_5Board_6nrungs = bRedC.sudo_5Board_6nrungs := by
    unfold bRec bTall withTally
    rfl
  have htierRec : bRec.sudo_5Board_1t = bRedC.sudo_5Board_1t := by
    unfold bRec bTall withTally
    rfl
  have hladB : b'.sudo_5Board_7ladder0 = b.sudo_5Board_7ladder0 := by
    unfold b'
    rw [withPark_ladder, hladRec, hredSame, hcarry.ladder, hP, hframe, withPark_ladder, hladE]
  have hnrB : b'.sudo_5Board_6nrungs = b.sudo_5Board_6nrungs := by
    unfold b'
    rw [withPark_nrungs, hnrRec, hredSame, hcarry.nrungs, hP, hframe, withPark_nrungs, hnrE]
  have htierB : b'.sudo_5Board_1t = b.sudo_5Board_1t := by
    unfold b'
    rw [withPark_tier, htierRec, hredSame, hcarry.tier, htierP]
  have hlenRow : s'.row.length = s.row.length := by
    rw [hrowM, List.length_set, paintOnes_length, paintOnes_length, paintRed_length,
      afterPark_length]
  have hidx : s.ridx < base.R := by
    rw [h.idx]
    have hk := h.kLe
    simp [List.length_append, List.length_cons] at hk
    omega
  have hStep := successor_hole base.ladder0 base.R s.ridx s.parkAt s.row.length
    h.shape.park.l0pos hidx hParkAt h.shape.park.holeLt
  have hempty : rs.isEmpty = false := by
    cases rs with
    | nil => exact absurd rfl hrest
    | cons _ _ => rfl
  have hrowF : rowF = embed s'.row := by
    have hone : (1 : Int) = ((1 : Nat) : Int) := by
      simpa using (Int.ofNat_eq_coe (1 : Nat))
    unfold rowF
    rw [hone]
    have hset : rowOut.set ⟨s.t0 + 2 * s.tally, hixOut⟩ ((1 : Nat) : Int) =
        embed ((paintOnes (paintOnes xsP s.t0 s.tally) (s.t0 + s.tally) s.tally).set
          (s.t0 + 2 * s.tally) 1) := by
      unfold rowOut
      apply Array.ext
      · simp [embed, size_embed, List.length_set]
      · intro i hi hi'
        simp [embed, Array.getElem_set, List.getElem_set, ofNat_eq_natCast]
    rw [hset, hrowM]
  have hctrlF : ctrlF = (s'.ctrl : Int) := by
    rw [hctrlM]
    simp only [ctrlF, c0, Int.ofNat_eq_coe]
    exact congrArg (fun n : Nat => (n : Int)) (by omega)
  have hfromF : fromH = s'.fromHole := by rw [hfromM]
  have hridxF : ridxH = (s'.ridx : Int) := by
    rw [hridxM]
    simp only [ridxH, Int.ofNat_eq_coe]
  have hinv0 :=
    climbInv_atPark bRec s' rowF ctrlF fromH ridxH
      (by
        rw [show bRec.sudo_5Board_4home = bRedC.sudo_5Board_4home by simp [bRec, bTall, withTally],
          hredSame]
        exact Nat.lt_trans (by decide : (5 : Nat) < 6) hcarry.home6)
      (by
        rw [show bRec.sudo_5Board_4held = bRedC.sudo_5Board_4held by simp [bRec, bTall, withTally],
          hredSame]
        exact Nat.lt_trans (by decide : (5 : Nat) < 6) hcarry.held6)
      (by
        rw [show bRec.sudo_5Board_9marker_on = bRedC.sudo_5Board_9marker_on by
          simp [bRec, bTall, withTally], hredSame]
        exact hcarry.marker)
      (by
        rw [show bRec.sudo_5Board_9tally_len = Int.ofNat (2 * s.tally + 1) by simp [bRec], htall]
        simp only [Int.ofNat_eq_coe])
      (by
        rw [show bRec.sudo_5Board_4cost.sudo_5Costs_15control_highest =
          ((s.t0 + 2 * s.tally : Nat) : Int) by simp [bRec], hhighM])
      (by
        rw [show bRec.sudo_5Board_6tally0 = bRedC.sudo_5Board_6tally0 by simp [bRec, bTall, withTally],
          ht0Red, ht0M])
      (by
        rw [show bRec.sudo_5Board_9park_hole = bRedC.sudo_5Board_9park_hole by
          simp [bRec, bTall, withTally], hredSame, hcarry.park, hP, hframe, withPark_park,
          hparkE, hparkM])
      hrowF hctrlF hfromF hridxF
      (by
        intro hOff
        rw [honM] at hOff
        cases hOff)
      (by
        intro _
        have hnle : s.n ≤ s.benchlen := hnleB
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
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [show bRec.sudo_5Board_8bench_on = bRedC.sudo_5Board_8bench_on by
            simp [bRec, bTall, withTally], honC]
        · rw [show bRec.sudo_5Board_8bench_to = bRedC.sudo_5Board_8bench_to by
            simp [bRec, bTall, withTally], htoC]
        · rw [show bRec.sudo_5Board_5bench = bRedC.sudo_5Board_5bench by
            simp [bRec, bTall, withTally], hbenchC, hgap,
            show s'.n = s.n from rfl, show s'.benchlen = s.benchlen from rfl, htake]
        · rw [hwork, hgap])
  have hinv : ClimbInv b' s' := by
    simpa [b', hrowF, hctrlF, hfromF, hridxF] using hinv0
  have hrowRung : s'.row =
      rungRow s.row s.fromHole s.parkAt hole s.t0 s.tally 2 false := by
    rw [hrowM, hr]
    simp [rungRow, afterTally]
  have hseg : RowSeg s'.row s'.t0 s'.tally false := by
    have hsegR := rungRow_open_red_seg s.row s.fromHole s.parkAt hole s.t0 s.tally
      h.shape.seg h.parkBelow h.holeBelow (Or.inr (h.fromBelow hge)) hPast
    rw [hrowRung, ht0M, htall]
    exact hsegR
  have hopsB : 1 < b'.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [hopsF, hcarry.delta.opsSize, ← hδP.opsSize]
    exact hopsP
  have hstrictRec : bRec.sudo_5Board_4cost.sudo_5Costs_11peak_strict =
      bRedC.sudo_5Board_4cost.sudo_5Costs_11peak_strict := by
    unfold bRec bTall withTally
    rfl
  have hstrictF : b'.sudo_5Board_4cost.sudo_5Costs_11peak_strict =
      bRedP.sudo_5Board_4cost.sudo_5Costs_11peak_strict := by
    unfold b'
    rw [withPark_strict, hstrictRec, hredSame]
  have hholeRec : bRec.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      bRedC.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole := by
    unfold bRec bTall withTally
    rfl
  have hholeF : b'.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      bRedP.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole := by
    unfold b'
    rw [withPark_hole, hholeRec, hredSame]
  have htmaxEq : b'.sudo_5Board_4cost.sudo_5Costs_9tally_max =
      ((2 * s.tally + 1 : Nat) : Int) := by
    unfold b' bRec
    rw [withPark_tmax]
    simp only [Int.ofNat_eq_coe]
  exact ⟨b', hprog, red_open_finish h hge hr hrest hParkAt hCap hT hinv hδ' hladB hnrB
    htierB hhomeB hheldB hcarry hopsB hopsF hstrictF hholeF htmaxEq hprog⟩

end EcbsLink2.Link2
