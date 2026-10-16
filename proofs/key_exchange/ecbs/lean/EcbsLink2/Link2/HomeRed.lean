/-
  Idle red successors. The clear is the park-through-clear of an idle rung.
  A non-final rung then doubles, cubes the spare into the gap, multiplies by
  the input, and lays one peg. A final rung cubes and multiplies and stops.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.InvertStep

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- The parked clear, the unparked red cube and mul, and the cost projections.
    `red_cube_mul` is obtained once here. The row proof and the successor read
    this bundle, so they do not elaborate that theorem again. -/
theorem red_open_view
    {done rest : List Nat} {r : Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvKCore done (r :: rest) b s base)
    (hM : MoveHeadroom b base.n base.bench base.mMax)
    (hS : SlideHeadroom b base.n base.mMax)
    (hF : s.fromHole < 0) (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax)
    (hhome : s.onBench = false)
    (hxLen : base.x.length = base.n) (hxT : allTritList base.x) :
    ∃ (bClearP bClearU bCube bRed : Ecbs.Board),
      (do
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
          Ecbs.clear b (5 : Int)) = .ok bClearP ∧
      bClearP = withPark bClearU
        (embed (paintRed (afterPark s.row (-1) s.parkAt
          (climbAt base.ladder0 base.R s.ridx) r) s.t0 s.tally))
        (((s.ctrl + 2 + s.tally : Nat) : Int))
        (((climbAt base.ladder0 base.R s.ridx : Nat) : Int))
        (Int.ofNat (s.ridx + 1)) ∧
      bClearU.sudo_5Board_9tally_len = (s.tally : Int) ∧
      bClearU.sudo_5Board_6tally0 = (s.t0 : Int) ∧
      bClearU.sudo_5Board_3row = embed (paintRed s.row s.t0 s.tally) ∧
      bClearU.sudo_5Board_1t.sudo_4Tier_7control = (base.control : Int) ∧
      bClearU.sudo_5Board_4cost.sudo_5Costs_15control_highest = (s.high : Int) ∧
      bClearU.sudo_5Board_4cost.sudo_5Costs_4ctrl = ((s.ctrl + s.tally : Nat) : Int) ∧
      bClearU.sudo_5Board_4cost.sudo_5Costs_9tally_max =
        b.sudo_5Board_4cost.sudo_5Costs_9tally_max ∧
      bRed.sudo_5Board_6tally0 = (s.t0 : Int) ∧
      bRed.sudo_5Board_1t = bClearU.sudo_5Board_1t ∧
      (∀ (rowD rowP : Array Int) (len high tmax : Int) (ctrlD ctrlP fromHole ridx : Int),
        Ecbs.cube (withPark (withTally bClearU rowD len ctrlD high tmax) rowP ctrlP fromHole ridx)
            ((6 : Nat) : Int) ((5 : Nat) : Int) =
          .ok (withPark (withTally bCube rowD len ctrlD high tmax) rowP ctrlP fromHole ridx)) ∧
      (∀ (rowD rowP : Array Int) (len high tmax : Int) (ctrlD ctrlP fromHole ridx : Int),
        Ecbs.mul (withPark (withTally bCube rowD len ctrlD high tmax) rowP ctrlP fromHole ridx)
            ((5 : Nat) : Int) (base.xHome : Int) ((6 : Nat) : Int)
            false false false =
          .ok (withPark (withTally bRed rowD len ctrlD high tmax) rowP ctrlP fromHole ridx)) ∧
      (∃ (mvE mvR slE slR : Nat),
        b.sudo_5Board_4cost.sudo_5Costs_5moves = (mvE : Int) ∧
        bRed.sudo_5Board_4cost.sudo_5Costs_5moves = (mvR : Int) ∧
        mvR + 2 * base.n ≤ mvE + rungCharge base.n base.bench s.tally ∧
        b.sudo_5Board_4cost.sudo_5Costs_6slides = (slE : Int) ∧
        bRed.sudo_5Board_4cost.sudo_5Costs_6slides = (slR : Int) ∧
        slR + 2 * base.n ≤ slE + rungSlideCharge base.n s.tally) ∧
      bRed.sudo_5Board_8bench_on = true ∧
      bRed.sudo_5Board_8bench_to = (5 : Int) ∧
      bRed.sudo_5Board_9tally_len = (s.tally : Int) ∧
      bRed.sudo_5Board_5bench =
        embed (fieldMul s.n s.k s.benchlen base.x
          (fieldCube s.n s.k s.benchlen
            (fieldMul s.n s.k s.benchlen s.gap
              (cubeTimes s.n s.k s.benchlen s.gap s.tally))) ++
          List.replicate (s.benchlen - s.n) 0) ∧
      RungDelta b bClearP base s.tally ∧
      ClearSlots b.sudo_5Board_4cost.sudo_5Costs_3ops
        bClearP.sudo_5Board_4cost.sudo_5Costs_3ops s.tally ∧
      bClearP.sudo_5Board_7ladder0 = b.sudo_5Board_7ladder0 ∧
      bClearP.sudo_5Board_6nrungs = b.sudo_5Board_6nrungs ∧
      bClearP.sudo_5Board_9park_hole = (s.parkAt : Int) ∧
      bClearP.sudo_5Board_6tally0 = (s.t0 : Int) ∧
      bClearP.sudo_5Board_9marker_on = false ∧
      bClearP.sudo_5Board_1t = b.sudo_5Board_1t ∧
      bClearP.sudo_5Board_4cost.sudo_5Costs_9tally_max =
        b.sudo_5Board_4cost.sudo_5Costs_9tally_max ∧
      Ecbs.cube bClearU ((6 : Nat) : Int) ((5 : Nat) : Int) = .ok bCube ∧
      Ecbs.mul bCube ((5 : Nat) : Int) (base.xHome : Int) ((6 : Nat) : Int)
          false false false = .ok bRed ∧
      bClearP.sudo_5Board_8bench_on = true ∧
      bClearP.sudo_5Board_8bench_to = (5 : Int) ∧
      bClearP.sudo_5Board_5bench =
        embed (fieldMul s.n s.k s.benchlen s.gap
          (cubeTimes s.n s.k s.benchlen s.gap s.tally) ++
          List.replicate (s.benchlen - s.n) 0) ∧
      5 < bClearP.sudo_5Board_4home.size ∧
      5 < bClearP.sudo_5Board_4held.size ∧
      6 < bClearP.sudo_5Board_4home.size ∧
      6 < bClearP.sudo_5Board_4held.size ∧
      7 ≤ bClearP.sudo_5Board_4held.size ∧
      (∀ h5 : 5 < bClearP.sudo_5Board_4held.size,
        bClearP.sudo_5Board_4held[5]'h5 = false) ∧
      (∀ h6 : 6 < bClearP.sudo_5Board_4held.size,
        bClearP.sudo_5Board_4held[6]'h6 = false) ∧
      CellKeep bClearP base.xHome base.x ∧
      1 < bClearP.sudo_5Board_4cost.sudo_5Costs_3ops.size ∧
      (∃ c1 : Nat, ∀ (h1 : 1 < bClearP.sudo_5Board_4cost.sudo_5Costs_3ops.size),
        bClearP.sudo_5Board_4cost.sudo_5Costs_3ops[1]'h1 = (c1 : Int)) ∧
      (∃ p : Nat, bClearP.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (p : Int)) ∧
      (∃ holeN : Nat,
        bClearP.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = (holeN : Int)) ∧
      allTritList (fieldMul s.n s.k s.benchlen s.gap
        (cubeTimes s.n s.k s.benchlen s.gap s.tally)) ∧
      (∃ mv mvC : Nat,
        b.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int) ∧
        bClearP.sudo_5Board_4cost.sudo_5Costs_5moves = (mvC : Int) ∧
        mvC + 2 * base.n ≤ mv + base.n + s.tally * pegCharge base.n base.bench +
          mulCharge base.n base.bench + base.n) ∧
      (∃ sl slC : Nat,
        b.sudo_5Board_4cost.sudo_5Costs_6slides = (sl : Int) ∧
        bClearP.sudo_5Board_4cost.sudo_5Costs_6slides = (slC : Int) ∧
        slC ≤ sl + s.tally * (2 * base.n)) ∧
      SideKeep bClearP base ∧
      QuietKeep bClearP base := by

  let hole := climbAt base.ladder0 base.R s.ridx
  obtain ⟨bClearP, hAll⟩ := gap_clear_emit h hM hS hF hm hT hhome h.parkBelow h.holeBelow
  rcases hAll with ⟨hrun, _hrowE, _hctrlE, _hfromE, _hridxE, _hlenE, ht0E, hparkE,
      _hhighE, hmarkE, hbonE, htoE, hbenchE, htierE, hladE, hnrE, htmaxE,
      h5H, h5D, h6H, h6D, h7E, h5f, h6f, hkeep, htrits, hopsE, hc1E, hpkSE,
      hholeE, hδs, hctx, hside, hquiet⟩
  obtain ⟨hδ, hslots, hpieceM, hpieceS⟩ := hδs
  obtain ⟨cG, bMulG, hclearG, hmulG, hrowG, hctrlG, hmG, ht0G, hgG, hnG, hkG, hbG, hsrcG,
      ⟨bParkG, hparkG, hcopyG⟩⟩ := hctx
  obtain ⟨bLoopU, bMulU0, bClearU, bCube0, bRed0, hmulU, _hclearU, hcubeU, hredU,
      _hbounds, hlenC, ht0C, hrowC, hctrlN, hhighC, hctrlC, hmaxC,
      _ht0Cube, ht0Red, _htierCube, htierRed, _hcubeF, _hmulF,
      honR, htoR, hlenR, hbenchR, hclearP, _hcubeP, _hmulP,
      hcubeBoth, hmulBoth, hpack, hrel, _hhighR, _htmaxR⟩ :=
    red_cube_mul h hM hS hm hT hhome hxLen hxT
  obtain ⟨cU, _ysU, _mvU, _slU, _hoU, _pkU, _psU, _cOpsU, _hHU, _hDU, _hopsU,
      hloopU, hrowU, hctrlU, hgU, hmU, hnU, hkU, hbU, hsrcU, ht0U, _hnamed,
      _hys, _hmv, _hsl, _hho, _hpk, _hps, hcopyU⟩ := hpack
  obtain ⟨bMulU, bMulD, ⟨cP, bLoopP, hmulP, hloopP, hcopyP, hrowP, hctrlP, hgP,
      hmP, hnP, hkP, hbP, hsrcP, ht0P⟩, ⟨cD, hmulD, hrowD, hctrlD, hmD, ht0D, hgD,
      hnD, hkD, hbD, hsrcD, ⟨bParkD, hparkD, hcopyD⟩⟩, hrelP⟩ :=
    parked_gap_is_withPark h hM hS hF hm hT hhome
  have hb0U : cP.b0 = cU.b0 := by injection hcopyP.symm.trans hcopyU
  have hboardsU := pegBoard_same_copy cP cU hb0U
    (hsrcU.trans hsrcP.symm) (hgU.trans hgP.symm) (hnU.trans hnP.symm)
    (hkU.trans hkP.symm) (hbU.trans hbP.symm) (hrowU.trans hrowP.symm)
    (ht0U.trans ht0P.symm) (hctrlU.trans hctrlP.symm) (hmU.trans hmP.symm)
  have hloopsU : bLoopU = bLoopP := by
    rw [hloopU, hloopP, hboardsU]
  have hmulSame : bMulU0 = bMulU := by
    rw [hloopsU] at hmulU
    injection hmulU.symm.trans hmulP
  have hparkMul : bMulD = withPark bMulU0
      (embed (paintRed (afterPark s.row (-1) s.parkAt hole r) s.t0 s.tally))
      (((s.ctrl + 2 + s.tally : Nat) : Int))
      ((hole : Nat) : Int) (Int.ofNat (s.ridx + 1)) := by
    simpa [hmulSame, hole] using hrelP
  have hbPark : bParkG = bParkD := by injection hparkG.symm.trans hparkD
  have hb0D : cG.b0 = cD.b0 := by
    have hcg := hcopyG
    rw [hbPark] at hcg
    injection hcg.symm.trans hcopyD
  have hboardsD := pegBoard_same_copy cG cD hb0D
    (hsrcD.trans hsrcG.symm) (hgD.trans hgG.symm) (hnD.trans hnG.symm)
    (hkD.trans hkG.symm) (hbD.trans hbG.symm) (hrowD.trans hrowG.symm)
    (ht0D.trans ht0G.symm) (hctrlD.trans hctrlG.symm) (hmD.trans hmG.symm)
  have hmulGD : bMulG = bMulD := by
    rw [← hboardsD] at hmulG
    injection hmulG.symm.trans hmulD
  let rowRed := embed (paintRed (afterPark s.row (-1) s.parkAt hole r) s.t0 s.tally)
  let ctrlRed := ((s.ctrl + 2 + s.tally : Nat) : Int)
  let fromH := ((hole : Nat) : Int)
  let ridxH := Int.ofNat (s.ridx + 1)
  have hclearW := hclearP rowRed ctrlRed fromH ridxH
  rw [← hparkMul, ← hmulGD] at hclearW
  have hClearEq : bClearP = withPark bClearU rowRed ctrlRed fromH ridxH := by
    injection hclearG.symm.trans hclearW
  exact ⟨bClearP, bClearU, bCube0, bRed0, hrun, hClearEq, hlenC, ht0C, hrowC, hctrlN,
    hhighC, hctrlC, hmaxC, ht0Red, htierRed, hcubeBoth, hmulBoth, hrel, honR, htoR,
    hlenR, hbenchR, hδ, hslots, hladE, hnrE, hparkE, ht0E, hmarkE, htierE, htmaxE,
    hcubeU, hredU, hbonE, htoE, hbenchE, h5H, h5D, h6H, h6D, h7E, h5f, h6f, hkeep,
    hopsE, hc1E, hpkSE, hholeE, htrits, hpieceM, hpieceS, hside, hquiet⟩

theorem settle_park (b : Ecbs.Board) (home : Nat)
    (hin : HomeIn b home)
    (xs : List Nat) (n moves slides peak : Nat) :
    (settleBoard b home hin.hH hin.hD xs n moves slides peak).sudo_5Board_9park_hole =
      b.sudo_5Board_9park_hole ∧
    (settleBoard b home hin.hH hin.hD xs n moves slides peak).sudo_5Board_7ladder0 =
      b.sudo_5Board_7ladder0 ∧
    (settleBoard b home hin.hH hin.hD xs n moves slides peak).sudo_5Board_6nrungs =
      b.sudo_5Board_6nrungs ∧
    (settleBoard b home hin.hH hin.hD xs n moves slides peak).sudo_5Board_6tally0 =
      b.sudo_5Board_6tally0 ∧
    (settleBoard b home hin.hH hin.hD xs n moves slides peak).sudo_5Board_1t =
      b.sudo_5Board_1t := by
  unfold settleBoard
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem cube_live_park (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (bud : Budget b 1)
    (hin : HomeIn b src) :
    (cubeLiveBoard b dst src xs bud hin).sudo_5Board_9park_hole =
      b.sudo_5Board_9park_hole ∧
    (cubeLiveBoard b dst src xs bud hin).sudo_5Board_7ladder0 =
      b.sudo_5Board_7ladder0 ∧
    (cubeLiveBoard b dst src xs bud hin).sudo_5Board_6nrungs =
      b.sudo_5Board_6nrungs ∧
    (cubeLiveBoard b dst src xs bud hin).sudo_5Board_6tally0 =
      b.sudo_5Board_6tally0 ∧
    (cubeLiveBoard b dst src xs bud hin).sudo_5Board_9marker_on =
      false := by
  unfold cubeLiveBoard cubeOffBoard
  have hs := settle_park b src ⟨hin.hH, hin.hD⟩ xs bud.n bud.moves bud.slides bud.peak
  exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, rfl⟩

theorem mul_live_park (b : Ecbs.Board) (dst second : Nat) (xs ys : List Nat)
    (bud : Budget b 0)
    (hin : HomeIn b second) :
    (mulNoLiveBoard b dst second xs ys bud hin).sudo_5Board_9park_hole =
      b.sudo_5Board_9park_hole ∧
    (mulNoLiveBoard b dst second xs ys bud hin).sudo_5Board_7ladder0 =
      b.sudo_5Board_7ladder0 ∧
    (mulNoLiveBoard b dst second xs ys bud hin).sudo_5Board_6nrungs =
      b.sudo_5Board_6nrungs ∧
    (mulNoLiveBoard b dst second xs ys bud hin).sudo_5Board_6tally0 =
      b.sudo_5Board_6tally0 ∧
    (mulNoLiveBoard b dst second xs ys bud hin).sudo_5Board_9marker_on =
      false ∧
    (mulNoLiveBoard b dst second xs ys bud hin).sudo_5Board_1t =
      b.sudo_5Board_1t := by
  unfold mulNoLiveBoard mulNoOffBoard
  have hs := settle_park b second ⟨hin.hH, hin.hD⟩ ys bud.n bud.moves bud.slides bud.peak
  exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, rfl, hs.2.2.2.2⟩

theorem clearSlots_cast {entry a b : Array Int} {tally : Nat}
    (hs : ClearSlots entry a tally) (h : a = b) : ClearSlots entry b tally := by
  cases h
  exact hs

/-- The tail of a bench padded with zeros is zero. -/
theorem pad_zero (xs : List Nat) (k i : Nat)
    (hn : xs.length ≤ i) (hi : i < (xs ++ List.replicate k 0).length) :
    (xs ++ List.replicate k 0)[i]'hi = 0 := by
  rw [List.getElem_append_right hn]
  simp [List.getElem_replicate]

/-- What the unparked spare cube and the mul by the input leave, read off the
    named live boards. Ops and peak are the `RungDelta`. Park, ladder, marker,
    tier, the spare, and the input cell are field projections. -/
structure RedCarry (b bRed bClear : Ecbs.Board) (base : ClimbBudget) (tally xHome : Nat)
    (x : List Nat) : Prop where
  delta : RungDelta b bRed base tally
  park : bRed.sudo_5Board_9park_hole = bClear.sudo_5Board_9park_hole
  ladder : bRed.sudo_5Board_7ladder0 = bClear.sudo_5Board_7ladder0
  nrungs : bRed.sudo_5Board_6nrungs = bClear.sudo_5Board_6nrungs
  tally0 : bRed.sudo_5Board_6tally0 = bClear.sudo_5Board_6tally0
  marker : bRed.sudo_5Board_9marker_on = false
  tier : bRed.sudo_5Board_1t = bClear.sudo_5Board_1t
  home6 : 6 < bRed.sudo_5Board_4home.size
  held6 : 6 < bRed.sudo_5Board_4held.size
  held7 : 7 ≤ bRed.sudo_5Board_4held.size
  empty5 : bRed.sudo_5Board_4held[5]'(Nat.lt_trans (by decide : (5 : Nat) < 6) held6) = false
  empty6 : bRed.sudo_5Board_4held[6]'held6 = false
  keep : CellKeep bRed xHome x
  side : SideKeep bRed base
  quiet : QuietKeep bRed base
  strict : ∃ p : Nat, bRed.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (p : Int)
  hole : ∃ h : Nat, bRed.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = (h : Int)
  opsTight : ∀ i (hi : i < b.sudo_5Board_4cost.sudo_5Costs_3ops.size),
    ∃ c c' : Nat,
      b.sudo_5Board_4cost.sudo_5Costs_3ops[i] = (c : Int) ∧
      bRed.sudo_5Board_4cost.sudo_5Costs_3ops[i]'(delta.opsSize ▸ hi) = (c' : Int) ∧
      c' ≤ c + (base.mMax + 2)

/-- Spare cube, then the mul by the input, on the unparked clear. The cube writes
    ops slot 1 only. The mul writes ops slot 0 only. Each peak stays at most
    `max(entry, 7)`. Live boards are named only for those projections. -/
theorem red_unparked_delta
    {done rest : List Nat} {r : Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvKCore done (r :: rest) b s base)
    (hM : MoveHeadroom b base.n base.bench base.mMax)
    (hS : SlideHeadroom b base.n base.mMax)
    (_hm : 0 < s.tally) (hT : s.tally ≤ base.mMax)
    (_hhome : s.onBench = false)
    (hxLen : base.x.length = base.n) (hxT : allTritList base.x)
    (bClearP bClearU bCube0 bRed0 : Ecbs.Board)
    (row : Array Int) (ctrl fromHole ridx : Int)
    (hClearEq : bClearP = withPark bClearU row ctrl fromHole ridx)
    (hδ : RungDelta b bClearP base s.tally)
    (hslots : ClearSlots b.sudo_5Board_4cost.sudo_5Costs_3ops
      bClearP.sudo_5Board_4cost.sudo_5Costs_3ops s.tally)
    (hmarkE : bClearP.sudo_5Board_9marker_on = false)
    (htierE : bClearP.sudo_5Board_1t = b.sudo_5Board_1t)
    (hcubeU : Ecbs.cube bClearU ((6 : Nat) : Int) ((5 : Nat) : Int) = .ok bCube0)
    (hredU : Ecbs.mul bCube0 ((5 : Nat) : Int) (base.xHome : Int) ((6 : Nat) : Int)
      false false false = .ok bRed0)
    (hrel : ∃ mvE mvR slE slR : Nat,
      b.sudo_5Board_4cost.sudo_5Costs_5moves = (mvE : Int) ∧
      bRed0.sudo_5Board_4cost.sudo_5Costs_5moves = (mvR : Int) ∧
      mvR + 2 * base.n ≤ mvE + rungCharge base.n base.bench s.tally ∧
      b.sudo_5Board_4cost.sudo_5Costs_6slides = (slE : Int) ∧
      bRed0.sudo_5Board_4cost.sudo_5Costs_6slides = (slR : Int) ∧
      slR + 2 * base.n ≤ slE + rungSlideCharge base.n s.tally)
    (hbonE : bClearP.sudo_5Board_8bench_on = true)
    (htoE : bClearP.sudo_5Board_8bench_to = (5 : Int))
    (hbenchE : bClearP.sudo_5Board_5bench =
      embed (fieldMul s.n s.k s.benchlen s.gap
        (cubeTimes s.n s.k s.benchlen s.gap s.tally) ++
        List.replicate (s.benchlen - s.n) 0))
    (h5H : 5 < bClearP.sudo_5Board_4home.size)
    (h5D : 5 < bClearP.sudo_5Board_4held.size)
    (h6H : 6 < bClearP.sudo_5Board_4home.size)
    (h6D : 6 < bClearP.sudo_5Board_4held.size)
    (h7E : 7 ≤ bClearP.sudo_5Board_4held.size)
    (h5f : ∀ h5 : 5 < bClearP.sudo_5Board_4held.size,
      bClearP.sudo_5Board_4held[5]'h5 = false)
    (h6f : ∀ h6 : 6 < bClearP.sudo_5Board_4held.size,
      bClearP.sudo_5Board_4held[6]'h6 = false)
    (hkeep : CellKeep bClearP base.xHome base.x)
    (hopsE : 1 < bClearP.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hc1E : ∃ c1 : Nat, ∀ h1 : 1 < bClearP.sudo_5Board_4cost.sudo_5Costs_3ops.size,
      bClearP.sudo_5Board_4cost.sudo_5Costs_3ops[1]'h1 = (c1 : Int))
    (hpkSE : ∃ p : Nat, bClearP.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (p : Int))
    (hholeE : ∃ holeN : Nat,
      bClearP.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = (holeN : Int))
    (htrits : allTritList (fieldMul s.n s.k s.benchlen s.gap
      (cubeTimes s.n s.k s.benchlen s.gap s.tally)))
    (hpieceM : ∃ mv mvC : Nat,
      b.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int) ∧
      bClearP.sudo_5Board_4cost.sudo_5Costs_5moves = (mvC : Int) ∧
      mvC + 2 * base.n ≤ mv + base.n + s.tally * pegCharge base.n base.bench +
        mulCharge base.n base.bench + base.n)
    (_hpieceS : ∃ sl slC : Nat,
      b.sudo_5Board_4cost.sudo_5Costs_6slides = (sl : Int) ∧
      bClearP.sudo_5Board_4cost.sudo_5Costs_6slides = (slC : Int) ∧
      slC ≤ sl + s.tally * (2 * base.n))
    (hsideC : SideKeep bClearP base)
    (hquietC : QuietKeep bClearP base) :
    RedCarry b bRed0 bClearP base s.tally base.xHome base.x := by
  have hmarkU : bClearU.sudo_5Board_9marker_on = false := by
    have hback : bClearU.sudo_5Board_9marker_on = bClearP.sudo_5Board_9marker_on := by
      rw [hClearEq]; rfl
    exact hback.trans hmarkE
  have honU : bClearU.sudo_5Board_8bench_on = true := by
    have hback : bClearU.sudo_5Board_8bench_on = bClearP.sudo_5Board_8bench_on := by
      rw [hClearEq]; rfl
    exact hback.trans hbonE
  have htoU : bClearU.sudo_5Board_8bench_to = (5 : Int) := by
    have hback : bClearU.sudo_5Board_8bench_to = bClearP.sudo_5Board_8bench_to := by
      rw [hClearEq]; rfl
    exact hback.trans htoE
  let gap := fieldMul s.n s.k s.benchlen s.gap
    (cubeTimes s.n s.k s.benchlen s.gap s.tally)
  let xs := gap ++ List.replicate (s.benchlen - s.n) 0
  have hbenchU : bClearU.sudo_5Board_5bench = embed xs := by
    have hback : bClearU.sudo_5Board_5bench = bClearP.sudo_5Board_5bench := by
      rw [hClearEq]; rfl
    simpa [xs, gap] using hback.trans hbenchE
  have hhomeU : bClearU.sudo_5Board_4home = bClearP.sudo_5Board_4home := by
    rw [hClearEq]; rfl
  have hheldU : bClearU.sudo_5Board_4held = bClearP.sudo_5Board_4held := by
    rw [hClearEq]; rfl
  have h5HU : 5 < bClearU.sudo_5Board_4home.size := by rw [hhomeU]; exact h5H
  have h5DU : 5 < bClearU.sudo_5Board_4held.size := by rw [hheldU]; exact h5D
  have h7U : 7 ≤ bClearU.sudo_5Board_4held.size := by rw [hheldU]; exact h7E
  have hemptyU : bClearU.sudo_5Board_4held[5]'h5DU = false := by
    have hget := arr_get hheldU 5 h5DU
    exact hget.trans (h5f (hheldU ▸ h5DU))
  have htierU : bClearU.sudo_5Board_1t = b.sudo_5Board_1t := by
    have hback : bClearU.sudo_5Board_1t = bClearP.sudo_5Board_1t := by
      rw [hClearEq]; rfl
    exact hback.trans htierE
  have hnU : bClearU.sudo_5Board_1t.sudo_4Tier_1n = (s.n : Int) := by
    rw [htierU]; exact h.shape.tierN
  have hkU : bClearU.sudo_5Board_1t.sudo_4Tier_1k = (s.k : Int) := by
    rw [htierU]; exact h.shape.tierK
  have hblU : bClearU.sudo_5Board_1t.sudo_4Tier_8benchlen = (s.benchlen : Int) := by
    rw [htierU]; exact h.shape.tierB
  have hcgU : bClearU.sudo_5Board_1t.sudo_4Tier_7combgap = (base.cg : Int) := by
    rw [htierU]; exact h.shape.tierCg
  have hwU : bClearU.sudo_5Board_1t.sudo_4Tier_1w = (base.w : Int) := by
    rw [htierU]; exact h.shape.tierW
  have hhU : bClearU.sudo_5Board_1t.sudo_4Tier_1h = (base.h : Int) := by
    rw [htierU]; exact h.shape.tierH
  have hrU : bClearU.sudo_5Board_1t.sudo_4Tier_1r = (base.r : Int) := by
    rw [htierU]; exact h.shape.tierR
  have hopsU : bClearU.sudo_5Board_4cost.sudo_5Costs_3ops =
      bClearP.sudo_5Board_4cost.sudo_5Costs_3ops := by
    rw [hClearEq]; rfl
  have hops1U : 1 < bClearU.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [hopsU]; exact hopsE
  obtain ⟨c1, hc1⟩ := hc1E
  have hop1U : bClearU.sudo_5Board_4cost.sudo_5Costs_3ops[1]'hops1U = (c1 : Int) := by
    exact (arr_get hopsU 1 hops1U).trans (hc1 (hopsU ▸ hops1U))
  obtain ⟨pkS, hpkS⟩ := hpkSE
  have hstrictU : bClearU.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (pkS : Int) := by
    have hback : bClearU.sudo_5Board_4cost.sudo_5Costs_11peak_strict =
        bClearP.sudo_5Board_4cost.sudo_5Costs_11peak_strict := by
      rw [hClearEq]; rfl
    exact hback.trans hpkS
  obtain ⟨holeN, hholeN⟩ := hholeE
  have hholeU : bClearU.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = (holeN : Int) := by
    have hback : bClearU.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
        bClearP.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole := by
      rw [hClearEq]; rfl
    exact hback.trans hholeN
  obtain ⟨mv, mvC, hmv, hmvC, hpiece⟩ := hpieceM
  have hmovesU : bClearU.sudo_5Board_4cost.sudo_5Costs_5moves = (mvC : Int) := by
    have hback : bClearU.sudo_5Board_4cost.sudo_5Costs_5moves =
        bClearP.sudo_5Board_4cost.sudo_5Costs_5moves := by
      rw [hClearEq]; rfl
    exact hback.trans hmvC
  obtain ⟨sl, slC, hsl, hslC, hpieceS⟩ := _hpieceS
  have hslidesU : bClearU.sudo_5Board_4cost.sudo_5Costs_6slides = (slC : Int) := by
    have hback : bClearU.sudo_5Board_4cost.sudo_5Costs_6slides =
        bClearP.sudo_5Board_4cost.sudo_5Costs_6slides := by
      rw [hClearEq]; rfl
    exact hback.trans hslC
  obtain ⟨pk, pkC, hpk, hpkC, hpkLe⟩ := hδ.peak
  have hpeakU : bClearU.sudo_5Board_4cost.sudo_5Costs_4peak = (pkC : Int) := by
    have hback : bClearU.sudo_5Board_4cost.sudo_5Costs_4peak =
        bClearP.sudo_5Board_4cost.sudo_5Costs_4peak := by
      rw [hClearEq]; rfl
    exact hback.trans hpkC
  have hnleB : s.n ≤ s.benchlen := by
    have hsp := h.shape.peg.span
    omega
  have hlenG : gap.length = s.n :=
    fieldMul_len s.n s.k s.benchlen s.gap
      (cubeTimes s.n s.k s.benchlen s.gap s.tally) hnleB
  have hlenX : xs.length = s.benchlen := by
    simp [xs, hlenG, List.length_replicate, Nat.add_sub_of_le hnleB]
  have hposX : 0 < xs.length := by
    rw [hlenX]
    exact Nat.lt_of_lt_of_le h.shape.peg.n_pos hnleB
  have hnleX : s.n ≤ xs.length := by rw [hlenX]; exact hnleB
  have hzeroX : ∀ i, s.n ≤ i → ∀ hi : i < xs.length, xs[i] = 0 := by
    intro i hi hix
    have hlenI : gap.length ≤ i := by rw [hlenG]; exact hi
    simpa [xs] using pad_zero gap (s.benchlen - s.n) i hlenI hix
  have htake : xs.take s.n = gap := by
    have hle : s.n ≤ gap.length := Nat.le_of_eq hlenG.symm
    rw [show xs = gap ++ List.replicate (s.benchlen - s.n) 0 from rfl,
      List.take_append_of_le_length hle]
    exact List.take_of_length_le (Nat.le_of_eq hlenG)
  have htriX : allTritList (xs.take s.n) := by rw [htake]; exact htrits
  have hpegX : pegCount (xs.take s.n) ≤ s.n := by
    rw [htake]
    exact Nat.le_trans (pegCount_le gap) (Nat.le_of_eq hlenG)
  have hstepR : done.length + 1 ≤ base.R := by
    have hk := h.kLe
    simp [List.length_append, List.length_cons] at hk
    omega
  have hmvEq : mv = hM.mv := ofNat_inj_nat (hmv.symm.trans hM.eq)
  have hpieceN : mvC ≤ mv + base.n + s.tally * pegCharge base.n base.bench +
      mulCharge base.n base.bench + base.n :=
    Nat.le_trans (Nat.le_add_right mvC (2 * base.n)) hpiece
  have hpegN : pegCount (xs.take base.n) ≤ base.n := by
    rw [← h.hn]
    exact hpegX
  have hroomM : FitsLen (mv + (rungCharge base.n base.bench base.mMax - 2 * base.n)) := by
    rw [hmvEq]; exact hM.room
  have hfitM4 := clear_move_fit base.n base.bench s.tally base.mMax mv mvC
    (pegCount (xs.take base.n)) hT hroomM hpieceN hpegN
  have hslEq : sl = hS.sl := ofNat_inj_nat (hsl.symm.trans hS.eq)
  have hroomS : FitsLen (sl + (rungSlideCharge base.n base.mMax - 2 * base.n)) := by
    rw [hslEq]; exact hS.room
  have hpieceSloose : slC ≤ sl + s.tally * (2 * base.n) + 2 * base.n :=
    Nat.le_trans hpieceS (Nat.le_add_right _ (2 * base.n))
  have hfitS := clear_slide_fit base.n s.tally base.mMax sl slC
    (pegCount (xs.take base.n)) hT hroomS hpieceSloose hpegN
  have h1e : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size := hδ.opsSize ▸ hopsE
  obtain ⟨cE, cC, hcE, hcC, _h0s, h1s, _hrest⟩ := hslots.slots 1 h1e
  have hplus : cC = cE + s.tally := h1s rfl
  have hc1eq : c1 = cC := by
    apply ofNat_inj_nat
    have hget := arr_get hopsU 1 hops1U
    have hcP : bClearP.sudo_5Board_4cost.sudo_5Costs_3ops[1]'(hopsU ▸ hops1U) = (cC : Int) :=
      (array_get_irrel (h1 := hopsU ▸ hops1U) (h2 := hslots.size ▸ h1e)).trans hcC
    exact hop1U.symm.trans (hget.trans hcP)
  obtain ⟨cSlot, hcSlot, hcLe⟩ := h.ops 1 h1e
  have hcEeq : cE = cSlot := ofNat_inj_nat (hcE.symm.trans hcSlot)
  have hent : cE ≤ base.ops0 + done.length * (base.mMax + 3) := by
    rw [hcEeq]; exact hcLe
  have hfitO := clear_ops_fit base.ops0 base.R done.length base.mMax cE s.tally c1
    hT hstepR hent (by rw [hc1eq, hplus])
  have hlive := cube_eq_live bClearU 6 5 xs base.w base.h base.r s.n s.k mvC slC holeN s.benchlen pkC pkS c1 base.cg hmarkU honU htoU h5HU h5DU h7U hemptyU hbenchU hnU h.shape.peg.n_pos hposX hnleX hzeroX h.shape.peg.fitN (by rw [hlenX]; exact h.shape.peg.fitBn) hmovesU hslidesU hpeakU (by
      have h2 := hfitM4.1
      have hidx : xs.take base.n = xs.take s.n := by rw [h.hn]
      rw [hidx] at h2
      exact h2) (by
      have h2 := hfitM4.2.1
      have hidx : xs.take base.n = xs.take s.n := by rw [h.hn]
      rw [hidx] at h2
      exact h2) (by
      have h2 := hfitS
      have hidx : xs.take base.n = xs.take s.n := by rw [h.hn]
      rw [hidx] at h2
      exact h2) hops1U hop1U (FitsLen.of_le base.fitO hfitO) hblU hcgU h.shape.peg.span htriX h.shape.peg.fit3 (by
      have h2 := hfitM4.2.2.1
      have hidx : xs.take base.n = xs.take s.n := by rw [h.hn]
      have htwo : 2 * base.n = 2 * s.n := by rw [h.hn]
      rw [hidx, htwo] at h2
      exact h2) ⟨h.shape.w0, h.shape.h0, h.shape.rlt, h.shape.r0, h.shape.n_eq, h.shape.k_le, h.shape.gap_eq⟩ hwU hhU hrU hkU hholeU hstrictU h.shape.peg.small h.shape.peg.n_small h.shape.peg.fitBn (by
      have h2 := hfitM4.2.2.2
      have hidx : xs.take base.n = xs.take s.n := by rw [h.hn]
      have htwo : 2 * base.n = 2 * s.n := by rw [h.hn]
      have hsub : base.bench - base.n = s.benchlen - s.n := by rw [h.hn, h.hbench]
      rw [hidx, htwo, hsub] at h2
      exact h2)
  have hEq : bCube0 = cubeLiveBoard bClearU 6 5 xs ⟨s.n, s.k, mvC, slC, holeN, s.benchlen, pkC, pkS, c1, hops1U⟩ ⟨h5HU, h5DU⟩ := by
    injection hcubeU.symm.trans hlive
  have hOps := cube_live_ops bClearU 6 5 xs ⟨s.n, s.k, mvC, slC, holeN, s.benchlen, pkC, pkS, c1, hops1U⟩ ⟨h5HU, h5DU⟩
  have hOpsB : bCube0.sudo_5Board_4cost.sudo_5Costs_3ops =
      (cubeLiveBoard bClearU 6 5 xs ⟨s.n, s.k, mvC, slC, holeN, s.benchlen, pkC, pkS, c1, hops1U⟩ ⟨h5HU, h5DU⟩).sudo_5Board_4cost.sudo_5Costs_3ops :=
    congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_4cost.sudo_5Costs_3ops) hEq
  let occ1 := countHeld (bClearU.sudo_5Board_4held.set ⟨5, h5DU⟩ true) 7
  let bS := settleBoard bClearU 5 h5HU h5DU xs s.n mvC slC pkC
  let hFs := settle_held_lt bClearU 5 ⟨h5HU, h5DU⟩ xs s.n mvC slC pkC
  let occ2 := countHeld (bS.sudo_5Board_4held.set ⟨5, hFs⟩ false) 7
  let pkU := raisedPeak (raisedPeak pkC occ1) occ2
  have hpkLive := cube_live_peak bClearU 6 5 xs ⟨s.n, s.k, mvC, slC, holeN, s.benchlen, pkC, pkS, c1, hops1U⟩ ⟨h5HU, h5DU⟩
  have hpkB : bCube0.sudo_5Board_4cost.sudo_5Costs_4peak =
      (cubeLiveBoard bClearU 6 5 xs ⟨s.n, s.k, mvC, slC, holeN, s.benchlen, pkC, pkS, c1, hops1U⟩ ⟨h5HU, h5DU⟩).sudo_5Board_4cost.sudo_5Costs_4peak :=
    congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_4cost.sudo_5Costs_4peak) hEq
  have hpkU : bCube0.sudo_5Board_4cost.sudo_5Costs_4peak = (pkU : Int) := by
    have hraw := hpkB.trans hpkLive
    simpa [pkU, occ1, occ2, bS, hFs, ofNat_eq_natCast] using hraw
  have hpkUle : pkU ≤ max pk 7 :=
    raised_twice_le pk pkC occ1 occ2 hpkLe (countHeld_seven _) (countHeld_seven _)
  have h0e : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size :=
    Nat.lt_trans (by decide : (0 : Nat) < 1) h1e
  obtain ⟨cE0, cC0, hcE0, hcC0, h0s, _h1s0, _hrest0⟩ := hslots.slots 0 h0e
  have h0plus : cC0 = cE0 + 1 := h0s rfl
  have h0u : 0 < bClearU.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [hopsU]; exact Nat.lt_trans (by decide : (0 : Nat) < 1) hopsE
  have hc0U : bClearU.sudo_5Board_4cost.sudo_5Costs_3ops[0]'h0u = (cC0 : Int) := by
    have hget := arr_get hopsU 0 h0u
    have hcP : bClearP.sudo_5Board_4cost.sudo_5Costs_3ops[0]'(hopsU ▸ h0u) = (cC0 : Int) :=
      (array_get_irrel (h1 := hopsU ▸ h0u) (h2 := hslots.size ▸ h0e)).trans hcC0
    exact hget.trans hcP
  have h0cubeSz : 0 < bCube0.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    have hsz : bCube0.sudo_5Board_4cost.sudo_5Costs_3ops.size =
        bClearU.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
      rw [hEq]
      exact cube_live_ops_size bClearU 6 5 xs ⟨s.n, s.k, mvC, slC, holeN, s.benchlen, pkC, pkS, c1, hops1U⟩ ⟨h5HU, h5DU⟩
    exact hsz.symm ▸ h0u
  have hop0C : bCube0.sudo_5Board_4cost.sudo_5Costs_3ops[0]'h0cubeSz =
      bClearU.sudo_5Board_4cost.sudo_5Costs_3ops[0] :=
    cube_live_op0 bClearU bCube0 6 5 xs ⟨s.n, s.k, mvC, slC, holeN, s.benchlen, pkC, pkS, c1, hops1U⟩ ⟨h5HU, h5DU⟩ hEq h0cubeSz
  have hv0 : bCube0.sudo_5Board_4cost.sudo_5Costs_3ops[0]'h0cubeSz = (cC0 : Int) :=
    hop0C.trans hc0U
  let pegX := pegCount (xs.take s.n)
  let mvCube := cubeMoves (mvC + 2 * pegX) (xs.take s.n) s.n s.k s.benchlen
  let slCube := slC + 2 * pegX
  have hCubeLe : mvCube ≤ mvC + pegCharge base.n base.bench := by
    have hraw := cube_moves_delta mvC xs s.n s.k s.benchlen
    have hle : mvCube ≤ mvC + pegCharge s.n s.benchlen := by
      simpa [mvCube, pegX] using hraw
    rw [h.hn, h.hbench] at hle
    exact hle
  let ys := laneFold s.n (s.n - s.k) (combStrip s.n s.benchlen (xs.take s.n))
  have hlenY : ys.length = s.benchlen := by
    have hcomb : (combStrip s.n s.benchlen (xs.take s.n)).length = s.benchlen :=
      combStrip_length s.n s.benchlen (xs.take s.n)
    simpa [ys, hcomb] using
      laneFold_length s.n (s.n - s.k) (combStrip s.n s.benchlen (xs.take s.n))
        (by rw [hcomb]; exact hnleB)
  have hgapPos : 0 < s.n - s.k := by
    rw [h.shape.gap_eq]
    exact Nat.mul_pos h.shape.w0 h.shape.r0
  have hzeroY : ∀ i, s.n ≤ i → ∀ hi : i < ys.length, ys[i] = 0 := by
    intro i hi hix
    have hixB : i < s.benchlen := by rw [← hlenY]; exact hix
    have hcoeff := cube_live_high xs s.n s.k s.benchlen h.shape.peg.n_pos hgapPos i hi hixB
    exact (coeff_eq_get ys i hix).symm.trans hcoeff
  have hposY : 0 < ys.length := by
    rw [hlenY]
    exact Nat.lt_of_lt_of_le h.shape.peg.n_pos hnleB
  have hnleY : s.n ≤ ys.length := by rw [hlenY]; exact hnleB
  have htriStrip : allTritList (combStrip s.n s.benchlen (xs.take s.n)) :=
    combStrip_trits (xs.take s.n) s.n s.benchlen htriX (by
      have hsp := h.shape.peg.span
      exact Nat.lt_of_le_of_lt (Nat.le_add_right _ base.cg) hsp)
  have htriY : allTritList (ys.take s.n) := by
    have hfold := laneFold_trits s.n (s.n - s.k) (combStrip s.n s.benchlen (xs.take s.n))
      htriStrip (Nat.sub_le _ _) (by
        rw [combStrip_length]; exact hnleB)
    simpa [ys] using allTritList_take hfold s.n
  have hpegY : pegCount (ys.take s.n) ≤ s.n := by
    exact Nat.le_trans (pegCount_le (ys.take s.n)) (by
      rw [List.length_take]
      exact Nat.min_le_left _ _)
  have hmvCubeB : bCube0.sudo_5Board_4cost.sudo_5Costs_5moves = (mvCube : Int) := by
    have hB := congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_4cost.sudo_5Costs_5moves) hEq
    have hlive := cube_live_moves bClearU 6 5 xs ⟨s.n, s.k, mvC, slC, holeN, s.benchlen, pkC, pkS, c1, hops1U⟩ ⟨h5HU, h5DU⟩
    simpa [mvCube, pegX, ofNat_eq_natCast] using hB.trans hlive
  have hslCubeB : bCube0.sudo_5Board_4cost.sudo_5Costs_6slides = (slCube : Int) := by
    have hB := congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_4cost.sudo_5Costs_6slides) hEq
    have hlive := cube_live_slides bClearU 6 5 xs ⟨s.n, s.k, mvC, slC, holeN, s.benchlen, pkC, pkS, c1, hops1U⟩ ⟨h5HU, h5DU⟩
    simpa [slCube, pegX, ofNat_eq_natCast] using hB.trans hlive
  have hbenchC : bCube0.sudo_5Board_5bench = embed ys := by
    have hB := congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_5bench) hEq
    have hlive := cube_live_bench bClearU 6 5 xs ⟨s.n, s.k, mvC, slC, holeN, s.benchlen, pkC, pkS, c1, hops1U⟩ ⟨h5HU, h5DU⟩
    simpa [ys] using hB.trans hlive
  have hmkC : bCube0.sudo_5Board_9marker_on = false := by
    have hB := congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_9marker_on) hEq
    exact hB.trans (cube_live_marker bClearU 6 5 xs ⟨s.n, s.k, mvC, slC, holeN, s.benchlen, pkC, pkS, c1, hops1U⟩ ⟨h5HU, h5DU⟩)
  have honC : bCube0.sudo_5Board_8bench_on = true := by
    have hB := congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_8bench_on) hEq
    exact hB.trans (cube_live_on bClearU 6 5 xs ⟨s.n, s.k, mvC, slC, holeN, s.benchlen, pkC, pkS, c1, hops1U⟩ ⟨h5HU, h5DU⟩)
  have htoC : bCube0.sudo_5Board_8bench_to = (6 : Int) := by
    have hB := congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_8bench_to) hEq
    exact hB.trans (cube_live_to bClearU 6 5 xs ⟨s.n, s.k, mvC, slC, holeN, s.benchlen, pkC, pkS, c1, hops1U⟩ ⟨h5HU, h5DU⟩)
  have hheldSz : bCube0.sudo_5Board_4held.size = bClearU.sudo_5Board_4held.size := by
    have hB := congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_4held.size) hEq
    exact hB.trans (cube_live_held_size bClearU 6 5 xs ⟨s.n, s.k, mvC, slC, holeN, s.benchlen, pkC, pkS, c1, hops1U⟩ ⟨h5HU, h5DU⟩)
  have h6DU : 6 < bClearU.sudo_5Board_4held.size := by rw [hheldU]; exact h6D
  have h6fU : bClearU.sudo_5Board_4held[6]'h6DU = false :=
    (arr_get hheldU 6 h6DU).trans (h6f (hheldU ▸ h6DU))
  have h6DC : 6 < bCube0.sudo_5Board_4held.size := by rw [hheldSz]; exact h6DU
  have hempty6 : bCube0.sudo_5Board_4held[6]'h6DC = false :=
    (cube_live_held_other bClearU bCube0 6 5 6 xs ⟨s.n, s.k, mvC, slC, holeN, s.benchlen, pkC, pkS, c1, hops1U⟩ ⟨h5HU, h5DU⟩ hEq (by decide : (5 : Nat) ≠ 6) h6DU h6DC).trans h6fU
  have hhomeSz : bCube0.sudo_5Board_4home.size = bClearU.sudo_5Board_4home.size := by
    have hL := (congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_4home) hEq).trans
      (cube_live_home bClearU 6 5 xs ⟨s.n, s.k, mvC, slC, holeN, s.benchlen, pkC, pkS, c1, hops1U⟩ ⟨h5HU, h5DU⟩)
    have hs := congrArg Array.size hL
    rw [Array.size_set] at hs
    exact hs
  have h6HC : 6 < bCube0.sudo_5Board_4home.size := by
    rw [hhomeSz, hhomeU]; exact h6H
  let holeC := raisedHole holeN (topIdx (combStrip s.n s.benchlen (xs.take s.n)))
  have hholeC : bCube0.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = (holeC : Int) := by
    have hB := congrArg
      (fun bd : Ecbs.Board => bd.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole) hEq
    have hlive := cube_live_hole bClearU 6 5 xs ⟨s.n, s.k, mvC, slC, holeN, s.benchlen, pkC, pkS, c1, hops1U⟩ ⟨h5HU, h5DU⟩
    simpa [holeC, ofNat_eq_natCast] using hB.trans hlive
  let peakSC := raisedPeak pkS (countHeld bS.sudo_5Board_4held 7)
  have hstrictC : bCube0.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakSC : Int) := by
    have hB := congrArg
      (fun bd : Ecbs.Board => bd.sudo_5Board_4cost.sudo_5Costs_11peak_strict) hEq
    have hlive := cube_live_strict bClearU 6 5 xs ⟨s.n, s.k, mvC, slC, holeN, s.benchlen, pkC, pkS, c1, hops1U⟩ ⟨h5HU, h5DU⟩
    simpa [peakSC, bS, ofNat_eq_natCast] using hB.trans hlive
  have htierC : bCube0.sudo_5Board_1t = bClearU.sudo_5Board_1t := by
    have hB := congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_1t) hEq
    exact hB.trans (cubeLive_fixed bClearU 6 5 xs ⟨s.n, s.k, mvC, slC, holeN, s.benchlen, pkC, pkS, c1, hops1U⟩ ⟨h5HU, h5DU⟩).2.2.2
  have hxDU : base.xHome < bClearU.sudo_5Board_4held.size := by
    rw [hheldU]; exact hkeep.heldLt
  have hxHU : base.xHome < bClearU.sudo_5Board_4home.size := by
    rw [hhomeU]; exact hkeep.homeLt
  have hxHeldU : bClearU.sudo_5Board_4held[base.xHome]'hxDU = true :=
    (arr_get hheldU base.xHome hxDU).trans (by
      simpa using hkeep.held)
  have hxArrU : bClearU.sudo_5Board_4home[base.xHome]'hxHU = embed base.x :=
    (arr_get hhomeU base.xHome hxHU).trans (by
      simpa using hkeep.arr)
  have hxDC : base.xHome < bCube0.sudo_5Board_4held.size := by rw [hheldSz]; exact hxDU
  have hxHC : base.xHome < bCube0.sudo_5Board_4home.size := by rw [hhomeSz]; exact hxHU
  have hxHeldC : bCube0.sudo_5Board_4held[base.xHome]'hxDC = true :=
    (cube_live_held_other bClearU bCube0 6 5 base.xHome xs ⟨s.n, s.k, mvC, slC, holeN, s.benchlen, pkC, pkS, c1, hops1U⟩ ⟨h5HU, h5DU⟩ hEq (Ne.symm h.shape.xNe5) hxDU hxDC).trans hxHeldU
  have hxArrC : bCube0.sudo_5Board_4home[base.xHome]'hxHC = embed base.x := by
    have hL := (congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_4home) hEq).trans
      (cube_live_home bClearU 6 5 xs ⟨s.n, s.k, mvC, slC, holeN, s.benchlen, pkC, pkS, c1, hops1U⟩ ⟨h5HU, h5DU⟩)
    have hget := arr_get hL base.xHome hxHC
    rw [hget, Array.getElem_set_ne _ ⟨5, h5HU⟩ _ _ (Ne.symm h.shape.xNe5)]
    exact hxArrU
  have hspan2 : 2 * (s.n - 1) < s.benchlen := by
    have hsp := h.shape.peg.span
    have h2 : 2 * (s.n - 1) ≤ 3 * (s.n - 1) :=
      Nat.mul_le_mul_right _ (by decide : (2 : Nat) ≤ 3)
    exact Nat.lt_of_le_of_lt h2 (Nat.lt_of_le_of_lt (Nat.le_add_right _ base.cg) hsp)
  have hfitMul := red_mul_move_fit base.n base.bench s.tally base.mMax mv mvC mvCube
    (pegCount (ys.take base.n)) hT hroomM hpiece hCubeLe
    (by
      have hp := hpegY
      rw [h.hn] at hp
      exact hp)
  have hfitSl := red_slide_fit base.n s.tally base.mMax sl slC pegX
    (pegCount (ys.take base.n)) hT hroomS hpieceS
    (by
      have hp : pegX ≤ s.n := hpegX
      rw [h.hn] at hp
      exact hp)
    (by rw [h.hn] at hpegY; exact hpegY)
  obtain ⟨cSlot0, hcSlot0, hcLe0⟩ := h.ops 0 h0e
  have hcE0eq : cE0 = cSlot0 := ofNat_inj_nat (hcE0.symm.trans hcSlot0)
  have hent0 : cE0 ≤ base.ops0 + done.length * (base.mMax + 3) := by
    rw [hcE0eq]; exact hcLe0
  have hfitOp0 := mul_ops_fit base.ops0 base.R done.length base.mMax cE0 cC0
    hstepR hent0 h0plus
  have hmulLive := mul_eq_live bCube0 5 base.xHome 6 base.x ys base.w base.h base.r s.n s.k mvCube slCube holeC s.benchlen pkU peakSC cC0 hmkC honC htoC h6HC h6DC (by
      rw [hheldSz]
      exact h7U) hempty6 hbenchC (by rw [htierC]; exact hnU) h.shape.peg.n_pos hposY hnleY hzeroY h.shape.peg.fitN (by rw [hlenY]; exact h.shape.peg.fitBn) hmvCubeB hslCubeB hpkU (by
      have h2 := hfitMul.1
      have hidx : ys.take base.n = ys.take s.n := by rw [h.hn]
      rw [hidx] at h2
      exact h2) (by
      have h2 := hfitMul.2.1
      have hidx : ys.take base.n = ys.take s.n := by rw [h.hn]
      rw [hidx] at h2
      exact h2) (by
      have h2 := hfitSl
      have hidx : ys.take base.n = ys.take s.n := by rw [h.hn]
      rw [hidx] at h2
      exact h2) h0cubeSz hv0 (FitsLen.of_le base.fitO hfitOp0) (by rw [htierC]; exact hblU) hxDC hxHC hxHeldC hxArrC h.shape.xNe6 (by rw [h.hn]; exact hxLen) hspan2 hxT (FitsLen.of_le h.shape.peg.fit3
      (Nat.mul_le_mul_right _ (by decide : (2 : Nat) ≤ 3))) (by
      have h2 := hfitMul.2.2.1
      have hidx : ys.take base.n = ys.take s.n := by rw [h.hn]
      have hnn : base.n * (base.n + 1) = s.n * (s.n + 1) := by rw [h.hn]
      rw [hidx, hnn] at h2
      exact h2) ⟨h.shape.w0, h.shape.h0, h.shape.rlt, h.shape.r0, h.shape.n_eq, h.shape.k_le, h.shape.gap_eq⟩ (by rw [htierC]; exact hwU) (by rw [htierC]; exact hhU) (by rw [htierC]; exact hrU) (by rw [htierC]; exact hkU) hholeC hstrictC h.shape.peg.small h.shape.peg.n_small h.shape.peg.fitBn (by
      have h2 := hfitMul.2.2.2
      have hidx : ys.take base.n = ys.take s.n := by rw [h.hn]
      have hnn : base.n * (base.n + 1) = s.n * (s.n + 1) := by rw [h.hn]
      have hsub : base.bench - base.n = s.benchlen - s.n := by rw [h.hn, h.hbench]
      rw [hidx, hnn, hsub] at h2
      exact h2)
  have hRedEq : bRed0 = mulNoLiveBoard bCube0 5 6 base.x ys ⟨s.n, s.k, mvCube, slCube, holeC, s.benchlen, pkU, peakSC, cC0, h0cubeSz⟩ ⟨h6HC, h6DC⟩ := by
    injection hredU.symm.trans hmulLive
  have hmulOps := mul_live_ops bCube0 5 6 base.x ys ⟨s.n, s.k, mvCube, slCube, holeC, s.benchlen, pkU, peakSC, cC0, h0cubeSz⟩ ⟨h6HC, h6DC⟩
  have hsettleOps := settle_ops bCube0 6 ⟨h6HC, h6DC⟩ ys s.n mvCube slCube pkU
  have hidx0 := settle_ops_lt bCube0 0 6 h0cubeSz ⟨h6HC, h6DC⟩ ys s.n mvCube slCube pkU
  have hstep := ops_set_transport hsettleOps 0 hidx0 h0cubeSz
    (Int.ofNat (cC0 + 1)) (Int.ofNat (cC0 + 1)) rfl
  have hRedOpsB : bRed0.sudo_5Board_4cost.sudo_5Costs_3ops =
      (mulNoLiveBoard bCube0 5 6 base.x ys ⟨s.n, s.k, mvCube, slCube, holeC, s.benchlen, pkU, peakSC, cC0, h0cubeSz⟩ ⟨h6HC, h6DC⟩).sudo_5Board_4cost.sudo_5Costs_3ops :=
    congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_4cost.sudo_5Costs_3ops) hRedEq
  have hRedSet : bRed0.sudo_5Board_4cost.sudo_5Costs_3ops =
      bCube0.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨0, h0cubeSz⟩ (Int.ofNat (cC0 + 1)) :=
    hRedOpsB.trans (hmulOps.trans hstep)
  let occM1 := countHeld (bCube0.sudo_5Board_4held.set ⟨6, h6DC⟩ true) 7
  let bSM := settleBoard bCube0 6 h6HC h6DC ys s.n mvCube slCube pkU
  let hFsM := settle_held_lt bCube0 6 ⟨h6HC, h6DC⟩ ys s.n mvCube slCube pkU
  let occM2 := countHeld (bSM.sudo_5Board_4held.set ⟨6, hFsM⟩ false) 7
  let pkR := raisedPeak (raisedPeak pkU occM1) occM2
  have hpkMul := mul_live_peak bCube0 5 6 base.x ys ⟨s.n, s.k, mvCube, slCube, holeC, s.benchlen, pkU, peakSC, cC0, h0cubeSz⟩ ⟨h6HC, h6DC⟩
  have hpkRB : bRed0.sudo_5Board_4cost.sudo_5Costs_4peak =
      (mulNoLiveBoard bCube0 5 6 base.x ys ⟨s.n, s.k, mvCube, slCube, holeC, s.benchlen, pkU, peakSC, cC0, h0cubeSz⟩ ⟨h6HC, h6DC⟩).sudo_5Board_4cost.sudo_5Costs_4peak :=
    congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_4cost.sudo_5Costs_4peak) hRedEq
  have hpkR : bRed0.sudo_5Board_4cost.sudo_5Costs_4peak = (pkR : Int) := by
    have hraw := hpkRB.trans hpkMul
    simpa [pkR, occM1, occM2, bSM, hFsM, ofNat_eq_natCast] using hraw
  have hpkRle : pkR ≤ max pk 7 :=
    raised_twice_le pk pkU occM1 occM2 hpkUle (countHeld_seven _) (countHeld_seven _)
  obtain ⟨mvE, mvR, slE, slR, hmvE, hmvR, hmovR, hslE, hslR, hsldR⟩ := hrel
  have hszR : bRed0.sudo_5Board_4cost.sudo_5Costs_3ops.size =
      b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [hRedSet, Array.size_set, hOpsB.trans hOps, Array.size_set, hopsU]
    exact hδ.opsSize
  have hslotsR : ∀ i (hi : i < b.sudo_5Board_4cost.sudo_5Costs_3ops.size),
      ∃ c c' : Nat,
        b.sudo_5Board_4cost.sudo_5Costs_3ops[i] = (c : Int) ∧
        bRed0.sudo_5Board_4cost.sudo_5Costs_3ops[i]'(hszR ▸ hi) = (c' : Int) ∧
        c' ≤ c + (base.mMax + 3) := by
    intro i hi
    have hraw := red_ops_on_clear b.sudo_5Board_4cost.sudo_5Costs_3ops
      bClearU.sudo_5Board_4cost.sudo_5Costs_3ops
      bCube0.sudo_5Board_4cost.sudo_5Costs_3ops
      bRed0.sudo_5Board_4cost.sudo_5Costs_3ops
      s.tally base.mMax c1 cC0 hT
      (clearSlots_cast hslots (by
        have hback : bClearP.sudo_5Board_4cost.sudo_5Costs_3ops =
            bClearU.sudo_5Board_4cost.sudo_5Costs_3ops := hopsU.symm
        exact hback))
      (by rw [hOpsB.trans hOps, Array.size_set])
      (by rw [hRedSet, Array.size_set])
      hops1U h0cubeSz hop1U (hOpsB.trans hOps) hv0 hRedSet
    obtain ⟨c, c', hc, hc', hle⟩ := hraw.2 i hi
    refine ⟨c, c', hc, ?_, hle⟩
    exact (array_get_irrel (h1 := hszR ▸ hi)
      (h2 := by rw [hraw.1]; exact hi)).trans hc'
  have hopsTight : ∀ i (hi : i < b.sudo_5Board_4cost.sudo_5Costs_3ops.size),
      ∃ c c' : Nat,
        b.sudo_5Board_4cost.sudo_5Costs_3ops[i] = (c : Int) ∧
        bRed0.sudo_5Board_4cost.sudo_5Costs_3ops[i]'(hszR ▸ hi) = (c' : Int) ∧
        c' ≤ c + (base.mMax + 2) := by
    intro i hi
    have hraw := red_ops_slack b.sudo_5Board_4cost.sudo_5Costs_3ops
      bClearU.sudo_5Board_4cost.sudo_5Costs_3ops
      bCube0.sudo_5Board_4cost.sudo_5Costs_3ops
      bRed0.sudo_5Board_4cost.sudo_5Costs_3ops
      s.tally base.mMax c1 cC0 hT
      (clearSlots_cast hslots (by
        have hback : bClearP.sudo_5Board_4cost.sudo_5Costs_3ops =
            bClearU.sudo_5Board_4cost.sudo_5Costs_3ops := hopsU.symm
        exact hback))
      (by rw [hOpsB.trans hOps, Array.size_set])
      (by rw [hRedSet, Array.size_set])
      hops1U h0cubeSz hop1U (hOpsB.trans hOps) hv0 hRedSet
    obtain ⟨c, c', hc, hc', hle⟩ := hraw.2 i hi
    refine ⟨c, c', hc, ?_, hle⟩
    exact (array_get_irrel (h1 := hszR ▸ hi)
      (h2 := by rw [hraw.1]; exact hi)).trans hc'
  have hmovLoose : mvR ≤ mvE + rungCharge base.n base.bench s.tally := by
    omega
  have hsldLoose : slR ≤ slE + rungSlideCharge base.n s.tally := by
    omega
  have hδRed : RungDelta b bRed0 base s.tally :=
    rungDelta_cube_mul hmvE hmvR hmovLoose hslE hslR hsldLoose hpk hpkR hpkRle hszR hslotsR
  have hfixC := cube_live_park bClearU 6 5 xs ⟨s.n, s.k, mvC, slC, holeN, s.benchlen, pkC, pkS, c1, hops1U⟩ ⟨h5HU, h5DU⟩
  have hfixM := mul_live_park bCube0 5 6 base.x ys ⟨s.n, s.k, mvCube, slCube, holeC, s.benchlen, pkU, peakSC, cC0, h0cubeSz⟩ ⟨h6HC, h6DC⟩
  have hparkC : bCube0.sudo_5Board_9park_hole = bClearU.sudo_5Board_9park_hole :=
    (congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_9park_hole) hEq).trans hfixC.1
  have hparkR : bRed0.sudo_5Board_9park_hole = bCube0.sudo_5Board_9park_hole :=
    (congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_9park_hole) hRedEq).trans hfixM.1
  have hparkU : bClearU.sudo_5Board_9park_hole = bClearP.sudo_5Board_9park_hole := by
    rw [hClearEq]; rfl
  have hladC : bCube0.sudo_5Board_7ladder0 = bClearU.sudo_5Board_7ladder0 :=
    (congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_7ladder0) hEq).trans hfixC.2.1
  have hladR : bRed0.sudo_5Board_7ladder0 = bCube0.sudo_5Board_7ladder0 :=
    (congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_7ladder0) hRedEq).trans hfixM.2.1
  have hladU : bClearU.sudo_5Board_7ladder0 = bClearP.sudo_5Board_7ladder0 := by
    rw [hClearEq]; rfl
  have hnrC : bCube0.sudo_5Board_6nrungs = bClearU.sudo_5Board_6nrungs :=
    (congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_6nrungs) hEq).trans hfixC.2.2.1
  have hnrR : bRed0.sudo_5Board_6nrungs = bCube0.sudo_5Board_6nrungs :=
    (congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_6nrungs) hRedEq).trans hfixM.2.2.1
  have hnrU : bClearU.sudo_5Board_6nrungs = bClearP.sudo_5Board_6nrungs := by
    rw [hClearEq]; rfl
  have ht0C : bCube0.sudo_5Board_6tally0 = bClearU.sudo_5Board_6tally0 :=
    (congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_6tally0) hEq).trans hfixC.2.2.2.1
  have ht0R : bRed0.sudo_5Board_6tally0 = bCube0.sudo_5Board_6tally0 :=
    (congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_6tally0) hRedEq).trans hfixM.2.2.2.1
  have ht0U : bClearU.sudo_5Board_6tally0 = bClearP.sudo_5Board_6tally0 := by
    rw [hClearEq]; rfl
  have hmarkR : bRed0.sudo_5Board_9marker_on = false :=
    (congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_9marker_on) hRedEq).trans hfixM.2.2.2.2.1
  have htierR : bRed0.sudo_5Board_1t = bClearU.sudo_5Board_1t := by
    have hM := (congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_1t) hRedEq).trans hfixM.2.2.2.2.2
    exact hM.trans htierC
  have htierP : bClearU.sudo_5Board_1t = bClearP.sudo_5Board_1t := by
    rw [hClearEq]; rfl
  let hFs5 := settle_held_lt bClearU 5 ⟨h5HU, h5DU⟩ xs s.n mvC slC pkC
  have h5set : bCube0.sudo_5Board_4held =
      (settleBoard bClearU 5 h5HU h5DU xs s.n mvC slC pkC).sudo_5Board_4held.set
        ⟨5, hFs5⟩ false := by
    have hB := congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_4held) hEq
    have hlive := cube_live_held bClearU 6 5 xs ⟨s.n, s.k, mvC, slC, holeN, s.benchlen, pkC, pkS, c1, hops1U⟩ ⟨h5HU, h5DU⟩
    simpa [hFs5] using hB.trans hlive
  have h5DC : 5 < bCube0.sudo_5Board_4held.size := by
    rw [h5set, Array.size_set,
      settle_held_eq bClearU 5 ⟨h5HU, h5DU⟩ xs s.n mvC slC pkC,
      Array.size_set, hheldU]
    exact h5D
  have h5fC : bCube0.sudo_5Board_4held[5]'h5DC = false := by
    have hget := arr_get h5set 5 h5DC
    rw [hget]
    exact Array.getElem_set_eq _ ⟨5, hFs5⟩ false rfl _
  have hhomeRsz : bRed0.sudo_5Board_4home.size = bCube0.sudo_5Board_4home.size := by
    have hL := (congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_4home) hRedEq).trans
      (mul_live_home bCube0 5 6 base.x ys ⟨s.n, s.k, mvCube, slCube, holeC, s.benchlen, pkU, peakSC, cC0, h0cubeSz⟩ ⟨h6HC, h6DC⟩)
    have hs := congrArg Array.size hL
    rw [Array.size_set] at hs
    exact hs
  have h6HR : 6 < bRed0.sudo_5Board_4home.size := by rw [hhomeRsz]; exact h6HC
  let hFsR := settle_held_lt bCube0 6 ⟨h6HC, h6DC⟩ ys s.n mvCube slCube pkU
  have hheldSet : bRed0.sudo_5Board_4held =
      (settleBoard bCube0 6 h6HC h6DC ys s.n mvCube slCube pkU).sudo_5Board_4held.set
        ⟨6, hFsR⟩ false := by
    have hB := congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_4held) hRedEq
    have hlive := mul_live_held bCube0 5 6 base.x ys ⟨s.n, s.k, mvCube, slCube, holeC, s.benchlen, pkU, peakSC, cC0, h0cubeSz⟩ ⟨h6HC, h6DC⟩
    simpa [hFsR] using hB.trans hlive
  have hheldRsz : bRed0.sudo_5Board_4held.size = bCube0.sudo_5Board_4held.size := by
    rw [hheldSet, Array.size_set,
      settle_held_eq bCube0 6 ⟨h6HC, h6DC⟩ ys s.n mvCube slCube pkU,
      Array.size_set]
  have h6DR : 6 < bRed0.sudo_5Board_4held.size := by rw [hheldRsz]; exact h6DC
  have h7R : 7 ≤ bRed0.sudo_5Board_4held.size := by
    rw [hheldRsz, hheldSz, hheldU]
    exact h7E
  have h6fR : bRed0.sudo_5Board_4held[6]'h6DR = false := by
    have hget := arr_get hheldSet 6 h6DR
    rw [hget]
    exact Array.getElem_set_eq _ ⟨6, hFsR⟩ false rfl _
  have h5DR : 5 < bRed0.sudo_5Board_4held.size :=
    Nat.lt_trans (by decide : (5 : Nat) < 6) h6DR
  have h5fR : bRed0.sudo_5Board_4held[5]'h5DR = false := by
    have hget := arr_get hheldSet 5 h5DR
    rw [hget]
    rw [Array.getElem_set_ne _ ⟨6, hFsR⟩ _ _ (by decide : (6 : Nat) ≠ 5)]
    have hS := settle_held_eq bCube0 6 ⟨h6HC, h6DC⟩ ys s.n mvCube slCube pkU
    have hszS : 5 <
        (settleBoard bCube0 6 h6HC h6DC ys s.n mvCube slCube pkU).sudo_5Board_4held.size := by
      rw [hS, Array.size_set]
      exact h5DC
    have hgetS := arr_get hS 5 hszS
    rw [hgetS]
    rw [Array.getElem_set_ne _ ⟨6, h6DC⟩ _ _ (by decide : (6 : Nat) ≠ 5)]
    exact (idx_irrel (h2 := h5DC)).trans h5fC
  have hxDR : base.xHome < bRed0.sudo_5Board_4held.size := by rw [hheldRsz]; exact hxDC
  have hxHR : base.xHome < bRed0.sudo_5Board_4home.size := by rw [hhomeRsz]; exact hxHC
  have hxHeldR : bRed0.sudo_5Board_4held[base.xHome]'hxDR = true := by
    have hget := arr_get hheldSet base.xHome hxDR
    rw [hget]
    rw [Array.getElem_set_ne _ ⟨6, hFsR⟩ _ _ (Ne.symm h.shape.xNe6)]
    have hS := settle_held_eq bCube0 6 ⟨h6HC, h6DC⟩ ys s.n mvCube slCube pkU
    have hszS : base.xHome <
        (settleBoard bCube0 6 h6HC h6DC ys s.n mvCube slCube pkU).sudo_5Board_4held.size := by
      rw [hS, Array.size_set]
      exact hxDC
    have hgetS := arr_get hS base.xHome hszS
    rw [hgetS]
    rw [Array.getElem_set_ne _ ⟨6, h6DC⟩ _ _ (Ne.symm h.shape.xNe6)]
    exact (idx_irrel (h2 := hxDC)).trans hxHeldC
  have hxArrR : bRed0.sudo_5Board_4home[base.xHome]'hxHR = embed base.x := by
    have hL := (congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_4home) hRedEq).trans
      (mul_live_home bCube0 5 6 base.x ys ⟨s.n, s.k, mvCube, slCube, holeC, s.benchlen, pkU, peakSC, cC0, h0cubeSz⟩ ⟨h6HC, h6DC⟩)
    have hget := arr_get hL base.xHome hxHR
    rw [hget]
    rw [Array.getElem_set_ne _ ⟨6, h6HC⟩ _ _ (Ne.symm h.shape.xNe6)]
    exact (idx_irrel (h2 := hxHC)).trans hxArrC
  have hkeepR : CellKeep bRed0 base.xHome base.x :=
    { heldLt := hxDR, held := hxHeldR, homeLt := hxHR, arr := hxArrR }
  have hsideU : SideKeep bClearU base := by
    have hH : bClearU.sudo_5Board_4home = bClearP.sudo_5Board_4home := by
      rw [hClearEq, withPark_home]
    have hD : bClearU.sudo_5Board_4held = bClearP.sudo_5Board_4held := by
      rw [hClearEq, withPark_held]
    exact side_arrays hsideC hH hD
  have hsideCube0 := side_cubeLive hsideU 6 5 xs
    ⟨s.n, s.k, mvC, slC, holeN, s.benchlen, pkC, pkS, c1, hops1U⟩ ⟨h5HU, h5DU⟩
    (by decide) (by decide) (by decide)
  have hsideCube : SideKeep bCube0 base :=
    side_arrays hsideCube0
      (congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_4home) hEq)
      (congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_4held) hEq)
  have hsideMul0 := side_mulLive hsideCube 5 6 base.x ys
    ⟨s.n, s.k, mvCube, slCube, holeC, s.benchlen, pkU, peakSC, cC0, h0cubeSz⟩
    ⟨h6HC, h6DC⟩ (by decide) (by decide) (by decide)
  have hsideR : SideKeep bRed0 base :=
    side_arrays hsideMul0
      (congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_4home) hRedEq)
      (congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_4held) hRedEq)
  have hquietU : QuietKeep bClearU base := by
    have hH : bClearU.sudo_5Board_4home = bClearP.sudo_5Board_4home := by
      rw [hClearEq, withPark_home]
    have hD : bClearU.sudo_5Board_4held = bClearP.sudo_5Board_4held := by
      rw [hClearEq, withPark_held]
    have ht : bClearU.sudo_5Board_1t = bClearP.sudo_5Board_1t := by
      rw [hClearEq]; exact (withPark_tier _ _ _ _ _).symm
    have hm : bClearU.sudo_5Board_6marker = bClearP.sudo_5Board_6marker := by
      rw [hClearEq]; exact (withPark_ix _ _ _ _ _).symm
    have hx : bClearU.sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
        bClearP.sudo_5Board_4cost.sudo_5Costs_17script_marker_max := by
      rw [hClearEq]; exact (withPark_mx _ _ _ _ _).symm
    exact quiet_of hquietC (congrArg Array.size hH) (congrArg Array.size hD) ht hm hx
  have hquietCube0 := quiet_cubeLive hquietU 6 5 xs
    ⟨s.n, s.k, mvC, slC, holeN, s.benchlen, pkC, pkS, c1, hops1U⟩ ⟨h5HU, h5DU⟩
  have hquietCube : QuietKeep bCube0 base :=
    quiet_of hquietCube0
      (congrArg Array.size (congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_4home) hEq))
      (congrArg Array.size (congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_4held) hEq))
      (congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_1t) hEq)
      (congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_6marker) hEq)
      (congrArg (fun bd : Ecbs.Board =>
        bd.sudo_5Board_4cost.sudo_5Costs_17script_marker_max) hEq)
  have hquietMul0 := quiet_mulLive hquietCube 5 6 base.x ys
    ⟨s.n, s.k, mvCube, slCube, holeC, s.benchlen, pkU, peakSC, cC0, h0cubeSz⟩
    ⟨h6HC, h6DC⟩
  have hquietR : QuietKeep bRed0 base :=
    quiet_of hquietMul0
      (congrArg Array.size (congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_4home) hRedEq))
      (congrArg Array.size (congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_4held) hRedEq))
      (congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_1t) hRedEq)
      (congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_6marker) hRedEq)
      (congrArg (fun bd : Ecbs.Board =>
        bd.sudo_5Board_4cost.sudo_5Costs_17script_marker_max) hRedEq)
  have hstrictR : ∃ p : Nat,
      bRed0.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (p : Int) := by
    let occ := countHeld
      (settleBoard bCube0 6 h6HC h6DC ys s.n mvCube slCube pkU).sudo_5Board_4held 7
    refine ⟨raisedPeak peakSC occ, ?_⟩
    have hB := congrArg
      (fun bd : Ecbs.Board => bd.sudo_5Board_4cost.sudo_5Costs_11peak_strict) hRedEq
    have hlive := mul_live_strict bCube0 5 6 base.x ys ⟨s.n, s.k, mvCube, slCube, holeC, s.benchlen, pkU, peakSC, cC0, h0cubeSz⟩ ⟨h6HC, h6DC⟩
    simpa [occ, ofNat_eq_natCast] using hB.trans hlive
  have hholeR : ∃ holeR : Nat,
      bRed0.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = (holeR : Int) := by
    let holeR := raisedHole holeC (topIdx
      (school s.n base.x (ys.take s.n) (List.replicate s.benchlen 0) false))
    refine ⟨holeR, ?_⟩
    have hB := congrArg
      (fun bd : Ecbs.Board => bd.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole) hRedEq
    have hlive := mulLive_hole bCube0 5 6 base.x ys ⟨s.n, s.k, mvCube, slCube, holeC, s.benchlen, pkU, peakSC, cC0, h0cubeSz⟩ ⟨h6HC, h6DC⟩
    simpa [holeR, ofNat_eq_natCast] using hB.trans hlive
  exact {
    delta := hδRed
    park := hparkR.trans (hparkC.trans hparkU)
    ladder := hladR.trans (hladC.trans hladU)
    nrungs := hnrR.trans (hnrC.trans hnrU)
    tally0 := ht0R.trans (ht0C.trans ht0U)
    marker := hmarkR
    tier := htierR.trans htierP
    home6 := h6HR
    held6 := h6DR
    held7 := h7R
    empty5 := (idx_irrel (h2 := h5DR)).trans h5fR
    empty6 := h6fR
    keep := hkeepR
    side := hsideR
    quiet := hquietR
    strict := hstrictR
    hole := hholeR
    opsTight := hopsTight }
/-- Idle non-final red rung. The parked clear is the unparked clear with the
    park row and a counter `2` higher. `tally_double` and `tally_add_one` keep
    that offset. The spare cube and the mul by the input are `withPark` of the
    unparked results, on the doubled park row. -/
theorem red_open_emit
    {done rest : List Nat} {r : Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvKCore done (r :: rest) b s base)
    (hM : MoveHeadroom b base.n base.bench base.mMax)
    (hS : SlideHeadroom b base.n base.mMax)
    (hF : s.fromHole < 0) (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax)
    (hhome : s.onBench = false) (hr : r = 2) (hrest : rest ≠ [])
    (hxLen : base.x.length = base.n) (hxT : allTritList base.x) :
    ∃ bAdd,
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
          Ecbs.tally_add_one b) = .ok bAdd ∧
      bAdd.sudo_5Board_4cost.sudo_5Costs_4ctrl =
        ((s.ctrl + 2 + 3 * s.tally + 1 : Nat) : Int) ∧
      bAdd.sudo_5Board_9tally_len = ((2 * s.tally + 1 : Nat) : Int) ∧
      bAdd.sudo_5Board_4cost.sudo_5Costs_15control_highest =
        ((max s.high (s.t0 + 2 * s.tally) : Nat) : Int) ∧
      bAdd.sudo_5Board_11parked_from =
        ((climbAt base.ladder0 base.R s.ridx : Nat) : Int) ∧
      bAdd.sudo_5Board_8rung_idx = ((s.ridx + 1 : Nat) : Int) ∧
      bAdd.sudo_5Board_3row =
        embed (modelRung s base.x r (climbAt base.ladder0 base.R s.ridx) false).row ∧
      bAdd.sudo_5Board_4cost.sudo_5Costs_9tally_max =
        ((2 * s.tally + 1 : Nat) : Int) ∧
      RungDelta b bAdd base s.tally ∧
      ∃ (bClearP bClearU _bCube bR : Ecbs.Board),
        bAdd.sudo_5Board_4cost.sudo_5Costs_5moves =
          bR.sudo_5Board_4cost.sudo_5Costs_5moves ∧
        bAdd.sudo_5Board_4cost.sudo_5Costs_6slides =
          bR.sudo_5Board_4cost.sudo_5Costs_6slides ∧
        bAdd.sudo_5Board_4cost.sudo_5Costs_3ops =
          bR.sudo_5Board_4cost.sudo_5Costs_3ops ∧
        bAdd.sudo_5Board_4cost.sudo_5Costs_4peak =
          bR.sudo_5Board_4cost.sudo_5Costs_4peak ∧
        bAdd.sudo_5Board_4held = bR.sudo_5Board_4held ∧
        bAdd.sudo_5Board_4home = bR.sudo_5Board_4home ∧
        bAdd.sudo_5Board_5bench = bR.sudo_5Board_5bench ∧
        bAdd.sudo_5Board_8bench_on = bR.sudo_5Board_8bench_on ∧
        bAdd.sudo_5Board_8bench_to = bR.sudo_5Board_8bench_to ∧
        bAdd.sudo_5Board_9marker_on = bR.sudo_5Board_9marker_on ∧
        bAdd.sudo_5Board_1t = bR.sudo_5Board_1t ∧
        bAdd.sudo_5Board_6marker = bR.sudo_5Board_6marker ∧
        bAdd.sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
          bR.sudo_5Board_4cost.sudo_5Costs_17script_marker_max ∧
        bAdd.sudo_5Board_7ladder0 = bR.sudo_5Board_7ladder0 ∧
        bAdd.sudo_5Board_6nrungs = bR.sudo_5Board_6nrungs ∧
        bAdd.sudo_5Board_9park_hole = bR.sudo_5Board_9park_hole ∧
        bAdd.sudo_5Board_6tally0 = bR.sudo_5Board_6tally0 ∧
        bAdd.sudo_5Board_4cost.sudo_5Costs_11peak_strict =
          bR.sudo_5Board_4cost.sudo_5Costs_11peak_strict ∧
        bAdd.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
          bR.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole ∧
        bClearP = withPark bClearU
          (embed (paintRed (afterPark s.row (-1) s.parkAt
            (climbAt base.ladder0 base.R s.ridx) r) s.t0 s.tally))
          (((s.ctrl + 2 + s.tally : Nat) : Int))
          (((climbAt base.ladder0 base.R s.ridx : Nat) : Int))
          (Int.ofNat (s.ridx + 1)) ∧
        RungDelta b bClearP base s.tally ∧
        ClearSlots b.sudo_5Board_4cost.sudo_5Costs_3ops
          bClearP.sudo_5Board_4cost.sudo_5Costs_3ops s.tally ∧
        (∃ (mvE mvR slE slR : Nat),
          b.sudo_5Board_4cost.sudo_5Costs_5moves = (mvE : Int) ∧
          bR.sudo_5Board_4cost.sudo_5Costs_5moves = (mvR : Int) ∧
          mvR + 2 * base.n ≤ mvE + rungCharge base.n base.bench s.tally ∧
          b.sudo_5Board_4cost.sudo_5Costs_6slides = (slE : Int) ∧
          bR.sudo_5Board_4cost.sudo_5Costs_6slides = (slR : Int) ∧
          slR + 2 * base.n ≤ slE + rungSlideCharge base.n s.tally) ∧
        bClearP.sudo_5Board_7ladder0 = b.sudo_5Board_7ladder0 ∧
        bClearP.sudo_5Board_6nrungs = b.sudo_5Board_6nrungs ∧
        bClearP.sudo_5Board_9park_hole = (s.parkAt : Int) ∧
        bClearP.sudo_5Board_6tally0 = (s.t0 : Int) ∧
        bClearP.sudo_5Board_9marker_on = false ∧
        bClearP.sudo_5Board_1t = b.sudo_5Board_1t ∧
        bR.sudo_5Board_8bench_on = true ∧
        bR.sudo_5Board_8bench_to = (5 : Int) ∧
        bR.sudo_5Board_9tally_len = (s.tally : Int) ∧
        bR.sudo_5Board_6tally0 = (s.t0 : Int) ∧
        bR.sudo_5Board_5bench =
          embed (fieldMul s.n s.k s.benchlen base.x
            (fieldCube s.n s.k s.benchlen
              (fieldMul s.n s.k s.benchlen s.gap
                (cubeTimes s.n s.k s.benchlen s.gap s.tally))) ++
            List.replicate (s.benchlen - s.n) 0) ∧
        RedCarry b bR bClearP base s.tally base.xHome base.x := by

  let hole := climbAt base.ladder0 base.R s.ridx
  obtain ⟨bClearP, bClearU, bCube0, bRed0, hrun, hClearEq, _hlenC, _ht0C, _hrowC,
      _hctrlN, _hhighC, _hctrlC, _hmaxC, ht0Red, _htierRed, hcubeBoth, hmulBoth,
      hrel, honR, htoR, hlenR, hbenchR, hδ, hslots, hladE, hnrE, hparkE,
      ht0E, hmarkE, htierE, _htmaxE, hcubeU, hredU, hbonE, htoE, hbenchE,
      h5H, h5D, h6H, h6D, h7E, h5f, h6f, hkeep, hopsE, hc1E, hpkSE, hholeE,
      htrits, hpieceM, hpieceS, hside, hquiet⟩ :=
    red_open_view h hM hS hF hm hT hhome hxLen hxT
  let fromH := ((hole : Nat) : Int)
  let ridxH := Int.ofNat (s.ridx + 1)
  have hge : 2 ≤ (r :: rest).length := by
    cases rest with
    | nil => exact absurd rfl hrest
    | cons _ _ => simp
  have hRoom : s.t0 + 2 * s.tally ≤ base.control := h.openRoom hge
  have hHighEq : s.t0 + s.tally - 1 ≤ s.high := by
    rw [h.highTop]
    exact Nat.le_max_right _ _
  obtain ⟨tmax0, hMax, hNote0⟩ := h.tmaxLt
  have hNote : tmax0 < 2 * s.tally := hNote0 hm
  have hdone2 : done.length + 2 ≤ base.R := by
    have hk := h.kLe
    simp [h.idx, List.length_append, List.length_cons] at hk
    cases rest with
    | nil => exact absurd rfl hrest
    | cons _ _ =>
      simp at hk
      omega
  have hfits := open_white_ctrl_fit s.ctrl s.tally base.ctrl0 done.length base.R
    base.mMax h.ctrlLe hT hdone2 base.fitCtrl
  have hFitI : FitsLen (s.t0 + 2 * s.tally) :=
    (double_index_fit_le hRoom base.fitControl).1
  have hFitM : FitsLen (2 * s.tally) :=
    (double_index_fit_le hRoom base.fitControl).2.1
  have hRpos : 0 < base.R := by
    have hk := h.kLe
    simp [List.length_append] at hk
    omega
  have hn0 : 0 < base.n := by rw [← h.hn]; exact h.shape.peg.n_pos
  have hFitL1 : FitsLen (2 * s.tally + 1) := double_len_fit hn0 hRpos hT base.fitM
  have hdone : done.length ≤ base.R := by
    have hk := h.kLe
    simp [List.length_append] at hk
    omega
  have hCtrlU := double_ctrl_fit h.ctrlLe hT hdone base.fitCtrl
  have hfitCU : FitsLen (s.ctrl + s.tally + 2 * s.tally) :=
    FitsLen.of_le hCtrlU.1 (by omega)
  have hfitCP : FitsLen (s.ctrl + s.tally + 2 + 2 * s.tally) := by
    rw [show s.ctrl + s.tally + 2 + 2 * s.tally = s.ctrl + 2 + 3 * s.tally by omega]
    exact hfits.1
  let xs := paintRed s.row s.t0 s.tally
  let xsP := paintRed (afterPark s.row (-1) s.parkAt hole r) s.t0 s.tally
  have htwo : 2 * s.tally = s.tally + s.tally := Nat.two_mul s.tally
  have hle2 : s.t0 + s.tally ≤ s.t0 + 2 * s.tally := by
    rw [htwo]
    exact Nat.add_le_add_left (Nat.le_add_left s.tally s.tally) s.t0
  have hsumEq : (s.t0 + s.tally) + s.tally = s.t0 + 2 * s.tally := by
    rw [Nat.add_assoc, ← htwo]
  have hixHalf (k : Nat) (hk : k < s.tally) : s.t0 + s.tally + k < s.row.length := by
    rw [h.shape.rowLen]
    have hassoc : s.t0 + s.tally + k = s.t0 + (s.tally + k) := Nat.add_assoc _ _ _
    have hlt : s.t0 + (s.tally + k) < s.t0 + (s.tally + s.tally) :=
      Nat.add_lt_add_left (Nat.add_lt_add_left hk s.tally) s.t0
    have h2 : s.t0 + (s.tally + s.tally) = s.t0 + 2 * s.tally := by rw [← htwo]
    have hlt' : s.t0 + s.tally + k < s.t0 + 2 * s.tally := by
      rw [hassoc, ← h2]
      exact hlt
    exact Nat.lt_of_lt_of_le hlt' hRoom
  have hRed : ∀ j (hj : j < s.tally),
      xs[s.t0 + j]'(by
        dsimp only [xs]
        rw [paintRed_length]
        exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj s.t0) h.shape.seg.room) = 2 := by
    intro j hj
    exact paintRed_get_lo s.row s.t0 s.tally j hj h.shape.seg.room
  have hRedP : ∀ j (hj : j < s.tally),
      xsP[s.t0 + j]'(by
        dsimp only [xsP]
        rw [paintRed_length, afterPark_length]
        exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj s.t0) h.shape.seg.room) = 2 := by
    intro j hj
    exact paintRed_get_lo (afterPark s.row (-1) s.parkAt hole r) s.t0 s.tally j hj
      (by rw [afterPark_length]; exact h.shape.seg.room)
  have hZero : ∀ k (hk : k < s.tally),
      xs[s.t0 + s.tally + k]'(by
        dsimp only [xs]
        rw [paintRed_length]
        exact hixHalf k hk) = 0 := by
    intro k hk
    have hsrc := h.openZero hge k hk (hixHalf k hk)
    have hget := paintRed_get_hi s.row s.t0 s.tally (s.t0 + s.tally + k)
      (Nat.le_add_right _ k) (hixHalf k hk)
    dsimp only [xs]
    exact hget.trans hsrc
  have hZeroP : ∀ k (hk : k < s.tally),
      xsP[s.t0 + s.tally + k]'(by
        dsimp only [xsP]
        rw [paintRed_length, afterPark_length]
        exact hixHalf k hk) = 0 := by
    intro k hk
    have hleJ : s.t0 ≤ s.t0 + s.tally + k :=
      Nat.le_trans (Nat.le_add_right s.t0 s.tally) (Nat.le_add_right _ k)
    have hAp := afterPark_get s.row (-1) s.parkAt hole r (s.t0 + s.tally + k)
      (Nat.lt_of_lt_of_le h.parkBelow hleJ)
      (Nat.lt_of_lt_of_le h.holeBelow hleJ)
      (Or.inl (by decide)) (hixHalf k hk)
    have hget := paintRed_get_hi (afterPark s.row (-1) s.parkAt hole r) s.t0 s.tally
      (s.t0 + s.tally + k) (Nat.le_add_right _ k)
      (by rw [afterPark_length]; exact hixHalf k hk)
    have hsrc := h.openZero hge k hk (hixHalf k hk)
    dsimp only [xsP]
    exact hget.trans (hAp.trans hsrc)
  have hctrlPark :
      (((s.ctrl + 2 + s.tally : Nat) : Int)) = ((s.ctrl + s.tally + 2 : Nat) : Int) := by
    apply congrArg Int.ofNat
    omega
  have hdouble := tally_double_withPark bClearU xs xsP s.t0 s.tally (s.ctrl + s.tally)
    s.high base.control tmax0 fromH ridxH
    hm _hlenC _ht0C
    (by dsimp only [xs]; rw [paintRed_length, h.shape.rowLen]; exact hRoom)
    (by dsimp only [xsP]; rw [paintRed_length, afterPark_length, h.shape.rowLen]; exact hRoom)
    hRed hRedP hZero hZeroP _hctrlN _hhighC hHighEq
    _hctrlC hRoom hFitI hfitCU hfitCP hFitM (by rw [_hmaxC]; exact hMax) hNote
  have hClear0 := hClearEq
  rw [hctrlPark] at hClearEq
  rw [← hClearEq] at hdouble
  let rowD := embed (paintOnes (paintOnes xs s.t0 s.tally) (s.t0 + s.tally) s.tally)
  let rowP := embed (paintOnes (paintOnes xsP s.t0 s.tally) (s.t0 + s.tally) s.tally)
  let lenD := Int.ofNat (2 * s.tally)
  let ctrlD := Int.ofNat (s.ctrl + s.tally + 2 * s.tally)
  let highD := ((max s.high (s.t0 + 2 * s.tally - 1) : Nat) : Int)
  let maxD := Int.ofNat (2 * s.tally)
  let ctrlP := Int.ofNat (s.ctrl + s.tally + 2 + 2 * s.tally)
  have hcube := hcubeBoth rowD rowP lenD highD maxD ctrlD ctrlP fromH ridxH
  have hmul := hmulBoth rowD rowP lenD highD maxD ctrlD ctrlP fromH ridxH
  -- The double result is the withPark form hcube reads.
  have hDoubleForm :
      Ecbs.tally_double bClearP =
        .ok (withPark (withTally bClearU rowD lenD ctrlD highD maxD) rowP ctrlP fromH ridxH) := by
    dsimp only [rowD, rowP, lenD, ctrlD, highD, maxD, ctrlP, xs, xsP, withTally, hole]
    exact hdouble
  have hcubeRun :
      Ecbs.cube (withPark (withTally bClearU rowD lenD ctrlD highD maxD) rowP ctrlP fromH ridxH)
          ((6 : Nat) : Int) ((5 : Nat) : Int) =
        .ok (withPark (withTally bCube0 rowD lenD ctrlD highD maxD) rowP ctrlP fromH ridxH) :=
    hcube
  have hmulRun :
      Ecbs.mul (withPark (withTally bCube0 rowD lenD ctrlD highD maxD) rowP ctrlP fromH ridxH)
          ((5 : Nat) : Int) (base.xHome : Int) ((6 : Nat) : Int) false false false =
        .ok (withPark (withTally bRed0 rowD lenD ctrlD highD maxD) rowP ctrlP fromH ridxH) :=
    hmul
  let bRedP := withPark (withTally bRed0 rowD lenD ctrlD highD maxD) rowP ctrlP fromH ridxH
  have hPast : s.t0 + 2 * s.tally < base.control := by
    have hfit := h.tailFit
    have hgrow := red_final_gt s.tally r rest hr hrest
    have hwhole : climbTally s.tally (r :: rest) =
        climbTally base.tally0 (done ++ (r :: rest)) := by
      rw [h.htally0]
      exact climbTally_prefix_rest base.tally0 done (r :: rest)
    rw [h.shape.rowLen] at hfit
    have hlt : 2 * s.tally < climbTally base.tally0 (done ++ (r :: rest)) := by
      rw [← hwhole]; exact hgrow
    omega
  have hixP : s.t0 + 2 * s.tally < rowP.size := by
    dsimp only [rowP]
    rw [size_embed, paintOnes_length, paintOnes_length, paintRed_length, afterPark_length,
      h.shape.rowLen]
    exact hPast
  have hzeroCell : rowP[s.t0 + 2 * s.tally]'hixP = 0 := by
    have hwide := paintOnes_get_hi (paintOnes xsP s.t0 s.tally) (s.t0 + s.tally) s.tally
      (s.t0 + 2 * s.tally) (Nat.le_of_eq hsumEq)
      (by dsimp only [xsP]; rw [paintOnes_length, paintRed_length, afterPark_length, h.shape.rowLen]; exact hPast)
    have hmid := paintOnes_get_hi xsP s.t0 s.tally (s.t0 + 2 * s.tally) hle2
      (by dsimp only [xsP]; rw [paintRed_length, afterPark_length, h.shape.rowLen]; exact hPast)
    have hred := paintRed_get_hi (afterPark s.row (-1) s.parkAt hole r) s.t0 s.tally
      (s.t0 + 2 * s.tally) hle2
      (by rw [afterPark_length, h.shape.rowLen]; exact hPast)
    have hAp := afterPark_get s.row (-1) s.parkAt hole r (s.t0 + 2 * s.tally)
      (Nat.lt_of_lt_of_le h.parkBelow (Nat.le_add_right _ _))
      (Nat.lt_of_lt_of_le h.holeBelow (Nat.le_add_right _ _))
      (Or.inl (by decide)) (by rw [h.shape.rowLen]; exact hPast)
    have htail := h.tailZero (2 * s.tally) (by omega)
      (by
        have hgrow := red_final_gt s.tally r rest hr hrest
        have hwhole : climbTally s.tally (r :: rest) =
            climbTally base.tally0 (done ++ (r :: rest)) := by
          rw [h.htally0]
          exact climbTally_prefix_rest base.tally0 done (r :: rest)
        rw [← hwhole]; exact hgrow)
      (by rw [h.shape.rowLen]; exact hPast)
    have hrowIx : s.t0 + 2 * s.tally < s.row.length := by
      rw [h.shape.rowLen]; exact hPast
    have hlist0 :
        (paintOnes (paintOnes xsP s.t0 s.tally) (s.t0 + s.tally) s.tally)[s.t0 + 2 * s.tally]'(by
          rw [paintOnes_length, paintOnes_length]
          dsimp only [xsP]
          rw [paintRed_length, afterPark_length]
          exact hrowIx) = 0 :=
      hwide.trans (hmid.trans (hred.trans (hAp.trans htail)))
    dsimp only [rowP, embed]
    rw [Array.getElem_mk, List.getElem_map, hlist0]
    rfl
  have hAdd := tally_add_one_withPark
      (withTally bRed0 rowD lenD ctrlD highD maxD) s.t0 (2 * s.tally)
      (max s.high (s.t0 + 2 * s.tally - 1)) base.control
      (s.ctrl + s.tally + 2 * s.tally) (2 * s.tally)
      rowP fromH ridxH
      (by simp [withTally, lenD]) (by simp [withTally, ht0Red])
      (by
        rw [withTally_row]
        dsimp only [rowD]
        rw [size_embed, paintOnes_length, paintOnes_length, paintRed_length, h.shape.rowLen]
        exact hPast)
      hixP
      hzeroCell
      (by simp [withTally, _htierRed, _hctrlN]) hPast
      (by simp [withTally, highD]) hFitI
      (by
        have h1 : FitsLen (s.ctrl + 2 + 3 * s.tally + 1) := by
          have hpos : 1 ≤ 2 * s.tally :=
            Nat.le_trans hm (by rw [Nat.two_mul]; exact Nat.le_add_left s.tally s.tally)
          exact FitsLen.of_le hfits.2.2.2
            (Nat.add_le_add_left hpos (s.ctrl + 2 + 3 * s.tally))
        have hsame : s.ctrl + s.tally + 2 * s.tally + 2 + 1 =
            s.ctrl + 2 + 3 * s.tally + 1 := by omega
        exact hsame.symm ▸ h1)
      hFitL1 (by simp [withTally, maxD]) (by omega)
  have hctrlOut : ((s.ctrl + s.tally + 2 * s.tally + 2 : Nat) : Int) = ctrlP := by
    apply congrArg (fun n : Nat => (n : Int))
    omega
  rw [hctrlOut] at hAdd
  have hflat : max (max s.high (s.t0 + 2 * s.tally - 1)) (s.t0 + 2 * s.tally) =
      max s.high (s.t0 + 2 * s.tally) := by
    rw [Nat.max_assoc]
    exact congrArg (max s.high) (Nat.max_eq_right (Nat.sub_le _ _))
  rw [hflat] at hAdd
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
          Ecbs.tally_add_one b) = .ok
        (withPark
          { withTally bRed0 rowD lenD ctrlD highD maxD with
              sudo_5Board_3row :=
                (withTally bRed0 rowD lenD ctrlD highD maxD).sudo_5Board_3row.set
                  ⟨s.t0 + 2 * s.tally, by
                    rw [withTally_row]
                    dsimp only [rowD]
                    rw [size_embed, paintOnes_length, paintOnes_length, paintRed_length,
                      h.shape.rowLen]
                    exact hPast⟩ (1 : Int)
              sudo_5Board_9tally_len := Int.ofNat (2 * s.tally + 1)
              sudo_5Board_4cost :=
                { (withTally bRed0 rowD lenD ctrlD highD maxD).sudo_5Board_4cost with
                    sudo_5Costs_15control_highest :=
                      ((max s.high (s.t0 + 2 * s.tally) : Nat) : Int)
                    sudo_5Costs_4ctrl := Int.ofNat (s.ctrl + s.tally + 2 * s.tally + 1)
                    sudo_5Costs_9tally_max := Int.ofNat (2 * s.tally + 1) } }
          (rowP.set ⟨s.t0 + 2 * s.tally, hixP⟩ (1 : Int))
          (Int.ofNat (s.ctrl + s.tally + 2 * s.tally + 2 + 1))
          fromH ridxH) := by
    rw [hrun, ok_bind, hDoubleForm, ok_bind, hcubeRun, ok_bind, hmulRun, ok_bind]
    simpa [bRedP] using hAdd
  have hpack :=
    red_unparked_delta h hM hS
      hm hT hhome hxLen hxT
      bClearP bClearU bCube0 bRed0
      (embed (paintRed (afterPark s.row (-1) s.parkAt
        (climbAt base.ladder0 base.R s.ridx) r) s.t0 s.tally))
      (((s.ctrl + 2 + s.tally : Nat) : Int))
      (((climbAt base.ladder0 base.R s.ridx : Nat) : Int))
      (Int.ofNat (s.ridx + 1))
      hClear0 hδ hslots hmarkE htierE hcubeU hredU hrel
      hbonE htoE hbenchE h5H h5D h6H h6D h7E h5f h6f hkeep hopsE hc1E hpkSE hholeE
      htrits hpieceM hpieceS hside hquiet
  have hδRed : RungDelta b bRed0 base s.tally := hpack.delta
  refine ⟨_, hprog, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [withPark, withTally, ctrlD]
    omega
  · simp [withPark, withTally, lenD]
  · simp [withPark, withTally]
  · simp [withPark, fromH]
  · simp [withPark, ridxH]
  · rw [withPark_row]
    have hFrom : s.fromHole = -1 := h.shape.park.fromIdle hF
    obtain ⟨_, _, _, _, _, _, hrowM, _, _, _, _, _, _, _⟩ :=
      model_open_red s base.x r hole hr hF
    let xsL := paintOnes (paintOnes xsP s.t0 s.tally) (s.t0 + s.tally) s.tally
    have hlist : xsL.set (s.t0 + 2 * s.tally) 1 =
        (modelRung s base.x r hole false).row := by
      simpa [xsL, xsP, hFrom, hole] using hrowM.symm
    have hlenL : s.t0 + 2 * s.tally < xsL.length := by
      dsimp only [xsL]
      rw [paintOnes_length, paintOnes_length]
      dsimp only [xsP]
      rw [paintRed_length, afterPark_length, h.shape.rowLen]
      exact hPast
    have hrowP : rowP = embed xsL := by simp [rowP, xsL]
    have hixL : s.t0 + 2 * s.tally < (embed xsL).size := by
      rw [size_embed]; exact hlenL
    rw [show (1 : Int) = Int.ofNat 1 from rfl]
    rw [arr_set_congr hrowP (s.t0 + 2 * s.tally) hixP (Int.ofNat 1)]
    rw [array_set_idx (h1 := hrowP ▸ hixP) (h2 := hixL)]
    rw [embed_set xsL (s.t0 + 2 * s.tally) 1 hlenL, hlist]
  · rw [withPark_tmax]
    rfl
  · exact rungDelta_cost hδRed
      (by rw [withPark_moves, withTally_moves])
      (by rw [withPark_slides, withTally_slides])
      (by rw [withPark_ops, withTally_ops])
      (by rw [withPark_peak, withTally_peak])
  · refine ⟨bClearP, bClearU, bCube0, bRed0,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      hClear0, hδ, hslots, hrel, hladE, hnrE, hparkE, ht0E, hmarkE, htierE,
      honR, htoR, hlenR, ht0Red, hbenchR, hpack⟩
    · rw [withPark_moves]; rfl
    · rw [withPark_slides]; rfl
    · rw [withPark_ops]; rfl
    · rw [withPark_peak]; rfl
    · rw [withPark_held]; rfl
    · rw [withPark_home]; rfl
    · rw [withPark_bench]; rfl
    · rw [withPark_on]; rfl
    · rw [withPark_to]; rfl
    · rw [withPark_marker]; rfl
    · rw [withPark_tier]; rfl
    · rw [withPark_ix]; rfl
    · rw [withPark_mx]; rfl
    · rw [withPark_ladder]; rfl
    · rw [withPark_nrungs]; rfl
    · rw [withPark_park]; rfl
    · rw [withPark_tally0]; rfl
    · rw [withPark_strict]; rfl
    · rw [withPark_hole]; rfl

/-- Idle non-final red rung. Park through the clear, the double, the spare cube,
    the mul by the input, and the extra peg. The cost is the unparked
    `RungDelta`: park, the double, and the peg do not add moves, slides, or
    ops, and they do not change peak. -/
theorem red_open_k
    {done rest : List Nat} {r : Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvKCore done (r :: rest) b s base)
    (hM : MoveHeadroom b base.n base.bench base.mMax)
    (hS : SlideHeadroom b base.n base.mMax)
    (hF : s.fromHole < 0) (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax)
    (hhome : s.onBench = false) (hr : r = 2) (hrest : rest ≠ [])
    (hParkAt : s.parkAt = base.ladder0 + base.R)
    (hCap : climbTallyPrefix base.tally0 done (r :: rest) ≤ base.mMax)
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
      ClimbInvKCore (done ++ [r]) rest b'
        (modelRung s base.x r (climbAt base.ladder0 base.R s.ridx) false) base ∧
      RungDeltaTight b b' base s.tally := by
  obtain ⟨bAdd, hprog, hctrlA, hlenA, hhighA, hfromA, hridxA, hrowA, htmaxA, hδA,
      _bCP, _bCU, _bC, bR,
      hmvA, hslA, hopsA, hpkA,
      hheldA, hhomeA, hbenchA, honA, htoA, hmarkA, htierA, hixA, hmxA,
      hladA, hnrA, hparkA, ht0A, hstrictA, hholeA,
      _hClear, _hδC, _hslots, hrel,
      hladE, hnrE, hparkE, _ht0E, _hmarkE, htierE,
      honR, htoR, _hlenR, ht0R, hbenchR, hcarry⟩ :=
    red_open_emit h hM hS hF hm hT hhome hr hrest hxLen hxT
  let hole := climbAt base.ladder0 base.R s.ridx
  let s' := modelRung s base.x r hole false
  obtain ⟨hgap, htall, hon, hwork, hctrlM, hhighM, hrowM, hfromM, hridxM, ht0M,
      hparkM, hnM, hkM, hbM⟩ := model_open_red s base.x r hole hr hF
  have hge : 2 ≤ (r :: rest).length := by
    cases rest with
    | nil => exact absurd rfl hrest
    | cons _ _ => simp
  have hdone2 : done.length + 2 ≤ base.R := by
    have hk := h.kLe
    simp [h.idx, List.length_append, List.length_cons] at hk
    cases rest with
    | nil => exact absurd rfl hrest
    | cons _ _ =>
      simp at hk
      omega
  have hfits := open_red_ctrl_fit s.ctrl s.tally base.ctrl0 done.length base.R
    base.mMax h.ctrlLe hT hdone2 base.fitCtrl
  have hidx : s.ridx < base.R := by
    rw [h.idx]
    omega
  have hStep := successor_hole base.ladder0 base.R s.ridx s.parkAt s.row.length
    h.shape.park.l0pos hidx hParkAt h.shape.park.holeLt
  have hlenRow : s'.row.length = s.row.length := by
    rw [hrowM, List.length_set, paintOnes_length, paintOnes_length, paintRed_length,
      afterPark_length]
  have htierB : bAdd.sudo_5Board_1t = b.sudo_5Board_1t :=
    (htierA.trans hcarry.tier).trans htierE
  have hinv : ClimbInv bAdd s' := by
    refine
      { hG := ?_
        hGs := ?_
        marker := hmarkA.trans hcarry.marker
        len := hlenA.trans (congrArg (fun n : Nat => (n : Int)) htall.symm)
        ctrl := hctrlA.trans (congrArg (fun n : Nat => (n : Int)) hctrlM.symm)
        high := hhighA.trans (congrArg (fun n : Nat => (n : Int)) hhighM.symm)
        t0 := (ht0A.trans ht0R).trans (congrArg (fun n : Nat => (n : Int)) ht0M.symm)
        row := hrowA
        park := (hparkA.trans (hcarry.park.trans hparkE)).trans
          (congrArg (fun n : Nat => (n : Int)) hparkM.symm)
        fromP := hfromA.trans hfromM.symm
        ridx := hridxA.trans (congrArg (fun n : Nat => (n : Int)) hridxM.symm)
        gapHome := ?_
        gapBench := ?_ }
    · rw [hhomeA]
      exact Nat.lt_trans (by decide : (5 : Nat) < 6) hcarry.home6
    · rw [hheldA]
      exact Nat.lt_trans (by decide : (5 : Nat) < 6) hcarry.held6
    · intro hOff
      rw [hon] at hOff
      cases hOff
    · intro _
      refine ⟨honA.trans honR, htoA.trans htoR, ?_, hwork.trans hgap.symm⟩
      have hnle := span_n_le s.n base.cg s.benchlen h.shape.peg.n_pos h.shape.peg.span
      have hlenG := fieldMul_len s.n s.k s.benchlen base.x
        (fieldCube s.n s.k s.benchlen
          (fieldMul s.n s.k s.benchlen s.gap
            (cubeTimes s.n s.k s.benchlen s.gap s.tally))) hnle
      rw [hbenchA, hbenchR, hgap, hnM, hbM,
        List.take_of_length_le (Nat.le_of_eq hlenG)]
  have hempty : rest.isEmpty = false := by
    cases rest with
    | nil => exact absurd rfl hrest
    | cons _ _ => rfl
  have hPast : s.t0 + 2 * s.tally < s.row.length := by
    have hgrow := red_final_gt s.tally r rest hr hrest
    have hwhole : climbTally s.tally (r :: rest) =
        climbTally base.tally0 (done ++ (r :: rest)) := by
      rw [h.htally0]
      exact climbTally_prefix_rest base.tally0 done (r :: rest)
    have hlt : 2 * s.tally < climbTally base.tally0 (done ++ (r :: rest)) := by
      rw [← hwhole]
      exact hgrow
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hlt s.t0) h.tailFit
  have hseg : RowSeg s'.row s'.t0 s'.tally rest.isEmpty := by
    rw [hempty]
    have hrowS : s'.row =
        rungRow s.row s.fromHole s.parkAt hole s.t0 s.tally 2 false := by
      simp [s', modelRung, hr]
    have hseg0 : RowSeg s.row s.t0 s.tally false := by
      simpa using h.shape.seg
    rw [hrowS, ht0M, htall]
    exact rungRow_open_red_seg s.row s.fromHole s.parkAt hole s.t0 s.tally
      hseg0 h.parkBelow h.holeBelow (Or.inl hF) hPast
  have hpark' : ParkRead bAdd s' rest base := by
    refine
      { ladder0B := by rw [hladA, hcarry.ladder, hladE]; exact h.shape.park.ladder0B
        nrungsB := by rw [hnrA, hcarry.nrungs, hnrE]; exact h.shape.park.nrungsB
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
    · have hL : bAdd.sudo_5Board_7ladder0 = Int.ofNat base.ladder0 := by
        rw [hladA, hcarry.ladder, hladE, h.shape.park.ladder0B, ← ofNat_eq_natCast]
      have hN : bAdd.sudo_5Board_6nrungs = Int.ofNat base.R := by
        rw [hnrA, hcarry.nrungs, hnrE, h.shape.park.nrungsB, ← ofNat_eq_natCast]
      exact climb_holes_refines bAdd base.ladder0 base.R hL hN h.shape.park.l0pos
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
      exact Nat.le_trans
        (Nat.le_trans (Nat.le_of_lt h.parkBelow) (Nat.le_add_right s.t0 (2 * s.tally)))
        (Nat.le_max_right _ _)
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
    · intro hnn
      rw [hfromM] at hnn
      refine ⟨?_, ?_, ?_, ?_⟩
      · have hlt : hole < s.row.length := h.shape.park.holeLt
        rw [← hlenRow] at hlt
        simpa [Int.toNat_ofNat] using hlt
      · have hlt : hole < s.row.length := h.shape.park.holeLt
        rw [h.shape.rowLen] at hlt
        simpa [Int.toNat_ofNat] using hlt
      · rw [hhighM]
        simpa [Int.toNat_ofNat] using
          Nat.le_trans
            (Nat.le_trans (Nat.le_of_lt h.holeBelow) (Nat.le_add_right s.t0 (2 * s.tally)))
            (Nat.le_max_right _ _)
      · have hne : hole ≠ climbAt base.ladder0 base.R (s.ridx + 1) := hStep.2.2
        rw [← hridxM] at hne
        simpa [Int.toNat_ofNat] using hne
    · intro _
      have hlt : s'.parkAt < s'.row.length := by
        have h0 : s.parkAt < s.row.length := h.shape.park.parkLt
        rw [← hparkM, ← hlenRow] at h0
        exact h0
      exact ⟨s'.row[s'.parkAt]'hlt, rfl⟩
    · intro r2 rs hrs
      have hlt0 : climbAt base.ladder0 base.R (s.ridx + 1) < s.row.length := hStep.1
      have ⟨hcol, hnz⟩ := h.shape.park.ladderTail 1 (by simp [hrs]) hlt0
      have hbelow : climbAt base.ladder0 base.R (s.ridx + 1) < s.t0 :=
        climb_below base.ladder0 base.R s.ridx 1 s.t0 h.shape.park.l0pos
          (by omega) h.holeBelow
      have hneP : s.parkAt ≠ climbAt base.ladder0 base.R (s.ridx + 1) :=
        (climbAt_ne_sum base.ladder0 base.R (s.ridx + 1) s.parkAt
          h.shape.park.l0pos (by omega) hParkAt).symm
      have hneH : hole ≠ climbAt base.ladder0 base.R (s.ridx + 1) := hStep.2.2
      have hget := rungRow_red_below s.row s.fromHole s.parkAt hole s.t0 s.tally
        (climbAt base.ladder0 base.R (s.ridx + 1)) hF hneP hneH hbelow hlt0
      have hrowR : s'.row =
          rungRow s.row s.fromHole s.parkAt hole s.t0 s.tally 2 false := by
        simp [s', modelRung, hr]
      have hhead : (r :: rest)[1]'(by simp [hrs]) = r2 := by simp [hrs]
      refine ⟨?_, ?_⟩
      · simpa [hrowR, hridxM, hhead] using hget.trans hcol
      · simpa [hhead] using hnz
    · intro k hk hlt
      have hoff : s.ridx + (1 + k) ≤ base.R := by
        rw [h.idx]
        have hlen := h.kLe
        simp [List.length_append, List.length_cons] at hlen
        omega
      have hlt0 : climbAt base.ladder0 base.R (s.ridx + 1 + k) < s.row.length := by
        rw [← hlenRow, ← hridxM]
        exact hlt
      have hltTail : climbAt base.ladder0 base.R (s.ridx + (1 + k)) < s.row.length := by
        simpa [Nat.add_assoc] using hlt0
      have ⟨hcol, hnz⟩ := h.shape.park.ladderTail (1 + k) (by simp; omega) hltTail
      have hclimb : climbAt base.ladder0 base.R (s.ridx + 1 + k) =
          climbAt base.ladder0 base.R (s.ridx + (1 + k)) := by
        simp [Nat.add_assoc]
      have hcol' :=
        (getElem_congr (c := s.row)
          (i := climbAt base.ladder0 base.R (s.ridx + 1 + k))
          (j := climbAt base.ladder0 base.R (s.ridx + (1 + k)))
          (h := hlt0) hclimb).trans hcol
      have hbelow : climbAt base.ladder0 base.R (s.ridx + 1 + k) < s.t0 := by
        simpa [Nat.add_assoc] using
          (climb_below base.ladder0 base.R s.ridx (1 + k) s.t0 h.shape.park.l0pos hoff
            h.holeBelow)
      have hneP : s.parkAt ≠ climbAt base.ladder0 base.R (s.ridx + 1 + k) :=
        (climbAt_ne_sum base.ladder0 base.R (s.ridx + 1 + k) s.parkAt
          h.shape.park.l0pos (by omega) hParkAt).symm
      have hneH : hole ≠ climbAt base.ladder0 base.R (s.ridx + 1 + k) := by
        intro heq
        have hL : 0 < base.ladder0 := h.shape.park.l0pos
        simp [hole, climbAt] at heq
        omega
      have hget := rungRow_red_below s.row s.fromHole s.parkAt hole s.t0 s.tally
        (climbAt base.ladder0 base.R (s.ridx + 1 + k)) hF hneP hneH hbelow hlt0
      have hrowR : s'.row =
          rungRow s.row s.fromHole s.parkAt hole s.t0 s.tally 2 false := by
        simp [s', modelRung, hr]
      refine ⟨?_, ?_⟩
      · have hixEq : climbAt base.ladder0 base.R (s'.ridx + k) =
            climbAt base.ladder0 base.R (s.ridx + 1 + k) := by
          rw [hridxM]
        have hmove := getElem_congr (c := s'.row)
          (i := climbAt base.ladder0 base.R (s'.ridx + k))
          (j := climbAt base.ladder0 base.R (s.ridx + 1 + k))
          (h := hlt) hixEq
        have hcoll := getElem_congr_coll (c := s'.row)
          (d := rungRow s.row s.fromHole s.parkAt hole s.t0 s.tally 2 false)
          (i := climbAt base.ladder0 base.R (s.ridx + 1 + k))
          (h := by rw [← hixEq]; exact hlt) hrowR
        have hlist := cons_tail r rest k hk
        exact hmove.trans (hcoll.trans ((hget.trans hcol').trans hlist))
      · exact fun hz => hnz ((cons_tail r rest k hk).trans hz)
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
  have hnleG := span_n_le s.n base.cg s.benchlen h.shape.peg.n_pos h.shape.peg.span
  have hgapLen : s'.gap.length = s'.n := by
    rw [hgap, hnM]
    exact fieldMul_len s.n s.k s.benchlen base.x
      (fieldCube s.n s.k s.benchlen
        (fieldMul s.n s.k s.benchlen s.gap
          (cubeTimes s.n s.k s.benchlen s.gap s.tally))) hnleG
  have hpeg : PegRead bAdd s' base := by
    refine
      { opsGt := ?_
        cOps := ?_
        peakS := ?_
        holeM := ?_
        trits := ?_
        top := ?_
        fitRow := ?_
        fitTall := ?_
        fitCtrl := ?_
        n_pos := ?_
        span := ?_
        small := ?_
        n_small := ?_
        fitN := ?_
        fitBn := ?_
        fit3 := ?_ }
    · rw [hδA.opsSize]
      exact h.shape.peg.opsGt
    · have h1 : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size := h.shape.peg.opsGt
      obtain ⟨_, c', _, hc', _⟩ := hδA.ops 1 h1
      refine ⟨c', ?_⟩
      exact (array_get_irrel (h2 := hδA.opsSize ▸ h1)).trans hc'
    · obtain ⟨p, hp⟩ := hcarry.strict
      exact ⟨p, hstrictA.trans hp⟩
    · obtain ⟨hn, hh⟩ := hcarry.hole
      exact ⟨hn, hholeA.trans hh⟩
    · rw [hgap]
      have h3 : 3 * (s.n - 1) < s.benchlen :=
        Nat.lt_of_le_of_lt (Nat.le_add_right _ base.cg) h.shape.peg.span
      have hlenC : (fieldCube s.n s.k s.benchlen
          (fieldMul s.n s.k s.benchlen s.gap
            (cubeTimes s.n s.k s.benchlen s.gap s.tally))).length ≤ s.n := by
        rw [fieldCube, List.length_take]
        exact Nat.min_le_left _ _
      rw [← List.take_of_length_le hlenC]
      exact fieldMul_trits s.n s.k s.benchlen base.x
        (fieldCube s.n s.k s.benchlen
          (fieldMul s.n s.k s.benchlen s.gap
            (cubeTimes s.n s.k s.benchlen s.gap s.tally))) h3 hnleG
    · intro _
      rw [ht0M, htall, hhighM]
      exact Nat.le_trans (open_red_high s.t0 s.tally) (Nat.le_max_right _ _)
    · rw [ht0M, htall]
      exact open_red_row_fit s.t0 s.tally base.control (h.openRoom hge) base.fitControl
    · rw [htall]
      exact (double_index_fit_le (h.openRoom hge) base.fitControl).2.2
    · rw [hctrlM, htall]
      exact hfits.2.2
    · rw [hnM]
      exact h.shape.peg.n_pos
    · rw [hnM, hbM]
      exact h.shape.peg.span
    · rw [hbM]
      exact h.shape.peg.small
    · rw [hnM]
      exact h.shape.peg.n_small
    · rw [hnM]
      exact h.shape.peg.fitN
    · rw [hbM]
      exact h.shape.peg.fitBn
    · exact h.shape.peg.fit3
  have hshape : ClimbShape bAdd s' rest base :=
    shape_refresh h.shape bAdd s' rest hnM hkM hbM hgapLen hseg
      (by rw [hheldA]; exact hcarry.held6)
      (by rw [hhomeA]; exact hcarry.home6)
      (by exact cell_eq_of hheldA hcarry.empty6)
      (by rw [hheldA]; exact hcarry.held7)
      (by intro _; exact cell_eq_of hheldA hcarry.empty5)
      (by intro hOff; rw [hon] at hOff; cases hOff)
      (by rw [hheldA]; exact hcarry.keep.heldLt)
      (by rw [hhomeA]; exact hcarry.keep.homeLt)
      (by exact cell_eq_of hheldA hcarry.keep.held)
      (by exact cell_eq_of hhomeA hcarry.keep.arr)
      (by rw [htierB, hnM]; exact h.shape.tierN)
      (by rw [htierB, hkM]; exact h.shape.tierK)
      (by rw [htierB, hbM]; exact h.shape.tierB)
      (by rw [htierB]; exact h.shape.tierW)
      (by rw [htierB]; exact h.shape.tierH)
      (by rw [htierB]; exact h.shape.tierR)
      (by rw [htierB]; exact h.shape.tierCg)
      (by rw [htierB]; exact h.shape.tierC)
      (by rw [hlenRow]; exact h.shape.rowLen)
      hpark' hpeg (side_arrays hcarry.side hhomeA hheldA)
      (quiet_of hcarry.quiet
        (congrArg Array.size hhomeA) (congrArg Array.size hheldA)
        htierA hixA hmxA)
  have htmax : ∃ tmax : Nat,
      bAdd.sudo_5Board_4cost.sudo_5Costs_9tally_max = (tmax : Int) ∧
        (0 < s'.tally → tmax < 2 * s'.tally) := by
    refine ⟨2 * s.tally + 1, htmaxA, ?_⟩
    intro _
    rw [htall]
    exact open_red_tmax_lt s.tally
  have hTight : RungDeltaTight b bAdd base s.tally :=
    rungTight_cost (rungTight_of_rel hcarry.delta hrel hcarry.opsTight) hmvA hslA hopsA hpkA
  have hK := climbInvKCore_succ h (by simpa [hempty] using hinv) hδA hCap
    (by simpa [hempty] using hshape) h.holeBelow (by simpa [hempty] using htmax) rfl
  exact ⟨bAdd, hprog, by simpa [hempty] using hK, by simpa [hempty] using hTight⟩

/-- Ops after the red cube and the red mul, read off the idle clear. The cube
    writes slot 1 and the mul writes slot 0. -/
theorem red_rung_ops {b bClear bCube bRed : Ecbs.Board} {base : ClimbBudget} {tally : Nat}
    (ht : tally ≤ base.mMax)
    (hs : ClearSlots b.sudo_5Board_4cost.sudo_5Costs_3ops
      bClear.sudo_5Board_4cost.sudo_5Costs_3ops tally)
    (hcost : ∃ (v1 v0 : Nat)
        (h1 : 1 < bClear.sudo_5Board_4cost.sudo_5Costs_3ops.size)
        (h0 : 0 < bCube.sudo_5Board_4cost.sudo_5Costs_3ops.size),
      bClear.sudo_5Board_4cost.sudo_5Costs_3ops[1]'h1 = (v1 : Int) ∧
      bCube.sudo_5Board_4cost.sudo_5Costs_3ops =
        bClear.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨1, h1⟩ (Int.ofNat (v1 + 1)) ∧
      bCube.sudo_5Board_4cost.sudo_5Costs_3ops[0]'h0 = (v0 : Int) ∧
      bRed.sudo_5Board_4cost.sudo_5Costs_3ops =
        bCube.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨0, h0⟩ (Int.ofNat (v0 + 1))) :
    bRed.sudo_5Board_4cost.sudo_5Costs_3ops.size =
      b.sudo_5Board_4cost.sudo_5Costs_3ops.size ∧
    ∀ i (hi : i < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
      (hi' : i < bRed.sudo_5Board_4cost.sudo_5Costs_3ops.size),
      ∃ c c' : Nat,
        b.sudo_5Board_4cost.sudo_5Costs_3ops[i] = (c : Int) ∧
        bRed.sudo_5Board_4cost.sudo_5Costs_3ops[i]'hi' = (c' : Int) ∧
        c' ≤ c + (base.mMax + 3) := by
  obtain ⟨v1, v0, h1, h0, hv1, hcube, hv0, hmul⟩ := hcost
  have hszU : bCube.sudo_5Board_4cost.sudo_5Costs_3ops.size =
      bClear.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [hcube, Array.size_set]
  have hszR : bRed.sudo_5Board_4cost.sudo_5Costs_3ops.size =
      bCube.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [hmul, Array.size_set]
  have hraw := red_ops_on_clear b.sudo_5Board_4cost.sudo_5Costs_3ops
    bClear.sudo_5Board_4cost.sudo_5Costs_3ops
    bCube.sudo_5Board_4cost.sudo_5Costs_3ops
    bRed.sudo_5Board_4cost.sudo_5Costs_3ops
    tally base.mMax v1 v0 ht hs hszU hszR h1 h0 hv1 hcube hv0 hmul
  refine ⟨hraw.1, ?_⟩
  intro i hi hi'
  obtain ⟨c, c', hc, hc', hle⟩ := hraw.2 i hi
  refine ⟨c, c', hc, ?_, hle⟩
  exact (array_get_irrel (h1 := hi') (h2 := by rw [hszR, hszU, hs.size]; exact hi)).trans hc'

/-- Idle non-final red rung is a `ClimbInvK` successor. Costs are the unparked
    red board's costs: park, the double, and the extra peg do not add moves,
    slides, or ops, and they do not change peak. -/
theorem rungDelta_withPark {b b1 : Ecbs.Board} {base : ClimbBudget} {m : Nat}
    (hδ : RungDelta b b1 base m) (row : Array Int) (ctrl fromHole ridx : Int) :
    RungDelta b (withPark b1 row ctrl fromHole ridx) base m := by
  obtain ⟨hmv, hsl, hops, hpk⟩ := withPark_counters b1 row ctrl fromHole ridx
  exact rungDelta_cost hδ hmv hsl hops hpk

/-- `withPark` copies the counters, so a tight delta survives the frame. -/
theorem rungTight_withPark {b b1 : Ecbs.Board} {base : ClimbBudget} {m : Nat}
    (hδ : RungDeltaTight b b1 base m) (row : Array Int) (ctrl fromHole ridx : Int) :
    RungDeltaTight b (withPark b1 row ctrl fromHole ridx) base m := by
  obtain ⟨hmv, hsl, hops, hpk⟩ := withPark_counters b1 row ctrl fromHole ridx
  exact rungTight_cost hδ hmv hsl hops hpk

/-- Unpark then park, as a list. The restored colour is the one that was sitting
    in the parking hole. -/
theorem afterPark_resume (row : List Nat) (src park hole colour prev : Nat)
    (_hsrc : src < row.length) (hpark : park < row.length) (hprev : row[park]'hpark = prev) :
    afterPark row (src : Int) park hole colour =
      (((row.set src prev).set park 0).set park colour).set hole 0 := by
  have hnn : ¬ ((src : Int) < 0) := fun hlt => by
    have : (0 : Int) ≤ (src : Int) := Int.ofNat_nonneg src
    omega
  unfold afterPark
  simp only [hnn, Int.toNat_ofNat, if_false]
  have hopt : (row[park]?).getD 0 = prev := by
    rw [List.getElem?_eq_getElem hpark]
    simp [hprev]
  simp [hopt]

/-- A rung that is already parked unparks, then parks. The row is `afterPark`
    and the counter grows by 4. Later copy and cube steps are still the idle
    ones on this board; this is only the park those steps start from. -/
theorem resume_park_row
    {done rest : List Nat} {r : Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvKCore done (r :: rest) b s base)
    (hge : 0 ≤ s.fromHole) :
    ∃ bPark,
      Ecbs.park_rung b (r : Int) = .ok bPark ∧
      bPark.sudo_5Board_3row =
        embed (afterPark s.row s.fromHole s.parkAt
          (climbAt base.ladder0 base.R s.ridx) r) ∧
      bPark.sudo_5Board_4cost.sudo_5Costs_4ctrl = ((s.ctrl + 4 : Nat) : Int) ∧
      bPark.sudo_5Board_11parked_from =
        ((climbAt base.ladder0 base.R s.ridx : Nat) : Int) ∧
      bPark.sudo_5Board_8rung_idx = ((s.ridx + 1 : Nat) : Int) ∧
      bPark.sudo_5Board_4home = b.sudo_5Board_4home ∧
      bPark.sudo_5Board_4held = b.sudo_5Board_4held ∧
      bPark.sudo_5Board_1t = b.sudo_5Board_1t ∧
      bPark.sudo_5Board_4cost.sudo_5Costs_5moves =
        b.sudo_5Board_4cost.sudo_5Costs_5moves ∧
      bPark.sudo_5Board_4cost.sudo_5Costs_4peak =
        b.sudo_5Board_4cost.sudo_5Costs_4peak ∧
      ∃ (hRowP : s.parkAt < b.sudo_5Board_3row.size)
        (hRowH : climbAt base.ladder0 base.R s.ridx < b.sudo_5Board_3row.size),
        bPark = withPark
          (parkKeepBoard b (climbAt base.ladder0 base.R s.ridx) s.parkAt r
            s.ridx s.ctrl hRowP hRowH)
          (embed (afterPark s.row s.fromHole s.parkAt
            (climbAt base.ladder0 base.R s.ridx) r))
          (((s.ctrl + 4 : Nat) : Int))
          (((climbAt base.ladder0 base.R s.ridx : Nat) : Int))
          (Int.ofNat (s.ridx + 1)) := by
  let hole := climbAt base.ladder0 base.R s.ridx
  let holes := downFrom (base.ladder0 + base.R - 1) base.R
  have hidxN : s.ridx < base.R := by
    rw [h.idx]
    have hk := h.kLe
    simp [List.length_append, List.length_cons] at hk
    omega
  have hAt : s.ridx < holes.length := by
    simpa [holes, downFromLen] using hidxN
  have hHole : holes[s.ridx] = hole := by
    simpa [holes, hole, climbAt] using
      downFromAt (base.ladder0 + base.R - 1) base.R s.ridx hidxN
  have hrung := h.shape.park.nextRung r rest rfl
  have hRowH : hole < b.sudo_5Board_3row.size := by
    rw [h.inv.row, size_embed]; exact h.shape.park.holeLt
  have hRowP : s.parkAt < b.sudo_5Board_3row.size := by
    rw [h.inv.row, size_embed]; exact h.shape.park.parkLt
  have hColour : b.sudo_5Board_3row[hole] = (r : Int) := by
    have harr := arr_get h.inv.row hole hRowH
    have hemb := embed_nat s.row hole h.shape.park.holeLt
    exact harr.trans ((idx_irrel
      (h2 := by rw [size_embed]; exact h.shape.park.holeLt)).trans
      (hemb.trans (congrArg (fun n : Nat => (n : Int)) hrung.1)))
  have hpos : r ≠ 0 := hrung.2
  obtain ⟨prev, hprev⟩ := h.shape.park.parkHeld hge
  have hsrc := h.shape.park.srcOk hge
  have hFrom : b.sudo_5Board_11parked_from = (s.fromHole.toNat : Int) := by
    rw [h.inv.fromP]
    exact h.shape.park.fromNat hge
  have hPrevB : b.sudo_5Board_3row[s.parkAt] = (prev : Int) := by
    have harr := arr_get h.inv.row s.parkAt hRowP
    have hemb := embed_nat s.row s.parkAt h.shape.park.parkLt
    exact harr.trans ((idx_irrel
      (h2 := by rw [size_embed]; exact h.shape.park.parkLt)).trans
      (hemb.trans (congrArg (fun n : Nat => (n : Int)) hprev)))
  have hRowS : s.fromHole.toNat < b.sudo_5Board_3row.size := by
    rw [h.inv.row, size_embed]; exact hsrc.1
  have hNat : s.fromHole = (s.fromHole.toNat : Int) := h.shape.park.fromNat hge
  let src := s.fromHole.toNat
  let bU := unparkedBoard b src s.parkAt prev s.ctrl hRowS hRowP
  let bPark :=
    { bU with
      sudo_5Board_3row :=
        ((bU.sudo_5Board_3row.set
            ⟨s.parkAt, by simp [bU, unparkedBoard, Array.size_set]; exact hRowP⟩ (r : Int)).set
          ⟨hole, by simp [bU, unparkedBoard, Array.size_set]; exact hRowH⟩ (0 : Int))
      sudo_5Board_4cost :=
        { bU.sudo_5Board_4cost with
          sudo_5Costs_4ctrl := Int.ofNat ((s.ctrl + 2) + 2) }
      sudo_5Board_11parked_from := (hole : Int)
      sudo_5Board_8rung_idx := Int.ofNat (s.ridx + 1) }
  have hres := park_rung_resume b holes s.ridx src hole s.parkAt prev r
    s.high base.control s.ctrl h.shape.park.climbH h.inv.ridx hAt hHole hFrom h.inv.park
    hRowS hRowH hRowP hPrevB hColour hpos h.shape.tierC hsrc.2.1 h.shape.park.parkIn
    h.inv.high hsrc.2.2.1 h.shape.park.parkLe h.inv.ctrl h.shape.park.fit2 h.shape.park.fit4
    h.shape.park.parkNe (Ne.symm hsrc.2.2.2) h.shape.park.fitI
  have hrun : Ecbs.park_rung b (r : Int) = .ok bPark := by
    simpa [bPark, bU, src] using hres
  let bKeep := parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH
  have hrowEq : bPark.sudo_5Board_3row =
      embed (afterPark s.row s.fromHole s.parkAt hole r) := by
    have hlist := afterPark_resume s.row src s.parkAt hole r prev
      hsrc.1 h.shape.park.parkLt hprev
    have hfromRow : afterPark s.row s.fromHole s.parkAt hole r =
        afterPark s.row (src : Int) s.parkAt hole r := by
      rw [← hNat]
    rw [hfromRow, hlist]
    apply Array.ext
    · simp [bPark, bU, unparkedBoard, Array.size_set, h.inv.row, size_embed,
        List.length_set]
    · intro j hj1 hj2
      simp [bPark, bU, unparkedBoard, h.inv.row, embed, Array.getElem_set,
        Array.getElem_mk, List.getElem_set, ofNat_eq_natCast, hsrc.1,
        h.shape.park.parkLt, h.shape.park.holeLt]
      by_cases hhj : hole = j
      · simp [hhj]
      · by_cases hpj : s.parkAt = j
        · simp [hhj, hpj]
        · by_cases hsj : src = j
          · simp [hhj, hpj, hsj]
          · simp [hhj, hpj, hsj]
  have hframe : bPark = withPark bKeep
      (embed (afterPark s.row s.fromHole s.parkAt hole r))
      (Int.ofNat ((s.ctrl + 2) + 2))
      (((hole : Nat) : Int))
      (Int.ofNat (s.ridx + 1)) := by
    apply board_ext
    case hrow =>
      rw [hrowEq, withPark_row]
    case hcost =>
      apply cost_ext
      case hctrl =>
        simp [bPark, bU, unparkedBoard, bKeep, parkKeepBoard, withPark]
      all_goals
        simp [bPark, bU, unparkedBoard, bKeep, parkKeepBoard, withPark]
    all_goals
      simp [bPark, bU, unparkedBoard, bKeep, parkKeepBoard, withPark]
  refine ⟨bPark, hrun, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hrowEq
  · dsimp [bPark, bU, unparkedBoard]
  · dsimp [bPark]
  · dsimp [bPark]
  · dsimp [bPark, bU, unparkedBoard]
  · dsimp [bPark, bU, unparkedBoard]
  · dsimp [bPark, bU, unparkedBoard]
  · dsimp [bPark, bU, unparkedBoard]
  · dsimp [bPark, bU, unparkedBoard]
  · refine ⟨hRowP, hRowH, ?_⟩
    have h4 : Int.ofNat ((s.ctrl + 2) + 2) = ((s.ctrl + 4 : Nat) : Int) := by
      apply congrArg Int.ofNat
      omega
    rw [← h4]
    exact hframe

/-- Unpark-then-park is keep-park of the same board, with the restored row and a
    counter two higher. Later `place`, `settle`, `cube`, `mul`, `tally_double`,
    and `tally_add_one` already commute with `withPark`, so a parked rung is that
    transport of the idle rung. -/
theorem resume_park_withPark
    {done rest : List Nat} {r : Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvKCore done (r :: rest) b s base)
    (hge : 0 ≤ s.fromHole) :
    ∃ (bPark bKeep : Ecbs.Board)
      (hRowP : s.parkAt < b.sudo_5Board_3row.size)
      (hRowH : climbAt base.ladder0 base.R s.ridx < b.sudo_5Board_3row.size),
      Ecbs.park_rung b (r : Int) = .ok bPark ∧
      bKeep = parkKeepBoard b (climbAt base.ladder0 base.R s.ridx) s.parkAt r
        s.ridx s.ctrl hRowP hRowH ∧
      bPark = withPark bKeep
        (embed (afterPark s.row s.fromHole s.parkAt
          (climbAt base.ladder0 base.R s.ridx) r))
        (((s.ctrl + 4 : Nat) : Int))
        (((climbAt base.ladder0 base.R s.ridx : Nat) : Int))
        (Int.ofNat (s.ridx + 1)) := by
  obtain ⟨bPark, hpark, _hrow, _hctrl, _hfrom, _hridx, _hhome, _hheld, _htier, _hmv, _hpk,
      hRowP, hRowH, hframe⟩ := resume_park_row h hge
  exact ⟨bPark, _, hRowP, hRowH, hpark, rfl, hframe⟩

/-- Park does not write home or held. The spare stays empty and the gap stays
    held at home 5, so the copy is `place` of the gap, as on an idle rung. -/
theorem resume_copy
    {done rest : List Nat} {r : Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvKCore done (r :: rest) b s base)
    (hM : MoveHeadroom b base.n base.bench base.mMax)
    (hge : 0 ≤ s.fromHole) (_hm : 0 < s.tally) (hT : s.tally ≤ base.mMax)
    (hhome : s.onBench = false) :
    ∃ (bPark bCopy : Ecbs.Board) (moves peak : Nat)
      (h6H : 6 < bPark.sudo_5Board_4home.size)
      (h6D : 6 < bPark.sudo_5Board_4held.size),
      Ecbs.park_rung b (r : Int) = .ok bPark ∧
      Ecbs.copy_band bPark ((6 : Nat) : Int) ((5 : Nat) : Int) false = .ok bCopy ∧
      bCopy = placeBoard bPark 6 h6H h6D s.gap moves peak ∧
      b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int) ∧
      b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int) := by
  obtain ⟨bPark, hpark, _hrow, _hctrl, _hfrom, _hridx, hhomeEq, hheldEq, htierEq, hmvEq, hpkEq,
      _hRowP, _hRowH, _hframe⟩ :=
    resume_park_row h hge
  have hmv := hM.eq
  let mv := hM.mv
  obtain ⟨pk, hpk, _hpkLe⟩ := h.peak
  have h6H : 6 < bPark.sudo_5Board_4home.size := by
    rw [hhomeEq]; exact h.shape.spareH
  have h6D : 6 < bPark.sudo_5Board_4held.size := by
    rw [hheldEq]; exact h.shape.spareD
  have h5H : 5 < bPark.sudo_5Board_4home.size := by
    rw [hhomeEq]; exact h.inv.hG
  have h5D : 5 < bPark.sudo_5Board_4held.size := by
    rw [hheldEq]; exact h.inv.hGs
  have h7 : 7 ≤ bPark.sudo_5Board_4held.size := by
    rw [hheldEq]; exact h.shape.h7
  have hheld5 : bPark.sudo_5Board_4held[5]'h5D = true :=
    cell_eq_of hheldEq (h.inv.gapHome hhome).1
  have harr5 : bPark.sudo_5Board_4home[5]'h5H = embed s.gap :=
    cell_eq_of hhomeEq (h.inv.gapHome hhome).2
  have hempty : bPark.sudo_5Board_4held[6]'h6D = false :=
    cell_eq_of hheldEq h.shape.spareE
  have hn : bPark.sudo_5Board_1t.sudo_4Tier_1n = ((s.gap.length : Nat) : Int) := by
    rw [htierEq, h.shape.gapLen]
    exact h.shape.tierN
  have hmvP : bPark.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int) := hmvEq.trans hmv
  have hpkP : bPark.sudo_5Board_4cost.sudo_5Costs_4peak = (pk : Int) := hpkEq.trans hpk
  have hpegN : pegCount s.gap ≤ base.n := by
    have h1 : pegCount s.gap ≤ s.gap.length := pegCount_le s.gap
    rw [h.shape.gapLen, h.hn] at h1
    exact h1
  have hcopyLe := gap_copy_le_rung base.n base.bench base.mMax s.tally
    (pegCount s.gap) hpegN hT
  have hR1 : done.length + 1 ≤ base.R := by
    have hlenK := h.kLe
    rw [List.length_append, List.length_cons] at hlenK
    omega
  have hfitBig := copy_then_pegs_fit mv
    (rungCharge base.n base.bench base.mMax - 2 * base.n) (pegCount s.gap) 0
    (MoveHeadroom.at hM hmv)
    (Nat.le_trans (Nat.le_add_right (pegCount s.gap) _)
      (gap_copy_room base.n base.bench base.mMax s.tally (pegCount s.gap) hpegN hT))
  have hfit : FitsLen (mv + pegCount s.gap) := by
    simpa using hfitBig
  have hlenFit : FitsLen s.gap.length := by
    rw [h.shape.gapLen]; exact h.shape.peg.fitN
  have hcopy := copy_band_refines bPark 6 5 s.gap mv pk h6H h6D h5H h5D h7
    hheld5 harr5 hempty hn hlenFit hmvP hpkP hfit
  exact ⟨bPark, _, mv, pk, h6H, h6D, hpark, hcopy, rfl, hmv, hpk⟩

/-- `place` writes one home. Marker, bench flag, tier, strict peak, and the
    recorded bench hole stay. -/
theorem place_side (b : Ecbs.Board) (home : Nat)
    (hin : HomeIn b home)
    (xs : List Nat) (moves peak : Nat) :
    (placeBoard b home hin.hH hin.hD xs moves peak).sudo_5Board_9marker_on =
      b.sudo_5Board_9marker_on ∧
    (placeBoard b home hin.hH hin.hD xs moves peak).sudo_5Board_8bench_on =
      b.sudo_5Board_8bench_on ∧
    (placeBoard b home hin.hH hin.hD xs moves peak).sudo_5Board_1t = b.sudo_5Board_1t ∧
    (placeBoard b home hin.hH hin.hD xs moves peak).sudo_5Board_4cost.sudo_5Costs_11peak_strict =
      b.sudo_5Board_4cost.sudo_5Costs_11peak_strict ∧
    (placeBoard b home hin.hH hin.hD xs moves peak).sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole := by
  unfold placeBoard
  dsimp only
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem place_held_src (b : Ecbs.Board) (home : Nat)
    (hin : HomeIn b home)
    (xs : List Nat) (moves peak : Nat)
    (hF : home < (placeBoard b home hin.hH hin.hD xs moves peak).sudo_5Board_4held.size) :
    (placeBoard b home hin.hH hin.hD xs moves peak).sudo_5Board_4held[home] = true := by
  have hEq : (placeBoard b home hin.hH hin.hD xs moves peak).sudo_5Board_4held =
      b.sudo_5Board_4held.set ⟨home, hin.hD⟩ true := by
    unfold placeBoard
    dsimp only
    split <;> rfl
  simpa [Array.getElem_set] using idx_get hEq home hF

theorem place_home_src (b : Ecbs.Board) (home : Nat)
    (hin : HomeIn b home)
    (xs : List Nat) (moves peak : Nat)
    (hF : home < (placeBoard b home hin.hH hin.hD xs moves peak).sudo_5Board_4home.size) :
    (placeBoard b home hin.hH hin.hD xs moves peak).sudo_5Board_4home[home] = embed xs := by
  have hEq : (placeBoard b home hin.hH hin.hD xs moves peak).sudo_5Board_4home =
      b.sudo_5Board_4home.set ⟨home, hin.hH⟩ (embed xs) := by
    unfold placeBoard
    dsimp only
    split <;> rfl
  simpa [Array.getElem_set] using idx_get hEq home hF

/-- The white scan reads the tally segment and returns the board it was given.
    Park writes sit before that segment, so the scan on `withPark` is the idle
    scan with the parked row and counter put back: both sides are the parked
    board, unchanged. -/
theorem list_idx_irrel {α : Type} {xs : List α} {i : Nat} {h1 h2 : i < xs.length} :
    xs[i]'h1 = xs[i]'h2 := by
  have : (⟨i, h1⟩ : Fin xs.length) = ⟨i, h2⟩ := Fin.ext rfl
  simp [this]

theorem get_add_eq {xs : List Nat} {a b j : Nat} (hab : a = b)
    (ha : a + j < xs.length) :
    xs[a + j]'ha = xs[b + j]'(hab ▸ ha) := by
  cases hab
  rfl

theorem list_eq_get {xs ys : List Nat} (h : xs = ys) {i : Nat} (hi : i < xs.length) :
    xs[i]'hi = ys[i]'(h ▸ hi) := by
  cases h
  rfl

theorem board_home_cell {b b' : Ecbs.Board} (h : b = b') (i : Nat)
    (hi : i < b.sudo_5Board_4home.size) :
    b.sudo_5Board_4home[i] = b'.sudo_5Board_4home[i]'(h ▸ hi) := by
  cases h
  rfl

theorem board_held_cell {b b' : Ecbs.Board} (h : b = b') (i : Nat)
    (hi : i < b.sudo_5Board_4held.size) :
    b.sudo_5Board_4held[i] = b'.sudo_5Board_4held[i]'(h ▸ hi) := by
  cases h
  rfl

theorem white_scan_withPark
    (b : Ecbs.Board) (xs xsP : List Nat) (t0 m : Nat)
    (row : Array Int) (ctrl fromHole ridx : Int)
    (hm : 0 < m)
    (hT0 : b.sudo_5Board_6tally0 = (t0 : Int))
    (hRowP : row = embed xsP)
    (hRoom : t0 + m ≤ xs.length) (hRoomP : t0 + m ≤ xsP.length)
    (hAgree : ∀ j (hj : j < m),
      xsP[t0 + j]'(Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj t0) hRoomP) =
        xs[t0 + j]'(Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj t0) hRoom))
    (hWhite : ∀ j (hj : j < m),
      xs[t0 + j]'(Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj t0) hRoom) = 1)
    (hfit : FitsLen (t0 + m)) (hfitM : FitsLen m) :
    SudoRt.runLoopOn (Int.ofNat 0)
        (fuelRange (Int.ofNat 0) (Int.ofNat (m - 1)))
        (whiteStep (withPark b row ctrl fromHole ridx) (Int.ofNat (m - 1)))
        (fun j => .ok (withPark b row ctrl fromHole ridx, j))
        (fun _ => .ok (withPark b row ctrl fromHole ridx, (0 : Int))) =
      .ok (withPark b row ctrl fromHole ridx, Int.ofNat (m - 1)) := by
  have hWhiteP : ∀ j (hj : j < m), xsP[t0 + j]'(by omega) = 1 := by
    intro j hj
    have hA := hAgree j hj
    have hW := hWhite j hj
    have hAp : xsP[t0 + j]'(by omega) =
        xsP[t0 + j]'(Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj t0) hRoomP) :=
      list_idx_irrel
    exact hAp.trans (hA.trans hW)
  exact white_scan_loop_refines (withPark b row ctrl fromHole ridx) xsP t0 m hm
    (by rw [withPark_tally0]; exact hT0)
    (by rw [withPark_row]; exact hRowP)
    hRoomP hWhiteP hfit hfitM

/-- `pegPack_twin` read at the last index: the parked peg board is the idle peg
    board with the painted park row, the parked counter, and the park hole. -/
theorem pegBoard_park (c d : PegCtx) (t : PegTwin c d) :
    pegBoard d c.m =
      withPark (pegBoard c c.m)
        (embed (paintRed d.row0 d.t0 c.m))
        (Int.ofNat (d.ctrl0 + c.m)) t.fromHole t.ridx := by
  have hloop := pegPack_twin c d t c.m c.hm (Nat.le_refl _)
  have hPc := (pegPack_board c c.m c.hm (Nat.le_refl _)).1
  have hD := packEqBoard d c.m c.hm _ hloop
  rw [hPc] at hD
  exact hD

/-- The cube-peg loop on the parked start is the idle loop with that park frame.
    `pegPack_twin` is the step; this only rewrites the loop equality. -/
theorem cube_peg_loop_withPark (c d : PegCtx) (t : PegTwin c d) :
    SudoRt.runLoopOn (Int.ofNat 0, d.b0)
        (fuelRange (Int.ofNat 0) (Int.ofNat (d.m - 1)))
        (cubePegStep d.src (Int.ofNat (d.m - 1)))
        (fun σ => .ok σ)
        (fun r => .ok ((0 : Int), r)) =
      .ok (Int.ofNat (c.m - 1),
        withPark (pegBoard c c.m)
          (embed (paintRed d.row0 d.t0 c.m))
          (Int.ofNat (d.ctrl0 + c.m)) t.fromHole t.ridx) := by
  rw [cube_peg_loop_refines d]
  have hsub : d.m - 1 = c.m - 1 := by rw [t.m]
  have hboard : pegBoard d d.m = pegBoard d c.m := by rw [t.m]
  rw [hsub, hboard, pegBoard_park c d t]

/-- `clear` of a held home copies the park frame. The cleared board is `withPark`
    of the idle clear. -/
theorem clear_withPark
    (b : Ecbs.Board) (row : Array Int) (ctrl fromHole ridx : Int)
    (home : Nat) (xs : List Nat) (moves : Nat)
    (hH : home < b.sudo_5Board_4home.size)
    (hD : home < b.sudo_5Board_4held.size)
    (hheld : b.sudo_5Board_4held[home] = true)
    (harr : b.sudo_5Board_4home[home] = embed xs)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hf : FitsLen xs.length)
    (hfit : FitsLen (moves + pegCount xs)) :
    Ecbs.clear (withPark b row ctrl fromHole ridx) (home : Int) =
      .ok (withPark (clearHeldBoard b home xs moves hH hD) row ctrl fromHole ridx) := by
  let bW := withPark b row ctrl fromHole ridx
  have hHW : home < bW.sudo_5Board_4home.size :=
    withPark_home b row ctrl fromHole ridx ▸ hH
  have hDW : home < bW.sudo_5Board_4held.size :=
    withPark_held b row ctrl fromHole ridx ▸ hD
  have hheldW : bW.sudo_5Board_4held[home] = true := by
    simpa [bW, withPark] using hheld
  have harrW : bW.sudo_5Board_4home[home] = embed xs := by
    simpa [bW, withPark] using harr
  have hmvW : bW.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int) := by
    simpa [bW, withPark] using hmoves
  rw [clear_held_refines bW home xs moves hHW hDW hheldW harrW hmvW hf hfit]
  rw [← clearHeld_withPark b row ctrl fromHole ridx home xs moves ⟨hH, hD⟩]
  rfl

/-- Same cube-peg context, with a replacement row, counter, parked-from hole,
    and rung index. Every field the cube reads is the original one. -/
def pegCtxPark (c : PegCtx) (row0 : List Nat) (ctrl0 : Nat)
    (fromHole ridx : Int)
    (hRoom : c.t0 + c.m ≤ row0.length)
    (hCtrlB : FitsLen (ctrl0 + c.m)) : PegCtx where
  b0 := withPark c.b0 (embed row0) ((ctrl0 : Nat) : Int) fromHole ridx
  src := c.src
  g := c.g
  row0 := row0
  w := c.w
  h := c.h
  r := c.r
  n := c.n
  k := c.k
  bench := c.bench
  cg := c.cg
  moves0 := c.moves0
  slides0 := c.slides0
  hole0 := c.hole0
  peak0 := c.peak0
  peakS0 := c.peakS0
  cOps0 := c.cOps0
  t0 := c.t0
  high := c.high
  control := c.control
  ctrl0 := ctrl0
  m := c.m
  hm := c.hm
  hmk := c.hmk
  hoff := c.hoff
  hops0 := c.hops0
  hop10 := c.hop10
  hbl := c.hbl
  hcg := c.hcg
  hspan := c.hspan
  hF := c.hF
  hHome := c.hHome
  hHF := c.hHF
  hArr := c.hArr
  h7 := c.h7
  hn0 := c.hn0
  hn := c.hn
  hlenx := c.hlenx
  hf := c.hf
  hmoves0 := c.hmoves0
  hpeak0 := c.hpeak0
  hpeakS0 := c.hpeakS0
  hxsT := c.hxsT
  h3 := c.h3
  hw0 := c.hw0
  hh0 := c.hh0
  hrR := c.hrR
  hrP := c.hrP
  hnE := c.hnE
  hkLe := c.hkLe
  hgap := c.hgap
  hwF := c.hwF
  hhF := c.hhF
  hrF := c.hrF
  hkF := c.hkF
  hHole0 := c.hHole0
  hsm := c.hsm
  hnsm := c.hnsm
  hfitB := c.hfitB
  hT0 := c.hT0
  hRow := by rw [withPark_row]
  hRoom := hRoom
  hCtrlN := c.hCtrlN
  hHigh := c.hHigh
  hTop := c.hTop
  hIn := c.hIn
  hCtrl0 := by rw [withPark_ctrl]
  hslides0 := c.hslides0
  hfitRow := c.hfitRow
  hfitM := c.hfitM
  hBudget := c.hBudget
  hSlide := c.hSlide
  hOpsB := c.hOpsB
  hCtrlB := hCtrlB

/-- The parked context is a `PegTwin` of the idle one. -/
def pegTwinPark (c : PegCtx) (row0 : List Nat) (ctrl0 : Nat)
    (fromHole ridx : Int)
    (hRoom : c.t0 + c.m ≤ row0.length)
    (hCtrlB : FitsLen (ctrl0 + c.m)) :
    PegTwin c (pegCtxPark c row0 ctrl0 fromHole ridx hRoom hCtrlB) where
  src := rfl
  g := rfl
  n := rfl
  k := rfl
  bench := rfl
  moves0 := rfl
  slides0 := rfl
  hole0 := rfl
  peak0 := rfl
  peakS0 := rfl
  cOps0 := rfl
  t0 := rfl
  m := rfl
  fromHole := fromHole
  ridx := ridx
  b0 := rfl

/-- Park, copy, the white scan, the cube-peg loop, `mul`, and `clear`, rewritten
    from the six equations. Nothing in the block is unfolded. -/
theorem parked_prefix_rw
    (b bPark bCopy bPeg bMul bClear : Ecbs.Board) (rung m : Nat)
    (hPark : Ecbs.park_rung b (rung : Int) = .ok bPark)
    (hCopy : Ecbs.copy_band bPark ((6 : Nat) : Int) ((5 : Nat) : Int) false = .ok bCopy)
    (hScan : SudoRt.runLoopOn (Int.ofNat 0)
        (fuelRange (Int.ofNat 0) (Int.ofNat (m - 1)))
        (whiteStep bCopy (Int.ofNat (m - 1)))
        (fun j => .ok (bCopy, j))
        (fun _ => .ok (bCopy, (0 : Int))) = .ok (bCopy, Int.ofNat (m - 1)))
    (hPeg : SudoRt.runLoopOn (Int.ofNat 0, bCopy)
        (fuelRange (Int.ofNat 0) (Int.ofNat (m - 1)))
        (cubePegStep 6 (Int.ofNat (m - 1)))
        (fun σ => .ok σ)
        (fun r => .ok ((0 : Int), r)) = .ok (Int.ofNat (m - 1), bPeg))
    (hMul : Ecbs.mul bPeg (5 : Int) (5 : Int) (6 : Int) false false false = .ok bMul)
    (hClear : Ecbs.clear bMul (5 : Int) = .ok bClear) :
    (do
        let b ← Ecbs.park_rung b (rung : Int)
        let b ← Ecbs.copy_band b ((6 : Nat) : Int) ((5 : Nat) : Int) false
        let _ ← SudoRt.runLoopOn (Int.ofNat 0)
            (fuelRange (Int.ofNat 0) (Int.ofNat (m - 1)))
            (whiteStep b (Int.ofNat (m - 1)))
            (fun j => .ok (b, j))
            (fun _ => .ok (b, (0 : Int)))
        let out ← SudoRt.runLoopOn (Int.ofNat 0, b)
            (fuelRange (Int.ofNat 0) (Int.ofNat (m - 1)))
            (cubePegStep 6 (Int.ofNat (m - 1)))
            (fun σ => .ok σ)
            (fun r => .ok ((0 : Int), r))
        let b := out.2
        let b ← Ecbs.mul b (5 : Int) (5 : Int) (6 : Int) false false false
        Ecbs.clear b (5 : Int)) = .ok bClear := by
  rw [hPark, ok_bind, hCopy, ok_bind, hScan, ok_bind, hPeg, ok_bind]
  dsimp only
  rw [hMul, ok_bind, hClear]

/-- Park, copy, white scan, and the cube-peg loop, then `mul` and `clear`.
    The scan and the loop are the idle ones under `withPark`. `mul` and `clear`
    are the existing park transports, passed in as the two equations they
    return. The block is only `rw`. -/
theorem parked_clear_transport
    (b bPark bCopy : Ecbs.Board) (rung : Nat)
    (c : PegCtx) (xs row0 : List Nat) (ctrl0 : Nat) (fromHole ridx : Int)
    (hPark : Ecbs.park_rung b (rung : Int) = .ok bPark)
    (hCopy : Ecbs.copy_band bPark ((6 : Nat) : Int) ((5 : Nat) : Int) false = .ok bCopy)
    (hFrame : bCopy =
      withPark c.b0 (embed row0) ((ctrl0 : Nat) : Int) fromHole ridx)
    (hRoom0 : c.t0 + c.m ≤ row0.length)
    (hCtrlB : FitsLen (ctrl0 + c.m))
    (hsrc : c.src = 6)
    (hT0 : c.b0.sudo_5Board_6tally0 = (c.t0 : Int))
    (_hRowIdle : c.b0.sudo_5Board_3row = embed xs)
    (hRoom : c.t0 + c.m ≤ xs.length)
    (hAgree : ∀ j (hj : j < c.m),
      row0[c.t0 + j]'(Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj c.t0) hRoom0) =
        xs[c.t0 + j]'(Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj c.t0) hRoom))
    (hWhite : ∀ j (hj : j < c.m),
      xs[c.t0 + j]'(Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj c.t0) hRoom) = 1)
    (bMul bClear : Ecbs.Board)
    (hMul : Ecbs.mul
        (withPark (pegBoard c c.m)
          (embed (paintRed row0 c.t0 c.m))
          (Int.ofNat (ctrl0 + c.m)) fromHole ridx)
        (5 : Int) (5 : Int) (6 : Int) false false false = .ok bMul)
    (hClear : Ecbs.clear bMul (5 : Int) = .ok bClear) :
    (do
        let b ← Ecbs.park_rung b (rung : Int)
        let b ← Ecbs.copy_band b ((6 : Nat) : Int) ((5 : Nat) : Int) false
        let _ ← SudoRt.runLoopOn (Int.ofNat 0)
            (fuelRange (Int.ofNat 0) (Int.ofNat (c.m - 1)))
            (whiteStep b (Int.ofNat (c.m - 1)))
            (fun j => .ok (b, j))
            (fun _ => .ok (b, (0 : Int)))
        let out ← SudoRt.runLoopOn (Int.ofNat 0, b)
            (fuelRange (Int.ofNat 0) (Int.ofNat (c.m - 1)))
            (cubePegStep 6 (Int.ofNat (c.m - 1)))
            (fun σ => .ok σ)
            (fun r => .ok ((0 : Int), r))
        let b := out.2
        let b ← Ecbs.mul b (5 : Int) (5 : Int) (6 : Int) false false false
        Ecbs.clear b (5 : Int)) = .ok bClear := by
  let d := pegCtxPark c row0 ctrl0 fromHole ridx hRoom0 hCtrlB
  let t := pegTwinPark c row0 ctrl0 fromHole ridx hRoom0 hCtrlB
  have hScan0 := white_scan_withPark c.b0 xs row0 c.t0 c.m
    (embed row0) ((ctrl0 : Nat) : Int) fromHole ridx
    c.hm hT0 rfl hRoom hRoom0 hAgree hWhite c.hfitRow c.hfitM
  have hScan : SudoRt.runLoopOn (Int.ofNat 0)
      (fuelRange (Int.ofNat 0) (Int.ofNat (c.m - 1)))
      (whiteStep bCopy (Int.ofNat (c.m - 1)))
      (fun j => .ok (bCopy, j))
      (fun _ => .ok (bCopy, (0 : Int))) =
      .ok (bCopy, Int.ofNat (c.m - 1)) := by
    simpa [hFrame] using hScan0
  have hPeg0 := cube_peg_loop_withPark c d t
  have hd0 : d.b0 = bCopy := by
    unfold d pegCtxPark
    exact hFrame.symm
  have hsrcD : d.src = 6 := by
    unfold d pegCtxPark
    exact hsrc
  have hmD : d.m = c.m := by
    unfold d pegCtxPark
    rfl
  have hrowD : d.row0 = row0 := by
    unfold d pegCtxPark
    rfl
  have ht0D : d.t0 = c.t0 := by
    unfold d pegCtxPark
    rfl
  have hctrlD : d.ctrl0 = ctrl0 := by
    unfold d pegCtxPark
    rfl
  have hfromT : t.fromHole = fromHole := by
    unfold t pegTwinPark
    rfl
  have hridxT : t.ridx = ridx := by
    unfold t pegTwinPark
    rfl
  rw [hd0, hsrcD, hmD, hrowD, ht0D, hctrlD, hfromT, hridxT] at hPeg0
  exact parked_prefix_rw b bPark bCopy
    (withPark (pegBoard c c.m)
      (embed (paintRed row0 c.t0 c.m))
      (Int.ofNat (ctrl0 + c.m)) fromHole ridx)
    bMul bClear rung c.m hPark hCopy hScan hPeg0 hMul hClear

theorem withTally_id (b : Ecbs.Board) :
    withTally b b.sudo_5Board_3row b.sudo_5Board_9tally_len
      b.sudo_5Board_4cost.sudo_5Costs_4ctrl
      b.sudo_5Board_4cost.sudo_5Costs_15control_highest
      b.sudo_5Board_4cost.sudo_5Costs_9tally_max = b := by
  apply board_ext
  case hcost =>
    apply cost_ext
    all_goals rfl
  all_goals rfl

/-- Idle final red rung: the clear, then one spare cube onto the gap and the mul
    by the input. No tally double and no extra peg. The rung delta is the clear's
    delta plus that cube (ops slot 1) and that mul (ops slot 0). -/
theorem red_final_k
    {done : List Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvKCore done [2] b s base)
    (hM : MoveHeadroom b base.n base.bench base.mMax)
    (hS : SlideHeadroom b base.n base.mMax)
    (hF : s.fromHole < 0) (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax)
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
      ClimbInvKCore (done ++ [2]) [] b'
        (modelRung s base.x 2 (climbAt base.ladder0 base.R s.ridx) true) base ∧
      RungDeltaTight b b' base s.tally := by
  obtain ⟨bClearP, bClearU, bCube0, bRed0, hrun, hClearEq, hlenC, _ht0C, _hrowC,
      _hctrlN, hhighC, _hctrlC, hmaxC, ht0Red, _htierRed, hcubeBoth, hmulBoth,
      hrel, honR, htoR, _hlenR, hbenchR, hδ, hslots, hladE, hnrE, hparkE,
      _ht0E, _hmarkE, htierE, _htmaxE, hcubeU, hredU, hbonE, htoE, hbenchE,
      _h5H, _h5D, _h6H, _h6D, _h7E, _h5f, _h6f, _hkeep, hopsE, _hc1E, _hpkSE, _hholeE,
      _htrits, hpieceM, hpieceS, hside, hquiet⟩ :=
    red_open_view h hM hS hF hm hT hhome hxLen hxT
  have hpack :=
    red_unparked_delta h hM hS
      hm hT hhome hxLen hxT
      bClearP bClearU bCube0 bRed0
      (embed (paintRed (afterPark s.row (-1) s.parkAt
        (climbAt base.ladder0 base.R s.ridx) 2) s.t0 s.tally))
      (((s.ctrl + 2 + s.tally : Nat) : Int))
      (((climbAt base.ladder0 base.R s.ridx : Nat) : Int))
      (Int.ofNat (s.ridx + 1))
      hClearEq hδ hslots _hmarkE htierE hcubeU hredU hrel
      hbonE htoE hbenchE _h5H _h5D _h6H _h6D _h7E _h5f _h6f _hkeep hopsE _hc1E
      _hpkSE _hholeE _htrits hpieceM hpieceS hside hquiet
  let hole := climbAt base.ladder0 base.R s.ridx
  let rowU := bClearU.sudo_5Board_3row
  let lenU := bClearU.sudo_5Board_9tally_len
  let ctrlU := bClearU.sudo_5Board_4cost.sudo_5Costs_4ctrl
  let highU := bClearU.sudo_5Board_4cost.sudo_5Costs_15control_highest
  let maxU := bClearU.sudo_5Board_4cost.sudo_5Costs_9tally_max
  let rowRed := embed (paintRed (afterPark s.row (-1) s.parkAt hole 2) s.t0 s.tally)
  let ctrlRed := ((s.ctrl + 2 + s.tally : Nat) : Int)
  let fromH := ((hole : Nat) : Int)
  let ridxH := Int.ofNat (s.ridx + 1)
  have hcube0 := hcubeBoth rowU rowRed lenU highU maxU ctrlU ctrlRed fromH ridxH
  have hid : withTally bClearU rowU lenU ctrlU highU maxU = bClearU := withTally_id bClearU
  rw [hid] at hcube0
  have hClearEq' : bClearP = withPark bClearU rowRed ctrlRed fromH ridxH := by
    simpa [rowRed, ctrlRed, fromH, ridxH, hole] using hClearEq
  rw [← hClearEq'] at hcube0
  have hmul0 := hmulBoth rowU rowRed lenU highU maxU ctrlU ctrlRed fromH ridxH
  let b' := withPark (withTally bRed0 rowU lenU ctrlU highU maxU) rowRed ctrlRed fromH ridxH
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
    rw [hrun, ok_bind, hcube0, ok_bind]
    exact hmul0
  have hδR : RungDelta b b' base s.tally :=
    rungDelta_cost hpack.delta
      (by rw [withPark_moves, withTally_moves])
      (by rw [withPark_slides, withTally_slides])
      (by rw [withPark_ops, withTally_ops])
      (by rw [withPark_peak, withTally_peak])
  have hTight : RungDeltaTight b b' base s.tally :=
    rungTight_cost (rungTight_of_rel hpack.delta hrel hpack.opsTight)
      (by rw [withPark_moves, withTally_moves])
      (by rw [withPark_slides, withTally_slides])
      (by rw [withPark_ops, withTally_ops])
      (by rw [withPark_peak, withTally_peak])
  let s' := modelRung s base.x 2 hole true
  have hM := model_final_red s base.x hole hF
  obtain ⟨hgap, htall, _hon, hwork, hctrlM, hhighM, hrowM, hfromM, hridxM, _ht0M,
      _hparkM⟩ := hM
  have hIdle : s.fromHole = -1 := h.shape.park.fromIdle hF
  have hidx : s.ridx < base.R := by
    rw [h.idx]
    have hk := h.kLe
    simp [List.length_append] at hk
    omega
  have hlenRow : s'.row.length = s.row.length := by
    rw [hrowM, paintRed_length, afterPark_length]
  have hStep := successor_hole base.ladder0 base.R s.ridx s.parkAt s.row.length
    h.shape.park.l0pos hidx hParkAt h.shape.park.holeLt
  have hhomeB : b'.sudo_5Board_4home = bRed0.sudo_5Board_4home := by
    rw [withPark_home, withTally_home]
  have hheldB : b'.sudo_5Board_4held = bRed0.sudo_5Board_4held := by
    rw [withPark_held, withTally_held]
  have hinv : ClimbInv b' s' := by
    refine
      { hG := ?_
        hGs := ?_
        marker := ?_
        len := ?_
        ctrl := ?_
        high := ?_
        t0 := ?_
        row := ?_
        park := ?_
        fromP := ?_
        ridx := ?_
        gapHome := ?_
        gapBench := ?_ }
    · rw [hhomeB]
      exact Nat.lt_trans (by decide : (5 : Nat) < 6) hpack.home6
    · rw [hheldB]
      exact Nat.lt_trans (by decide : (5 : Nat) < 6) hpack.held6
    · rw [withPark_marker]
      simpa [withTally] using hpack.marker
    · rw [withPark_len, withTally_len]
      unfold lenU
      rw [hlenC, htall]
    · rw [withPark_ctrl]
      unfold ctrlRed
      rw [hctrlM]
    · rw [withPark_high, withTally_high]
      unfold highU
      rw [hhighC, hhighM]
    · rw [withPark_tally0]
      simp only [withTally]
      rw [ht0Red, _ht0M]
    · rw [withPark_row, hrowM, hIdle]
    · have hpB : b'.sudo_5Board_9park_hole = bRed0.sudo_5Board_9park_hole := by
        rw [withPark_park]
        rfl
      rw [hpB, hpack.park, hparkE, _hparkM]
    · rw [withPark_from]
      unfold fromH
      rw [hfromM]
    · rw [withPark_ridx]
      unfold ridxH
      rw [hridxM]
      exact (ofNat_eq_natCast _).symm
    · intro hOff
      simp [s', modelRung] at hOff
    · intro _
      refine ⟨?_, ?_, ?_, rfl⟩
      · rw [withPark_on]
        simpa [withTally] using honR
      · rw [withPark_to]
        simpa [withTally] using htoR
      · rw [withPark_bench, withTally_bench, hbenchR, hgap]
        have hnle : s.n ≤ s.benchlen :=
          span_n_le s.n base.cg s.benchlen h.shape.peg.n_pos h.shape.peg.span
        have hlenG : s'.gap.length = s.n := by
          rw [hgap]
          exact fieldMul_len s.n s.k s.benchlen base.x
            (fieldCube s.n s.k s.benchlen
              (fieldMul s.n s.k s.benchlen s.gap
                (cubeTimes s.n s.k s.benchlen s.gap s.tally))) hnle
        have hn' : s'.n = s.n := rfl
        have hb' : s'.benchlen = s.benchlen := rfl
        have htake :
            (fieldMul s.n s.k s.benchlen base.x
              (fieldCube s.n s.k s.benchlen
                (fieldMul s.n s.k s.benchlen s.gap
                  (cubeTimes s.n s.k s.benchlen s.gap s.tally)))).take s.n =
              fieldMul s.n s.k s.benchlen base.x
                (fieldCube s.n s.k s.benchlen
                  (fieldMul s.n s.k s.benchlen s.gap
                    (cubeTimes s.n s.k s.benchlen s.gap s.tally))) := by
          apply List.take_of_length_le
          have hlen := hlenG
          rw [hgap] at hlen
          exact Nat.le_of_eq hlen
        rw [hn', hb', htake]
  have hseg : RowSeg s'.row s'.t0 s'.tally true := by
    have hred := rungRow_final_seg s.row s.fromHole s.parkAt hole s.t0 s.tally 2
      h.shape.seg h.parkBelow h.holeBelow (Or.inl hF)
    have hEq : s'.row =
        rungRow s.row s.fromHole s.parkAt hole s.t0 s.tally 2 true := by
      rw [hrowM, rungRow, afterTally]
      simp
    simpa [hEq, s'] using hred
  have hdone : done.length + 1 ≤ base.R := by
    have hk := h.kLe
    simp [List.length_append] at hk
    exact hk
  have hfits := final_white_ctrl_fit s.ctrl s.tally base.ctrl0 done.length base.R
    base.mMax h.ctrlLe hT hdone base.fitCtrl
  have hpark' : ParkRead b' s' [] base := by
    refine
      { ladder0B := ?_
        nrungsB := ?_
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
    · rw [withPark_ladder]
      simp only [withTally]
      rw [hpack.ladder, hladE]
      exact h.shape.park.ladder0B
    · rw [withPark_nrungs]
      simp only [withTally]
      rw [hpack.nrungs, hnrE]
      exact h.shape.park.nrungsB
    · have hL : b'.sudo_5Board_7ladder0 = Int.ofNat base.ladder0 := by
        rw [withPark_ladder]
        simp only [withTally]
        rw [hpack.ladder, hladE, h.shape.park.ladder0B]
        exact (ofNat_eq_natCast _).symm
      have hN : b'.sudo_5Board_6nrungs = Int.ofNat base.R := by
        rw [withPark_nrungs]
        simp only [withTally]
        rw [hpack.nrungs, hnrE, h.shape.park.nrungsB]
        exact (ofNat_eq_natCast _).symm
      exact climb_holes_refines b' base.ladder0 base.R hL hN h.shape.park.l0pos
        h.shape.park.fitL0 h.shape.park.fitLR
    · have hlt : climbAt base.ladder0 base.R (s.ridx + 1) < s.row.length := hStep.1
      rw [← hridxM, ← hlenRow] at hlt
      exact hlt
    · have hlt : s.parkAt < s.row.length := h.shape.park.parkLt
      rw [← hlenRow] at hlt
      exact hlt
    · have hne : climbAt base.ladder0 base.R (s.ridx + 1) ≠ s.parkAt := hStep.2.1
      rw [← hridxM] at hne
      exact hne
    · rw [hhighM]
      exact h.shape.park.parkLe
    · exact h.shape.park.parkIn
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
    · intro _hnn
      rw [hfromM]
      rfl
    · intro hnn
      rw [hfromM] at hnn
      refine ⟨?_, ?_, ?_, ?_⟩
      · have hlt : hole < s.row.length := h.shape.park.holeLt
        rw [← hlenRow] at hlt
        simpa [Int.toNat_ofNat] using hlt
      · have hlt : hole < s.row.length := h.shape.park.holeLt
        rw [h.shape.rowLen] at hlt
        simpa [Int.toNat_ofNat] using hlt
      · have hle : hole ≤ s.high := by
          have hhi : hole < s.t0 := h.holeBelow
          have htop : s.t0 + s.tally - 1 ≤ s.high := by
            rw [h.highTop]
            exact Nat.le_max_right _ _
          omega
        rw [hhighM]
        simpa [Int.toNat_ofNat] using hle
      · have hne : hole ≠ climbAt base.ladder0 base.R (s.ridx + 1) := hStep.2.2
        rw [← hridxM] at hne
        simpa [Int.toNat_ofNat] using hne
    · intro _
      have hlt : s'.parkAt < s'.row.length := by
        have h0 : s.parkAt < s.row.length := h.shape.park.parkLt
        rw [← hlenRow] at h0
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
    rw [withPark_ops, withTally_ops, hpack.delta.opsSize, ← hδ.opsSize]
    exact hopsE
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
        n_pos := ?_
        span := ?_
        small := ?_
        n_small := ?_
        fitN := ?_
        fitBn := ?_
        fit3 := ?_ }
    · have hi : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
        rw [← hδ.opsSize]
        exact hopsE
      obtain ⟨_, c', _, hc', _⟩ := hpack.delta.ops 1 hi
      refine ⟨c', ?_⟩
      have hOpsEq : b'.sudo_5Board_4cost.sudo_5Costs_3ops =
          bRed0.sudo_5Board_4cost.sudo_5Costs_3ops := by
        rw [withPark_ops, withTally_ops]
      exact (arr_get hOpsEq 1 hopsB).trans hc'
    · obtain ⟨p, hp⟩ := hpack.strict
      refine ⟨p, ?_⟩
      rw [withPark_strict]
      simpa [withTally] using hp
    · obtain ⟨hn0, hh⟩ := hpack.hole
      refine ⟨hn0, ?_⟩
      rw [withPark_hole]
      simpa [withTally] using hh
    · have hspan3 : 3 * (s.n - 1) < s.benchlen := by
        have hs := h.shape.peg.span
        omega
      have hnle : s.n ≤ s.benchlen := by
        have hs := h.shape.peg.span
        omega
      have htri := fieldMul_trits s.n s.k s.benchlen base.x
        (fieldCube s.n s.k s.benchlen
          (fieldMul s.n s.k s.benchlen s.gap
            (cubeTimes s.n s.k s.benchlen s.gap s.tally))) hspan3 hnle
      simpa [hgap, fieldCube, List.take_take] using htri
    · intro hpos
      rw [_ht0M, htall, hhighM]
      rw [h.highTop]
      exact Nat.le_max_right _ _
    · rw [htall]
      exact h.shape.peg.fitRow
    · rw [htall]
      exact h.shape.peg.fitTall
    · rw [hctrlM, htall]
      exact hfits.2.2
    · exact h.shape.peg.n_pos
    · exact h.shape.peg.span
    · exact h.shape.peg.small
    · exact h.shape.peg.n_small
    · exact h.shape.peg.fitN
    · exact h.shape.peg.fitBn
    · exact h.shape.peg.fit3
  have h7' : 7 ≤ b'.sudo_5Board_4held.size := by
    rw [hheldB]
    exact hpack.held7
  have hshape : ClimbShape b' s' [] base :=
    shape_refresh h.shape b' s' [] rfl rfl rfl
      (by
        rw [hgap]
        have hnle : s.n ≤ s.benchlen := by
          have hs := h.shape.peg.span
          omega
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
      h7'
      (by
        intro _
        exact cell_eq_of hheldB hpack.empty5)
      (by
        intro hOff
        simp [s', modelRung] at hOff)
      (by rw [hheldB]; exact hpack.keep.heldLt)
      (by rw [hhomeB]; exact hpack.keep.homeLt)
      (by exact cell_eq_of hheldB hpack.keep.held)
      (by exact cell_eq_of hhomeB hpack.keep.arr)
      (by rw [withPark_tier]; simpa [withTally, hpack.tier, htierE] using h.shape.tierN)
      (by rw [withPark_tier]; simpa [withTally, hpack.tier, htierE] using h.shape.tierK)
      (by rw [withPark_tier]; simpa [withTally, hpack.tier, htierE] using h.shape.tierB)
      (by rw [withPark_tier]; simpa [withTally, hpack.tier, htierE] using h.shape.tierW)
      (by rw [withPark_tier]; simpa [withTally, hpack.tier, htierE] using h.shape.tierH)
      (by rw [withPark_tier]; simpa [withTally, hpack.tier, htierE] using h.shape.tierR)
      (by rw [withPark_tier]; simpa [withTally, hpack.tier, htierE] using h.shape.tierCg)
      (by rw [withPark_tier]; simpa [withTally, hpack.tier, htierE] using h.shape.tierC)
      (by rw [hlenRow]; exact h.shape.rowLen)
      hpark' hpeg' (side_arrays hpack.side hhomeB hheldB)
      (quiet_of hpack.quiet
        (congrArg Array.size hhomeB) (congrArg Array.size hheldB)
        rfl rfl rfl)
  have htmax : ∃ tmax : Nat,
      b'.sudo_5Board_4cost.sudo_5Costs_9tally_max = (tmax : Int) ∧
        (0 < s'.tally → tmax < 2 * s'.tally) := by
    obtain ⟨tmax, htm, hnote⟩ := h.tmaxLt
    refine ⟨tmax, ?_, ?_⟩
    · rw [withPark_tmax, withTally_max]
      unfold maxU
      rw [hmaxC, htm]
    · intro hpos
      have hlt := hnote (by rw [← htall]; exact hpos)
      rw [htall]
      exact hlt
  have hK := climbInvKCore_succ h hinv hδR hCap hshape h.holeBelow htmax rfl
  exact ⟨b', hprog, hK, hTight⟩


end EcbsLink2.Link2
