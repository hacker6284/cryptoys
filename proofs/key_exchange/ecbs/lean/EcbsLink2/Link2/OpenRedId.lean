/-
  One view of the three big obtains for a parked non-final red rung.
  The caller sees only the boards and the equations, not the proof terms.
-/
import EcbsLink2.Link2.ParkFrame

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- The parked clear, the idle clear, and the unparked cube and mul, identified
    by the copy-mul-clear determinism chain. -/
structure RedOpenId
    (done rs : List Nat) (r : Nat) (b : Ecbs.Board)
    (s : ClimbModel) (base : ClimbBudget) : Type where
  bClearU : Ecbs.Board
  bCubeP : Ecbs.Board
  bRedP : Ecbs.Board
  bClearG : Ecbs.Board
  bIdle : Ecbs.Board
  bClearC : Ecbs.Board
  bCubeC : Ecbs.Board
  bRedC : Ecbs.Board
  hclearProg :
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
        Ecbs.clear b (5 : Int)) =
      .ok (withPark bClearU
        (embed (paintRed (afterPark s.row s.fromHole s.parkAt
          (climbAt base.ladder0 base.R s.ridx) r) s.t0 s.tally))
        (Int.ofNat (s.ctrl + 4 + s.tally))
        (((climbAt base.ladder0 base.R s.ridx : Nat) : Int))
        (Int.ofNat (s.ridx + 1)))
  hcubeU : Ecbs.cube bClearU ((6 : Nat) : Int) ((5 : Nat) : Int) = .ok bCubeP
  hredU : Ecbs.mul bCubeP ((5 : Nat) : Int) (base.xHome : Int) ((6 : Nat) : Int)
      false false false = .ok bRedP
  hrelP : ∃ mvE mvR slE slR : Nat,
    b.sudo_5Board_4cost.sudo_5Costs_5moves = (mvE : Int) ∧
    bRedP.sudo_5Board_4cost.sudo_5Costs_5moves = (mvR : Int) ∧
    mvR ≤ mvE + rungCharge base.n base.bench s.tally ∧
    b.sudo_5Board_4cost.sudo_5Costs_6slides = (slE : Int) ∧
    bRedP.sudo_5Board_4cost.sudo_5Costs_6slides = (slR : Int) ∧
    slR ≤ slE + rungSlideCharge base.n s.tally
  hrun :
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
        Ecbs.clear b (5 : Int)) = .ok bClearG
  hframe : bClearG = withPark bIdle
      (embed (paintRed (afterPark s.row s.fromHole s.parkAt
        (climbAt base.ladder0 base.R s.ridx) r) s.t0 s.tally))
      (((s.ctrl + 4 + s.tally : Nat) : Int))
      (((climbAt base.ladder0 base.R s.ridx : Nat) : Int))
      (Int.ofNat (s.ridx + 1))
  hbenchE : bIdle.sudo_5Board_5bench =
      embed (fieldMul s.n s.k s.benchlen s.gap
        (cubeTimes s.n s.k s.benchlen s.gap s.tally) ++
        List.replicate (s.benchlen - s.n) 0)
  hbonE : bIdle.sudo_5Board_8bench_on = true
  htoE : bIdle.sudo_5Board_8bench_to = (5 : Int)
  hmarkE : bIdle.sudo_5Board_9marker_on = false
  hlenE : bIdle.sudo_5Board_9tally_len = (s.tally : Int)
  ht0E : bIdle.sudo_5Board_6tally0 = (s.t0 : Int)
  hparkE : bIdle.sudo_5Board_9park_hole = (s.parkAt : Int)
  hhighE : bIdle.sudo_5Board_4cost.sudo_5Costs_15control_highest = (s.high : Int)
  htierE : bIdle.sudo_5Board_1t = b.sudo_5Board_1t
  hladE : bIdle.sudo_5Board_7ladder0 = b.sudo_5Board_7ladder0
  hnrE : bIdle.sudo_5Board_6nrungs = b.sudo_5Board_6nrungs
  htmaxE : bIdle.sudo_5Board_4cost.sudo_5Costs_9tally_max =
    b.sudo_5Board_4cost.sudo_5Costs_9tally_max
  h5H : 5 < bIdle.sudo_5Board_4home.size
  h5D : 5 < bIdle.sudo_5Board_4held.size
  h6H : 6 < bIdle.sudo_5Board_4home.size
  h6D : 6 < bIdle.sudo_5Board_4held.size
  h7E : 7 ≤ bIdle.sudo_5Board_4held.size
  h5f : ∀ h5 : 5 < bIdle.sudo_5Board_4held.size, bIdle.sudo_5Board_4held[5] = false
  h6f : ∀ h6 : 6 < bIdle.sudo_5Board_4held.size, bIdle.sudo_5Board_4held[6] = false
  hkeep : CellKeep bIdle base.xHome base.x
  hps : ∃ ps : Nat, bIdle.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (ps : Int)
  hhn : ∃ hn : Nat, bIdle.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = (hn : Int)
  hrowIdle : bIdle.sudo_5Board_3row =
    embed (paintRed (afterPark s.row (-1) s.parkAt
      (climbAt base.ladder0 base.R s.ridx) r) s.t0 s.tally)
  hctrlIdle : bIdle.sudo_5Board_4cost.sudo_5Costs_4ctrl =
    ((s.ctrl + 2 + s.tally : Nat) : Int)
  hδ : RungDelta b bClearG base s.tally
  hslots : ClearSlots b.sudo_5Board_4cost.sudo_5Costs_3ops
    bClearG.sudo_5Board_4cost.sudo_5Costs_3ops s.tally
  hpieceM : ∃ mv mvC : Nat,
    b.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int) ∧
    bClearG.sudo_5Board_4cost.sudo_5Costs_5moves = (mvC : Int) ∧
    mvC ≤ mv + base.n + s.tally * pegCharge base.n base.bench +
      mulCharge base.n base.bench + base.n
  hpieceS : ∃ sl slC : Nat,
    b.sudo_5Board_4cost.sudo_5Costs_6slides = (sl : Int) ∧
    bClearG.sudo_5Board_4cost.sudo_5Costs_6slides = (slC : Int) ∧
    slC ≤ sl + s.tally * (2 * base.n) + 2 * base.n
  hclearSame : bClearC = bClearU
  hredSame : bRedC = bRedP
  hcubeBoth : ∀ (rowD rowP : Array Int) (len high tmax ctrlD ctrlP fromHole ridx : Int),
    Ecbs.cube (withPark (withTally bClearC rowD len ctrlD high tmax) rowP ctrlP fromHole ridx)
        ((6 : Nat) : Int) ((5 : Nat) : Int) =
      .ok (withPark (withTally bCubeC rowD len ctrlD high tmax) rowP ctrlP fromHole ridx)
  hmulBoth : ∀ (rowD rowP : Array Int) (len high tmax ctrlD ctrlP fromHole ridx : Int),
    Ecbs.mul (withPark (withTally bCubeC rowD len ctrlD high tmax) rowP ctrlP fromHole ridx)
        ((5 : Nat) : Int) (base.xHome : Int) ((6 : Nat) : Int) false false false =
      .ok (withPark (withTally bRedC rowD len ctrlD high tmax) rowP ctrlP fromHole ridx)
  hctrlN : bClearC.sudo_5Board_1t.sudo_4Tier_7control = (base.control : Int)
  ht0Red : bRedC.sudo_5Board_6tally0 = (s.t0 : Int)
  htierRed : bRedC.sudo_5Board_1t = bClearC.sudo_5Board_1t
  honC : bRedC.sudo_5Board_8bench_on = true
  htoC : bRedC.sudo_5Board_8bench_to = (5 : Int)
  hbenchC : bRedC.sudo_5Board_5bench =
    embed (fieldMul s.n s.k s.benchlen base.x
      (fieldCube s.n s.k s.benchlen
        (fieldMul s.n s.k s.benchlen s.gap
          (cubeTimes s.n s.k s.benchlen s.gap s.tally))) ++
      List.replicate (s.benchlen - s.n) 0)

/-- Run the parked clear, the idle clear, and the unparked cube and mul once.
    The two clears are the same board. -/
theorem red_open_idents
    {done rs : List Nat} {r : Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvK done (r :: rs) b s base)
    (hge : 0 ≤ s.fromHole) (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax)
    (hhome : s.onBench = false)
    (hxLen : base.x.length = base.n) (hxT : allTritList base.x) :
    Nonempty (RedOpenId done rs r b s base) := by
  obtain ⟨bClearU, bCubeP, bRedP, hclearProg, _hcubeF, _hmulF, hcubeU, hredU, hrelP,
      _honP, _htoP, _hlenP, _hbenchP, _hhighP, _htmaxP, bLoopP, bMulP, hmulP, hclearP,
      hpackP⟩ :=
    parked_clear_unparked h hge hm hT hhome hxLen hxT
  obtain ⟨cP, _ysP, _mvPk, _slPk, _hoPk, _pkPk, _psPk, _opsPk, _hHP, _hDP, _hopsP,
      hloopP, hrowP0, hctrlP0, hgP, hmP, hnP, hkP, hbP, hsrcP, ht0P, _hnamedP,
      _hysP, _hmvP, _hslP, _hhoP, _hpkP, _hpsP, hcopyP⟩ := hpackP
  obtain ⟨bClearG, bIdle, hrun, hframe, hbenchE, hbonE, htoE, hmarkE, hlenE, ht0E,
      hparkE, hhighE, htierE, hladE, hnrE, htmaxE, h5H, h5D, h6H, h6D, h7E, h5f, h6f,
      hkeep, ⟨ps, hpsEq⟩, ⟨hnat, hhnEq⟩, hrowIdle, hctrlIdle, hδ, hslots, hpieceM, hpieceS⟩ :=
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
  exact ⟨RedOpenId.mk
    bClearU bCubeP bRedP bClearG bIdle bClearC bCubeC bRedC
    hclearProg hcubeU hredU hrelP hrun hframe
    hbenchE hbonE htoE hmarkE hlenE ht0E hparkE hhighE htierE hladE hnrE htmaxE
    h5H h5D h6H h6D h7E h5f h6f hkeep
    ⟨ps, hpsEq⟩ ⟨hnat, hhnEq⟩
    hrowIdle hctrlIdle hδ hslots hpieceM hpieceS
    hclearSame hredSame hcubeBoth hmulBoth hctrlN ht0Red htierRed
    honC htoC hbenchC⟩

end EcbsLink2.Link2
