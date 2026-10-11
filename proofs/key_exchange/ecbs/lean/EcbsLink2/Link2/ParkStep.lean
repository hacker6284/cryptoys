/-
  Parked white successors. The clear is the idle clear transported into the
  resume frame. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.HomeRed

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- Settle copies the ladder, the rung count, and `tally_max`. -/
theorem settle_keeps_frame (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (n moves slides peak : Nat) :
    let s := settleBoard b home hH hD xs n moves slides peak
    s.sudo_5Board_7ladder0 = b.sudo_5Board_7ladder0 ∧
    s.sudo_5Board_6nrungs = b.sudo_5Board_6nrungs ∧
    s.sudo_5Board_4cost.sudo_5Costs_9tally_max =
      b.sudo_5Board_4cost.sudo_5Costs_9tally_max := by
  unfold settleBoard
  split <;> exact ⟨rfl, rfl, rfl⟩

/-- The nocopy mul copies those three fields off its input board. -/
theorem mulOff_keeps_frame (b : Ecbs.Board) (dst second : Nat) (xs ys : List Nat)
    (n k moves hole bench peak peakS cOps : Nat)
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hS : second < b.sudo_5Board_4held.size)
    (hHomeS : second < b.sudo_5Board_4home.size) :
    let m := mulNoOffBoard b dst second xs ys n k moves hole bench peak peakS cOps
      hops hS hHomeS
    m.sudo_5Board_7ladder0 = b.sudo_5Board_7ladder0 ∧
    m.sudo_5Board_6nrungs = b.sudo_5Board_6nrungs ∧
    m.sudo_5Board_4cost.sudo_5Costs_9tally_max =
      b.sudo_5Board_4cost.sudo_5Costs_9tally_max := by
  unfold mulNoOffBoard
  exact ⟨rfl, rfl, rfl⟩

/-- Clear copies those three fields. -/
theorem clearHeld_keeps_frame (b : Ecbs.Board) (home : Nat) (xs : List Nat) (moves : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size) :
    let c := clearHeldBoard b home xs moves hH hD
    c.sudo_5Board_7ladder0 = b.sudo_5Board_7ladder0 ∧
    c.sudo_5Board_6nrungs = b.sudo_5Board_6nrungs ∧
    c.sudo_5Board_4cost.sudo_5Costs_9tally_max =
      b.sudo_5Board_4cost.sudo_5Costs_9tally_max := by
  unfold clearHeldBoard
  exact ⟨rfl, rfl, rfl⟩

/-- A parked resume spends two more control steps than an idle park. The peg
    loop still fits the same counter budget: `4 + tally ≤ 3 · mMax + 5`. -/
theorem ctrl_resume_peg_fit {ctrl tally ctrl0 done R mMax : Nat}
    (hctrl : ctrl ≤ ctrl0 + done * (3 * mMax + 5))
    (ht : tally ≤ mMax) (_hm : 0 < tally) (hd : done ≤ R)
    (hf : FitsLen (ctrl0 + (R + 1) * (3 * mMax + 5))) :
    FitsLen (ctrl + 4 + tally) := by
  apply FitsLen.of_le hf
  have hmul : (done + 1) * (3 * mMax + 5) =
      done * (3 * mMax + 5) + (3 * mMax + 5) := by rw [Nat.succ_mul]
  have hstep : ctrl + 4 + tally ≤ ctrl0 + (done + 1) * (3 * mMax + 5) := by
    have hpiece : 4 + tally ≤ 3 * mMax + 5 := by omega
    omega
  have hR : ctrl0 + (done + 1) * (3 * mMax + 5) ≤
      ctrl0 + (R + 1) * (3 * mMax + 5) := by
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega : done + 1 ≤ R + 1)) _
  omega

theorem parkKeep_irrel (b : Ecbs.Board) (hole park rung i ctrl : Nat)
    (hRowP hRowP' : park < b.sudo_5Board_3row.size)
    (hRowH hRowH' : hole < b.sudo_5Board_3row.size) :
    parkKeepBoard b hole park rung i ctrl hRowP hRowH =
      parkKeepBoard b hole park rung i ctrl hRowP' hRowH' := by
  have hp : hRowP = hRowP' := Subsingleton.elim _ _
  have hh : hRowH = hRowH' := Subsingleton.elim _ _
  subst hp
  subst hh
  rfl

theorem place_of_eq {b b' : Ecbs.Board} (hbb : b = b') (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat) :
    placeBoard b home hH hD xs moves peak =
      placeBoard b' home (hbb ▸ hH) (hbb ▸ hD) xs moves peak := by
  cases hbb
  rfl

/-- The idle park-and-copy peg context, for any rung whose gap is in home 5.
    `peg_of_shape` is the copy of the entry. Keep-park is `withPark` of that
    entry, so the peg context after the idle park is the same context with the
    park row and a counter two higher. `fromHole` is not read. -/
theorem idle_park_peg
    {done rest : List Nat} {r : Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvKCore done (r :: rest) b s base)
    (hM : MoveHeadroom b base.n base.bench base.mMax)
    (hS : SlideHeadroom b base.n base.mMax)
    (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax)
    (hhome : s.onBench = false) :
    ∃ (c : PegCtx),
      c.row0 = afterPark s.row (-1) s.parkAt (climbAt base.ladder0 base.R s.ridx) r ∧
      c.ctrl0 = s.ctrl + 2 ∧
      c.m = s.tally ∧
      c.t0 = s.t0 ∧
      c.src = 6 ∧
      c.g = s.gap ∧
      c.n = s.n ∧
      c.k = s.k ∧
      c.bench = s.benchlen ∧
      ∃ (hRowP : s.parkAt < b.sudo_5Board_3row.size)
        (hRowH : climbAt base.ladder0 base.R s.ridx < b.sudo_5Board_3row.size)
        (mv pk sl : Nat),
        b.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int) ∧
        b.sudo_5Board_4cost.sudo_5Costs_4peak = (pk : Int) ∧
        b.sudo_5Board_4cost.sudo_5Costs_6slides = (sl : Int) ∧
        c.moves0 = mv + pegCount s.gap ∧
        c.slides0 = sl ∧
        c.b0 = placeBoard
          (parkKeepBoard b (climbAt base.ladder0 base.R s.ridx) s.parkAt r
            s.ridx s.ctrl hRowP hRowH)
          6 h.shape.spareH h.shape.spareD s.gap mv pk := by
  let hole := climbAt base.ladder0 base.R s.ridx
  obtain ⟨mv, pk, sl, cE, hmv, hpk, hsl, hb0, _hcopy, hsrc, hg, hmT,
      _hrow0, hn, hkN, hbch, hmv0, hsl0, ht0, _hctrl0, _hhigh, _hcontrol, _hlen, _hmax⟩ :=
    peg_of_shape h hM hS hm hT hhome
  let rowI := afterPark s.row (-1) s.parkAt hole r
  have hRoom : cE.t0 + cE.m ≤ rowI.length := by
    have hlenA : rowI.length = s.row.length :=
      afterPark_length s.row (-1) s.parkAt hole r
    rw [ht0, hmT, hlenA]
    exact h.shape.seg.room
  have hdoneLe : done.length ≤ base.R := by
    have hlenK := h.kLe
    simp [List.length_append, List.length_cons] at hlenK
    exact Nat.le_trans (Nat.le_add_right done.length _) hlenK
  have hCtrl : FitsLen ((s.ctrl + 2) + s.tally) :=
    ctrl_park_peg_fit h.ctrlLe hT hm hdoneLe base.fitCtrl
  let c := pegCtxPark cE rowI (s.ctrl + 2) ((hole : Nat) : Int) (Int.ofNat (s.ridx + 1))
    hRoom (by rw [hmT]; exact hCtrl)
  have hRowP : s.parkAt < b.sudo_5Board_3row.size := by
    rw [h.inv.row, size_embed]; exact h.shape.park.parkLt
  have hRowH : hole < b.sudo_5Board_3row.size := by
    rw [h.inv.row, size_embed]; exact h.shape.park.holeLt
  have hPW := parkKeep_withPark b s.row hole s.parkAt r s.ridx s.ctrl hRowP hRowH
    h.inv.row h.shape.park.parkLt h.shape.park.holeLt
  have hpl := placeBoard_withPark b (embed rowI) (Int.ofNat (s.ctrl + 2))
    ((hole : Nat) : Int) (Int.ofNat (s.ridx + 1))
    6 h.shape.spareH h.shape.spareD s.gap mv pk
  have hb0p : placeBoard b 6 h.shape.spareH h.shape.spareD s.gap mv pk = cE.b0 := hb0.symm
  have hplace : placeBoard
      (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH)
      6 h.shape.spareH h.shape.spareD s.gap mv pk = c.b0 := by
    have h1 := place_of_eq hPW 6 h.shape.spareH h.shape.spareD s.gap mv pk
    have hir := placeBoard_irrel
      (withPark b (embed rowI) (Int.ofNat (s.ctrl + 2)) ((hole : Nat) : Int)
        (Int.ofNat (s.ridx + 1)))
      6 (hPW ▸ h.shape.spareH) (withPark_home _ _ _ _ _ ▸ h.shape.spareH)
      (hPW ▸ h.shape.spareD) (withPark_held _ _ _ _ _ ▸ h.shape.spareD)
      s.gap mv pk
    rw [h1, hir, hpl, hb0p]
    unfold c pegCtxPark
    rfl
  refine ⟨c, rfl, rfl, ?_, ?_, hsrc, hg, hn, hkN, hbch, hRowP, hRowH, mv, pk, sl,
      hmv, hpk, hsl, ?_, ?_, hplace.symm⟩
  · dsimp [c, pegCtxPark]; exact hmT
  · dsimp [c, pegCtxPark]; exact ht0
  · dsimp [c, pegCtxPark]; exact hmv0
  · dsimp [c, pegCtxPark]; exact hsl0

/-- A parked rung's copy is the idle park-and-copy peg context with the restored
    row and a counter two higher. `parked_peg_ctx` is that idle context; this is
    the same context after `withPark`. -/
theorem parked_peg_ctx_ge
    {done rest : List Nat} {r : Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvKCore done (r :: rest) b s base)
    (hM : MoveHeadroom b base.n base.bench base.mMax)
    (hS : SlideHeadroom b base.n base.mMax)
    (hge : 0 ≤ s.fromHole) (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax)
    (hhome : s.onBench = false) :
    ∃ (bPark bCopy : Ecbs.Board) (cIdle c : PegCtx),
      Ecbs.park_rung b (r : Int) = .ok bPark ∧
      Ecbs.copy_band bPark ((6 : Nat) : Int) ((5 : Nat) : Int) false = .ok bCopy ∧
      bCopy = withPark cIdle.b0
        (embed (afterPark s.row s.fromHole s.parkAt
          (climbAt base.ladder0 base.R s.ridx) r))
        (((s.ctrl + 4 : Nat) : Int))
        (((climbAt base.ladder0 base.R s.ridx : Nat) : Int))
        (Int.ofNat (s.ridx + 1)) ∧
      c.b0 = bCopy ∧
      c.row0 = afterPark s.row s.fromHole s.parkAt
        (climbAt base.ladder0 base.R s.ridx) r ∧
      c.ctrl0 = s.ctrl + 4 ∧
      c.m = s.tally ∧
      c.t0 = s.t0 ∧
      c.src = 6 ∧
      c.g = s.gap ∧
      cIdle.row0 = afterPark s.row (-1) s.parkAt
        (climbAt base.ladder0 base.R s.ridx) r ∧
      cIdle.ctrl0 = s.ctrl + 2 ∧
      cIdle.m = s.tally ∧
      cIdle.t0 = s.t0 ∧
      cIdle.src = 6 ∧
      cIdle.g = s.gap ∧
      cIdle.n = s.n ∧
      cIdle.k = s.k ∧
      cIdle.bench = s.benchlen ∧
      ∃ (mv pk sl : Nat)
        (hRowP : s.parkAt < b.sudo_5Board_3row.size)
        (hRowH : climbAt base.ladder0 base.R s.ridx < b.sudo_5Board_3row.size),
        b.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int) ∧
        b.sudo_5Board_4cost.sudo_5Costs_4peak = (pk : Int) ∧
        b.sudo_5Board_4cost.sudo_5Costs_6slides = (sl : Int) ∧
        cIdle.moves0 = mv + pegCount s.gap ∧
        cIdle.slides0 = sl ∧
        cIdle.b0 = placeBoard
          (parkKeepBoard b (climbAt base.ladder0 base.R s.ridx) s.parkAt r
            s.ridx s.ctrl hRowP hRowH)
          6 h.shape.spareH h.shape.spareD s.gap mv pk := by
  let hole := climbAt base.ladder0 base.R s.ridx
  obtain ⟨cIdle, hrowI, hctrlI, hmI, htI, hsrcI, hgI, hnI, hkI, hbI,
      hRowP, hRowH, mv, pk, sl, hmv, hpk, hsl, hmv0, hsl0, hplace⟩ :=
    idle_park_peg h hM hS hm hT hhome
  obtain ⟨bPark, bKeep, hRowP', hRowH', hpark, hkeep, hframe⟩ :=
    resume_park_withPark h hge
  have hKeepEq : bKeep =
      parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH := by
    rw [hkeep]
  have h6H : 6 < bPark.sudo_5Board_4home.size := by
    rw [hframe, withPark_home, hKeepEq]
    exact h.shape.spareH
  have h6D : 6 < bPark.sudo_5Board_4held.size := by
    rw [hframe, withPark_held, hKeepEq]
    exact h.shape.spareD
  have h5H : 5 < bPark.sudo_5Board_4home.size := by
    rw [hframe, withPark_home, hKeepEq]
    exact h.inv.hG
  have h5D : 5 < bPark.sudo_5Board_4held.size := by
    rw [hframe, withPark_held, hKeepEq]
    exact h.inv.hGs
  have h7 : 7 ≤ bPark.sudo_5Board_4held.size := by
    rw [hframe, withPark_held, hKeepEq]
    exact h.shape.h7
  have hheld5 : bPark.sudo_5Board_4held[5] = true := by
    have hEq : bPark.sudo_5Board_4held = b.sudo_5Board_4held := by
      rw [hframe, withPark_held, hKeepEq]
      rfl
    exact cell_eq_of hEq (h.inv.gapHome hhome).1
  have harr5 : bPark.sudo_5Board_4home[5] = embed s.gap := by
    have hEq : bPark.sudo_5Board_4home = b.sudo_5Board_4home := by
      rw [hframe, withPark_home, hKeepEq]
      rfl
    exact cell_eq_of hEq (h.inv.gapHome hhome).2
  have hempty : bPark.sudo_5Board_4held[6] = false := by
    have hEq : bPark.sudo_5Board_4held = b.sudo_5Board_4held := by
      rw [hframe, withPark_held, hKeepEq]
      rfl
    exact cell_eq_of hEq h.shape.spareE
  have hnP : bPark.sudo_5Board_1t.sudo_4Tier_1n = (s.gap.length : Int) := by
    have hEq : bPark.sudo_5Board_1t = b.sudo_5Board_1t := by
      rw [hframe, withPark_tier, hKeepEq]
      rfl
    rw [hEq, h.shape.gapLen]
    exact h.shape.tierN
  have hmvP : bPark.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int) := by
    rw [hframe, withPark_moves, hKeepEq]
    exact hmv
  have hpkP : bPark.sudo_5Board_4cost.sudo_5Costs_4peak = (pk : Int) := by
    rw [hframe, withPark_peak, hKeepEq]
    exact hpk
  have hpegN : pegCount s.gap ≤ base.n := by
    have h1 : pegCount s.gap ≤ s.gap.length := pegCount_le s.gap
    rw [h.shape.gapLen, h.hn] at h1
    exact h1
  have hcopyLe := gap_copy_le_rung base.n base.bench base.mMax s.tally
    (pegCount s.gap) hpegN hT
  have hR1 : done.length + 1 ≤ base.R := by
    have hlenK := h.kLe
    rw [List.length_append, List.length_cons] at hlenK
    exact Nat.le_trans (Nat.succ_le_succ (Nat.le_add_right _ _)) hlenK
  have hmvE := hM.eq
  have hmvSame : mv = hM.mv := ofNat_inj_nat (hmv.symm.trans hmvE)
  have hfitBig := copy_then_pegs_fit hM.mv
    (rungCharge base.n base.bench base.mMax - 2 * base.n) (pegCount s.gap) 0
    hM.room
    (Nat.le_trans (Nat.le_add_right (pegCount s.gap) _)
      (gap_copy_room base.n base.bench base.mMax s.tally (pegCount s.gap) hpegN hT))
  have hfit : FitsLen (mv + pegCount s.gap) := by
    rw [hmvSame]
    simpa using hfitBig
  have hlenFit : FitsLen s.gap.length := by
    rw [h.shape.gapLen]; exact h.shape.peg.fitN
  have hcopy := copy_band_refines bPark 6 5 s.gap mv pk h6H h6D h5H h5D h7
    hheld5 harr5 hempty hnP hlenFit hmvP hpkP hfit
  let rowP := afterPark s.row s.fromHole s.parkAt hole r
  have hRoomP : cIdle.t0 + cIdle.m ≤ rowP.length := by
    rw [htI, hmI, afterPark_length]
    exact h.shape.seg.room
  have hdoneLe : done.length ≤ base.R :=
    Nat.le_trans (Nat.le_succ done.length) hR1
  have hCtrl4 : FitsLen ((s.ctrl + 4) + s.tally) :=
    ctrl_resume_peg_fit h.ctrlLe hT hm hdoneLe base.fitCtrl
  have hCtrlP : FitsLen (cIdle.ctrl0 + cIdle.m) := by
    rw [hctrlI, hmI]
    have hsum : s.ctrl + 2 + s.tally ≤ s.ctrl + 4 + s.tally := by omega
    exact FitsLen.of_le hCtrl4 hsum
  let c := pegCtxPark cIdle rowP (s.ctrl + 4) ((hole : Nat) : Int) (Int.ofNat (s.ridx + 1))
    hRoomP (by rw [hmI]; exact hCtrl4)
  have hpl := placeBoard_withPark
    (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH)
    (embed rowP) (((s.ctrl + 4 : Nat) : Int)) ((hole : Nat) : Int) (Int.ofNat (s.ridx + 1))
    6 h.shape.spareH h.shape.spareD s.gap mv pk
  have hframe' : bPark = withPark
      (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH)
      (embed rowP) (((s.ctrl + 4 : Nat) : Int)) ((hole : Nat) : Int) (Int.ofNat (s.ridx + 1)) := by
    rw [hframe, hKeepEq]
  have hbc : placeBoard bPark 6 h6H h6D s.gap mv pk =
      withPark cIdle.b0 (embed rowP) (((s.ctrl + 4 : Nat) : Int))
        ((hole : Nat) : Int) (Int.ofNat (s.ridx + 1)) := by
    have h1 := place_of_eq hframe' 6 h6H h6D s.gap mv pk
    have hir := placeBoard_irrel
      (withPark (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH)
        (embed rowP) (((s.ctrl + 4 : Nat) : Int)) ((hole : Nat) : Int) (Int.ofNat (s.ridx + 1)))
      6 (hframe' ▸ h6H) (withPark_home _ _ _ _ _ ▸ h.shape.spareH)
      (hframe' ▸ h6D) (withPark_held _ _ _ _ _ ▸ h.shape.spareD) s.gap mv pk
    rw [h1, hir, hpl, ← hplace]
  refine ⟨bPark, _, cIdle, c, hpark, hcopy, hbc, ?_, rfl, rfl, ?_, ?_, ?_, ?_,
      hrowI, hctrlI, hmI, htI, hsrcI, hgI, hnI, hkI, hbI,
      mv, pk, sl, hRowP, hRowH, hmv, hpk, hsl, hmv0, hsl0, hplace⟩
  · dsimp [c, pegCtxPark]
    exact hbc.symm
  · dsimp [c, pegCtxPark]; exact hmI
  · dsimp [c, pegCtxPark]; exact htI
  · dsimp [c, pegCtxPark]; exact hsrcI
  · dsimp [c, pegCtxPark]; exact hgI

/-- Park, copy, the white scan, the cube-peg loop, `mul`, and `clear` on a rung
    that is already parked. The peg context is the idle one transported across
    the resume frame, and the block is `parked_clear_transport`. -/
theorem parked_clear_ge
    {done rest : List Nat} {r : Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvKCore done (r :: rest) b s base)
    (hM : MoveHeadroom b base.n base.bench base.mMax)
    (hS : SlideHeadroom b base.n base.mMax)
    (hge : 0 ≤ s.fromHole) (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax)
    (hhome : s.onBench = false) :
    ∃ bClear bIdle,
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
          Ecbs.clear b (5 : Int)) = .ok bClear ∧
      bClear = withPark bIdle
        (embed (paintRed (afterPark s.row s.fromHole s.parkAt
          (climbAt base.ladder0 base.R s.ridx) r) s.t0 s.tally))
        (((s.ctrl + 4 + s.tally : Nat) : Int))
        (((climbAt base.ladder0 base.R s.ridx : Nat) : Int))
        (Int.ofNat (s.ridx + 1)) ∧
      bIdle.sudo_5Board_5bench =
        embed (fieldMul s.n s.k s.benchlen s.gap
          (cubeTimes s.n s.k s.benchlen s.gap s.tally) ++
          List.replicate (s.benchlen - s.n) 0) ∧
      bIdle.sudo_5Board_8bench_on = true ∧
      bIdle.sudo_5Board_8bench_to = (5 : Int) ∧
      bIdle.sudo_5Board_9marker_on = false ∧
      bIdle.sudo_5Board_9tally_len = (s.tally : Int) ∧
      bIdle.sudo_5Board_6tally0 = (s.t0 : Int) ∧
      bIdle.sudo_5Board_9park_hole = (s.parkAt : Int) ∧
      bIdle.sudo_5Board_4cost.sudo_5Costs_15control_highest = (s.high : Int) ∧
      bIdle.sudo_5Board_1t = b.sudo_5Board_1t ∧
      bIdle.sudo_5Board_7ladder0 = b.sudo_5Board_7ladder0 ∧
      bIdle.sudo_5Board_6nrungs = b.sudo_5Board_6nrungs ∧
      bIdle.sudo_5Board_4cost.sudo_5Costs_9tally_max =
        b.sudo_5Board_4cost.sudo_5Costs_9tally_max ∧
      5 < bIdle.sudo_5Board_4home.size ∧
      5 < bIdle.sudo_5Board_4held.size ∧
      6 < bIdle.sudo_5Board_4home.size ∧
      6 < bIdle.sudo_5Board_4held.size ∧
      7 ≤ bIdle.sudo_5Board_4held.size ∧
      (∀ h5 : 5 < bIdle.sudo_5Board_4held.size, bIdle.sudo_5Board_4held[5] = false) ∧
      (∀ h6 : 6 < bIdle.sudo_5Board_4held.size, bIdle.sudo_5Board_4held[6] = false) ∧
      CellKeep bIdle base.xHome base.x ∧
      (∃ ps : Nat, bIdle.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (ps : Int)) ∧
      (∃ hn : Nat, bIdle.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = (hn : Int)) ∧
      bIdle.sudo_5Board_3row =
        embed (paintRed (afterPark s.row (-1) s.parkAt
          (climbAt base.ladder0 base.R s.ridx) r) s.t0 s.tally) ∧
      bIdle.sudo_5Board_4cost.sudo_5Costs_4ctrl = ((s.ctrl + 2 + s.tally : Nat) : Int) ∧
      RungDelta b bClear base s.tally ∧
      ClearSlots b.sudo_5Board_4cost.sudo_5Costs_3ops
        bClear.sudo_5Board_4cost.sudo_5Costs_3ops s.tally ∧
      (∃ mv mvC : Nat,
        b.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int) ∧
        bClear.sudo_5Board_4cost.sudo_5Costs_5moves = (mvC : Int) ∧
        mvC + 2 * base.n ≤ mv + base.n + s.tally * pegCharge base.n base.bench +
          mulCharge base.n base.bench + base.n) ∧
      (∃ sl slC : Nat,
        b.sudo_5Board_4cost.sudo_5Costs_6slides = (sl : Int) ∧
        bClear.sudo_5Board_4cost.sudo_5Costs_6slides = (slC : Int) ∧
        slC ≤ sl + s.tally * (2 * base.n)) := by
  let hole := climbAt base.ladder0 base.R s.ridx
  obtain ⟨bPark, bCopy, cIdle, _cP, hpark, hcopy, hFrame, _hc0, _hrowP, _hctrlP,
      _hmP, _htP, _hsrcP, _hgP, hrowI, hctrlI, hmI, htI, hsrcI, hgI,
      hnI, hkI, hbI, mv, pk, sl, hRowP, hRowH, hmv, hpk, hsl, hmv0, hsl0, hplace⟩ :=
    parked_peg_ctx_ge h hM hS hge hm hT hhome
  let rowP := afterPark s.row s.fromHole s.parkAt hole r
  let rowI := afterPark s.row (-1) s.parkAt hole r
  have hRoom : cIdle.t0 + cIdle.m ≤ cIdle.row0.length := by
    rw [htI, hmI, hrowI, afterPark_length]
    exact h.shape.seg.room
  have hRoom0 : cIdle.t0 + cIdle.m ≤ rowP.length := by
    rw [htI, hmI, afterPark_length]
    exact h.shape.seg.room
  have hseg0 := h.shape.seg
  have hAgree : ∀ j (hj : j < cIdle.m),
      rowP[cIdle.t0 + j]'(Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj cIdle.t0) hRoom0) =
        cIdle.row0[cIdle.t0 + j]'(Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj cIdle.t0) hRoom) := by
    intro j hj
    have hjM : j < s.tally := by
      have h := hj
      rw [hmI] at h
      exact h
    have hix : s.t0 + j < s.row.length :=
      Nat.lt_of_lt_of_le (Nat.add_lt_add_left hjM s.t0) hseg0.room
    have hgetP := afterPark_get s.row s.fromHole s.parkAt hole r (s.t0 + j)
      (Nat.lt_of_lt_of_le h.parkBelow (Nat.le_add_right _ _))
      (Nat.lt_of_lt_of_le h.holeBelow (Nat.le_add_right _ _))
      (Or.inr (Nat.lt_of_lt_of_le (h.fromBelow hge) (Nat.le_add_right s.t0 j)))
      hix
    have hgetI := afterPark_get s.row (-1) s.parkAt hole r (s.t0 + j)
      (Nat.lt_of_lt_of_le h.parkBelow (Nat.le_add_right _ _))
      (Nat.lt_of_lt_of_le h.holeBelow (Nat.le_add_right _ _))
      (Or.inl (by decide : (-1 : Int) < 0))
      hix
    have hgoal := Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj cIdle.t0) hRoom0
    have hLP := get_add_eq htI hgoal
    have hixP : s.t0 + j < rowP.length := by
      unfold rowP
      rw [afterPark_length]
      exact hix
    have hmid : rowP[s.t0 + j]'(htI ▸ hgoal) = rowP[s.t0 + j]'hixP := list_idx_irrel
    have hgoalI := Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj cIdle.t0) hRoom
    have hrow := list_eq_get hrowI hgoalI
    have hixI : s.t0 + j < rowI.length := by
      unfold rowI
      rw [afterPark_length]
      exact hix
    have hback := get_add_eq htI.symm hixI
    exact hLP.trans (hmid.trans (hgetP.trans (hgetI.symm.trans
      ((list_idx_irrel).trans (hback.trans hrow.symm)))))
  have hWhite : ∀ j (hj : j < cIdle.m),
      cIdle.row0[cIdle.t0 + j]'(Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj cIdle.t0) hRoom) = 1 := by
    intro j hj
    have hjM : j < s.tally := by
      have h := hj
      rw [hmI] at h
      exact h
    have hsegI := afterPark_seg s.row (-1) s.parkAt hole r s.t0 s.tally hseg0
      h.parkBelow h.holeBelow (Or.inl (by decide : (-1 : Int) < 0))
    have hcol := hsegI.colour j hjM
    have hixI : s.t0 + j < rowI.length := by
      unfold rowI
      rw [afterPark_length]
      exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hjM s.t0) hseg0.room
    have h1 : rowI[s.t0 + j]'hixI = 1 := by
      unfold rowI at hixI ⊢
      exact list_idx_irrel.trans (by simpa using hcol)
    have hgoalI := Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj cIdle.t0) hRoom
    have hrow := list_eq_get hrowI hgoalI
    have hback := get_add_eq htI.symm hixI
    exact hrow.trans (hback.symm.trans h1)
  -- Home 5 survives the idle copy. The peg loop keeps it.
  have h5D : 5 < cIdle.b0.sudo_5Board_4held.size := by
    rw [hplace]
    have hsz := (place_book (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH)
      6 h.shape.spareH h.shape.spareD s.gap mv pk).2.2.2.2.2.2.2.2.2
    rw [hsz]
    simp [parkKeepBoard]
    exact h.inv.hGs
  have h5H : 5 < cIdle.b0.sudo_5Board_4home.size := by
    rw [hplace]
    have hsz := (place_book (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH)
      6 h.shape.spareH h.shape.spareD s.gap mv pk).2.2.2.2.2.2.2.2.1
    rw [hsz]
    simp [parkKeepBoard]
    exact h.inv.hG
  have hHeld5 : cIdle.b0.sudo_5Board_4held[5] = true := by
    have hF : 5 < (placeBoard (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH)
        6 h.shape.spareH h.shape.spareD s.gap mv pk).sudo_5Board_4held.size := by
      rw [← hplace]; exact h5D
    have h5K : 5 < (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH).sudo_5Board_4held.size := by
      simp [parkKeepBoard]
      exact h.inv.hGs
    have hcell := place_held_other (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH)
      6 5 h.shape.spareH h.shape.spareD s.gap mv pk (by decide) h5K hF
    have hpk : (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH).sudo_5Board_4held[5] = true := by
      simp [parkKeepBoard]
      exact (h.inv.gapHome hhome).1
    have hgot := hcell.trans hpk
    have hgot' := board_held_cell hplace.symm 5 hF
    exact hgot'.symm.trans hgot
  have hArr5 : cIdle.b0.sudo_5Board_4home[5] = embed cIdle.g := by
    have hF : 5 < (placeBoard (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH)
        6 h.shape.spareH h.shape.spareD s.gap mv pk).sudo_5Board_4home.size := by
      rw [← hplace]; exact h5H
    have h5K : 5 < (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH).sudo_5Board_4home.size := by
      simp [parkKeepBoard]
      exact h.inv.hG
    have hcell := place_home_other (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH)
      6 5 h.shape.spareH h.shape.spareD s.gap mv pk (by decide) h5K hF
    have hpk : (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH).sudo_5Board_4home[5] =
        embed s.gap := by
      simp [parkKeepBoard]
      exact (h.inv.gapHome hhome).2
    have hgot := hcell.trans hpk
    have hgot' := board_home_cell hplace.symm 5 hF
    have hfin : cIdle.b0.sudo_5Board_4home[5] = embed s.gap := hgot'.symm.trans hgot
    exact hfin.trans (congrArg embed hgI.symm)
  have hopsEq : cIdle.b0.sudo_5Board_4cost.sudo_5Costs_3ops =
      b.sudo_5Board_4cost.sudo_5Costs_3ops := by
    rw [hplace, place_ops_delta]
    simp [parkKeepBoard]
  have hopsZ : 0 < cIdle.b0.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [hopsEq]
    exact Nat.lt_trans (by decide : (0 : Nat) < 1) h.shape.peg.opsGt
  obtain ⟨cMul, hcMul, hcLe⟩ := h.ops 0 (by rw [← hopsEq]; exact hopsZ)
  have hopZ : cIdle.b0.sudo_5Board_4cost.sudo_5Costs_3ops[0] = (cMul : Int) :=
    (arr_get hopsEq 0 hopsZ).trans hcMul
  have hne5 : (5 : Nat) ≠ cIdle.src := by rw [hsrcI]; decide
  have hkeep := pegPack_keep cIdle 5 cIdle.g cMul cIdle.m cIdle.hm (Nat.le_refl _)
    h5D h5H hne5 hHeld5 hArr5 hopsZ hopZ
  let d := pegPack cIdle cIdle.m cIdle.hm (Nat.le_refl _)
  have hPack := pegPack_board cIdle cIdle.m cIdle.hm (Nat.le_refl _)
  have hpTake : pegCount (d.xs.take cIdle.n) ≤ cIdle.n := pegCount_take_le d.xs cIdle.n
  have hlenY : d.xs.length = cIdle.bench := by
    rw [d.hxs, cubeBenchIter_length cIdle.n cIdle.k cIdle.bench cIdle.g cIdle.n_le cIdle.m cIdle.hm]
  have hfitL : FitsLen d.xs.length := by rw [hlenY]; exact cIdle.hfitB
  have hspan2 : 2 * (cIdle.n - 1) < cIdle.bench := by
    have hs := cIdle.hspan
    omega
  have hfi : FitsLen (2 * (cIdle.n - 1)) := FitsLen.of_le cIdle.h3 (by omega)
  have hsum : d.moves + 2 * pegCount (d.xs.take cIdle.n) + cIdle.n * (cIdle.n + 1) +
      3 * (cIdle.bench - cIdle.n) ≤
      cIdle.moves0 + cIdle.m * pegCharge cIdle.n cIdle.bench + mulCharge cIdle.n cIdle.bench := by
    have hgeM := mulCharge_ge cIdle.n cIdle.bench d.moves d.xs d.xs cIdle.k cIdle.n_le hpTake
    exact Nat.le_trans hgeM (Nat.add_le_add_right d.hmovB _)
  have hmvE := hM.eq
  have hslE := hS.eq
  have hmvSame : mv = hM.mv := ofNat_inj_nat (hmv.symm.trans hmvE)
  have hslSame : sl = hS.sl := ofNat_inj_nat (hsl.symm.trans hslE)
  have hk : done.length + 1 ≤ base.R := by
    have hlenK := h.kLe
    simp [List.length_append, List.length_cons] at hlenK
    exact Nat.le_trans (Nat.succ_le_succ (Nat.le_add_right done.length _)) hlenK
  have hroomM : FitsLen (mv + (rungCharge base.n base.bench base.mMax - 2 * base.n)) := by
    rw [hmvSame]; exact hM.room
  have hfold : FitsLen (d.moves + 2 * pegCount (d.xs.take cIdle.n) + cIdle.n * (cIdle.n + 1) +
      3 * (cIdle.bench - cIdle.n)) := by
    apply FitsLen.of_le hroomM
    have hpegN : pegCount s.gap ≤ base.n := by
      have h1 : pegCount s.gap ≤ s.gap.length := pegCount_le s.gap
      rw [h.shape.gapLen, h.hn] at h1
      exact h1
    have hpc : pegCharge cIdle.n cIdle.bench = pegCharge base.n base.bench := by
      rw [hnI.trans h.hn, hbI.trans h.hbench]
    have hmc : mulCharge cIdle.n cIdle.bench = mulCharge base.n base.bench := by
      rw [hnI.trans h.hn, hbI.trans h.hbench]
    have hright : cIdle.moves0 + cIdle.m * pegCharge cIdle.n cIdle.bench +
        mulCharge cIdle.n cIdle.bench =
        mv + pegCount s.gap + s.tally * pegCharge base.n base.bench +
          mulCharge base.n base.bench := by
      rw [hmv0, hmI, hpc, hmc]
    have hmid := Nat.le_trans hsum (Nat.le_of_eq hright)
    have hpiece : d.moves + 2 * pegCount (d.xs.take cIdle.n) + cIdle.n * (cIdle.n + 1) +
        3 * (cIdle.bench - cIdle.n) ≤
        mv + base.n + s.tally * pegCharge base.n base.bench +
          mulCharge base.n base.bench + base.n :=
      Nat.le_trans hmid (by
        have hpeg := hpegN
        omega)
    have hbody := white_piece_in_room base.n base.bench s.tally mv _ hpiece
    exact Nat.le_trans hbody (Nat.add_le_add_left
      (Nat.sub_le_sub_right (rungCharge_mono base.n base.bench s.tally base.mMax hT) _) mv)
  have hfm : FitsLen (d.moves + 2 * pegCount (d.xs.take cIdle.n) + cIdle.n * (cIdle.n + 1)) :=
    FitsLen.of_le hfold (by omega)
  have hfitM : FitsLen (d.moves + 2 * pegCount (d.xs.take cIdle.n)) :=
    FitsLen.of_le hfm (by omega)
  have hpegF : FitsLen (2 * pegCount (d.xs.take cIdle.n)) := FitsLen.of_le hfitM (by omega)
  have hroomS : FitsLen (sl + (rungSlideCharge base.n base.mMax - 2 * base.n)) := by
    simpa [← hslSame] using hS.room
  have hfitS : FitsLen (d.slides + 2 * pegCount (d.xs.take cIdle.n)) := by
    apply FitsLen.of_le hroomS
    have h2 : 2 * pegCount (d.xs.take cIdle.n) ≤ 2 * cIdle.n :=
      Nat.mul_le_mul_left 2 hpTake
    have hprev : d.slides ≤ sl + s.tally * (2 * s.n) := by
      have hEq : cIdle.slides0 + cIdle.m * (2 * cIdle.n) = sl + s.tally * (2 * s.n) := by
        rw [hsl0, hmI, hnI]
      exact Nat.le_trans d.hsldB (Nat.le_of_eq hEq)
    have hloc : d.slides + 2 * pegCount (d.xs.take cIdle.n) ≤
        sl + s.tally * (2 * base.n) + 2 * base.n := by
      have h2s : 2 * pegCount (d.xs.take cIdle.n) ≤ 2 * s.n := by rw [← hnI]; exact h2
      have hsumL := Nat.add_le_add hprev h2s
      rw [h.hn] at hsumL
      exact hsumL
    exact loose_slide_in_room base.n s.tally base.mMax sl _ hT hloc
  have hfops : FitsLen (cMul + 1) := by
    apply FitsLen.of_le base.fitO
    have h1 : cMul + 1 ≤ base.ops0 + (done.length + 1) * (base.mMax + 3) := by
      have hone : (1 : Nat) ≤ base.mMax + 3 := Nat.le_add_left 1 (base.mMax + 2)
      have hsumC : cMul + 1 ≤
          base.ops0 + done.length * (base.mMax + 3) + (base.mMax + 3) :=
        Nat.add_le_add hcLe hone
      have hsplit : base.ops0 + done.length * (base.mMax + 3) + (base.mMax + 3) =
          base.ops0 + (done.length + 1) * (base.mMax + 3) := by
        rw [Nat.add_assoc, ← Nat.succ_mul]
      exact Nat.le_trans hsumC (Nat.le_of_eq hsplit)
    have hR : base.ops0 + (done.length + 1) * (base.mMax + 3) ≤
        base.ops0 + base.R * (base.mMax + 3) :=
      Nat.add_le_add_left (Nat.mul_le_mul_right _ hk) _
    exact Nat.le_trans h1 hR
  have hH6 : 6 < d.b.sudo_5Board_4home.size := by rw [← hsrcI]; exact d.hH
  have hD6 : 6 < d.b.sudo_5Board_4held.size := by rw [← hsrcI]; exact d.hD
  have hempty : d.b.sudo_5Board_4held[6] = false := by simpa [hsrcI] using d.hempty
  have hto : d.b.sudo_5Board_8bench_to = ((6 : Nat) : Int) := by rw [d.toB, hsrcI]
  have hnB : d.b.sudo_5Board_1t.sudo_4Tier_1n = (cIdle.n : Int) := by rw [d.tier]; exact cIdle.hn
  have hbl : d.b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat cIdle.bench := by
    rw [d.tier]; exact cIdle.hbl
  have hwF : d.b.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat cIdle.w := by rw [d.tier]; exact cIdle.hwF
  have hhF : d.b.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat cIdle.h := by rw [d.tier]; exact cIdle.hhF
  have hrF : d.b.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat cIdle.r := by rw [d.tier]; exact cIdle.hrF
  have hkF : d.b.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat cIdle.k := by rw [d.tier]; exact cIdle.hkF
  let paint := embed (paintRed rowP cIdle.t0 cIdle.m)
  let ctrlM := Int.ofNat ((s.ctrl + 4) + s.tally)
  let fromH := ((hole : Nat) : Int)
  let ridxH := Int.ofNat (s.ridx + 1)
  have hmulW := mul_eq_live_withPark d.b 5 5 6 cIdle.g d.xs cIdle.w cIdle.h cIdle.r cIdle.n cIdle.k
    d.moves d.slides d.hole cIdle.bench d.peak d.peakS cMul
    d.marker d.onB hto hH6 hD6 d.h7 hempty d.hbench
    hnB cIdle.hn0 d.hpos d.hnle d.hzero cIdle.hf hfitL
    d.hmoves d.hslides d.hpeak hpegF hfitM hfitS
    hkeep.opsLt hkeep.op0 hfops hbl
    hkeep.heldLt hkeep.homeLt hkeep.held hkeep.arr (by decide) cIdle.hlenx
    hspan2 cIdle.hxsT hfi hfm
    cIdle.hw0 cIdle.hh0 cIdle.hrR cIdle.hrP cIdle.hnE cIdle.hkLe cIdle.hgap hwF hhF hrF hkF
    d.hHole d.hpeakS cIdle.hsm cIdle.hnsm cIdle.hfitB hfold
    paint ctrlM fromH ridxH
  have hmulP : Ecbs.mul
      (withPark (pegBoard cIdle cIdle.m) paint ctrlM fromH ridxH)
      (5 : Int) (5 : Int) (6 : Int) false false false =
      .ok (withPark
        (mulNoLiveBoard d.b 5 6 cIdle.g d.xs cIdle.n cIdle.k d.moves d.slides d.hole cIdle.bench
          d.peak d.peakS cMul hH6 hD6 hkeep.opsLt)
        paint ctrlM fromH ridxH) := by
    have hcong := congrArg
      (fun bd => Ecbs.mul (withPark bd paint ctrlM fromH ridxH)
        (5 : Int) (5 : Int) (6 : Int) false false false) hPack.1
    exact hcong.symm.trans hmulW
  let bU := mulNoLiveBoard d.b 5 6 cIdle.g d.xs cIdle.n cIdle.k d.moves d.slides d.hole
    cIdle.bench d.peak d.peakS cMul hH6 hD6 hkeep.opsLt
  have hmvU : bU.sudo_5Board_4cost.sudo_5Costs_5moves =
      Int.ofNat (mulMovesNo (d.moves + 2 * pegCount (d.xs.take cIdle.n)) cIdle.g
        (d.xs.take cIdle.n) cIdle.n cIdle.k cIdle.bench) :=
    mul_live_moves d.b 5 6 cIdle.g d.xs cIdle.n cIdle.k d.moves d.slides d.hole cIdle.bench
      d.peak d.peakS cMul hH6 hD6 hkeep.opsLt
  let mvM := mulMovesNo (d.moves + 2 * pegCount (d.xs.take cIdle.n)) cIdle.g
    (d.xs.take cIdle.n) cIdle.n cIdle.k cIdle.bench
  have h5DU : 5 < bU.sudo_5Board_4held.size := by
    have hHeld := mul_live_held d.b 5 6 cIdle.g d.xs cIdle.n cIdle.k d.moves d.slides d.hole
      cIdle.bench d.peak d.peakS cMul hH6 hD6 hkeep.opsLt
    have hsz : bU.sudo_5Board_4held.size = d.b.sudo_5Board_4held.size := by
      rw [hHeld]
      simp only [Array.size_set]
      rw [settle_held_eq d.b 6 hH6 hD6 d.xs cIdle.n d.moves d.slides d.peak, Array.size_set]
    rw [hsz]
    exact hkeep.heldLt
  have hheldU : bU.sudo_5Board_4held[5] = true := by
    have hHeld := mul_live_held d.b 5 6 cIdle.g d.xs cIdle.n cIdle.k d.moves d.slides d.hole
      cIdle.bench d.peak d.peakS cMul hH6 hD6 hkeep.opsLt
    have h1 := arr_get hHeld 5 h5DU
    rw [h1, Array.getElem_set, if_neg (by decide : (6 : Nat) ≠ 5)]
    have hszS : 5 <
        (settleBoard d.b 6 hH6 hD6 d.xs cIdle.n d.moves d.slides d.peak).sudo_5Board_4held.size := by
      rw [settle_held_eq d.b 6 hH6 hD6 d.xs cIdle.n d.moves d.slides d.peak, Array.size_set]
      exact hkeep.heldLt
    have h2 := arr_get (settle_held_eq d.b 6 hH6 hD6 d.xs cIdle.n d.moves d.slides d.peak) 5 hszS
    rw [h2, Array.getElem_set, if_neg (by decide : (6 : Nat) ≠ 5)]
    exact hkeep.held
  have h5HU : 5 < bU.sudo_5Board_4home.size := by
    have hHome := mul_live_home d.b 5 6 cIdle.g d.xs cIdle.n cIdle.k d.moves d.slides d.hole
      cIdle.bench d.peak d.peakS cMul hH6 hD6 hkeep.opsLt
    rw [hHome, Array.size_set]
    exact hkeep.homeLt
  have harrU : bU.sudo_5Board_4home[5] = embed cIdle.g := by
    have hHome := mul_live_home d.b 5 6 cIdle.g d.xs cIdle.n cIdle.k d.moves d.slides d.hole
      cIdle.bench d.peak d.peakS cMul hH6 hD6 hkeep.opsLt
    have h1 := arr_get hHome 5 h5HU
    rw [h1, Array.getElem_set, if_neg (by decide : (6 : Nat) ≠ 5)]
    exact hkeep.arr
  have hmovD : d.moves ≤ mv + pegCount s.gap + s.tally * pegCharge base.n base.bench := by
    rw [← hmv0, ← hmI, ← h.hn, ← hnI, ← h.hbench, ← hbI]
    simpa [Nat.add_assoc] using d.hmovB
  have hmulLe : mvM ≤ d.moves + mulCharge base.n base.bench := by
    rw [← h.hn, ← hnI, ← h.hbench, ← hbI]
    simpa [mvM, mulStepMoves] using
      mul_moves_delta d.moves cIdle.n cIdle.k cIdle.bench cIdle.g d.xs cIdle.n_le
  have hpegC : pegCount s.gap ≤ base.n := by
    have h1 : pegCount s.gap ≤ s.gap.length := pegCount_le s.gap
    rw [h.shape.gapLen, h.hn] at h1
    exact h1
  have hpegG : pegCount cIdle.g ≤ base.n := by
    rw [hgI]; exact hpegC
  have hpiece := white_clear_move_le mv d.moves (pegCount s.gap) s.tally base.n base.bench
    (pegCount cIdle.g) mvM hmovD hmulLe hpegC hpegG
  have hfitC : FitsLen (mvM + pegCount cIdle.g) := by
    have hroom : FitsLen (mv + (rungCharge base.n base.bench base.mMax - 2 * base.n)) := by
      rw [hmvSame]; exact hM.room
    apply FitsLen.of_le hroom
    have hwhite := white_piece_room base.n base.bench s.tally
    have hmono := rungCharge_mono base.n base.bench s.tally base.mMax hT
    have hsub : rungCharge base.n base.bench s.tally - 2 * base.n ≤
        rungCharge base.n base.bench base.mMax - 2 * base.n :=
      Nat.sub_le_sub_right hmono _
    -- `hpiece` is `≤ mv + rungCharge`, which may sit `2 · n` above the tight room.
    -- The white piece is the bound `white_clear_move_le` unfolded.
    have hW : mvM + pegCount cIdle.g ≤
        mv + base.n + s.tally * pegCharge base.n base.bench +
          mulCharge base.n base.bench + base.n :=
      white_clear_move_piece mv d.moves (pegCount s.gap) s.tally base.n base.bench
        (pegCount cIdle.g) mvM hmovD hmulLe hpegC hpegG
    omega
  have hclearW := clear_withPark bU paint ctrlM fromH ridxH 5 cIdle.g mvM h5HU h5DU
    hheldU harrU (by simpa [mvM] using hmvU) (by rw [cIdle.hlenx]; exact cIdle.hf) hfitC
  have hdoneLe : done.length ≤ base.R := Nat.le_trans (Nat.le_succ done.length) hk
  have hCtrlB : FitsLen ((s.ctrl + 4) + cIdle.m) := by
    rw [hmI]
    exact ctrl_resume_peg_fit h.ctrlLe hT hm hdoneLe base.fitCtrl
  have hrun := parked_clear_transport b bPark bCopy r cIdle cIdle.row0 rowP (s.ctrl + 4)
    fromH ridxH hpark hcopy hFrame hRoom0 hCtrlB hsrcI cIdle.hT0 cIdle.hRow hRoom hAgree hWhite
    (withPark bU paint ctrlM fromH ridxH)
    (withPark (clearHeldBoard bU 5 cIdle.g mvM h5HU h5DU) paint ctrlM fromH ridxH)
    (by
      have hrowC : paint = embed (paintRed rowP cIdle.t0 cIdle.m) := rfl
      simpa [hmI, htI, hrowC] using hmulP)
    hclearW
  let bIdle0 := clearHeldBoard bU 5 cIdle.g mvM h5HU h5DU
  have hC := clearHeld_book bU 5 cIdle.g mvM h5HU h5DU
  have hMulB := mulLive_book d.b 5 6 cIdle.g d.xs cIdle.n cIdle.k d.moves d.slides d.hole
    cIdle.bench d.peak d.peakS cMul hH6 hD6 hkeep.opsLt
  have hPackB := pegPack_board cIdle cIdle.m cIdle.hm (Nat.le_refl _)
  have hPl := place_book (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH)
    6 h.shape.spareH h.shape.spareD s.gap mv pk
  have hPegF := pegPack_fixed cIdle cIdle.m cIdle.hm (Nat.le_refl _)
  have hpre : d.xs.take cIdle.n = cubeTimes cIdle.n cIdle.k cIdle.bench cIdle.g cIdle.m := by
    rw [d.hxs]
    exact cubeBenchIter_prefix cIdle.n cIdle.k cIdle.bench cIdle.g cIdle.hlenx cIdle.m
  have hbenchM := mul_live_bench_gap d.b 5 6 cIdle.g d.xs cIdle.n cIdle.k d.moves d.slides
    d.hole cIdle.bench d.peak d.peakS cMul hH6 hD6 hkeep.opsLt
    cIdle.hn0 cIdle.gap_pos cIdle.n_le
  have haim := mul_live_aimed d.b 5 6 cIdle.g d.xs cIdle.n cIdle.k d.moves d.slides d.hole
    cIdle.bench d.peak d.peakS cMul hH6 hD6 hkeep.opsLt
  have hmarkM := mul_live_marker d.b 5 6 cIdle.g d.xs cIdle.n cIdle.k d.moves d.slides d.hole
    cIdle.bench d.peak d.peakS cMul hH6 hD6 hkeep.opsLt
  have hbenchI : bIdle0.sudo_5Board_5bench =
      embed (fieldMul s.n s.k s.benchlen s.gap
        (cubeTimes s.n s.k s.benchlen s.gap s.tally) ++
        List.replicate (s.benchlen - s.n) 0) := by
    rw [hC.2.2.2.2.2.2.2.2.2.2.1, hbenchM, hpre, hmI, hgI, hnI, hkI, hbI, h.hn, h.hbench]
  have hlenI : bIdle0.sudo_5Board_9tally_len = (s.tally : Int) := by
    rw [hC.2.2.2.1, hMulB.2.2.1, hPackB.2.2.2.1, hplace, hPl.2.2.2.1]
    simpa [parkKeepBoard] using h.inv.len
  have ht0I : bIdle0.sudo_5Board_6tally0 = (s.t0 : Int) := by
    rw [hC.2.2.2.2.1, hMulB.2.2.2.1, hPackB.2.2.2.2.1, hplace, hPl.2.2.2.2.1]
    simpa [parkKeepBoard] using h.inv.t0
  have hparkI : bIdle0.sudo_5Board_9park_hole = (s.parkAt : Int) := by
    rw [hC.2.2.2.2.2.1, hMulB.2.2.2.2.1, hPackB.2.2.2.2.2.1, hplace, hPl.2.2.2.2.2.1]
    simpa [parkKeepBoard] using h.inv.park
  have hhighI : bIdle0.sudo_5Board_4cost.sudo_5Costs_15control_highest = (s.high : Int) := by
    rw [hC.2.2.2.2.2.2.1, hMulB.2.2.2.2.2.1, hPackB.2.2.2.2.2.2.1, hplace,
      hPl.2.2.2.2.2.2.1]
    simpa [parkKeepBoard] using h.inv.high
  have htierI : bIdle0.sudo_5Board_1t = b.sudo_5Board_1t := by
    have h1 : bIdle0.sudo_5Board_1t = bU.sudo_5Board_1t := by
      simp [bIdle0, clearHeldBoard]
    have h2 : bU.sudo_5Board_1t = d.b.sudo_5Board_1t := by
      simp [bU, mulNoLiveBoard, mulNoOffBoard, settleBoard]
      split <;> rfl
    rw [h1, h2, hPegF.2.2.2, hplace]
    simp [placeBoard, parkKeepBoard]
    split <;> rfl
  obtain ⟨c0, hc0, _⟩ := h.ops 0 (by
    exact Nat.lt_trans (by decide : (0 : Nat) < 1) h.shape.peg.opsGt)
  obtain ⟨c1, hc1, _⟩ := h.ops 1 h.shape.peg.opsGt
  have hszP : d.b.sudo_5Board_4cost.sudo_5Costs_3ops.size =
      b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [pegPack_ops_eq cIdle cIdle.m cIdle.hm (Nat.le_refl _), Array.size_set, hplace,
      place_ops_delta]
    simp [parkKeepBoard]
  have h1p : 1 < d.b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [hszP]; exact h.shape.peg.opsGt
  have h0p : 0 < d.b.sudo_5Board_4cost.sudo_5Costs_3ops.size :=
    Nat.lt_trans (by decide : (0 : Nat) < 1) h1p
  have hp1 : d.b.sudo_5Board_4cost.sudo_5Costs_3ops[1] = ((c1 + s.tally : Nat) : Int) := by
    have hArr := pegPack_ops_eq cIdle cIdle.m cIdle.hm (Nat.le_refl _)
    have hget := arr_get hArr 1 h1p
    rw [hget, Array.getElem_set, if_pos rfl, hmI]
    have hsz : cIdle.b0.sudo_5Board_4cost.sudo_5Costs_3ops.size =
        b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
      rw [hplace, place_ops_delta]
      simp [parkKeepBoard]
    have h1b : 1 < cIdle.b0.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
      rw [hsz]; exact h.shape.peg.opsGt
    have hplaceOps := place_ops_delta
      (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH)
      6 h.shape.spareH h.shape.spareD s.gap mv pk
    have hgetB := arr_get (hplace ▸ hplaceOps) 1 h1b
    have hpkOps : (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH).sudo_5Board_4cost.sudo_5Costs_3ops =
        b.sudo_5Board_4cost.sudo_5Costs_3ops := by simp [parkKeepBoard]
    have h1k : 1 < (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH).sudo_5Board_4cost.sudo_5Costs_3ops.size := by
      rw [hpkOps]; exact h.shape.peg.opsGt
    have hgetK := arr_get hpkOps 1 h1k
    have hcell := hgetB.trans (hgetK.trans hc1)
    have hcOps : cIdle.cOps0 = c1 := by
      apply ofNat_inj_nat
      exact cIdle.hop10.symm.trans hcell
    rw [hcOps, ofNat_eq_natCast]
  have hpNe : ∀ j, j ≠ 1 → ∀ (he : j < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
      (hp : j < d.b.sudo_5Board_4cost.sudo_5Costs_3ops.size),
      d.b.sudo_5Board_4cost.sudo_5Costs_3ops[j] = b.sudo_5Board_4cost.sudo_5Costs_3ops[j] := by
    intro j hne he hp
    have hsz0 : cIdle.b0.sudo_5Board_4cost.sudo_5Costs_3ops.size =
        b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
      rw [hplace, place_ops_delta]
      simp [parkKeepBoard]
    have hj0 : j < cIdle.b0.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
      rw [hsz0]; exact he
    have hpB : j < (pegBoard cIdle cIdle.m).sudo_5Board_4cost.sudo_5Costs_3ops.size :=
      hPackB.1.symm ▸ hp
    have hneB := pegBoard_ops_ne cIdle cIdle.m cIdle.hm (Nat.le_refl _) j hne hj0 hpB
    have hplaceOps := place_ops_delta
      (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH)
      6 h.shape.spareH h.shape.spareD s.gap mv pk
    have hpkOps : (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH).sudo_5Board_4cost.sudo_5Costs_3ops =
        b.sudo_5Board_4cost.sudo_5Costs_3ops := by simp [parkKeepBoard]
    have hjk : j < (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH).sudo_5Board_4cost.sudo_5Costs_3ops.size := by
      rw [hpkOps]; exact he
    have hcellB := (arr_get (hplace ▸ hplaceOps) j hj0).trans (arr_get hpkOps j hjk)
    have hBB : d.b.sudo_5Board_4cost.sudo_5Costs_3ops =
        (pegBoard cIdle cIdle.m).sudo_5Board_4cost.sudo_5Costs_3ops :=
      congrArg (fun bd => bd.sudo_5Board_4cost.sudo_5Costs_3ops) hPackB.1
    exact (arr_get hBB j hp).trans (hneB.trans hcellB)
  have hmulArr : bU.sudo_5Board_4cost.sudo_5Costs_3ops =
      d.b.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨0, h0p⟩ ((c0 + 1 : Nat) : Int) := by
    have hlive := mul_live_ops d.b 5 6 cIdle.g d.xs cIdle.n cIdle.k d.moves d.slides d.hole
      cIdle.bench d.peak d.peakS cMul hH6 hD6 hkeep.opsLt
    have hset := settle_ops d.b 6 hH6 hD6 d.xs cIdle.n d.moves d.slides d.peak
    have hcMul0 : cMul = c0 := by
      apply ofNat_inj_nat
      have h0b : 0 < cIdle.b0.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
        rw [hplace, place_ops_delta]
        simp [parkKeepBoard]
        exact Nat.lt_trans (by decide : (0 : Nat) < 1) h.shape.peg.opsGt
      have hplaceOps := place_ops_delta
        (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH)
        6 h.shape.spareH h.shape.spareD s.gap mv pk
      have hpkOps : (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH).sudo_5Board_4cost.sudo_5Costs_3ops =
          b.sudo_5Board_4cost.sudo_5Costs_3ops := by simp [parkKeepBoard]
      have h0k : 0 < (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH).sudo_5Board_4cost.sudo_5Costs_3ops.size := by
        rw [hpkOps]
        exact Nat.lt_trans (by decide : (0 : Nat) < 1) h.shape.peg.opsGt
      have hcell0 := (arr_get (hplace ▸ hplaceOps) 0 h0b).trans
        ((arr_get hpkOps 0 h0k).trans hc0)
      exact hopZ.symm.trans hcell0
    rw [hlive]
    have hidx := settle_ops_lt d.b 0 6 hkeep.opsLt hH6 hD6 d.xs cIdle.n d.moves d.slides d.peak
    exact ops_set_transport hset 0 hidx h0p (Int.ofNat (cMul + 1)) ((c0 + 1 : Nat) : Int)
      (by rw [hcMul0, ofNat_eq_natCast])
  have hclrArr : bIdle0.sudo_5Board_4cost.sudo_5Costs_3ops =
      bU.sudo_5Board_4cost.sudo_5Costs_3ops := by
    simp only [bIdle0, clearHeldBoard]
  have hNat : ∀ j (hj : j < b.sudo_5Board_4cost.sudo_5Costs_3ops.size),
      ∃ cN : Nat, b.sudo_5Board_4cost.sudo_5Costs_3ops[j] = (cN : Int) := by
    intro j hj
    obtain ⟨cN, hcN, _⟩ := h.ops j hj
    exact ⟨cN, hcN⟩
  have hslotsIdle := clearSlots_of_bump
    b.sudo_5Board_4cost.sudo_5Costs_3ops
    d.b.sudo_5Board_4cost.sudo_5Costs_3ops
    bU.sudo_5Board_4cost.sudo_5Costs_3ops
    bIdle0.sudo_5Board_4cost.sudo_5Costs_3ops
    s.tally c0 c1
    (Nat.lt_trans (by decide : (0 : Nat) < 1) h.shape.peg.opsGt) h.shape.peg.opsGt
    hc0 hc1 hNat h0p h1p hp1 hpNe hszP hmulArr hclrArr
  refine ⟨withPark bIdle0 paint ctrlM fromH ridxH, bIdle0, ?_, ?_, hbenchI, ?_, ?_, ?_,
      hlenI, ht0I, hparkI, hhighI, htierI, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hmI] using hrun
  · unfold paint ctrlM rowP
    rw [htI, hmI]
    rfl
  · rw [hC.2.2.2.2.2.2.2.2.1]
    exact haim.1
  · rw [hC.2.2.2.2.2.2.2.2.2.1]
    exact haim.2
  · rw [hC.2.2.2.2.2.2.2.2.2.2.2.1]
    exact hmarkM
  · have hClear := clearHeld_keeps_frame bU 5 cIdle.g mvM h5HU h5DU
    have hOff := mulOff_keeps_frame
      (settleBoard d.b 6 hH6 hD6 d.xs cIdle.n d.moves d.slides d.peak)
      5 6 cIdle.g (d.xs.take cIdle.n) cIdle.n cIdle.k
      (d.moves + 2 * pegCount (d.xs.take cIdle.n)) d.hole cIdle.bench
      (raisedPeak d.peak (countHeld (d.b.sudo_5Board_4held.set ⟨6, hD6⟩ true) 7))
      d.peakS cMul
      (settle_ops_lt d.b 0 6 hkeep.opsLt hH6 hD6 d.xs cIdle.n d.moves d.slides d.peak)
      (settle_held_lt d.b 6 hH6 hD6 d.xs cIdle.n d.moves d.slides d.peak)
      (settle_home_lt d.b 6 hH6 hD6 d.xs cIdle.n d.moves d.slides d.peak)
    have hSet := settle_keeps_frame d.b 6 hH6 hD6 d.xs cIdle.n d.moves d.slides d.peak
    have hLiveL : bU.sudo_5Board_7ladder0 = d.b.sudo_5Board_7ladder0 := by
      unfold bU mulNoLiveBoard
      exact hOff.1.trans hSet.1
    have hLiveN : bU.sudo_5Board_6nrungs = d.b.sudo_5Board_6nrungs := by
      unfold bU mulNoLiveBoard
      exact hOff.2.1.trans hSet.2.1
    have hLiveT : bU.sudo_5Board_4cost.sudo_5Costs_9tally_max =
        d.b.sudo_5Board_4cost.sudo_5Costs_9tally_max := by
      unfold bU mulNoLiveBoard
      exact hOff.2.2.trans hSet.2.2
    have hIdle : bIdle0.sudo_5Board_7ladder0 = bU.sudo_5Board_7ladder0 := by
      unfold bIdle0
      exact hClear.1
    have h1 : bIdle0.sudo_5Board_7ladder0 = d.b.sudo_5Board_7ladder0 :=
      hIdle.trans hLiveL
    rw [h1, hPegF.1, hplace]
    simp [placeBoard, parkKeepBoard]
    split <;> rfl
  · have hIdleN : bIdle0.sudo_5Board_6nrungs = bU.sudo_5Board_6nrungs := by
      unfold bIdle0
      exact (clearHeld_keeps_frame bU 5 cIdle.g mvM h5HU h5DU).2.1
    have h1 : bIdle0.sudo_5Board_6nrungs = d.b.sudo_5Board_6nrungs :=
      hIdleN.trans
        (by
          unfold bU mulNoLiveBoard
          exact (mulOff_keeps_frame
            (settleBoard d.b 6 hH6 hD6 d.xs cIdle.n d.moves d.slides d.peak)
            5 6 cIdle.g (d.xs.take cIdle.n) cIdle.n cIdle.k
            (d.moves + 2 * pegCount (d.xs.take cIdle.n)) d.hole cIdle.bench
            (raisedPeak d.peak (countHeld (d.b.sudo_5Board_4held.set ⟨6, hD6⟩ true) 7))
            d.peakS cMul
            (settle_ops_lt d.b 0 6 hkeep.opsLt hH6 hD6 d.xs cIdle.n d.moves d.slides d.peak)
            (settle_held_lt d.b 6 hH6 hD6 d.xs cIdle.n d.moves d.slides d.peak)
            (settle_home_lt d.b 6 hH6 hD6 d.xs cIdle.n d.moves d.slides d.peak)).2.1.trans
            (settle_keeps_frame d.b 6 hH6 hD6 d.xs cIdle.n d.moves d.slides d.peak).2.1)
    rw [h1, hPegF.2.1, hplace]
    simp [placeBoard, parkKeepBoard]
    split <;> rfl
  · have hIdleT : bIdle0.sudo_5Board_4cost.sudo_5Costs_9tally_max =
        bU.sudo_5Board_4cost.sudo_5Costs_9tally_max := by
      unfold bIdle0
      exact (clearHeld_keeps_frame bU 5 cIdle.g mvM h5HU h5DU).2.2
    have h1 : bIdle0.sudo_5Board_4cost.sudo_5Costs_9tally_max =
        d.b.sudo_5Board_4cost.sudo_5Costs_9tally_max :=
      hIdleT.trans
        (by
          unfold bU mulNoLiveBoard
          exact (mulOff_keeps_frame
            (settleBoard d.b 6 hH6 hD6 d.xs cIdle.n d.moves d.slides d.peak)
            5 6 cIdle.g (d.xs.take cIdle.n) cIdle.n cIdle.k
            (d.moves + 2 * pegCount (d.xs.take cIdle.n)) d.hole cIdle.bench
            (raisedPeak d.peak (countHeld (d.b.sudo_5Board_4held.set ⟨6, hD6⟩ true) 7))
            d.peakS cMul
            (settle_ops_lt d.b 0 6 hkeep.opsLt hH6 hD6 d.xs cIdle.n d.moves d.slides d.peak)
            (settle_held_lt d.b 6 hH6 hD6 d.xs cIdle.n d.moves d.slides d.peak)
            (settle_home_lt d.b 6 hH6 hD6 d.xs cIdle.n d.moves d.slides d.peak)).2.2.trans
            (settle_keeps_frame d.b 6 hH6 hD6 d.xs cIdle.n d.moves d.slides d.peak).2.2)
    rw [h1, hPegF.2.2.1, hplace]
    simp [placeBoard, parkKeepBoard]
    split <;> rfl
  · rw [hC.2.2.2.2.2.2.2.2.2.2.2.2.1]
    exact h5HU
  · rw [hC.2.2.2.2.2.2.2.2.2.2.2.2.2]
    exact h5DU
  · rw [hC.2.2.2.2.2.2.2.2.2.2.2.2.1, mul_live_home, Array.size_set]
    exact hH6
  · rw [hC.2.2.2.2.2.2.2.2.2.2.2.2.2, mul_live_held, Array.size_set, settle_held_eq,
      Array.size_set]
    exact hD6
  · rw [hC.2.2.2.2.2.2.2.2.2.2.2.2.2, mul_live_held, Array.size_set, settle_held_eq,
      Array.size_set]
    exact d.h7
  · intro h5
    simp [bIdle0, clearHeldBoard, Array.getElem_set]
  · intro h6
    have hsz : bIdle0.sudo_5Board_4held.size = bU.sudo_5Board_4held.size := by
      simp only [bIdle0, clearHeldBoard, Array.size_set]
    have h6u0 : 6 < bU.sudo_5Board_4held.size := by
      rw [← hsz]; exact h6
    have hEq : bIdle0.sudo_5Board_4held[6] = bU.sudo_5Board_4held[6]'h6u0 := by
      simp only [bIdle0, clearHeldBoard]
      rw [Array.getElem_set, if_neg (by decide : (5 : Nat) ≠ 6)]
    rw [hEq]
    have hmulH := mul_live_held d.b 5 6 cIdle.g d.xs cIdle.n cIdle.k d.moves d.slides d.hole
      cIdle.bench d.peak d.peakS cMul hH6 hD6 hkeep.opsLt
    have h6u : 6 < bU.sudo_5Board_4held.size := by
      rw [hmulH, Array.size_set, settle_held_eq, Array.size_set]
      exact hD6
    rw [arr_get hmulH 6 h6u, Array.getElem_set, if_pos rfl]
  · have hszH : cIdle.b0.sudo_5Board_4held.size = b.sudo_5Board_4held.size := by
      rw [hplace]
      simp [placeBoard, parkKeepBoard, Array.size_set]
      split <;> simp [Array.size_set]
    have hszO : cIdle.b0.sudo_5Board_4home.size = b.sudo_5Board_4home.size := by
      rw [hplace]
      simp [placeBoard, parkKeepBoard, Array.size_set]
      split <;> simp [Array.size_set]
    have hXD : base.xHome < cIdle.b0.sudo_5Board_4held.size := by
      rw [hszH]; exact h.shape.xD
    have hXH : base.xHome < cIdle.b0.sudo_5Board_4home.size := by
      rw [hszO]; exact h.shape.xH
    have hParkD : base.xHome <
        (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH).sudo_5Board_4held.size := by
      simp [parkKeepBoard]; exact h.shape.xD
    have hParkH : base.xHome <
        (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH).sudo_5Board_4home.size := by
      simp [parkKeepBoard]; exact h.shape.xH
    have hPlaceD : base.xHome <
        (placeBoard (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH)
          6 h.shape.spareH h.shape.spareD s.gap mv pk).sudo_5Board_4held.size :=
      hplace.symm ▸ hXD
    have hPlaceH : base.xHome <
        (placeBoard (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH)
          6 h.shape.spareH h.shape.spareD s.gap mv pk).sudo_5Board_4home.size :=
      hplace.symm ▸ hXH
    have hHeldEq : cIdle.b0.sudo_5Board_4held =
        (placeBoard (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH)
          6 h.shape.spareH h.shape.spareD s.gap mv pk).sudo_5Board_4held :=
      congrArg (fun bd => bd.sudo_5Board_4held) hplace
    have hHomeEq : cIdle.b0.sudo_5Board_4home =
        (placeBoard (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH)
          6 h.shape.spareH h.shape.spareD s.gap mv pk).sudo_5Board_4home :=
      congrArg (fun bd => bd.sudo_5Board_4home) hplace
    have hXheld : cIdle.b0.sudo_5Board_4held[base.xHome] = true :=
      (arr_get hHeldEq base.xHome hXD).trans
        ((place_held_other (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH)
          6 base.xHome h.shape.spareH h.shape.spareD s.gap mv pk (Ne.symm h.shape.xNe6)
          hParkD hPlaceD).trans (by simp [parkKeepBoard]; exact h.shape.xHeld))
    have hXarr : cIdle.b0.sudo_5Board_4home[base.xHome] = embed base.x :=
      (arr_get hHomeEq base.xHome hXH).trans
        ((place_home_other (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH)
          6 base.xHome h.shape.spareH h.shape.spareD s.gap mv pk (Ne.symm h.shape.xNe6)
          hParkH hPlaceH).trans (by simp [parkKeepBoard]; exact h.shape.xArr))
    have hsz0 : 0 < cIdle.b0.sudo_5Board_4cost.sudo_5Costs_3ops.size := hopsZ
    have hKeep := pegPack_keep cIdle base.xHome base.x cMul cIdle.m cIdle.hm (Nat.le_refl _)
      hXD hXH (by rw [hsrcI]; exact h.shape.xNe6) hXheld hXarr hsz0 hopZ
    have hKeepB : CellKeep d.b base.xHome base.x :=
      { heldLt := hKeep.heldLt, held := hKeep.held, homeLt := hKeep.homeLt, arr := hKeep.arr }
    have hMulK := mulLive_keep d.b 5 6 base.xHome cIdle.g d.xs cIdle.n cIdle.k d.moves d.slides
      d.hole cIdle.bench d.peak d.peakS cMul base.x hH6 hD6 hkeep.opsLt h.shape.xNe6
      hKeepB.heldLt hKeepB.homeLt hKeepB.held hKeepB.arr
    exact clearCell_keep bU 5 base.xHome cIdle.g mvM base.x h5HU h5DU
      (Ne.symm h.shape.xNe5) hMulK
  · refine ⟨raisedPeak d.peakS
      (countHeld (settleBoard d.b 6 hH6 hD6 d.xs cIdle.n d.moves d.slides d.peak).sudo_5Board_4held 7), ?_⟩
    have hI : bIdle0.sudo_5Board_4cost.sudo_5Costs_11peak_strict =
        bU.sudo_5Board_4cost.sudo_5Costs_11peak_strict := by
      simp only [bIdle0, clearHeldBoard]
    rw [hI]
    exact mul_live_strict d.b 5 6 cIdle.g d.xs cIdle.n cIdle.k d.moves d.slides d.hole
      cIdle.bench d.peak d.peakS cMul hH6 hD6 hkeep.opsLt
  · refine ⟨raisedHole d.hole (topIdx (school cIdle.n cIdle.g (d.xs.take cIdle.n)
      (List.replicate cIdle.bench 0) false)), ?_⟩
    have hI : bIdle0.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
        bU.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole := by
      simp only [bIdle0, clearHeldBoard]
    rw [hI]
    simp only [bU, mulNoLiveBoard, mulNoOffBoard]
    rw [ofNat_eq_natCast]
  · rw [hC.1, mul_live_row d.b 5 6 cIdle.g d.xs cIdle.n cIdle.k d.moves d.slides d.hole
      cIdle.bench d.peak d.peakS cMul hH6 hD6 hkeep.opsLt, d.hrow, hrowI, htI, hmI]
  · rw [hC.2.2.2.2.2.2.2.1, mul_live_ctrl d.b 5 6 cIdle.g d.xs cIdle.n cIdle.k d.moves
      d.slides d.hole cIdle.bench d.peak d.peakS cMul hH6 hD6 hkeep.opsLt, d.hctrl, d.hctrlN,
      hctrlI, hmI]
  · refine
      { moves := ?_
        slides := ?_
        opsSize := ?_
        ops := ?_
        peak := ?_ }
    · refine ⟨mv, mvM + pegCount cIdle.g, hmv, ?_, hpiece⟩
      rw [withPark_moves]
      simp [bIdle0, clearHeldBoard]
    · refine ⟨sl, d.slides + 2 * pegCount (d.xs.take cIdle.n), hsl, ?_, ?_⟩
      · rw [withPark_slides]
        simp [bIdle0, clearHeldBoard]
        exact mul_live_slides d.b 5 6 cIdle.g d.xs cIdle.n cIdle.k d.moves d.slides d.hole
          cIdle.bench d.peak d.peakS cMul hH6 hD6 hkeep.opsLt
      · have hprev : d.slides ≤ sl + s.tally * (2 * s.n) := by
          have hEq : cIdle.slides0 + cIdle.m * (2 * cIdle.n) = sl + s.tally * (2 * s.n) := by
            rw [hsl0, hmI, hnI]
          exact Nat.le_trans d.hsldB (Nat.le_of_eq hEq)
        have h2 : 2 * pegCount (d.xs.take cIdle.n) ≤ 2 * s.n := by
          rw [← hnI]
          exact Nat.mul_le_mul_left 2 (pegCount_take_le d.xs cIdle.n)
        have hloc : d.slides + 2 * pegCount (d.xs.take cIdle.n) ≤
            sl + s.tally * (2 * s.n) + 2 * s.n := Nat.add_le_add hprev h2
        have hstep : (s.tally + 1) * (2 * s.n) ≤ rungSlideCharge base.n s.tally := by
          unfold rungSlideCharge
          rw [h.hn]
          exact Nat.mul_le_mul_right _ (Nat.le_add_right (s.tally + 1) 2)
        have hsum : sl + s.tally * (2 * s.n) + 2 * s.n = sl + (s.tally + 1) * (2 * s.n) :=
          (Nat.add_assoc sl (s.tally * (2 * s.n)) (2 * s.n)).trans
            (congrArg (fun z => sl + z) (Nat.succ_mul s.tally (2 * s.n)).symm)
        exact Nat.le_trans hloc (Nat.le_trans (Nat.le_of_eq hsum) (Nat.add_le_add_left hstep sl))
    · rw [withPark_ops]
      have h1 : bIdle0.sudo_5Board_4cost.sudo_5Costs_3ops.size =
          bU.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
        simp [bIdle0, clearHeldBoard]
      have h2 : bU.sudo_5Board_4cost.sudo_5Costs_3ops.size =
          d.b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
        rw [mul_live_ops, Array.size_set, settle_ops]
      have h3 : d.b.sudo_5Board_4cost.sudo_5Costs_3ops.size =
          b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
        rw [pegPack_ops_eq cIdle cIdle.m cIdle.hm (Nat.le_refl _), Array.size_set, hplace,
          place_ops_delta]
        simp [parkKeepBoard]
      rw [h1, h2, h3]
    · intro i hi
      obtain ⟨c0, hc0, _⟩ := h.ops 0 (by
        have hgt := h.shape.peg.opsGt
        exact Nat.lt_trans (by decide : (0 : Nat) < 1) hgt)
      obtain ⟨c1, hc1, _⟩ := h.ops 1 h.shape.peg.opsGt
      have hszP : d.b.sudo_5Board_4cost.sudo_5Costs_3ops.size =
          b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
        rw [pegPack_ops_eq cIdle cIdle.m cIdle.hm (Nat.le_refl _), Array.size_set, hplace,
          place_ops_delta]
        simp [parkKeepBoard]
      have h1p : 1 < d.b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
        rw [hszP]; exact h.shape.peg.opsGt
      have h0p : 0 < d.b.sudo_5Board_4cost.sudo_5Costs_3ops.size :=
        Nat.lt_trans (by decide : (0 : Nat) < 1) h1p
      have hp1 : d.b.sudo_5Board_4cost.sudo_5Costs_3ops[1] = ((c1 + s.tally : Nat) : Int) := by
        have hArr := pegPack_ops_eq cIdle cIdle.m cIdle.hm (Nat.le_refl _)
        have hget := arr_get hArr 1 h1p
        rw [hget, Array.getElem_set, if_pos rfl, hmI]
        have hsz : cIdle.b0.sudo_5Board_4cost.sudo_5Costs_3ops.size =
            b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
          rw [hplace, place_ops_delta]
          simp [parkKeepBoard]
        have h1b : 1 < cIdle.b0.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
          rw [hsz]; exact h.shape.peg.opsGt
        have hplaceOps := place_ops_delta
          (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH)
          6 h.shape.spareH h.shape.spareD s.gap mv pk
        have hgetB := arr_get (hplace ▸ hplaceOps) 1 h1b
        have hpkOps : (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH).sudo_5Board_4cost.sudo_5Costs_3ops =
            b.sudo_5Board_4cost.sudo_5Costs_3ops := by simp [parkKeepBoard]
        have h1k : 1 < (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH).sudo_5Board_4cost.sudo_5Costs_3ops.size := by
          rw [hpkOps]; exact h.shape.peg.opsGt
        have hgetK := arr_get hpkOps 1 h1k
        have hcell := hgetB.trans (hgetK.trans hc1)
        have hcOps : cIdle.cOps0 = c1 := by
          apply ofNat_inj_nat
          exact cIdle.hop10.symm.trans hcell
        rw [hcOps, ofNat_eq_natCast]
      have hpNe : ∀ j, j ≠ 1 → ∀ (he : j < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
          (hp : j < d.b.sudo_5Board_4cost.sudo_5Costs_3ops.size),
          d.b.sudo_5Board_4cost.sudo_5Costs_3ops[j] = b.sudo_5Board_4cost.sudo_5Costs_3ops[j] := by
        intro j hne he hp
        have hsz0 : cIdle.b0.sudo_5Board_4cost.sudo_5Costs_3ops.size =
            b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
          rw [hplace, place_ops_delta]
          simp [parkKeepBoard]
        have hj0 : j < cIdle.b0.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
          rw [hsz0]; exact he
        have hpB : j < (pegBoard cIdle cIdle.m).sudo_5Board_4cost.sudo_5Costs_3ops.size :=
          hPackB.1.symm ▸ hp
        have hneB := pegBoard_ops_ne cIdle cIdle.m cIdle.hm (Nat.le_refl _) j hne hj0 hpB
        have hplaceOps := place_ops_delta
          (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH)
          6 h.shape.spareH h.shape.spareD s.gap mv pk
        have hpkOps : (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH).sudo_5Board_4cost.sudo_5Costs_3ops =
            b.sudo_5Board_4cost.sudo_5Costs_3ops := by simp [parkKeepBoard]
        have hjk : j < (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH).sudo_5Board_4cost.sudo_5Costs_3ops.size := by
          rw [hpkOps]; exact he
        have hcellB := (arr_get (hplace ▸ hplaceOps) j hj0).trans (arr_get hpkOps j hjk)
        have hBB : d.b.sudo_5Board_4cost.sudo_5Costs_3ops =
            (pegBoard cIdle cIdle.m).sudo_5Board_4cost.sudo_5Costs_3ops :=
          congrArg (fun bd => bd.sudo_5Board_4cost.sudo_5Costs_3ops) hPackB.1
        exact (arr_get hBB j hp).trans (hneB.trans hcellB)
      have hmulArr : bU.sudo_5Board_4cost.sudo_5Costs_3ops =
          d.b.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨0, h0p⟩ ((c0 + 1 : Nat) : Int) := by
        have hlive := mul_live_ops d.b 5 6 cIdle.g d.xs cIdle.n cIdle.k d.moves d.slides d.hole
          cIdle.bench d.peak d.peakS cMul hH6 hD6 hkeep.opsLt
        have hset := settle_ops d.b 6 hH6 hD6 d.xs cIdle.n d.moves d.slides d.peak
        have hcMul : cMul = c0 := by
          apply ofNat_inj_nat
          have h0b : 0 < cIdle.b0.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
            rw [hplace, place_ops_delta]
            simp [parkKeepBoard]
            exact Nat.lt_trans (by decide : (0 : Nat) < 1) h.shape.peg.opsGt
          have h0b : 0 < cIdle.b0.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
            have hsz : cIdle.b0.sudo_5Board_4cost.sudo_5Costs_3ops.size =
                b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
              rw [hplace, place_ops_delta]
              simp [parkKeepBoard]
            rw [hsz]
            exact Nat.lt_trans (by decide : (0 : Nat) < 1) h.shape.peg.opsGt
          have hplaceOps := place_ops_delta
            (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH)
            6 h.shape.spareH h.shape.spareD s.gap mv pk
          have hpkOps : (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH).sudo_5Board_4cost.sudo_5Costs_3ops =
              b.sudo_5Board_4cost.sudo_5Costs_3ops := by simp [parkKeepBoard]
          have h0k : 0 < (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH).sudo_5Board_4cost.sudo_5Costs_3ops.size := by
            rw [hpkOps]
            exact Nat.lt_trans (by decide : (0 : Nat) < 1) h.shape.peg.opsGt
          have hcell := (arr_get (hplace ▸ hplaceOps) 0 h0b).trans
            ((arr_get hpkOps 0 h0k).trans hc0)
          exact hopZ.symm.trans hcell
        rw [hlive]
        have hidx := settle_ops_lt d.b 0 6 hkeep.opsLt hH6 hD6 d.xs cIdle.n d.moves d.slides d.peak
        exact ops_set_transport hset 0 hidx h0p (Int.ofNat (cMul + 1)) ((c0 + 1 : Nat) : Int)
          (by rw [hcMul, ofNat_eq_natCast])
      have hclrArr : bIdle0.sudo_5Board_4cost.sudo_5Costs_3ops =
          bU.sudo_5Board_4cost.sudo_5Costs_3ops := by
        simp only [bIdle0, clearHeldBoard]
      have hNat : ∀ j (hj : j < b.sudo_5Board_4cost.sudo_5Costs_3ops.size),
          ∃ cN : Nat, b.sudo_5Board_4cost.sudo_5Costs_3ops[j] = (cN : Int) := by
        intro j hj
        obtain ⟨cN, hcN, _⟩ := h.ops j hj
        exact ⟨cN, hcN⟩
      have hbump := rung_ops_of_bump
        b.sudo_5Board_4cost.sudo_5Costs_3ops
        d.b.sudo_5Board_4cost.sudo_5Costs_3ops
        bU.sudo_5Board_4cost.sudo_5Costs_3ops
        bIdle0.sudo_5Board_4cost.sudo_5Costs_3ops
        s.tally base.mMax c0 c1 hT
        (Nat.lt_trans (by decide : (0 : Nat) < 1) h.shape.peg.opsGt) h.shape.peg.opsGt
        hc0 hc1 hNat h0p h1p hp1 hpNe hszP hmulArr hclrArr
      have hiI : i < bIdle0.sudo_5Board_4cost.sudo_5Costs_3ops.size := hbump.1 ▸ hi
      obtain ⟨c, c', he, hc, hle⟩ := hbump.2 i hi hiI
      refine ⟨c, c', he, ?_, hle⟩
      have harr : (withPark bIdle0 paint ctrlM fromH ridxH).sudo_5Board_4cost.sudo_5Costs_3ops =
          bIdle0.sudo_5Board_4cost.sudo_5Costs_3ops := by rw [withPark_ops]
      exact (arr_get harr i (harr ▸ hiI)).symm.trans hc
    · obtain ⟨pk0, hpk0, _⟩ := h.peak
      have hpkSame : pk = pk0 := ofNat_inj_nat (hpk.symm.trans hpk0)
      let occ := countHeld (b.sudo_5Board_4held.set ⟨6, h.shape.spareD⟩ true) 7
      let pk1 := if pk < occ then occ else pk
      have hpk1 : pk1 ≤ max pk0 7 := by
        rw [← hpkSame]
        change (if pk < occ then occ else pk) ≤ max pk 7
        by_cases hlt : pk < occ
        · simp [hlt]
          exact Nat.le_trans (countHeld_seven _) (Nat.le_max_right _ _)
        · simp [hlt]
          exact Nat.le_max_left _ _
      have hpkNat : cIdle.peak0 = pk1 := by
        apply ofNat_inj_nat
        calc
          ((cIdle.peak0 : Nat) : Int) = cIdle.b0.sudo_5Board_4cost.sudo_5Costs_4peak :=
            cIdle.hpeak0.symm
          _ = (placeBoard (parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH)
              6 h.shape.spareH h.shape.spareD s.gap mv pk).sudo_5Board_4cost.sudo_5Costs_4peak := by
            rw [hplace]
          _ = (pk1 : Int) := by
            simp [placeBoard, parkKeepBoard, pk1, occ]
            split <;> simp [hpk]
      have hpegPk : d.peak ≤ max pk0 7 := by
        have hB := d.hpeakB
        rw [hpkNat] at hB
        exact Nat.le_trans hB (by
          have hmax : max pk1 7 ≤ max pk0 7 := by
            exact Nat.max_le.mpr ⟨hpk1, Nat.le_max_right _ _⟩
          exact hmax)
      let pkS := raisedPeak d.peak (countHeld (d.b.sudo_5Board_4held.set ⟨6, hD6⟩ true) 7)
      let bS := settleBoard d.b 6 hH6 hD6 d.xs cIdle.n d.moves d.slides d.peak
      let hFs := settle_held_lt d.b 6 hH6 hD6 d.xs cIdle.n d.moves d.slides d.peak
      let pkM := raisedPeak pkS (countHeld (bS.sudo_5Board_4held.set ⟨6, hFs⟩ false) 7)
      have hpkS : pkS ≤ max pk0 7 :=
        Nat.le_trans (raisedPeak_carry d.peak _ (countHeld_seven _))
          (Nat.max_le.mpr ⟨hpegPk, Nat.le_max_right _ _⟩)
      have hmulPk : pkM ≤ max pk0 7 :=
        Nat.le_trans (raisedPeak_carry pkS _ (countHeld_seven _))
          (Nat.max_le.mpr ⟨hpkS, Nat.le_max_right _ _⟩)
      refine ⟨pk0, pkM, hpk0, ?_, hmulPk⟩
      rw [withPark_peak]
      have hpkB : bIdle0.sudo_5Board_4cost.sudo_5Costs_4peak =
          bU.sudo_5Board_4cost.sudo_5Costs_4peak := by
        simp only [bIdle0, clearHeldBoard]
      rw [hpkB]
      exact mul_live_peak d.b 5 6 cIdle.g d.xs cIdle.n cIdle.k d.moves d.slides d.hole
        cIdle.bench d.peak d.peakS cMul hH6 hD6 hkeep.opsLt
  · exact clearSlots_cast hslotsIdle (withPark_ops bIdle0 paint ctrlM fromH ridxH).symm
  · refine ⟨mv, mvM + pegCount cIdle.g, hmv, ?_, ?_⟩
    · rw [withPark_moves]
      simp [bIdle0, clearHeldBoard]
    · have hslack := pegPack_move_slack cIdle cIdle.m cIdle.hm (Nat.le_refl _)
      have hloop : d.moves + 2 * base.n ≤
          mv + pegCount s.gap + s.tally * pegCharge base.n base.bench := by
        have hraw := hslack
        simp only [hmv0, hmI, hnI, h.hn, hbI, h.hbench] at hraw
        exact hraw
      have hmul' : mvM ≤ d.moves + mulCharge base.n base.bench := by
        simpa [mvM, hnI, h.hn, hbI, h.hbench] using hmulLe
      have hpeg' : pegCount cIdle.g ≤ base.n := hpegG
      omega
  · refine ⟨sl, d.slides + 2 * pegCount (d.xs.take cIdle.n), hsl, ?_, ?_⟩
    · rw [withPark_slides]
      simp [bIdle0, clearHeldBoard]
      exact mul_live_slides d.b 5 6 cIdle.g d.xs cIdle.n cIdle.k d.moves d.slides d.hole
        cIdle.bench d.peak d.peakS cMul hH6 hD6 hkeep.opsLt
    · have hslack := pegPack_slide_slack cIdle cIdle.m cIdle.hm (Nat.le_refl _)
      have hloop : d.slides + 2 * base.n ≤ sl + s.tally * (2 * base.n) := by
        have hraw := hslack
        simp only [hsl0, hmI, hnI, h.hn] at hraw
        exact hraw
      have h2 : 2 * pegCount (d.xs.take cIdle.n) ≤ 2 * base.n := by
        have htake := pegCount_take_le d.xs cIdle.n
        have hle : 2 * pegCount (d.xs.take cIdle.n) ≤ 2 * cIdle.n :=
          Nat.mul_le_mul_left 2 htake
        have hcn : cIdle.n = base.n := hnI.trans h.hn
        exact Nat.le_trans hle (Nat.le_of_eq (congrArg (fun k => 2 * k) hcn))
      omega


theorem final_white_ctrl_fit_ge (ctrl tally ctrl0 done R mMax : Nat)
    (hctrl : ctrl ≤ ctrl0 + done * (3 * mMax + 5))
    (ht : tally ≤ mMax) (hd : done + 1 ≤ R)
    (hf : FitsLen (ctrl0 + (R + 1) * (3 * mMax + 5))) :
    FitsLen ((ctrl + 4 + tally) + 2) ∧
    FitsLen (((ctrl + 4 + tally) + 2) + 2) ∧
    FitsLen ((ctrl + 4 + tally) + tally) := by
  have hx : 2 * (3 * mMax + 5) = 6 * mMax + 10 := by omega
  have hsplit : done * (3 * mMax + 5) + 2 * (3 * mMax + 5) =
      (done + 2) * (3 * mMax + 5) := (Nat.add_mul done 2 (3 * mMax + 5)).symm
  have hge : (done + 2) * (3 * mMax + 5) ≤ (R + 1) * (3 * mMax + 5) :=
    Nat.mul_le_mul_right _ (by omega : done + 2 ≤ R + 1)
  have hcap : ctrl + (6 * mMax + 10) ≤ ctrl0 + (R + 1) * (3 * mMax + 5) := by
    have h1 : ctrl + (6 * mMax + 10) ≤
        ctrl0 + done * (3 * mMax + 5) + (6 * mMax + 10) := by omega
    have h2 : ctrl0 + done * (3 * mMax + 5) + (6 * mMax + 10) =
        ctrl0 + (done * (3 * mMax + 5) + 2 * (3 * mMax + 5)) := by
      rw [← hx]
      exact Nat.add_assoc _ _ _
    have h3 : ctrl0 + (done * (3 * mMax + 5) + 2 * (3 * mMax + 5)) ≤
        ctrl0 + (R + 1) * (3 * mMax + 5) := by
      rw [hsplit]
      exact Nat.add_le_add_left hge _
    exact Nat.le_trans (Nat.le_trans h1 (Nat.le_of_eq h2)) h3
  refine ⟨FitsLen.of_le hf (by omega), FitsLen.of_le hf (by omega),
    FitsLen.of_le hf (by omega)⟩

/-- A parked final white rung. The clear is the idle clear with the restored
    row and a counter two higher, and that board is the `ClimbInvK` successor. -/
theorem white_final_ge
    {done : List Nat} {r : Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvKCore done [r] b s base)
    (hM : MoveHeadroom b base.n base.bench base.mMax)
    (hS : SlideHeadroom b base.n base.mMax)
    (hge : 0 ≤ s.fromHole) (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax)
    (hhome : s.onBench = false) (hwhite : r ≠ 2)
    (hParkAt : s.parkAt = base.ladder0 + base.R)
    (hCap : climbTallyPrefix base.tally0 done [r] ≤ base.mMax) :
    ∃ b',
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
          Ecbs.clear b (5 : Int)) = .ok b' ∧
      ClimbInvKCore (done ++ [r]) [] b'
        (modelRung s base.x r (climbAt base.ladder0 base.R s.ridx) true) base ∧
      RungDeltaTight b b' base s.tally := by
  let hole := climbAt base.ladder0 base.R s.ridx
  let s' := modelRung s base.x r hole true
  obtain ⟨b', bIdle, hrun, hframe, hbenchE, hbonE, htoE, hmarkE, hlenE, ht0E, hparkE,
      hhighE, htierE, hladE, hnrE, htmaxE, h5H, h5D, h6H, h6D, h7E, h5f, h6f, hkeep,
      ⟨ps, hps⟩, ⟨hnat, hhn⟩, _hrowIdle, _hctrlIdle, hδ, hslots, hpieceM, hpieceS⟩ :=
    parked_clear_ge h hM hS hge hm hT hhome
  obtain ⟨hgap, htall, hon, hwork, hctrlM, hhighM, hrowM, hfromM, hridxM, ht0M,
      hparkM, hnM, hkM, hbM⟩ := model_final_white_ge s base.x r hole hwhite hge
  have hrowE : b'.sudo_5Board_3row =
      embed (paintRed (afterPark s.row s.fromHole s.parkAt hole r) s.t0 s.tally) := by
    rw [hframe, withPark_row]
  have hctrlE : b'.sudo_5Board_4cost.sudo_5Costs_4ctrl = ((s.ctrl + 4 + s.tally : Nat) : Int) := by
    rw [hframe, withPark_ctrl]
  have hfromE : b'.sudo_5Board_11parked_from = ((hole : Nat) : Int) := by
    rw [hframe, withPark_from]
  have hridxE : b'.sudo_5Board_8rung_idx = Int.ofNat (s.ridx + 1) := by
    rw [hframe, withPark_ridx]
  have hlenB : b'.sudo_5Board_9tally_len = (s.tally : Int) := by
    rw [hframe, withPark_len, hlenE]
  have ht0B : b'.sudo_5Board_6tally0 = (s.t0 : Int) := by
    rw [hframe, withPark_tally0, ht0E]
  have hparkB : b'.sudo_5Board_9park_hole = (s.parkAt : Int) := by
    rw [hframe, withPark_park, hparkE]
  have hhighB : b'.sudo_5Board_4cost.sudo_5Costs_15control_highest = (s.high : Int) := by
    rw [hframe, withPark_high, hhighE]
  have hmarkB : b'.sudo_5Board_9marker_on = false := by
    rw [hframe, withPark_marker, hmarkE]
  have hbonB : b'.sudo_5Board_8bench_on = true := by
    rw [hframe, withPark_on, hbonE]
  have htoB : b'.sudo_5Board_8bench_to = (5 : Int) := by
    rw [hframe, withPark_to, htoE]
  have hbenchB : b'.sudo_5Board_5bench = bIdle.sudo_5Board_5bench := by
    rw [hframe, withPark_bench]
  have htierB : b'.sudo_5Board_1t = b.sudo_5Board_1t := by
    rw [hframe, withPark_tier, htierE]
  have hladB : b'.sudo_5Board_7ladder0 = b.sudo_5Board_7ladder0 := by
    rw [hframe, withPark_ladder, hladE]
  have hnrB : b'.sudo_5Board_6nrungs = b.sudo_5Board_6nrungs := by
    rw [hframe, withPark_nrungs, hnrE]
  have htmaxB : b'.sudo_5Board_4cost.sudo_5Costs_9tally_max =
      b.sudo_5Board_4cost.sudo_5Costs_9tally_max := by
    rw [hframe, withPark_tmax, htmaxE]
  have hidx : s.ridx < base.R := by
    rw [h.idx]
    have hk := h.kLe
    simp [List.length_append] at hk
    omega
  have hlenRow : s'.row.length = s.row.length := by
    rw [hrowM, paintRed_length, afterPark_length]
  have hStep := successor_hole base.ladder0 base.R s.ridx s.parkAt s.row.length
    h.shape.park.l0pos hidx hParkAt h.shape.park.holeLt
  have hinv : ClimbInv b' s' := by
    refine
      { hG := ?_
        hGs := ?_
        marker := hmarkB
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
    · rw [hframe, withPark_home]
      exact h5H
    · rw [hframe, withPark_held]
      exact h5D
    · rw [hlenB, htall]
    · rw [hctrlE, hctrlM]
    · rw [hhighB, hhighM]
    · rw [ht0B, ht0M]
    · rw [hrowE, hrowM]
    · rw [hparkB, hparkM]
    · rw [hfromE, hfromM]
    · rw [hridxE, hridxM, ofNat_eq_natCast]
    · intro hOff
      rw [hon] at hOff
      cases hOff
    · intro _
      have hnle : s.n ≤ s.benchlen := by
        have hsp := h.shape.peg.span
        omega
      have hprod := fieldMul_len s.n s.k s.benchlen s.gap
        (cubeTimes s.n s.k s.benchlen s.gap s.tally) hnle
      have htake : (fieldMul s.n s.k s.benchlen s.gap
          (cubeTimes s.n s.k s.benchlen s.gap s.tally)).take s.n =
          fieldMul s.n s.k s.benchlen s.gap
            (cubeTimes s.n s.k s.benchlen s.gap s.tally) :=
        List.take_of_length_le (Nat.le_of_eq hprod)
      refine ⟨hbonB, htoB, ?_, ?_⟩
      · rw [hbenchB, hbenchE, hgap, hnM, hbM, htake]
      · rw [hwork]
        exact hgap.symm
  have hseg : RowSeg s'.row s'.t0 s'.tally true := by
    have hsegR := rungRow_final_seg s.row s.fromHole s.parkAt hole s.t0 s.tally r
      h.shape.seg h.parkBelow h.holeBelow (Or.inr (h.fromBelow hge))
    rw [hrowM, ht0M, htall]
    exact hsegR
  have hdone : done.length + 1 ≤ base.R := by
    have hk := h.kLe
    simp [List.length_append] at hk
    exact hk
  have hfits := final_white_ctrl_fit_ge s.ctrl s.tally base.ctrl0 done.length base.R
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
    · rw [hladB, h.shape.park.ladder0B]
    · rw [hnrB, h.shape.park.nrungsB]
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
  have h6B : 6 < b'.sudo_5Board_4held.size := by
    rw [hframe, withPark_held]; exact h6D
  have h6H' : 6 < b'.sudo_5Board_4home.size := by
    rw [hframe, withPark_home]; exact h6H
  have h7B : 7 ≤ b'.sudo_5Board_4held.size := by
    rw [hframe, withPark_held]; exact h7E
  have h6fB : b'.sudo_5Board_4held[6] = false := by
    have hEq : b'.sudo_5Board_4held = bIdle.sudo_5Board_4held := by
      rw [hframe, withPark_held]
    exact (arr_get hEq 6 h6B).trans (h6f h6D)
  have h5fB : b'.sudo_5Board_4held[5] = false := by
    have hEq : b'.sudo_5Board_4held = bIdle.sudo_5Board_4held := by
      rw [hframe, withPark_held]
    have h5B : 5 < b'.sudo_5Board_4held.size := by
      rw [hframe, withPark_held]; exact h5D
    exact (arr_get hEq 5 h5B).trans (h5f h5D)
  have hkeepB : CellKeep b' base.xHome base.x := by
    have hHeld : b'.sudo_5Board_4held = bIdle.sudo_5Board_4held := by
      rw [hframe, withPark_held]
    have hHome : b'.sudo_5Board_4home = bIdle.sudo_5Board_4home := by
      rw [hframe, withPark_home]
    exact
      { heldLt := by rw [hHeld]; exact hkeep.heldLt
        held := (arr_get hHeld base.xHome (by rw [hHeld]; exact hkeep.heldLt)).trans hkeep.held
        homeLt := by rw [hHome]; exact hkeep.homeLt
        arr := (arr_get hHome base.xHome (by rw [hHome]; exact hkeep.homeLt)).trans hkeep.arr }
  have hpeg' : PegRead b' s' base := by
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
    · have hsz : b'.sudo_5Board_4cost.sudo_5Costs_3ops.size =
          b.sudo_5Board_4cost.sudo_5Costs_3ops.size := hδ.opsSize
      exact hsz ▸ h.shape.peg.opsGt
    · have h1 : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size := h.shape.peg.opsGt
      obtain ⟨_c, c', _he, hc, _⟩ := hδ.ops 1 h1
      exact ⟨c', hc⟩
    · exact ⟨ps, by rw [hframe, withPark_strict, hps]⟩
    · exact ⟨hnat, by rw [hframe, withPark_hole, hhn]⟩
    · rw [hgap]
      have hspan : 3 * (s.n - 1) < s.benchlen := by
        have hs := h.shape.peg.span
        omega
      have hnle : s.n ≤ s.benchlen := by
        have hs := h.shape.peg.span
        omega
      have htri := fieldMul_trits s.n s.k s.benchlen s.gap
        (cubeBenchIter s.n s.k s.benchlen s.gap s.tally) hspan hnle
      rw [cubeBenchIter_prefix s.n s.k s.benchlen s.gap (h.shape.gapLen)] at htri
      exact htri
    · intro hpos
      rw [ht0M, htall, hhighM]
      exact Nat.le_of_eq (h.highTop (htall.symm ▸ hpos)).symm
    · rw [ht0M, htall]; exact h.shape.peg.fitRow
    · rw [htall]; exact h.shape.peg.fitTall
    · rw [hctrlM, htall]; exact hfits.2.2
    · rw [hnM]; exact h.shape.peg.n_pos
    · rw [hnM, hbM]; exact h.shape.peg.span
    · rw [hbM]; exact h.shape.peg.small
    · rw [hnM]; exact h.shape.peg.n_small
    · rw [hnM]; exact h.shape.peg.fitN
    · rw [hbM]; exact h.shape.peg.fitBn
    · exact h.shape.peg.fit3
  have hnle : s.n ≤ s.benchlen := by
    have hsp := h.shape.peg.span
    omega
  have hgapLen : s'.gap.length = s'.n := by
    rw [hgap, hnM]
    exact fieldMul_len s.n s.k s.benchlen s.gap
      (cubeTimes s.n s.k s.benchlen s.gap s.tally) hnle
  have hshape : ClimbShape b' s' [] base :=
    shape_refresh h.shape b' s' [] hnM hkM hbM hgapLen
      hseg h6B h6H' h6fB h7B
      (by intro _; exact h5fB)
      (by intro hOff; rw [hon] at hOff; cases hOff)
      hkeepB.heldLt hkeepB.homeLt hkeepB.held hkeepB.arr
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
  have htmax : ∃ tmax : Nat,
      b'.sudo_5Board_4cost.sudo_5Costs_9tally_max = (tmax : Int) ∧
        (0 < s'.tally → tmax < 2 * s'.tally) := by
    obtain ⟨tmax, htm, hnote⟩ := h.tmaxLt
    refine ⟨tmax, by rw [htmaxB, htm], ?_⟩
    intro hpos
    have hlt := hnote (by rw [← htall]; exact hpos)
    rw [htall]
    exact hlt
  have hK := climbInvKCore_succ h hinv hδ hCap hshape h.holeBelow htmax rfl
  exact ⟨b', hrun, hK, rungTight_of_clear hδ hpieceM hpieceS
    (opsTight_of_clear hδ hT hslots)⟩

theorem open_white_ctrl_fit_ge (ctrl tally ctrl0 done R mMax : Nat)
    (hctrl : ctrl ≤ ctrl0 + done * (3 * mMax + 5))
    (ht : tally ≤ mMax) (hd : done + 2 ≤ R)
    (hf : FitsLen (ctrl0 + (R + 1) * (3 * mMax + 5))) :
    FitsLen (ctrl + 4 + 3 * tally) ∧
    FitsLen ((ctrl + 4 + 3 * tally) + 2) ∧
    FitsLen ((ctrl + 4 + 3 * tally) + 4) ∧
    FitsLen (ctrl + 4 + 3 * tally + 2 * tally) := by
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

/-- A parked non-final white rung. The clear is the idle clear transported
    across the resume frame; doubling that frame is `tally_double_withPark`. -/
theorem white_open_ge
    {done rest : List Nat} {r : Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvKCore done (r :: rest) b s base)
    (hM : MoveHeadroom b base.n base.bench base.mMax)
    (hS : SlideHeadroom b base.n base.mMax)
    (hge : 0 ≤ s.fromHole) (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax)
    (hhome : s.onBench = false) (hwhite : r ≠ 2) (hrest : rest ≠ [])
    (hParkAt : s.parkAt = base.ladder0 + base.R)
    (hCap : climbTallyPrefix base.tally0 done (r :: rest) ≤ base.mMax) :
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
          Ecbs.tally_double b) = .ok b' ∧
      ClimbInvKCore (done ++ [r]) rest b'
        (modelRung s base.x r (climbAt base.ladder0 base.R s.ridx) false) base ∧
      RungDeltaTight b b' base s.tally := by
  let hole := climbAt base.ladder0 base.R s.ridx
  let s' := modelRung s base.x r hole false
  have habove := h.srcAbove hge
  obtain ⟨bClear, bIdle, hrun, hframe, hbenchE, hbonE, htoE, hmarkE, hlenE, ht0E, hparkE,
      hhighE, htierE, hladE, hnrE, htmaxE, h5H, h5D, h6H, h6D, h7E, h5f, h6f, hkeep,
      ⟨ps, hps⟩, ⟨hnat, hhn⟩, hrowIdle, hctrlIdle, hδ, hslots, hpieceM, hpieceS⟩ :=
    parked_clear_ge h hM hS hge hm hT hhome
  obtain ⟨hgap, htall, hon, hwork, hctrlM, hhighM, hrowM, hfromM, hridxM, ht0M,
      hparkM, hnM, hkM, hbM⟩ := model_open_white_ge s base.x r hole hwhite hge
  let c0 := s.ctrl + 2 + s.tally
  let xs := paintRed (afterPark s.row (-1) s.parkAt hole r) s.t0 s.tally
  let xsP := paintRed (afterPark s.row s.fromHole s.parkAt hole r) s.t0 s.tally
  have hgeLen : 2 ≤ (r :: rest).length := by
    cases rest with
    | nil => exact absurd rfl hrest
    | cons _ _ => simp
  have hRoom : s.t0 + 2 * s.tally ≤ base.control := h.openRoom hgeLen
  have hHighEq : s.high = s.t0 + s.tally - 1 := h.highTop hm
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
  have hfits := open_white_ctrl_fit_ge s.ctrl s.tally base.ctrl0 done.length base.R
    base.mMax h.ctrlLe hT hdone2 base.fitCtrl
  have hFitI : FitsLen (s.t0 + 2 * s.tally) :=
    (double_index_fit_le hRoom base.fitControl).1
  have hFitM : FitsLen (2 * s.tally) :=
    (double_index_fit_le hRoom base.fitControl).2.1
  have hRowLen : s.t0 + 2 * s.tally ≤ s.row.length := by
    rw [h.shape.rowLen]; exact hRoom
  have hRedIdle : ∀ j (hj : j < s.tally),
      xs[s.t0 + j]'(by
        simp [xs, paintRed_length, afterPark_length]
        exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj s.t0) h.shape.seg.room) = 2 := by
    intro j hj
    simpa [xs] using paintRed_get_lo (afterPark s.row (-1) s.parkAt hole r) s.t0 s.tally j hj
      (by rw [afterPark_length]; exact h.shape.seg.room)
  have hRedPark : ∀ j (hj : j < s.tally),
      xsP[s.t0 + j]'(by
        simp [xsP, paintRed_length, afterPark_length]
        exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj s.t0) h.shape.seg.room) = 2 := by
    intro j hj
    simpa [xsP] using paintRed_get_lo (afterPark s.row s.fromHole s.parkAt hole r) s.t0 s.tally j hj
      (by rw [afterPark_length]; exact h.shape.seg.room)
  have hZeroIdle : ∀ k (hk : k < s.tally),
      xs[s.t0 + s.tally + k]'(by
        simp [xs, paintRed_length, afterPark_length]
        exact Nat.lt_of_lt_of_le (by omega) hRowLen) = 0 := by
    intro k hk
    have hjLen : s.t0 + s.tally + k < s.row.length := by
      have hlt : s.t0 + s.tally + k < s.t0 + 2 * s.tally := by omega
      exact Nat.lt_of_lt_of_le hlt hRowLen
    have hsrc := h.openZero hgeLen k hk (by simpa [Nat.add_assoc] using hjLen)
    have hAp := afterPark_get s.row (-1) s.parkAt hole r (s.t0 + s.tally + k)
      (Nat.lt_of_lt_of_le h.parkBelow (by omega))
      (Nat.lt_of_lt_of_le h.holeBelow (by omega))
      (Or.inl (by decide : (-1 : Int) < 0)) hjLen
    have hget := paintRed_get_hi (afterPark s.row (-1) s.parkAt hole r) s.t0 s.tally
      (s.t0 + s.tally + k) (by omega) (by rw [afterPark_length]; exact hjLen)
    simpa [xs] using hget.trans (hAp.trans hsrc)
  have hZeroPark : ∀ k (hk : k < s.tally),
      xsP[s.t0 + s.tally + k]'(by
        simp [xsP, paintRed_length, afterPark_length]
        exact Nat.lt_of_lt_of_le (by omega) hRowLen) = 0 := by
    intro k hk
    have hjLen : s.t0 + s.tally + k < s.row.length := by
      have hlt : s.t0 + s.tally + k < s.t0 + 2 * s.tally := by omega
      exact Nat.lt_of_lt_of_le hlt hRowLen
    have hsrc := h.openZero hgeLen k hk (by simpa [Nat.add_assoc] using hjLen)
    have hAp := afterPark_get s.row s.fromHole s.parkAt hole r (s.t0 + s.tally + k)
      (Nat.lt_of_lt_of_le h.parkBelow (by omega))
      (Nat.lt_of_lt_of_le h.holeBelow (by omega))
      (Or.inr (Nat.lt_of_lt_of_le (h.fromBelow hge) (by omega))) hjLen
    have hget := paintRed_get_hi (afterPark s.row s.fromHole s.parkAt hole r) s.t0 s.tally
      (s.t0 + s.tally + k) (by omega) (by rw [afterPark_length]; exact hjLen)
    simpa [xsP] using hget.trans (hAp.trans hsrc)
  have hctrlN : bIdle.sudo_5Board_1t.sudo_4Tier_7control = (base.control : Int) := by
    rw [htierE, h.shape.tierC]
  have htallD := tally_double_withPark bIdle xs xsP s.t0 s.tally c0
    (s.t0 + s.tally - 1) base.control tmax0 ((hole : Nat) : Int) (Int.ofNat (s.ridx + 1))
    hm hlenE ht0E hrowIdle
    (by simp [xs, paintRed_length, afterPark_length]; exact hRowLen)
    (by simp [xsP, paintRed_length, afterPark_length]; exact hRowLen)
    hRedIdle hRedPark hZeroIdle hZeroPark hctrlN
    (by rw [hhighE, hHighEq]) rfl hctrlIdle hRoom hFitI
    (FitsLen.of_le hfits.1 (by omega))
    (FitsLen.of_le hfits.2.1 (by omega))
    hFitM (htmaxE.trans hMax) hNote
  have hctr : ((c0 + 2 : Nat) : Int) = ((s.ctrl + 4 + s.tally : Nat) : Int) := by
    unfold c0
    exact congrArg (fun n : Nat => (n : Int)) (by omega)
  have hmatch : withPark bIdle (embed xsP) (((c0 + 2 : Nat) : Int))
      ((hole : Nat) : Int) (Int.ofNat (s.ridx + 1)) = bClear := by
    rw [hctr, hframe]
  rw [hmatch] at htallD
  let bIn :=
    { bIdle with
        sudo_5Board_3row := embed (paintOnes (paintOnes xs s.t0 s.tally) (s.t0 + s.tally) s.tally)
        sudo_5Board_9tally_len := Int.ofNat (2 * s.tally)
        sudo_5Board_4cost := { bIdle.sudo_5Board_4cost with
          sudo_5Costs_4ctrl := Int.ofNat (c0 + 2 * s.tally)
          sudo_5Costs_15control_highest := ((s.t0 + 2 * s.tally - 1 : Nat) : Int)
          sudo_5Costs_9tally_max := Int.ofNat (2 * s.tally) } }
  have hmvIn : bIn.sudo_5Board_4cost.sudo_5Costs_5moves =
      bIdle.sudo_5Board_4cost.sudo_5Costs_5moves := rfl
  have hslIn : bIn.sudo_5Board_4cost.sudo_5Costs_6slides =
      bIdle.sudo_5Board_4cost.sudo_5Costs_6slides := rfl
  have hopsIn : bIn.sudo_5Board_4cost.sudo_5Costs_3ops =
      bIdle.sudo_5Board_4cost.sudo_5Costs_3ops := rfl
  have hpkIn : bIn.sudo_5Board_4cost.sudo_5Costs_4peak =
      bIdle.sudo_5Board_4cost.sudo_5Costs_4peak := rfl
  let b' := withPark bIn
    (embed (paintOnes (paintOnes xsP s.t0 s.tally) (s.t0 + s.tally) s.tally))
    (Int.ofNat (c0 + 2 + 2 * s.tally))
    ((hole : Nat) : Int) (Int.ofNat (s.ridx + 1))
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
          Ecbs.tally_double b) = .ok b' := by
    rw [hrun, ok_bind]
    simpa [b', bIn, xs, xsP, c0] using htallD
  have hlenRow : s'.row.length = s.row.length := by
    rw [hrowM, paintOnes_length, paintOnes_length, paintRed_length, afterPark_length]
  have hidx : s.ridx < base.R := by
    rw [h.idx]
    omega
  have hStep := successor_hole base.ladder0 base.R s.ridx s.parkAt s.row.length
    h.shape.park.l0pos hidx hParkAt h.shape.park.holeLt
  have hctrlNat : c0 + 2 + 2 * s.tally = s'.ctrl := by
    unfold s' c0
    rw [hctrlM]
    omega
  have hinv : ClimbInv b' s' := by
    refine
      { hG := by unfold b'; rw [withPark_home]; exact h5H
        hGs := by unfold b'; rw [withPark_held]; exact h5D
        marker := by unfold b'; rw [withPark_marker]; exact hmarkE
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
    · unfold b'; rw [withPark_len, htall]
      rfl
    · unfold b'; rw [withPark_ctrl, hctrlNat, ofNat_eq_natCast]
    · unfold b'; rw [withPark_high, hhighM]
    · unfold b'; rw [withPark_tally0, ht0E, ht0M]
    · unfold b'; rw [withPark_row, hrowM]
    · unfold b'; rw [withPark_park, hparkE, hparkM]
    · unfold b'; rw [withPark_from, hfromM]
    · unfold b'; rw [withPark_ridx, hridxM, ofNat_eq_natCast]
    · intro hOff
      rw [hon] at hOff
      cases hOff
    · intro _
      have hnle : s.n ≤ s.benchlen := by
        have hsp := h.shape.peg.span
        omega
      have hprod := fieldMul_len s.n s.k s.benchlen s.gap
        (cubeTimes s.n s.k s.benchlen s.gap s.tally) hnle
      have htake : (fieldMul s.n s.k s.benchlen s.gap
          (cubeTimes s.n s.k s.benchlen s.gap s.tally)).take s.n =
          fieldMul s.n s.k s.benchlen s.gap
            (cubeTimes s.n s.k s.benchlen s.gap s.tally) :=
        List.take_of_length_le (Nat.le_of_eq hprod)
      refine ⟨by unfold b'; rw [withPark_on]; exact hbonE, by unfold b'; rw [withPark_to]; exact htoE, ?_, ?_⟩
      · unfold b'; rw [withPark_bench, hbenchE, hgap, hnM, hbM, htake]
      · rw [hwork]
        exact hgap.symm
  have hempty : rest.isEmpty = false := by
    cases rest with
    | nil => exact absurd rfl hrest
    | cons _ _ => rfl
  have hseg : RowSeg s'.row s'.t0 s'.tally rest.isEmpty := by
    rw [hempty]
    have hsegR := rungRow_open_white_seg s.row s.fromHole s.parkAt hole s.t0 s.tally r
      h.shape.seg h.parkBelow h.holeBelow (Or.inr (h.fromBelow hge))
      (by rw [h.shape.rowLen]; exact hRoom) hwhite
    have hrowEq : s'.row = rungRow s.row s.fromHole s.parkAt hole s.t0 s.tally r false := by
      simp [s', modelRung, rungRow]
    rw [hrowEq, show s'.t0 = s.t0 by simp [s', modelRung], htall]
    exact hsegR
  have hδ' : RungDelta b b' base s.tally := by
    apply rungDelta_cost hδ
    · unfold b'; rw [withPark_moves, hmvIn, hframe, withPark_moves]
    · unfold b'; rw [withPark_slides, hslIn, hframe, withPark_slides]
    · unfold b'; rw [withPark_ops, hopsIn, hframe, withPark_ops]
    · unfold b'; rw [withPark_peak, hpkIn, hframe, withPark_peak]
  have hTight : RungDeltaTight b b' base s.tally :=
    rungTight_cost (rungTight_of_clear hδ hpieceM hpieceS
      (opsTight_of_clear hδ hT hslots))
      (by unfold b'; rw [withPark_moves, hmvIn, hframe, withPark_moves])
      (by unfold b'; rw [withPark_slides, hslIn, hframe, withPark_slides])
      (by unfold b'; rw [withPark_ops, hopsIn, hframe, withPark_ops])
      (by unfold b'; rw [withPark_peak, hpkIn, hframe, withPark_peak])
  have hpark' : ParkRead b' s' rest base := by
    refine
      { ladder0B := by unfold b'; rw [withPark_ladder, hladE, h.shape.park.ladder0B]
        nrungsB := by unfold b'; rw [withPark_nrungs, hnrE, h.shape.park.nrungsB]
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
        unfold b'; rw [withPark_ladder, hladE, h.shape.park.ladder0B, ← ofNat_eq_natCast]
      have hN : b'.sudo_5Board_6nrungs = Int.ofNat base.R := by
        unfold b'; rw [withPark_nrungs, hnrE, h.shape.park.nrungsB, ← ofNat_eq_natCast]
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
      · have hlt : hole < s.row.length := h.shape.park.holeLt
        rw [← hlenRow] at hlt
        simpa [Int.toNat_ofNat] using hlt
      · have hlt : hole < s.row.length := h.shape.park.holeLt
        rw [h.shape.rowLen] at hlt
        simpa [Int.toNat_ofNat] using hlt
      · rw [hhighM]
        have hhi : hole < s.t0 := h.holeBelow
        simpa [Int.toNat_ofNat] using (by omega : hole ≤ s.t0 + 2 * s.tally - 1)
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
      have hneS : s.fromHole.toNat ≠ climbAt base.ladder0 base.R (s.ridx + 1) := by
        have hL : 0 < base.ladder0 := h.shape.park.l0pos
        have hi : s.ridx + 1 ≤ base.R := by
          rw [h.idx]
          omega
        have hltC : climbAt base.ladder0 base.R (s.ridx + 1) <
            climbAt base.ladder0 base.R s.ridx := by
          unfold climbAt
          omega
        omega
      have hget := rungRow_white_below_ge s.row s.fromHole s.parkAt hole s.t0 s.tally r
        (climbAt base.ladder0 base.R (s.ridx + 1)) hwhite hneP hneH
        (Or.inr hneS) hbelow hlt0
      have hrowR : s'.row = rungRow s.row s.fromHole s.parkAt hole s.t0 s.tally r false := by
        simp [s', modelRung]
      have hhead : (r :: rest)[1]'(by simp [hrs]) = r2 := by simp [hrs]
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
        omega
      have hclimb : climbAt base.ladder0 base.R (s.ridx + 1 + k) =
          climbAt base.ladder0 base.R (s.ridx + (1 + k)) := by
        simp [Nat.add_assoc]
      have hcol' :=
        (getElem_congr (c := s.row)
          (i := climbAt base.ladder0 base.R (s.ridx + 1 + k))
          (j := climbAt base.ladder0 base.R (s.ridx + (1 + k)))
          (h := hlt0) hclimb).trans hcol
      have hget := rungRow_white_below_ge s.row s.fromHole s.parkAt hole s.t0 s.tally r
        (climbAt base.ladder0 base.R (s.ridx + 1 + k)) hwhite hneP hneH
        (Or.inr hneS) hbelow hlt0
      have hrowR : s'.row = rungRow s.row s.fromHole s.parkAt hole s.t0 s.tally r false := by
        simp [s', modelRung]
      have hixEq : climbAt base.ladder0 base.R (s'.ridx + k) =
          climbAt base.ladder0 base.R (s.ridx + 1 + k) := by rw [hridxM]
      have hmove := getElem_congr (c := s'.row)
        (i := climbAt base.ladder0 base.R (s'.ridx + k))
        (j := climbAt base.ladder0 base.R (s.ridx + 1 + k))
        (h := hlt) hixEq
      have hcoll := getElem_congr_coll (c := s'.row)
        (d := rungRow s.row s.fromHole s.parkAt hole s.t0 s.tally r false)
        (i := climbAt base.ladder0 base.R (s.ridx + 1 + k))
        (h := by rw [← hixEq]; exact hlt) hrowR
      have hlist := cons_tail r rest k hk
      refine ⟨?_, ?_⟩
      · exact hmove.trans (hcoll.trans ((hget.trans hcol').trans hlist))
      · exact fun hz => hnz ((cons_tail r rest k hk).trans hz)
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
      { opsGt := by
          have hsz : b'.sudo_5Board_4cost.sudo_5Costs_3ops.size =
              b.sudo_5Board_4cost.sudo_5Costs_3ops.size := hδ'.opsSize
          exact hsz ▸ h.shape.peg.opsGt
        cOps := by
          have h1 : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size := h.shape.peg.opsGt
          obtain ⟨_c, c', _he, hc, _⟩ := hδ'.ops 1 h1
          exact ⟨c', hc⟩
        peakS := ⟨ps, by unfold b'; rw [withPark_strict]; exact hps⟩
        holeM := ⟨hnat, by unfold b'; rw [withPark_hole]; exact hhn⟩
        trits := by
          rw [hgap]
          have hspan : 3 * (s.n - 1) < s.benchlen := by
            have hs := h.shape.peg.span
            omega
          have hnle : s.n ≤ s.benchlen := by
            have hs := h.shape.peg.span
            omega
          have htri := fieldMul_trits s.n s.k s.benchlen s.gap
            (cubeBenchIter s.n s.k s.benchlen s.gap s.tally) hspan hnle
          rw [cubeBenchIter_prefix s.n s.k s.benchlen s.gap h.shape.gapLen] at htri
          exact htri
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
    · intro hpos
      rw [ht0M, htall, hhighM]
      omega
    · rw [ht0M, htall]; exact hFitI
    · rw [htall]; exact hFitM
    · rw [hctrlM, htall]; exact hfits.2.2.2
    · rw [hnM]; exact h.shape.peg.n_pos
    · rw [hnM, hbM]; exact h.shape.peg.span
    · rw [hbM]; exact h.shape.peg.small
    · rw [hnM]; exact h.shape.peg.n_small
    · rw [hnM]; exact h.shape.peg.fitN
    · rw [hbM]; exact h.shape.peg.fitBn
    · exact h.shape.peg.fit3
  have hnle : s.n ≤ s.benchlen := by
    have hsp := h.shape.peg.span
    omega
  have hgapLen : s'.gap.length = s'.n := by
    rw [hgap, hnM]
    exact fieldMul_len s.n s.k s.benchlen s.gap
      (cubeTimes s.n s.k s.benchlen s.gap s.tally) hnle
  have hshape : ClimbShape b' s' rest base :=
    shape_refresh h.shape b' s' rest hnM hkM hbM hgapLen hseg
      (by unfold b'; rw [withPark_held]; exact h6D)
      (by unfold b'; rw [withPark_home]; exact h6H)
      (by
        have hEq : b'.sudo_5Board_4held = bIdle.sudo_5Board_4held := by
          unfold b'; rw [withPark_held]
        have h6 : 6 < b'.sudo_5Board_4held.size := by rw [hEq]; exact h6D
        exact (arr_get hEq 6 h6).trans (h6f h6D))
      (by unfold b'; rw [withPark_held]; exact h7E)
      (by
        intro _
        have hEq : b'.sudo_5Board_4held = bIdle.sudo_5Board_4held := by
          unfold b'; rw [withPark_held]
        have h5 : 5 < b'.sudo_5Board_4held.size := by rw [hEq]; exact h5D
        exact (arr_get hEq 5 h5).trans (h5f h5D))
      (by intro hOff; rw [hon] at hOff; cases hOff)
      (by
        have hEq : b'.sudo_5Board_4held = bIdle.sudo_5Board_4held := by unfold b'; rw [withPark_held]
        rw [hEq]; exact hkeep.heldLt)
      (by
        have hEq : b'.sudo_5Board_4home = bIdle.sudo_5Board_4home := by unfold b'; rw [withPark_home]
        rw [hEq]; exact hkeep.homeLt)
      (by
        have hEq : b'.sudo_5Board_4held = bIdle.sudo_5Board_4held := by unfold b'; rw [withPark_held]
        exact (arr_get hEq base.xHome (by rw [hEq]; exact hkeep.heldLt)).trans hkeep.held)
      (by
        have hEq : b'.sudo_5Board_4home = bIdle.sudo_5Board_4home := by unfold b'; rw [withPark_home]
        exact (arr_get hEq base.xHome (by rw [hEq]; exact hkeep.homeLt)).trans hkeep.arr)
      (by unfold b'; rw [withPark_tier, htierE, hnM]; exact h.shape.tierN)
      (by unfold b'; rw [withPark_tier, htierE, hkM]; exact h.shape.tierK)
      (by unfold b'; rw [withPark_tier, htierE, hbM]; exact h.shape.tierB)
      (by unfold b'; rw [withPark_tier, htierE]; exact h.shape.tierW)
      (by unfold b'; rw [withPark_tier, htierE]; exact h.shape.tierH)
      (by unfold b'; rw [withPark_tier, htierE]; exact h.shape.tierR)
      (by unfold b'; rw [withPark_tier, htierE]; exact h.shape.tierCg)
      (by unfold b'; rw [withPark_tier, htierE]; exact h.shape.tierC)
      (by rw [hlenRow]; exact h.shape.rowLen)
      hpark' hpeg'
  have htmax : ∃ tmax : Nat,
      b'.sudo_5Board_4cost.sudo_5Costs_9tally_max = (tmax : Int) ∧
        (0 < s'.tally → tmax < 2 * s'.tally) := by
    refine ⟨2 * s.tally, ?_, ?_⟩
    · unfold b'; rw [withPark_tmax]
      simp
    · intro hpos
      rw [htall]
      omega
  have hK := climbInvKCore_succ h (by simpa [hempty] using hinv) hδ' hCap
    (by simpa [hempty] using hshape) h.holeBelow (by simpa [hempty] using htmax) rfl
  exact ⟨b', hprog, by simpa [hempty] using hK, by simpa [hempty] using hTight⟩

/-- The emitted parked clear is `withPark` of the unparked clear. The keep-park
    copy for `fromHole ≥ 0` is `withPark` of the idle entry copy; `withPark`
    then pushes through the peg loop, the gap mul, and `clear`, and a second
    park overwrites the idle frame. -/
theorem parked_clear_unparked
    {done rest : List Nat} {r : Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvKCore done (r :: rest) b s base)
    (hM : MoveHeadroom b base.n base.bench base.mMax)
    (hS : SlideHeadroom b base.n base.mMax)
    (hge : 0 ≤ s.fromHole) (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax)
    (hhome : s.onBench = false)
    (hxLen : base.x.length = base.n) (hxT : allTritList base.x) :
    ∃ bClearU bCube bRed,
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
          (Int.ofNat (s.ridx + 1))) ∧
      Ecbs.cube (withPark bClearU
          (embed (paintRed (afterPark s.row s.fromHole s.parkAt
            (climbAt base.ladder0 base.R s.ridx) r) s.t0 s.tally))
          (Int.ofNat (s.ctrl + 4 + s.tally))
          (((climbAt base.ladder0 base.R s.ridx : Nat) : Int))
          (Int.ofNat (s.ridx + 1)))
          ((6 : Nat) : Int) ((5 : Nat) : Int) =
        .ok (withPark bCube
          (embed (paintRed (afterPark s.row s.fromHole s.parkAt
            (climbAt base.ladder0 base.R s.ridx) r) s.t0 s.tally))
          (Int.ofNat (s.ctrl + 4 + s.tally))
          (((climbAt base.ladder0 base.R s.ridx : Nat) : Int))
          (Int.ofNat (s.ridx + 1))) ∧
      Ecbs.mul (withPark bCube
          (embed (paintRed (afterPark s.row s.fromHole s.parkAt
            (climbAt base.ladder0 base.R s.ridx) r) s.t0 s.tally))
          (Int.ofNat (s.ctrl + 4 + s.tally))
          (((climbAt base.ladder0 base.R s.ridx : Nat) : Int))
          (Int.ofNat (s.ridx + 1)))
          ((5 : Nat) : Int) (base.xHome : Int) ((6 : Nat) : Int)
          false false false =
        .ok (withPark bRed
          (embed (paintRed (afterPark s.row s.fromHole s.parkAt
            (climbAt base.ladder0 base.R s.ridx) r) s.t0 s.tally))
          (Int.ofNat (s.ctrl + 4 + s.tally))
          (((climbAt base.ladder0 base.R s.ridx : Nat) : Int))
          (Int.ofNat (s.ridx + 1))) ∧
      Ecbs.cube bClearU ((6 : Nat) : Int) ((5 : Nat) : Int) = .ok bCube ∧
      Ecbs.mul bCube ((5 : Nat) : Int) (base.xHome : Int) ((6 : Nat) : Int)
          false false false = .ok bRed ∧
      (∃ mvE mvR slE slR : Nat,
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
      bRed.sudo_5Board_4cost.sudo_5Costs_15control_highest = (s.high : Int) ∧
      bRed.sudo_5Board_4cost.sudo_5Costs_9tally_max =
        b.sudo_5Board_4cost.sudo_5Costs_9tally_max ∧
      ∃ (bLoop bMul : Ecbs.Board),
        Ecbs.mul bLoop ((5 : Nat) : Int) ((5 : Nat) : Int) ((6 : Nat) : Int)
            false false false = .ok bMul ∧
        Ecbs.clear bMul ((5 : Nat) : Int) = .ok bClearU ∧
        (∃ (cU : PegCtx) (ys : List Nat) (moves slides hole peak peakS cOps : Nat)
          (hH : 6 < bLoop.sudo_5Board_4home.size)
          (hD : 6 < bLoop.sudo_5Board_4held.size)
          (hops : 0 < bLoop.sudo_5Board_4cost.sudo_5Costs_3ops.size),
          bLoop = pegBoard cU cU.m ∧
          cU.row0 = s.row ∧ cU.ctrl0 = s.ctrl ∧ cU.g = s.gap ∧ cU.m = s.tally ∧
          cU.n = s.n ∧ cU.k = s.k ∧ cU.bench = s.benchlen ∧ cU.src = 6 ∧
          cU.t0 = s.t0 ∧
          bMul = mulNoLiveBoard bLoop 5 6 cU.g ys cU.n cU.k moves slides hole cU.bench
            peak peakS cOps hH hD hops ∧
          ys = cubeBenchIter cU.n cU.k cU.bench cU.g cU.m ∧
          moves = (pegPack cU cU.m cU.hm (Nat.le_refl _)).moves ∧
          slides = (pegPack cU cU.m cU.hm (Nat.le_refl _)).slides ∧
          hole = (pegPack cU cU.m cU.hm (Nat.le_refl _)).hole ∧
          peak = (pegPack cU cU.m cU.hm (Nat.le_refl _)).peak ∧
          peakS = (pegPack cU cU.m cU.hm (Nat.le_refl _)).peakS ∧
          Ecbs.copy_band b ((6 : Nat) : Int) ((5 : Nat) : Int) false = .ok cU.b0) := by
  let hole := climbAt base.ladder0 base.R s.ridx
  obtain ⟨cM, bM, ys, moves, slides, holeM, peak, peakS, cOps, hH, hD, hops,
      hcopyM, hsrcM, hgM, hmM, hnM, hkM, hbM, hpegM, _hys, hGap, _hX,
      _hOp, _hRow, _htier, _hmk, _h7, _hop0, _hOpsLe, hctrlM, _hhigh,
      _hcontrol, _hlen, _hmax, ht0M, hmul, hrowM, _hmvB, _hslB, _hhoB, _hpkB, _hpsB,
      ⟨_, _, _⟩, ⟨_, _, _⟩, hmulW⟩ :=
    mul_of_shape h hM hS hm hT hhome
  obtain ⟨bLoopR, bMulR, bClearU, bCube, bRed, hmulR, hclearR, hcubeU, hredU,
      _bounds, _hlenC, _ht0C, _hrowC, _hctrlN, _hhighC, _hctrlC, _hmaxC,
      _ht0Cube, _ht0Red, _htierCube, _htierRed, _hcubeF, _hmulF,
      honR, htoR, hlenR, hbenchR, hclearP, hcubeP, hmulP,
      _hcubeBoth, _hmulBoth, hpack, hrel, hhighR, htmaxR⟩ :=
    red_cube_mul h hM hS hm hT hhome hxLen hxT
  have hpackKeep := hpack
  obtain ⟨cU, _ysU, _mvU, _slU, _hoU, _pkU, _psU, _cOpsU, _hHU, _hDU, _hopsU,
      hloopU, hrowU, hctrlU, hgU, hmU, hnU, hkU, hbU, hsrcU, ht0U, _hnamed,
      _hysU, _hmvU, _hslU, _hhoU, _hpkU, _hpsU, hcopyU⟩ := hpack
  obtain ⟨mv, pk, sl, cE, hmv, hpk, _hsl, hb0, hcopyE, _hsrcE, _hgE, _hmE,
      _hrowE, _hnE, _hkE, _hbE, _hmv0, _hsl0, _ht0E, _hctrlE, _hhighE, _hcontrolE,
      _hlenE, _hmaxE⟩ :=
    peg_of_shape h hM hS hm hT hhome
  have hb0M : cE.b0 = cM.b0 := by injection hcopyE.symm.trans hcopyM
  have hRowP : s.parkAt < b.sudo_5Board_3row.size := by
    rw [h.inv.row, size_embed]; exact h.shape.park.parkLt
  have hRowH : hole < b.sudo_5Board_3row.size := by
    rw [h.inv.row, size_embed]; exact h.shape.park.holeLt
  let rowI := afterPark s.row (-1) s.parkAt hole r
  let rowP := afterPark s.row s.fromHole s.parkAt hole r
  let bKeep := parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH
  have hPW := parkKeep_withPark b s.row hole s.parkAt r s.ridx s.ctrl hRowP hRowH
    h.inv.row h.shape.park.parkLt h.shape.park.holeLt
  have hplI := placeBoard_withPark b (embed rowI) (Int.ofNat (s.ctrl + 2))
    ((hole : Nat) : Int) (Int.ofNat (s.ridx + 1))
    6 h.shape.spareH h.shape.spareD s.gap mv pk
  have hb0p : placeBoard b 6 h.shape.spareH h.shape.spareD s.gap mv pk = cE.b0 := hb0.symm
  have hIdle : placeBoard bKeep 6 h.shape.spareH h.shape.spareD s.gap mv pk =
      withPark cE.b0 (embed rowI) (Int.ofNat (s.ctrl + 2))
        ((hole : Nat) : Int) (Int.ofNat (s.ridx + 1)) := by
    have h1 := place_of_eq hPW 6 h.shape.spareH h.shape.spareD s.gap mv pk
    have hir := placeBoard_irrel
      (withPark b (embed rowI) (Int.ofNat (s.ctrl + 2)) ((hole : Nat) : Int)
        (Int.ofNat (s.ridx + 1)))
      6 (hPW ▸ h.shape.spareH) (withPark_home _ _ _ _ _ ▸ h.shape.spareH)
      (hPW ▸ h.shape.spareD) (withPark_held _ _ _ _ _ ▸ h.shape.spareD)
      s.gap mv pk
    rw [h1, hir, hplI, hb0p]
  obtain ⟨bPark, bCopy, mvR, pkR, h6H, h6D, hpark, hcopy, hplaceR, hmvR, hpkR⟩ :=
    resume_copy h hM hge hm hT hhome
  obtain ⟨bPark', bKeep', hRowP', hRowH', hpark', hkeep', hframe⟩ :=
    resume_park_withPark h hge
  have hParkEq : bPark = bPark' := by injection hpark.symm.trans hpark'
  have hKeepEq : bKeep' = bKeep := by
    rw [hkeep']
  have hmvE : mv = mvR := ofNat_inj_nat (hmv.symm.trans hmvR)
  have hpkE : pk = pkR := ofNat_inj_nat (hpk.symm.trans hpkR)
  have hctrl4 : ((s.ctrl + 4 : Nat) : Int) = Int.ofNat (s.ctrl + 4) := rfl
  let fromH := ((hole : Nat) : Int)
  let ridxH := Int.ofNat (s.ridx + 1)
  let ctrlReal := ((s.ctrl + 4 : Nat) : Int)
  have hGePlace : placeBoard bPark 6 h6H h6D s.gap mvR pkR =
      withPark cE.b0 (embed rowP) ctrlReal fromH ridxH := by
    have hParkW : bPark = withPark bKeep (embed rowP) ctrlReal fromH ridxH := by
      rw [hParkEq, hframe, hKeepEq]
    have h1 := place_of_eq hParkW 6 h6H h6D s.gap mvR pkR
    have hIH : 6 < bKeep.sudo_5Board_4home.size := by
      simpa [bKeep, parkKeepBoard] using h.shape.spareH
    have hID : 6 < bKeep.sudo_5Board_4held.size := by
      simpa [bKeep, parkKeepBoard] using h.shape.spareD
    have hplP := placeBoard_withPark bKeep (embed rowP) ctrlReal fromH ridxH
      6 hIH hID s.gap mvR pkR
    have hir := placeBoard_irrel
      (withPark bKeep (embed rowP) ctrlReal fromH ridxH)
      6 (hParkW ▸ h6H) (withPark_home _ _ _ _ _ ▸ hIH)
      (hParkW ▸ h6D) (withPark_held _ _ _ _ _ ▸ hID)
      s.gap mvR pkR
    rw [h1, hir, hplP]
    have hmvR : mvR = mv := hmvE.symm
    have hpkR : pkR = pk := hpkE.symm
    rw [hmvR, hpkR, hIdle, withPark_withPark]
  have hFrame : bCopy = withPark cM.b0 (embed rowP) ctrlReal fromH ridxH := by
    rw [hplaceR, hGePlace, hb0M]
  have hRoom0 : cM.t0 + cM.m ≤ rowP.length := by
    rw [ht0M, hmM, afterPark_length]
    exact h.shape.seg.room
  have hRoom : cM.t0 + cM.m ≤ s.row.length := by
    rw [ht0M, hmM]
    exact h.shape.seg.room
  have hdoneLe : done.length ≤ base.R := by
    have hk := h.kLe
    simp [List.length_append, List.length_cons] at hk
    omega
  have hCtrlB : FitsLen (s.ctrl + 4 + s.tally) :=
    ctrl_resume_peg_fit h.ctrlLe hT hm hdoneLe base.fitCtrl
  have hCtrlM : FitsLen ((s.ctrl + 4) + cM.m) := by
    rw [hmM]; exact hCtrlB
  have hAgree : ∀ j (hj : j < cM.m),
      rowP[cM.t0 + j]'(Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj cM.t0) hRoom0) =
        s.row[cM.t0 + j]'(Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj cM.t0) hRoom) := by
    intro j hj
    have hjM : j < s.tally := by
      rw [hmM] at hj
      exact hj
    have hix : s.t0 + j < s.row.length :=
      Nat.lt_of_lt_of_le (Nat.add_lt_add_left hjM s.t0) h.shape.seg.room
    have hget := afterPark_get s.row s.fromHole s.parkAt hole r (s.t0 + j)
      (Nat.lt_of_lt_of_le h.parkBelow (Nat.le_add_right _ _))
      (Nat.lt_of_lt_of_le h.holeBelow (Nat.le_add_right _ _))
      (Or.inr (Nat.lt_of_lt_of_le (h.fromBelow hge) (Nat.le_add_right s.t0 j)))
      hix
    have ht : cM.t0 = s.t0 := ht0M
    have hL := get_add_eq ht (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj cM.t0) hRoom0)
    have hR := get_add_eq ht.symm hix
    exact hL.trans (hget.trans hR)
  have hWhite : ∀ j (hj : j < cM.m),
      s.row[cM.t0 + j]'(Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj cM.t0) hRoom) = 1 := by
    intro j hj
    have hjM : j < s.tally := by
      rw [hmM] at hj
      exact hj
    have hcol := h.shape.seg.colour j hjM
    have hfin : (r :: rest).isEmpty = false := by simp
    simpa [hfin, ht0M] using hcol
  have hRowIdle : cM.b0.sudo_5Board_3row = embed s.row := by
    rw [cM.hRow, hrowM]
  have hbLoop : bM = bLoopR := by
    have hb0U : cM.b0 = cU.b0 := by injection hcopyM.symm.trans hcopyU
    have hboards := pegBoard_same_copy cM cU hb0U
      (hsrcU.trans hsrcM.symm) (hgU.trans hgM.symm) (hnU.trans hnM.symm)
      (hkU.trans hkM.symm) (hbU.trans hbM.symm) (hrowU.trans hrowM.symm)
      (ht0U.trans ht0M.symm) (hctrlU.trans hctrlM.symm) (hmU.trans hmM.symm)
    rw [hpegM, hloopU, hboards]
  have hMulIn : mulNoLiveBoard bM 5 6 cM.g ys cM.n cM.k moves slides holeM cM.bench
      peak peakS cOps hH hD hops = bMulR := by
    have hmulR' : Ecbs.mul bM ((5 : Nat) : Int) ((5 : Nat) : Int) ((6 : Nat) : Int)
        false false false = .ok bMulR := by
      rw [hbLoop]
      exact hmulR
    have hjoin := hmul.symm.trans hmulR'
    injection hjoin
  let paint := embed (paintRed rowP cM.t0 cM.m)
  let ctrlP := Int.ofNat ((s.ctrl + 4) + cM.m)
  have hMulRun := hmulW paint ctrlP fromH ridxH
  have hMulRun' : Ecbs.mul (withPark bM paint ctrlP fromH ridxH)
      (5 : Int) (5 : Int) (6 : Int) false false false =
      .ok (withPark bMulR paint ctrlP fromH ridxH) := by
    simpa [hMulIn] using hMulRun
  have hClearRun := hclearP paint ctrlP fromH ridxH
  have hctrlN : ctrlP = Int.ofNat (s.ctrl + 4 + s.tally) := by
    unfold ctrlP
    rw [hmM]
  have hpaint : paint = embed (paintRed rowP s.t0 s.tally) := by
    unfold paint
    rw [ht0M, hmM]
  have hrun := parked_clear_transport b bPark bCopy r cM s.row rowP (s.ctrl + 4)
    fromH ridxH hpark hcopy hFrame hRoom0 hCtrlM hsrcM cM.hT0 hRowIdle hRoom
    hAgree hWhite
    (withPark bMulR paint ctrlP fromH ridxH)
    (withPark bClearU paint ctrlP fromH ridxH)
    (by
      rw [← hpegM]
      exact hMulRun')
    hClearRun
  rw [hctrlN, hpaint, hmM] at hrun
  unfold rowP hole fromH ridxH at hrun
  let paintF := embed (paintRed (afterPark s.row s.fromHole s.parkAt hole r) s.t0 s.tally)
  let ctrlF := Int.ofNat (s.ctrl + 4 + s.tally)
  let fromF := ((hole : Nat) : Int)
  let ridxF := Int.ofNat (s.ridx + 1)
  have hcube := hcubeP paintF ctrlF fromF ridxF
  have hmulF := hmulP paintF ctrlF fromF ridxF
  exact ⟨bClearU, bCube, bRed, hrun, hcube, hmulF, hcubeU, hredU, hrel,
    honR, htoR, hlenR, hbenchR, hhighR, htmaxR, bLoopR, bMulR, hmulR, hclearR, hpackKeep⟩

/-- `ClimbInvK` supplies the core and one charge of tight headroom. -/
noncomputable def parked_clear_unparked_ofK
    {done rest : List Nat} {r : Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvK done (r :: rest) b s base)
    (hge : 0 ≤ s.fromHole) (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax)
    (hhome : s.onBench = false)
    (hxLen : base.x.length = base.n) (hxT : allTritList base.x) :=
  parked_clear_unparked h.toCore (moveHeadroom_of_cons h) (slideHeadroom_of_cons h)
    hge hm hT hhome hxLen hxT


end EcbsLink2.Link2
