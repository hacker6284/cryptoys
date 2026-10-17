/-
  `marker_lift`, then `frobenius_affine`, is the step from one live cell's
  `RunFrame` to the next. Homes 0 and 1 become the field cubes. Homes 3 and 4
  stay the base point. The ladder, the row, and ops slots 2 and 3 stay.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.CellCube

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- The lifted board, its across cube, and the Frobenius board. `onEq` says the
    across cube is the marker-off cube of the lifted board, so every field that
    cube does not write is still the incoming `RunFrame`. -/
structure AffineCell (b : Ecbs.Board) (t : Spec.Tier) (accX accY : List Nat)
    (peak moves slides hole peakS ctrl mx opsCap : Nat) where
  bL : Ecbs.Board
  cubeOps : Nat
  a : DownAcross bL accX accY t.n t.k t.w t.h t.r t.benchlen t.combgap
    peak moves slides hole cubeOps (ctrl + 1) mx t.script
  hops : 1 < bL.sudo_5Board_4cost.sudo_5Costs_3ops.size
  h0D : 0 < bL.sudo_5Board_4held.size
  h0H : 0 < bL.sudo_5Board_4home.size
  liftEq : Ecbs.marker_lift b = .ok bL
  onEq : a.b1On = acrossBoard bL accX t.n t.k moves hole t.benchlen peak peakS
    cubeOps (ctrl + 1) mx hops h0D h0H
  frobEq : Ecbs.frobenius_affine bL = .ok (cellOut a)
  capLe : cubeOps ≤ opsCap

theorem cell_affine (b : Ecbs.Board) (t : Spec.Tier) (baseX accX accY : List Nat)
    (fr : RunFrame b t baseX accX)
    (hOk : BoardOk t) (sat : TierSat t) (hsh : TierShape t)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hA : fr.y1 = accY) (hf1 : fr.flag1 = true)
    (hyA : accY.length = t.n) (htriY : allTritList accY)
    (hMove : FitsLen (fr.moves + cubeCharge t.n t.benchlen + 3 * t.n))
    (hSlide : FitsLen (fr.slides + slideCharge t.n))
    (hCtrl : FitsLen (fr.ctrl + 5))
    (hOps : FitsLen (fr.opsCap + 2)) :
    Nonempty (AffineCell b t accX accY fr.peak fr.moves fr.slides fr.hole fr.peakS fr.ctrl
      fr.mx fr.opsCap) := by
  have hlift := marker_lift_refines b fr.mark fr.ctrl fr.hmark fr.hctrl
    (FitsLen.of_le hCtrl (by omega))
  let bL := { b with
    sudo_5Board_6marker := -1
    sudo_5Board_4cost := { b.sudo_5Board_4cost with
      sudo_5Costs_4ctrl := Int.ofNat (fr.ctrl + 1) } }
  have hopsB : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    exact Nat.lt_of_succ_lt fr.ops2
  have hops : 1 < bL.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    simp [bL]
    exact hopsB
  have h0D : 0 < bL.sudo_5Board_4held.size := by rw [show bL.sudo_5Board_4held = b.sudo_5Board_4held from rfl, fr.szD]; decide
  have h0H : 0 < bL.sudo_5Board_4home.size := by rw [show bL.sudo_5Board_4home = b.sudo_5Board_4home from rfl, fr.szH]; decide
  have h1D : 1 < bL.sudo_5Board_4held.size := by rw [show bL.sudo_5Board_4held = b.sudo_5Board_4held from rfl, fr.szD]; decide
  have h1H : 1 < bL.sudo_5Board_4home.size := by rw [show bL.sudo_5Board_4home = b.sudo_5Board_4home from rfl, fr.szH]; decide
  obtain ⟨cubeOps, hopRaw, hleRaw⟩ := fr.opsRoom 1 hopsB
  have hop1 : bL.sudo_5Board_4cost.sudo_5Costs_3ops[1]'hops = (cubeOps : Int) := by
    simpa [bL, ofNat_eq_natCast] using hopRaw
  have hcap : cubeOps ≤ fr.opsCap := by
    simpa [if_neg (by decide : (1 : Nat) ≠ 2), if_neg (by decide : (1 : Nat) ≠ 3)] using hleRaw
  have hfitC : FitsLen (cubeOps + 2) := FitsLen.of_le hOps (by omega)
  have hn0 : 0 < t.n := hOk.n_pos
  have hs1 : 1 < t.script := by have h := hsh.script_ge; omega
  have hspan : 3 * (t.n - 1) + t.combgap < t.benchlen := sat.cube_span
  have hnb : t.n ≤ t.benchlen := by have h := hspan; omega
  have hsm := hsh.small
  have hnsm := hsh.n_small
  have hcapN := smallCap t.n t.benchlen
  have hnFit : FitsLen t.n := geomFit t.n t.benchlen t.n hnsm hsm.2.2.2 hcapN.1
  have hbenchFit : FitsLen t.benchlen :=
    geomFit t.n t.benchlen t.benchlen hnsm hsm.2.2.2 hcapN.2.1
  have h3 : FitsLen (3 * (t.n - 1)) :=
    geomFit t.n t.benchlen (3 * (t.n - 1)) hnsm hsm.2.2.2 hcapN.2.2
  have hMv : FitsLen (fr.moves + cubeCharge t.n t.benchlen) :=
    FitsLen.of_le hMove (Nat.le_add_right _ _)
  have hfm : FitsLen (fr.moves + 2 * t.n) := by
    apply FitsLen.of_le hMv
    unfold cubeCharge
    omega
  have hfold : FitsLen (fr.moves + 2 * t.n + 3 * (t.benchlen - t.n)) := by
    apply FitsLen.of_le hMv
    unfold cubeCharge
    omega
  have hmNeg : bL.sudo_5Board_6marker < 0 := by
    have hmEq : bL.sudo_5Board_6marker = -1 := rfl
    rw [hmEq]
    decide
  have hc : bL.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (fr.ctrl + 1) := rfl
  have hmx : bL.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat fr.mx := by
    simp [bL, fr.hmx]
  have hscript : bL.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat t.script := by
    simp [bL, fr.tier, embTier]
  have hn : bL.sudo_5Board_1t.sudo_4Tier_1n = (t.n : Int) := by
    simp [bL, fr.tier, embTier, ofNat_eq_natCast]
  have hk : bL.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat t.k := by simp [bL, fr.tier, embTier]
  have hw : bL.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat t.w := by simp [bL, fr.tier, embTier]
  have hh : bL.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat t.h := by simp [bL, fr.tier, embTier]
  have hr : bL.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat t.r := by simp [bL, fr.tier, embTier]
  have hbl : bL.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat t.benchlen := by
    simp [bL, fr.tier, embTier]
  have hcg : bL.sudo_5Board_1t.sudo_4Tier_7combgap = Int.ofNat t.combgap := by
    simp [bL, fr.tier, embTier]
  have hmoves : bL.sudo_5Board_4cost.sudo_5Costs_5moves = (fr.moves : Int) := by
    simp [bL, fr.hmoves, ofNat_eq_natCast]
  have hslides : bL.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat fr.slides := by
    simp [bL, fr.hslides]
  have hpeak : bL.sudo_5Board_4cost.sudo_5Costs_4peak = (fr.peak : Int) := by
    simp [bL, fr.hpeak, ofNat_eq_natCast]
  have hstrict : bL.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (fr.peakS : Int) := by
    simp [bL, fr.hstrict, ofNat_eq_natCast]
  have hhole : bL.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat fr.hole := by
    simp [bL, fr.hhole]
  have hheld0 : bL.sudo_5Board_4held[0]'h0D = true := by
    simpa [show bL.sudo_5Board_4held = b.sudo_5Board_4held from rfl] using fr.held0
  have hhome0 : bL.sudo_5Board_4home[0]'h0H = embed accX := by
    simpa [show bL.sudo_5Board_4home = b.sudo_5Board_4home from rfl] using fr.home0
  have hheld1 : bL.sudo_5Board_4held[1]'h1D = true := by
    have h := fr.held1
    simp [hf1] at h
    simpa [show bL.sudo_5Board_4held = b.sudo_5Board_4held from rfl] using h
  have hhome1 : bL.sudo_5Board_4home[1]'h1H = embed accY := by
    have h := fr.home1
    simp [hA] at h
    simpa [show bL.sudo_5Board_4home = b.sudo_5Board_4home from rfl] using h
  have hmkL : bL.sudo_5Board_9marker_on = true := by simpa [bL] using hmk
  have hoff : bL.sudo_5Board_8bench_on = false := by simpa [bL] using fr.bench
  let a := down_across bL accX accY t.w t.h t.r t.n t.k fr.moves fr.slides fr.peak fr.peakS
    fr.hole cubeOps (fr.ctrl + 1) fr.mx t.script fr.szH fr.szD hops fr.lenA hyA fr.triA htriY
    hmkL hoff hmNeg hc hmx hscript hs1
    (FitsLen.of_le hCtrl (by omega)) (FitsLen.of_le hCtrl (by omega)) hop1 hfitC
    hheld0 hhome0 hheld1 hhome1 hn hk hw hh hr hbl hcg hmoves hslides hpeak hstrict hhole
    hsh.w0 hsh.h0 hsh.rlt hsh.r0 hn0 hsh.n_eq hsh.k_le hsh.gap hspan hsm hnsm
    (by
      unfold cubeCharge at hMv
      simpa [Nat.add_assoc] using hMv)
    (by simpa [slideCharge] using hSlide)
  have hcube := cube_down_eq bL 0 0 accX t.w t.h t.r t.n t.k fr.moves fr.hole t.benchlen
    fr.peak fr.peakS cubeOps t.combgap (fr.ctrl + 1) fr.mx t.script hmkL hoff hmNeg hc hmx
    hscript (by have h := hsh.script_ge; omega) (FitsLen.of_le hCtrl (by omega)) hops hop1
    (FitsLen.of_le hfitC (by omega)) h0D h0H hheld0 hhome0 (by rw [fr.szD]; decide)
    hstrict hpeak hn0 hn fr.lenA hnFit hmoves hbl hcg hspan h3 hfm hhole fr.triA
    hsh.w0 hsh.h0 hsh.rlt hsh.r0 hsh.n_eq hsh.k_le hsh.gap hw hh hr hk hsm hnsm hbenchFit hfold
  have hOn : a.b1On = acrossBoard bL accX t.n t.k fr.moves fr.hole t.benchlen fr.peak fr.peakS
      cubeOps (fr.ctrl + 1) fr.mx hops h0D h0H :=
    Except.ok.inj (a.hcube.symm.trans hcube)
  have hnbL : t.n ≤ a.laneX.length := by rw [a.hlenX]; exact hnb
  have hfrob := cell_frob a htriY hyA hn0 hs1 (FitsLen.of_le hCtrl (by omega)) hfitC hspan h3
    hnFit hbenchFit hnbL hnb hsh.w0 hsh.h0 hsh.rlt hsh.r0 hsh.n_eq hsh.k_le hsh.gap hsm hnsm
    hMv hSlide
  refine Nonempty.intro ?_
  exact {
    bL := bL
    cubeOps := cubeOps
    a := a
    hops := hops
    h0D := h0D
    h0H := h0H
    liftEq := by simpa [bL] using hlift
    onEq := hOn
    frobEq := hfrob
    capLe := hcap
  }

/-- A projection the two settles, the two cubes, and the marker feeds do not
    change. The across cube is `onEq`, so the projection on the Frobenius board
    is the projection on the board that was lifted. -/
theorem affine_card {b : Ecbs.Board} {t : Spec.Tier} {accX accY : List Nat}
    {peak moves slides hole peakS ctrl mx opsCap : Nat}
    (cell : AffineCell b t accX accY peak moves slides hole peakS ctrl mx opsCap)
    {α : Type} (proj : Ecbs.Board → α)
    (hSettle : ∀ (b0 : Ecbs.Board) (home : Nat) (hin : HomeIn b0 home) (xs : List Nat)
        (n mv sl pk : Nat),
        proj (settleBoard b0 home hin.hH hin.hD xs n mv sl pk) = proj b0)
    (hCube : ∀ (b0 : Ecbs.Board) (dst src : Nat) (xs : List Nat)
        (n k mv holeN bench pk0 ps cOps : Nat)
        (hops : 1 < b0.sudo_5Board_4cost.sudo_5Costs_3ops.size)
        (hF : src < b0.sudo_5Board_4held.size) (hH : src < b0.sudo_5Board_4home.size),
        proj (cubeOffBoard b0 dst src xs n k mv holeN bench pk0 ps cOps hops hF hH) = proj b0)
    (hDown : ∀ (b0 : Ecbs.Board) (c m : Nat), proj (markerDownFeed b0 c m) = proj b0)
    (hUp : ∀ (b0 : Ecbs.Board) (m c mx0 : Nat), proj (markerUpFeed b0 m c mx0) = proj b0)
    (hFlag : ∀ (b0 : Ecbs.Board), proj { b0 with sudo_5Board_9marker_on := true } = proj b0)
    (hL : proj cell.bL = proj b) :
    proj (cellOut cell.a) = proj b := by
  have h1 : proj (cellOut cell.a) = proj (upFlag cell.a) := by
    rw [cellOut]
    exact hSettle (upFlag cell.a) 1 ⟨upFlagH cell.a, upFlag1 cell.a⟩ (upLane t.n t.k t.benchlen accY)
      t.n (upMv2 cell.a) (upSl cell.a) (upPk2 cell.a)
  have h2 : proj (upFlag cell.a) = proj (upBoard cell.a) := hFlag _
  have h3 : proj (upBoard cell.a) = proj (upSettled cell.a) := by
    rw [upBoard]
    exact hCube (upSettled cell.a) 1 1 accY t.n t.k (upMv cell.a) cell.a.hole1 t.benchlen
      (upPk cell.a) cell.a.peakS1 (cell.cubeOps + 1) (up_ops_lt cell.a) (up1D cell.a) (up1H cell.a)
  have h4 : proj (upSettled cell.a) = proj (upFeed cell.a) := by
    rw [upSettled]
    exact hSettle (upFeed cell.a) 0 ⟨upH cell.a, upD cell.a⟩ cell.a.laneX t.n cell.a.mv1 slides
      cell.a.pk1
  have h5 : proj (upFeed cell.a) = proj cell.a.b1On := by
    rw [upFeed]
    exact hUp _ 0 ((ctrl + 1) + 1) (max mx 1)
  have h6 : proj cell.a.b1On = proj (acrossBoard cell.bL accX t.n t.k moves hole t.benchlen peak
      peakS cell.cubeOps (ctrl + 1) mx cell.hops cell.h0D cell.h0H) := by
    rw [cell.onEq]
  have h7 : proj (acrossBoard cell.bL accX t.n t.k moves hole t.benchlen peak peakS cell.cubeOps
      (ctrl + 1) mx cell.hops cell.h0D cell.h0H) = proj (markerDownFeed cell.bL (ctrl + 1) mx) := by
    rw [acrossBoard]
    exact (hFlag _).trans
      (hCube (markerDownFeed cell.bL (ctrl + 1) mx) 0 0 accX t.n t.k moves hole t.benchlen peak
        peakS cell.cubeOps cell.hops cell.h0D cell.h0H)
  have h8 : proj (markerDownFeed cell.bL (ctrl + 1) mx) = proj cell.bL := hDown _ _ _
  exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans (h7.trans (h8.trans hL)))))))

/-- Homes other than across and up are the homes of the lifted board. -/
theorem affine_home {b : Ecbs.Board} {t : Spec.Tier} {accX accY : List Nat}
    {peak moves slides hole peakS ctrl mx opsCap : Nat}
    (cell : AffineCell b t accX accY peak moves slides hole peakS ctrl mx opsCap)
    (j : Nat) (hj0 : j ≠ 0) (hj1 : j ≠ 1)
    (hjF : j < (cellOut cell.a).sudo_5Board_4home.size)
    (hjU : j < (upFlag cell.a).sudo_5Board_4home.size)
    (hjB : j < (upBoard cell.a).sudo_5Board_4home.size)
    (hjS : j < (upSettled cell.a).sudo_5Board_4home.size)
    (hjE : j < (upFeed cell.a).sudo_5Board_4home.size)
    (hj1n : j < cell.a.b1On.sudo_5Board_4home.size)
    (hjL : j < cell.bL.sudo_5Board_4home.size)
    (hBL : cell.bL.sudo_5Board_4home = b.sudo_5Board_4home)
    (hj0b : j < b.sudo_5Board_4home.size) :
    (cellOut cell.a).sudo_5Board_4home[j] = b.sudo_5Board_4home[j] := by
  have h1 := (at_eq (cellOut_homeSet cell.a) hjF (by rw [Array.size_set]; exact hjU)).trans
    (set_ne (upFlag cell.a).sudo_5Board_4home 1 j (upFlagH cell.a)
      (embed ((upLane t.n t.k t.benchlen accY).take t.n)) (by omega) hjU)
  have hflag : (upFlag cell.a).sudo_5Board_4home[j] = (upBoard cell.a).sudo_5Board_4home[j] := rfl
  have hcube := cube_off_home (upSettled cell.a) 1 1 accY t.n t.k (upMv cell.a) cell.a.hole1
    t.benchlen (upPk cell.a) cell.a.peakS1 (cell.cubeOps + 1) (up_ops_lt cell.a) (up1D cell.a)
    (up1H cell.a)
  have h2 := (at_eq (by rw [upBoard]; exact hcube) hjB (by rw [Array.size_set]; exact hjS)).trans
    (set_ne (upSettled cell.a).sudo_5Board_4home 1 j (up1H cell.a) (#[]) (by omega) hjS)
  have hset := settle_home_eq (upFeed cell.a) 0 ⟨upH cell.a, upD cell.a⟩ cell.a.laneX t.n
    cell.a.mv1 slides cell.a.pk1
  have h3 := (at_eq hset hjS (by rw [Array.size_set]; exact hjE)).trans
    (set_ne (upFeed cell.a).sudo_5Board_4home 0 j (upH cell.a)
      (embed (cell.a.laneX.take t.n)) (by omega) hjE)
  have hfeed := at_eq (upFeed_home cell.a) hjE hj1n
  have hraw := raw_home cell.bL accX t.n t.k moves hole t.benchlen peak peakS cell.cubeOps
    (ctrl + 1) mx cell.hops cell.h0D cell.h0H
  have hhomeOn : cell.a.b1On.sudo_5Board_4home =
      (acrossBoard cell.bL accX t.n t.k moves hole t.benchlen peak peakS cell.cubeOps
        (ctrl + 1) mx cell.hops cell.h0D cell.h0H).sudo_5Board_4home :=
    congrArg (fun b => b.sudo_5Board_4home) cell.onEq
  have hszA : j < (acrossBoard cell.bL accX t.n t.k moves hole t.benchlen peak peakS cell.cubeOps
      (ctrl + 1) mx cell.hops cell.h0D cell.h0H).sudo_5Board_4home.size := by
    rw [hraw, Array.size_set, feed_home]
    exact hjL
  have hOn := at_eq hhomeOn hj1n hszA
  have hfeedSz : j < (markerDownFeed cell.bL (ctrl + 1) mx).sudo_5Board_4home.size := by
    rw [feed_home]; exact hjL
  have h4 := (hOn.trans (at_eq hraw hszA (by rw [Array.size_set]; exact hfeedSz))).trans
    (set_ne (markerDownFeed cell.bL (ctrl + 1) mx).sudo_5Board_4home 0 j cell.h0H (#[] )
      (by omega) hfeedSz)
  have hdown := at_eq (feed_home cell.bL (ctrl + 1) mx) (by rw [feed_home]; exact hjL) hjL
  have hbase := at_eq hBL hjL hj0b
  exact h1.trans (hflag.trans (h2.trans (h3.trans (hfeed.trans (h4.trans (hdown.trans hbase))))))

theorem lt_of_size {α : Type} {a : Array α} {n : Nat} (hs : a.size = 8) (hn : n < 8) :
    n < a.size := by
  rw [hs]
  exact hn

/-- `marker_lift` then `frobenius_affine`. Homes 0 and 1 are the field cubes.
    The control counter is the incoming counter plus four, and the marker sits at 1. -/
theorem cell_to_frame (b : Ecbs.Board) (t : Spec.Tier) (baseX accX accY : List Nat)
    (fr : RunFrame b t baseX accX)
    (hOk : BoardOk t) (sat : TierSat t) (hsh : TierShape t)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hA : fr.y1 = accY) (hf1 : fr.flag1 = true)
    (hyA : accY.length = t.n) (htriY : allTritList accY)
    (hMove : FitsLen (fr.moves + cubeCharge t.n t.benchlen + 3 * t.n))
    (hSlide : FitsLen (fr.slides + slideCharge t.n))
    (hCtrl : FitsLen (fr.ctrl + 5))
    (hOps : FitsLen (fr.opsCap + 2)) :
    ∃ bL bF, ∃ h0 : 0 < bF.sudo_5Board_4home.size, ∃ h1 : 1 < bF.sudo_5Board_4home.size,
      Ecbs.marker_lift b = .ok bL ∧
      Ecbs.frobenius_affine bL = .ok bF ∧
      bF.sudo_5Board_9marker_on = true ∧
      bF.sudo_5Board_4home[0] = embed (fieldCube t.n t.k t.benchlen accX) ∧
      bF.sudo_5Board_4home[1] = embed (fieldCube t.n t.k t.benchlen accY) ∧
      bF.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (fr.ctrl + 4) ∧
      bF.sudo_5Board_6marker = Int.ofNat 1 := by
  obtain ⟨cell⟩ := cell_affine b t baseX accX accY fr hOk sat hsh hmk hA hf1 hyA htriY
    hMove hSlide hCtrl hOps
  refine ⟨cell.bL, cellOut cell.a,
    lt_of_size (cellOut_szH cell.a) (by decide),
    lt_of_size (cellOut_szH cell.a) (by decide),
    cell.liftEq, cell.frobEq, cellOut_on cell.a, ?_, ?_, ?_, cellOut_mark cell.a⟩
  · exact cellOut_home0 cell.a (lt_of_size (cellOut_szH cell.a) (by decide))
  · exact cellOut_home1 cell.a (lt_of_size (cellOut_szH cell.a) (by decide))
  · have h := cellOut_ctrl cell.a
    have hsum : ((fr.ctrl + 1) + 1) + 2 = fr.ctrl + 4 := by omega
    simpa [hsum] using h

end EcbsLink2.Link2

