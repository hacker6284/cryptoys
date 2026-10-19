/-
  A zero cell keeps the frame. The incoming `FformAt` is `FrameAt` on the
  board the cell entered. `b1On_base` carries homes 3 and 4 through the lift
  and the across cube, and `comb_frame` carries them onto the comb.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FformFrob
import EcbsLink2.Link2.FformFrame
import EcbsLink2.Link2.FformZero
import EcbsLink2.Link2.FformCellInv
import EcbsLink2.Link2.FformComb
import EcbsLink2.Link2.FformSumRoom

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

private theorem flag_on_peak (b : Ecbs.Board) :
    ({ b with sudo_5Board_9marker_on := true }).sudo_5Board_4cost.sudo_5Costs_4peak =
      b.sudo_5Board_4cost.sudo_5Costs_4peak := rfl

private theorem flag_on_strict (b : Ecbs.Board) :
    ({ b with sudo_5Board_9marker_on := true }).sudo_5Board_4cost.sudo_5Costs_11peak_strict =
      b.sudo_5Board_4cost.sudo_5Costs_11peak_strict := rfl

private theorem flag_on_hole (b : Ecbs.Board) :
    ({ b with sudo_5Board_9marker_on := true }).sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole := rfl

private theorem flag_on_mon (b : Ecbs.Board) :
    ({ b with sudo_5Board_9marker_on := true }).sudo_5Board_9marker_on = true := rfl

/-- The comb's peak, strict peak, and bench hole, as the naturals the cube writes. -/
theorem bottomFlag_peak
    {b : Ecbs.Board} {x y : List Nat}
    {n k w h r bench cg pk moves slides holeN cOps ctrl mx script : Nat}
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (z : List Nat) :
    (bottomFlag a z).sudo_5Board_4cost.sudo_5Costs_4peak =
      Int.ofNat (raisedPeak
        (raisedPeak (upPk2 a)
          (countHeld ((pointFeed a).sudo_5Board_4held.set ⟨1, pointFeed_heldIx a⟩ true) 7))
        (countHeld ((seatAt a).sudo_5Board_4held.set ⟨2, seatAt_held2ix a⟩ false) 7)) := by
  have hflag : (bottomFlag a z).sudo_5Board_4cost.sudo_5Costs_4peak =
      (bottomOff a z).sudo_5Board_4cost.sudo_5Costs_4peak := by
    unfold bottomFlag
    exact flag_on_peak (bottomOff a z)
  have hoff : (bottomOff a z).sudo_5Board_4cost.sudo_5Costs_4peak =
      Int.ofNat (raisedPeak
        (raisedPeak (upPk2 a)
          (countHeld ((pointFeed a).sudo_5Board_4held.set ⟨1, pointFeed_heldIx a⟩ true) 7))
        (countHeld ((seatAt a).sudo_5Board_4held.set ⟨2, seatAt_held2ix a⟩ false) 7)) := by
    unfold bottomOff
    exact cube_off_peak (seatAt a) 2 2 z n k
      (upMv2 a + 2 * pegCount ((upLane n k bench y).take n))
      (raisedHole a.hole1 (topIdx (combStrip n bench y))) bench
      (raisedPeak (upPk2 a)
        (countHeld ((pointFeed a).sudo_5Board_4held.set ⟨1, pointFeed_heldIx a⟩ true) 7))
      (raisedPeak a.peakS1 (countHeld (upSettled a).sudo_5Board_4held 7))
      (cOps + 2) (seatAt_ops a) (seatAt_held2ix a) (seatAt_home2ix a)
  exact hflag.trans hoff

theorem bottomFlag_strict
    {b : Ecbs.Board} {x y : List Nat}
    {n k w h r bench cg pk moves slides holeN cOps ctrl mx script : Nat}
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (z : List Nat) :
    (bottomFlag a z).sudo_5Board_4cost.sudo_5Costs_11peak_strict =
      Int.ofNat (raisedPeak
        (raisedPeak a.peakS1 (countHeld (upSettled a).sudo_5Board_4held 7))
        (countHeld (seatAt a).sudo_5Board_4held 7)) := by
  have hflag : (bottomFlag a z).sudo_5Board_4cost.sudo_5Costs_11peak_strict =
      (bottomOff a z).sudo_5Board_4cost.sudo_5Costs_11peak_strict := by
    unfold bottomFlag
    exact flag_on_strict (bottomOff a z)
  have hoff : (bottomOff a z).sudo_5Board_4cost.sudo_5Costs_11peak_strict =
      Int.ofNat (raisedPeak
        (raisedPeak a.peakS1 (countHeld (upSettled a).sudo_5Board_4held 7))
        (countHeld (seatAt a).sudo_5Board_4held 7)) := by
    unfold bottomOff
    exact cube_off_strict (seatAt a) 2 2 z n k
      (upMv2 a + 2 * pegCount ((upLane n k bench y).take n))
      (raisedHole a.hole1 (topIdx (combStrip n bench y))) bench
      (raisedPeak (upPk2 a)
        (countHeld ((pointFeed a).sudo_5Board_4held.set ⟨1, pointFeed_heldIx a⟩ true) 7))
      (raisedPeak a.peakS1 (countHeld (upSettled a).sudo_5Board_4held 7))
      (cOps + 2) (seatAt_ops a) (seatAt_held2ix a) (seatAt_home2ix a)
  exact hflag.trans hoff

theorem bottomFlag_hole
    {b : Ecbs.Board} {x y : List Nat}
    {n k w h r bench cg pk moves slides holeN cOps ctrl mx script : Nat}
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (z : List Nat) :
    (bottomFlag a z).sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      Int.ofNat (raisedHole (raisedHole a.hole1 (topIdx (combStrip n bench y)))
        (topIdx (combStrip n bench z))) := by
  have hflag : (bottomFlag a z).sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      (bottomOff a z).sudo_5Board_4cost.sudo_5Costs_14max_bench_hole := by
    unfold bottomFlag
    exact flag_on_hole (bottomOff a z)
  have hoff : (bottomOff a z).sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      Int.ofNat (raisedHole (raisedHole a.hole1 (topIdx (combStrip n bench y)))
        (topIdx (combStrip n bench z))) := by
    unfold bottomOff
    exact cube_off_hole (seatAt a) 2 2 z n k
      (upMv2 a + 2 * pegCount ((upLane n k bench y).take n))
      (raisedHole a.hole1 (topIdx (combStrip n bench y))) bench
      (raisedPeak (upPk2 a)
        (countHeld ((pointFeed a).sudo_5Board_4held.set ⟨1, pointFeed_heldIx a⟩ true) 7))
      (raisedPeak a.peakS1 (countHeld (upSettled a).sudo_5Board_4held 7))
      (cOps + 2) (seatAt_ops a) (seatAt_held2ix a) (seatAt_home2ix a)
  exact hflag.trans hoff



theorem frame_of_at (t : Spec.Tier) (b : Ecbs.Board)
    (baseX baseY px py : List Nat) (done : Nat)
    (hAt : FformAt t b baseX baseY px py done) :
    FrameAt b t baseX baseY := by
  rcases hAt with ⟨_, htier, _, _, _, _, _, _, _, _, _, _,
      h3, h4, hH3, hH4, _, _, hszH, hszD, _⟩
  exact {
    tier := htier
    szH := hszH
    szD := hszD
    home3 := h3
    held3 := hH3
    home4 := h4
    held4 := hH4
  }

/-- Homes layout, colour still unread. The comb is `FrameAt` for the base
    point the cell entered with. -/
theorem zero_comb_frame
    (t : Spec.Tier) (b : Ecbs.Board)
    (baseX baseY px py xP yP zP : List Nat) (done : Nat)
    (hAt : FformAt t b baseX baseY px py done)
    (hsh : TierShape t) (hOk : BoardOk t) (sat : TierSat t)
    (hs2 : 2 < t.script)
    (hxL : xP.length = t.n) (hyL : yP.length = t.n) (hzL : zP.length = t.n)
    (hxT : allTritList xP) (hyT : allTritList yP) (hzT : allTritList zP)
    (hszH : b.sudo_5Board_4home.size = 8) (hszD : b.sudo_5Board_4held.size = 8)
    (h0 : b.sudo_5Board_4home[0]'(by rw [hszH]; decide) = embed xP)
    (h1 : b.sudo_5Board_4home[1]'(by rw [hszH]; decide) = embed yP)
    (h2 : b.sudo_5Board_4home[2]'(by rw [hszH]; decide) = embed zP)
    (hd0 : b.sudo_5Board_4held[0]'(by rw [hszD]; decide) = true)
    (hd1 : b.sudo_5Board_4held[1]'(by rw [hszD]; decide) = true)
    (hd2 : b.sudo_5Board_4held[2]'(by rw [hszD]; decide) = true)
    (hoff : b.sudo_5Board_8bench_on = false)
    (moves slides c0 mark mx pk peakS hole cOps : Nat)
    (hmv : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hsl : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hc0 : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat c0)
    (hmkN : b.sudo_5Board_6marker = Int.ofNat mark)
    (hmx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hpk : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk)
    (hstrict : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat peakS)
    (hhole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop1 : b.sudo_5Board_4cost.sudo_5Costs_3ops[1]'hops = (cOps : Int))
    (hCtrl : FitsLen (c0 + 6)) (hOps : FitsLen (cOps + 3))
    (hRoom : FitsLen (moves + cubeCharge t.n t.benchlen + 2 * t.n +
        3 * (t.benchlen - t.n)))
    (hSl : FitsLen (slides + slideCharge t.n)) :
    ∃ (bL : Ecbs.Board)
      (a : DownAcross bL xP yP t.n t.k t.w t.h t.r t.benchlen t.combgap
            pk moves slides hole cOps (c0 + 1) mx t.script),
      Ecbs.marker_lift b = .ok bL ∧
      Ecbs.frobenius_point bL = .ok (bottomFlag a zP) ∧
      FrameAt (bottomFlag a zP) t baseX baseY ∧
      (bottomFlag a zP).sudo_5Board_4held[5]? = some false ∧
      (bottomFlag a zP).sudo_5Board_4held[6]? = some false ∧
      (bottomFlag a zP).sudo_5Board_4cost.sudo_5Costs_3ops.size = 5 := by
  obtain ⟨bL, a, hlift, hhome?, hheld?⟩ :=
    fform_homes_across t b baseX baseY px py xP yP zP done hAt hsh hOk sat
      hxL hyL hxT hyT hszH hszD h0 h1 h2 hd0 hd1 hd2 hoff moves slides c0 mark mx
      pk peakS hole cOps hmv hsl hc0 hmkN hmx hpk hstrict hhole hops hop1 hCtrl hOps
      hRoom hSl
  have href := marker_lift_refines b mark c0 hmkN hc0 (FitsLen.of_le hCtrl (by omega))
  have hbL : bL = { b with
      sudo_5Board_6marker := -1
      sudo_5Board_4cost := { b.sudo_5Board_4cost with
        sudo_5Costs_4ctrl := Int.ofNat (c0 + 1) } } :=
    Except.ok.inj (hlift.symm.trans href)
  have hmkL : bL.sudo_5Board_9marker_on = true := by rw [hbL]; exact hAt.1
  have hoffL : bL.sudo_5Board_8bench_on = false := by rw [hbL]; exact hoff
  have hmNeg : bL.sudo_5Board_6marker < 0 := by
    have hmEq : bL.sudo_5Board_6marker = -1 := by rw [hbL]
    rw [hmEq]
    decide
  have hc : bL.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (c0 + 1) := by rw [hbL]
  have hmxL : bL.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx := by
    rw [hbL]; exact hmx
  have hte : bL.sudo_5Board_1t = embTier t := by rw [hbL]; exact hAt.2.1
  have hscript : bL.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat t.script := by
    rw [hte]; rfl
  have hopsL : 1 < bL.sudo_5Board_4cost.sudo_5Costs_3ops.size := by rw [hbL]; exact hops
  have hopL : bL.sudo_5Board_4cost.sudo_5Costs_3ops[1]'hopsL = (cOps : Int) := by
    have hArr : bL.sudo_5Board_4cost.sudo_5Costs_3ops =
        b.sudo_5Board_4cost.sudo_5Costs_3ops := by rw [hbL]
    exact (at_eq hArr hopsL hops).trans hop1
  have h0D : 0 < bL.sudo_5Board_4held.size := a.h0D
  have h0H : 0 < bL.sudo_5Board_4home.size := a.h0H
  have hheld0 : bL.sudo_5Board_4held[0]'h0D = true := by
    have hArr : bL.sudo_5Board_4held = b.sudo_5Board_4held := by rw [hbL]
    have hIdx : 0 < b.sudo_5Board_4held.size := by rw [hszD]; decide
    exact (at_eq hArr h0D hIdx).trans hd0
  have hhome0 : bL.sudo_5Board_4home[0]'h0H = embed xP := by
    have hArr : bL.sudo_5Board_4home = b.sudo_5Board_4home := by rw [hbL]
    have hIdx : 0 < b.sudo_5Board_4home.size := by rw [hszH]; decide
    exact (at_eq hArr h0H hIdx).trans h0
  have hstrictC : bL.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int) := by
    rw [hbL]; exact hstrict.trans (ofNat_eq_natCast peakS)
  have hpeakC : bL.sudo_5Board_4cost.sudo_5Costs_4peak = (pk : Int) := by
    rw [hbL]; exact hpk.trans (ofNat_eq_natCast pk)
  have hn0 : 0 < t.n := hOk.n_pos
  have hn : bL.sudo_5Board_1t.sudo_4Tier_1n = (t.n : Int) := by
    rw [hte]; simp [embTier, ofNat_eq_natCast]
  have hmovesC : bL.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int) := by
    rw [hbL]; exact hmv.trans (ofNat_eq_natCast moves)
  have hbl : bL.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat t.benchlen := by rw [hte]; rfl
  have hcg : bL.sudo_5Board_1t.sudo_4Tier_7combgap = Int.ofNat t.combgap := by rw [hte]; rfl
  have hholeL : bL.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole := by
    rw [hbL]; exact hhole
  have hw : bL.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat t.w := by rw [hte]; rfl
  have hh : bL.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat t.h := by rw [hte]; rfl
  have hr : bL.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat t.r := by rw [hte]; rfl
  have hk : bL.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat t.k := by rw [hte]; rfl
  have hspan : 3 * (t.n - 1) + t.combgap < t.benchlen := sat.cube_span
  have hsm := hsh.small
  have hnsm := hsh.n_small
  have hcapN := smallCap t.n t.benchlen
  have hnFit : FitsLen t.n := geomFit t.n t.benchlen t.n hnsm hsm.2.2.2 hcapN.1
  have hbenchFit : FitsLen t.benchlen :=
    geomFit t.n t.benchlen t.benchlen hnsm hsm.2.2.2 hcapN.2.1
  have h3 : FitsLen (3 * (t.n - 1)) :=
    geomFit t.n t.benchlen (3 * (t.n - 1)) hnsm hsm.2.2.2 hcapN.2.2
  have hMv : FitsLen (moves + cubeCharge t.n t.benchlen) := FitsLen.of_le hRoom (by omega)
  have hfm : FitsLen (moves + 2 * t.n) := by
    apply FitsLen.of_le hMv
    unfold cubeCharge
    omega
  have hfold : FitsLen (moves + 2 * t.n + 3 * (t.benchlen - t.n)) := by
    apply FitsLen.of_le hMv
    unfold cubeCharge
    omega
  have hdown := cube_down_eq bL 0 0 xP t.w t.h t.r t.n t.k moves hole t.benchlen pk peakS
    cOps t.combgap (c0 + 1) mx t.script hmkL hoffL hmNeg hc hmxL hscript
    (by have h := hsh.script_ge; omega) (FitsLen.of_le hCtrl (by omega)) hopsL hopL
    (FitsLen.of_le hOps (by omega)) h0D h0H hheld0 hhome0 (by rw [hbL, hszD]; decide)
    hstrictC hpeakC hn0 hn hxL hnFit hmovesC hbl hcg hspan h3 hfm hholeL hxT
    hsh.w0 hsh.h0 hsh.rlt hsh.r0 hsh.n_eq hsh.k_le hsh.gap hw hh hr hk hsm hnsm
    hbenchFit hfold
  have hOn : a.b1On = acrossBoard bL xP t.n t.k moves hole t.benchlen pk peakS cOps
      (c0 + 1) mx hopsL h0D h0H :=
    Except.ok.inj (a.hcube.symm.trans hdown)
  have hs1 : 1 < t.script := by have h := hsh.script_ge; omega
  have hnb : t.n ≤ t.benchlen := by omega
  have hnbL : t.n ≤ a.laneX.length := by rw [a.hlenX]; exact hnb
  have hgap0 : 0 < t.n - t.k := by rw [hsh.gap]; exact Nat.mul_pos hsh.w0 hsh.r0
  obtain ⟨hpeg, hfitMv, hfitSl⟩ := up_settle_fit a hMv hSl
  obtain ⟨_, hMu, _⟩ := up_out_le a
  have hleF : upMv2 a + 2 * pegCount ((upLane t.n t.k t.benchlen yP).take t.n) +
      2 * t.n + 3 * (t.benchlen - t.n) ≤
      moves + cubeCharge t.n t.benchlen + 2 * t.n + 3 * (t.benchlen - t.n) := by
    unfold cubeCharge at hMu
    unfold cubeCharge
    omega
  have hleM : upMv2 a + 2 * pegCount ((upLane t.n t.k t.benchlen yP).take t.n) +
      2 * t.n ≤
      moves + cubeCharge t.n t.benchlen + 2 * t.n + 3 * (t.benchlen - t.n) := by
    unfold cubeCharge at hMu
    unfold cubeCharge
    omega
  have hfmU : FitsLen (upMv2 a + 2 * pegCount ((upLane t.n t.k t.benchlen yP).take t.n) +
      2 * t.n) := FitsLen.of_le hRoom hleM
  have hfoldU : FitsLen (upMv2 a + 2 * pegCount ((upLane t.n t.k t.benchlen yP).take t.n) +
      2 * t.n + 3 * (t.benchlen - t.n)) := FitsLen.of_le hRoom hleF
  have hhome2 : a.b1On.sudo_5Board_4home[2]'(by rw [a.hszHOn]; decide) = embed zP := by
    have hsz : 2 < a.b1On.sudo_5Board_4home.size := by rw [a.hszHOn]; decide
    have h := hhome?
    rw [Array.getElem?_eq_getElem hsz] at h
    exact Option.some.inj h
  have hheld2 : a.b1On.sudo_5Board_4held[2]'(by rw [a.hszDOn]; decide) = true := by
    have hsz : 2 < a.b1On.sudo_5Board_4held.size := by rw [a.hszDOn]; decide
    have h := hheld?
    rw [Array.getElem?_eq_getElem hsz] at h
    exact Option.some.inj h
  have hflag := frobenius_is_flag a zP hyT hyL hheld2 hhome2 hzL hzT hn0 hnbL hnb hgap0
    hs1 hs2 (FitsLen.of_le hCtrl (by omega)) (FitsLen.of_le hOps (by omega))
    hCtrl hOps hspan h3 hnFit hbenchFit hpeg hfitMv hfitSl hfmU hfoldU
    hsh.w0 hsh.h0 hsh.rlt hsh.r0 hsh.n_eq hsh.k_le hsh.gap hsm hnsm
  have hfr := comb_frame t b bL (bottomFlag a zP) baseX baseY xP yP zP a c0 mark peakS
    (frame_of_at t b baseX baseY px py done hAt) hmkN hc0
    (FitsLen.of_le hCtrl (by omega)) hlift hopsL hOn rfl
  obtain ⟨h5, h6, hopsN⟩ := fform_open t b baseX baseY px py done hAt
  have h5L : bL.sudo_5Board_4held[5]? = some false := by
    have hheld : bL.sudo_5Board_4held = b.sudo_5Board_4held := by rw [hbL]
    rw [hheld]; exact h5
  have h6L : bL.sudo_5Board_4held[6]? = some false := by
    have hheld : bL.sudo_5Board_4held = b.sudo_5Board_4held := by rw [hbL]
    rw [hheld]; exact h6
  have hszL : bL.sudo_5Board_4held.size = 8 := by
    have hheld : bL.sudo_5Board_4held = b.sudo_5Board_4held := by rw [hbL]
    rw [hheld, hszD]
  have hopsBN : bL.sudo_5Board_4cost.sudo_5Costs_3ops.size = 5 := by
    have hopsA : bL.sudo_5Board_4cost.sudo_5Costs_3ops =
        b.sudo_5Board_4cost.sudo_5Costs_3ops := by rw [hbL]
    rw [hopsA]; exact hopsN
  obtain ⟨h5F, h6F⟩ := comb_gap_spare a zP peakS hopsL hOn hszL h5L h6L
  have hopsF := (comb_ops_len a zP peakS hopsL hOn).trans hopsBN
  exact ⟨bL, a, hlift, hflag, hfr, h5F, h6F, hopsF⟩

/-- `FrameAt` survives renaming the board. -/
theorem frame_cast (t : Spec.Tier) (b1 b2 : Ecbs.Board) (baseX baseY : List Nat)
    (h : b2 = b1) (fr : FrameAt b1 t baseX baseY) :
    FrameAt b2 t baseX baseY := by
  have hhome := congrArg (fun brd => brd.sudo_5Board_4home) h
  have hheld := congrArg (fun brd => brd.sudo_5Board_4held) h
  exact {
    tier := (congrArg (fun brd => brd.sudo_5Board_1t) h).trans fr.tier
    szH := (congrArg Array.size hhome).trans fr.szH
    szD := (congrArg Array.size hheld).trans fr.szD
    home3 := fun hi =>
      (at_eq hhome hi (by rw [fr.szH]; decide)).trans (fr.home3 (by rw [fr.szH]; decide))
    held3 := fun hi =>
      (at_eq hheld hi (by rw [fr.szD]; decide)).trans (fr.held3 (by rw [fr.szD]; decide))
    home4 := fun hi =>
      (at_eq hhome hi (by rw [fr.szH]; decide)).trans (fr.home4 (by rw [fr.szH]; decide))
    held4 := fun hi =>
      (at_eq hheld hi (by rw [fr.szD]; decide)).trans (fr.held4 (by rw [fr.szD]; decide))
  }

/-- The zero cell's board is the comb, and that comb is `FrameAt`. -/
theorem zero_bZ_frame
    (t : Spec.Tier) (b : Ecbs.Board)
    (baseX baseY px py xP yP zP : List Nat) (done : Nat)
    (hAt : FformAt t b baseX baseY px py done)
    (hsh : TierShape t) (hOk : BoardOk t) (sat : TierSat t)
    (hs2 : 2 < t.script)
    (hxL : xP.length = t.n) (hyL : yP.length = t.n) (hzL : zP.length = t.n)
    (hxT : allTritList xP) (hyT : allTritList yP) (hzT : allTritList zP)
    (hszH : b.sudo_5Board_4home.size = 8) (hszD : b.sudo_5Board_4held.size = 8)
    (h0 : b.sudo_5Board_4home[0]'(by rw [hszH]; decide) = embed xP)
    (h1 : b.sudo_5Board_4home[1]'(by rw [hszH]; decide) = embed yP)
    (h2 : b.sudo_5Board_4home[2]'(by rw [hszH]; decide) = embed zP)
    (hd0 : b.sudo_5Board_4held[0]'(by rw [hszD]; decide) = true)
    (hd1 : b.sudo_5Board_4held[1]'(by rw [hszD]; decide) = true)
    (hd2 : b.sudo_5Board_4held[2]'(by rw [hszD]; decide) = true)
    (hoff : b.sudo_5Board_8bench_on = false)
    (moves slides c0 mark mx pk peakS hole cOps : Nat)
    (hmv : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hsl : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hc0 : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat c0)
    (hmkN : b.sudo_5Board_6marker = Int.ofNat mark)
    (hmx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hpk : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk)
    (hstrict : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat peakS)
    (hhole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop1 : b.sudo_5Board_4cost.sudo_5Costs_3ops[1]'hops = (cOps : Int))
    (hCtrl : FitsLen (c0 + 6)) (hOps : FitsLen (cOps + 3))
    (hRoom : FitsLen (moves + cubeCharge t.n t.benchlen + 2 * t.n +
        3 * (t.benchlen - t.n)))
    (hSl : FitsLen (slides + slideCharge t.n))
    (cells : List Nat) (i : Nat)
    (hpos : 0 < t.cells) (hi : i ≤ t.cells - 1) (hlen : cells.length = t.cells)
    (hc : cells[i]'(by omega) = 0)
    (hfitI : FitsLen (i + 1)) :
    ∃ (bL : Ecbs.Board) (bZ : Ecbs.Board)
      (a : DownAcross bL xP yP t.n t.k t.w t.h t.r t.benchlen t.combgap
            pk moves slides hole cOps (c0 + 1) mx t.script),
      Ecbs.marker_lift b = .ok bL ∧
      Ecbs.frobenius_point bL = .ok bZ ∧
      (∀ h : 1 < bZ.sudo_5Board_4held.size, bZ.sudo_5Board_4held[1] = true) ∧
      (∀ h : 2 < bZ.sudo_5Board_4held.size, bZ.sudo_5Board_4held[2] = false) ∧
      (∀ h : 0 < bZ.sudo_5Board_4held.size, bZ.sudo_5Board_4held[0] = true) ∧
      bZ.sudo_5Board_4cost.sudo_5Costs_5moves =
        Int.ofNat (cubeMoves
          (upMv2 a + 2 * pegCount ((upLane t.n t.k t.benchlen yP).take t.n))
          zP t.n t.k t.benchlen) ∧
      bZ.sudo_5Board_4cost.sudo_5Costs_6slides =
        Int.ofNat (upSl a + 2 * pegCount ((upLane t.n t.k t.benchlen yP).take t.n)) ∧
      bZ.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (c0 + 6) ∧
      bZ.sudo_5Board_6marker = Int.ofNat 2 ∧
      bZ.sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
        Int.ofNat (max (max (max mx 1) 2) 3) ∧
      bZ.sudo_5Board_4cost.sudo_5Costs_4peak =
        Int.ofNat (raisedPeak
          (raisedPeak (upPk2 a)
            (countHeld ((pointFeed a).sudo_5Board_4held.set ⟨1, pointFeed_heldIx a⟩ true) 7))
          (countHeld ((seatAt a).sudo_5Board_4held.set ⟨2, seatAt_held2ix a⟩ false) 7)) ∧
      bZ.sudo_5Board_4cost.sudo_5Costs_11peak_strict =
        Int.ofNat (raisedPeak
          (raisedPeak a.peakS1 (countHeld (upSettled a).sudo_5Board_4held 7))
          (countHeld (seatAt a).sudo_5Board_4held 7)) ∧
      bZ.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
        Int.ofNat (raisedHole (raisedHole a.hole1 (topIdx (combStrip t.n t.benchlen yP)))
          (topIdx (combStrip t.n t.benchlen zP))) ∧
      bZ.sudo_5Board_4cost.sudo_5Costs_3ops[1]? = some ((cOps + 3 : Nat) : Int) ∧
      FrameAt bZ t baseX baseY ∧
      bZ.sudo_5Board_9marker_on = true ∧
      bZ.sudo_5Board_8bench_on = true ∧
      bZ.sudo_5Board_8bench_to = (2 : Int) ∧
      ∃ lane,
        bZ.sudo_5Board_5bench = embed lane ∧
        lane.take t.n = fieldCube t.n t.k t.benchlen zP ∧
        (∀ j, t.n ≤ j → ∀ hj : j < lane.length, lane[j] = 0) ∧
        bZ.sudo_5Board_4home[0]? = some (embed (fieldCube t.n t.k t.benchlen xP)) ∧
        bZ.sudo_5Board_4home[1]? = some (embed (fieldCube t.n t.k t.benchlen yP)) := by
  obtain ⟨bL, a, hlift, hflag, hfr, _, _, _⟩ :=
    zero_comb_frame t b baseX baseY px py xP yP zP done hAt hsh hOk sat hs2
      hxL hyL hzL hxT hyT hzT hszH hszD h0 h1 h2 hd0 hd1 hd2 hoff
      moves slides c0 mark mx pk peakS hole cOps hmv hsl hc0 hmkN hmx hpk hstrict
      hhole hops hop1 hCtrl hOps hRoom hSl
  obtain ⟨bL2, bZ, hlift2, hfrob, _hflow, _hwalk, hmon, hbon, hto, hlane⟩ :=
    zero_cell_flow t b baseX baseY px py xP yP zP done hAt hsh hOk sat hs2
      hxL hyL hzL hxT hyT hzT hszH hszD h0 h1 h2 hd0 hd1 hd2 hoff
      moves slides c0 mark mx pk peakS hole cOps hmv hsl hc0 hmkN hmx hpk hstrict
      hhole hops hop1 hCtrl hOps hRoom hSl cells i hpos hi hlen hc hfitI
  have hbL : bL2 = bL := Except.ok.inj (hlift2.symm.trans hlift)
  have hfrobL : Ecbs.frobenius_point bL = .ok bZ := by simpa [hbL] using hfrob
  have hbZ : bZ = bottomFlag a zP := Except.ok.inj (hfrobL.symm.trans hflag)
  have hH1 : ∀ h : 1 < bZ.sudo_5Board_4held.size, bZ.sudo_5Board_4held[1] = true := by
    intro h
    have harr := congrArg (fun brd => brd.sudo_5Board_4held) hbZ
    exact (at_eq harr h (by rw [bottomFlag_szD a zP]; decide)).trans (bottomFlag_held1 a zP)
  have hH2 : ∀ h : 2 < bZ.sudo_5Board_4held.size, bZ.sudo_5Board_4held[2] = false := by
    intro h
    have harr := congrArg (fun brd => brd.sudo_5Board_4held) hbZ
    exact (at_eq harr h (by rw [bottomFlag_szD a zP]; decide)).trans (bottomFlag_held2 a zP)
  have hH0 : ∀ h : 0 < bZ.sudo_5Board_4held.size, bZ.sudo_5Board_4held[0] = true := by
    intro h
    have harr := congrArg (fun brd => brd.sudo_5Board_4held) hbZ
    exact (at_eq harr h (by rw [bottomFlag_szD a zP]; decide)).trans (bottomFlag_held0 a zP)
  have hmvZ : bZ.sudo_5Board_4cost.sudo_5Costs_5moves =
      Int.ofNat (cubeMoves
        (upMv2 a + 2 * pegCount ((upLane t.n t.k t.benchlen yP).take t.n))
        zP t.n t.k t.benchlen) :=
    (congrArg (fun brd => brd.sudo_5Board_4cost.sudo_5Costs_5moves) hbZ).trans
      (bottomFlag_moves a zP)
  have hslZ : bZ.sudo_5Board_4cost.sudo_5Costs_6slides =
      Int.ofNat (upSl a + 2 * pegCount ((upLane t.n t.k t.benchlen yP).take t.n)) :=
    (congrArg (fun brd => brd.sudo_5Board_4cost.sudo_5Costs_6slides) hbZ).trans
      (bottomFlag_slides a zP)
  have hctrlZ : bZ.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (c0 + 6) := by
    have h := (congrArg (fun brd => brd.sudo_5Board_4cost.sudo_5Costs_4ctrl) hbZ).trans
      (bottomFlag_ctrl a zP)
    have hnat : (c0 + 1) + 5 = c0 + 6 := by omega
    simpa [hnat] using h
  have hmarkZ : bZ.sudo_5Board_6marker = Int.ofNat 2 :=
    (congrArg (fun brd => brd.sudo_5Board_6marker) hbZ).trans (bottomFlag_mark a zP)
  have hmxZ : bZ.sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
      Int.ofNat (max (max (max mx 1) 2) 3) :=
    (congrArg (fun brd => brd.sudo_5Board_4cost.sudo_5Costs_17script_marker_max) hbZ).trans
      (bottomFlag_mx a zP)
  have hpkZ : bZ.sudo_5Board_4cost.sudo_5Costs_4peak =
      Int.ofNat (raisedPeak
        (raisedPeak (upPk2 a)
          (countHeld ((pointFeed a).sudo_5Board_4held.set ⟨1, pointFeed_heldIx a⟩ true) 7))
        (countHeld ((seatAt a).sudo_5Board_4held.set ⟨2, seatAt_held2ix a⟩ false) 7)) :=
    (congrArg (fun brd => brd.sudo_5Board_4cost.sudo_5Costs_4peak) hbZ).trans
      (bottomFlag_peak a zP)
  have hstZ : bZ.sudo_5Board_4cost.sudo_5Costs_11peak_strict =
      Int.ofNat (raisedPeak
        (raisedPeak a.peakS1 (countHeld (upSettled a).sudo_5Board_4held 7))
        (countHeld (seatAt a).sudo_5Board_4held 7)) :=
    (congrArg (fun brd => brd.sudo_5Board_4cost.sudo_5Costs_11peak_strict) hbZ).trans
      (bottomFlag_strict a zP)
  have hholeZ : bZ.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      Int.ofNat (raisedHole (raisedHole a.hole1 (topIdx (combStrip t.n t.benchlen yP)))
        (topIdx (combStrip t.n t.benchlen zP))) :=
    (congrArg (fun brd => brd.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole) hbZ).trans
      (bottomFlag_hole a zP)
  have hopZ : bZ.sudo_5Board_4cost.sudo_5Costs_3ops[1]? =
      some ((cOps + 3 : Nat) : Int) := by
    have hopt : (bottomFlag a zP).sudo_5Board_4cost.sudo_5Costs_3ops[1]? =
        some (Int.ofNat (cOps + 3)) := by
      rw [Array.getElem?_eq_getElem (bottomFlag_ops a zP)]
      exact congrArg some (bottomFlag_op a zP)
    have harr := congrArg
      (fun brd => brd.sudo_5Board_4cost.sudo_5Costs_3ops[1]?) hbZ
    rw [ofNat_eq_natCast] at hopt
    exact harr.trans hopt
  exact ⟨bL, bZ, a, hlift, hfrobL, hH1, hH2, hH0, hmvZ, hslZ, hctrlZ, hmarkZ, hmxZ,
    hpkZ, hstZ, hholeZ, hopZ,
    frame_cast t (bottomFlag a zP) bZ baseX baseY hbZ hfr, hmon, hbon, hto, hlane⟩

/-- The zero cell's frame and `zBench` lane. The comb counters stay on
    `zero_bZ_frame`: this type does not name the comb. -/
theorem zero_bZ_lay
    (t : Spec.Tier) (b : Ecbs.Board)
    (baseX baseY px py xP yP zP : List Nat) (done : Nat)
    (hAt : FformAt t b baseX baseY px py done)
    (hsh : TierShape t) (hOk : BoardOk t) (sat : TierSat t)
    (hs2 : 2 < t.script)
    (hxL : xP.length = t.n) (hyL : yP.length = t.n) (hzL : zP.length = t.n)
    (hxT : allTritList xP) (hyT : allTritList yP) (hzT : allTritList zP)
    (hszH : b.sudo_5Board_4home.size = 8) (hszD : b.sudo_5Board_4held.size = 8)
    (h0 : b.sudo_5Board_4home[0]'(by rw [hszH]; decide) = embed xP)
    (h1 : b.sudo_5Board_4home[1]'(by rw [hszH]; decide) = embed yP)
    (h2 : b.sudo_5Board_4home[2]'(by rw [hszH]; decide) = embed zP)
    (hd0 : b.sudo_5Board_4held[0]'(by rw [hszD]; decide) = true)
    (hd1 : b.sudo_5Board_4held[1]'(by rw [hszD]; decide) = true)
    (hd2 : b.sudo_5Board_4held[2]'(by rw [hszD]; decide) = true)
    (hoff : b.sudo_5Board_8bench_on = false)
    (moves slides c0 mark mx pk peakS hole cOps : Nat)
    (hmv : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hsl : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hc0 : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat c0)
    (hmkN : b.sudo_5Board_6marker = Int.ofNat mark)
    (hmx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hpk : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk)
    (hstrict : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat peakS)
    (hhole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop1 : b.sudo_5Board_4cost.sudo_5Costs_3ops[1]'hops = (cOps : Int))
    (hCtrl : FitsLen (c0 + 6)) (hOps : FitsLen (cOps + 3))
    (hRoom : FitsLen (moves + cubeCharge t.n t.benchlen + 2 * t.n +
        3 * (t.benchlen - t.n)))
    (hSl : FitsLen (slides + slideCharge t.n))
    (cells : List Nat) (i : Nat)
    (hpos : 0 < t.cells) (hi : i ≤ t.cells - 1) (hlen : cells.length = t.cells)
    (hc : cells[i]'(by omega) = 0)
    (hfitI : FitsLen (i + 1)) :
    ∃ (bL : Ecbs.Board) (bZ : Ecbs.Board),
      Ecbs.marker_lift b = .ok bL ∧
      Ecbs.frobenius_point bL = .ok bZ ∧
      FrameAt bZ t baseX baseY ∧
      (∀ h : 1 < bZ.sudo_5Board_4held.size, bZ.sudo_5Board_4held[1] = true) ∧
      (∀ h : 2 < bZ.sudo_5Board_4held.size, bZ.sudo_5Board_4held[2] = false) ∧
      bZ.sudo_5Board_8bench_on = true ∧
      bZ.sudo_5Board_8bench_to = (2 : Int) ∧
      ∃ lane,
        bZ.sudo_5Board_5bench = embed lane ∧
        lane.take t.n = fieldCube t.n t.k t.benchlen zP ∧
        (∀ j, t.n ≤ j → ∀ hj : j < lane.length, lane[j] = 0) ∧
        bZ.sudo_5Board_4home[0]? = some (embed (fieldCube t.n t.k t.benchlen xP)) ∧
        bZ.sudo_5Board_4home[1]? = some (embed (fieldCube t.n t.k t.benchlen yP)) := by
  obtain ⟨bL, bZ, _a, hlift, hfrob, hH1, hH2, _hH0, _hmv, _hsl, _hctrl, _hmark,
      _hmx, _hpk, _hst, _hhole, _hop, hfr, _hmon, hbon, hto, hlane⟩ :=
    zero_bZ_frame t b baseX baseY px py xP yP zP done hAt hsh hOk sat hs2
      hxL hyL hzL hxT hyT hzT hszH hszD h0 h1 h2 hd0 hd1 hd2 hoff
      moves slides c0 mark mx pk peakS hole cOps hmv hsl hc0 hmkN hmx hpk hstrict
      hhole hops hop1 hCtrl hOps hRoom hSl cells i hpos hi hlen hc hfitI
  exact ⟨bL, bZ, hlift, hfrob, hfr, hH1, hH2, hbon, hto, hlane⟩

private theorem idx_of_some (a : Array Int) (i : Nat) (v : Int) (h : a[i]? = some v) :
    i < a.size := by
  suffices ¬ a.size ≤ i by omega
  intro hge
  have hn : a[i]? = none := Array.getElem?_eq_none_iff.mpr hge
  rw [h] at hn
  cases hn

/-- The zero cell's counters, as naturals. Three cubes, and slot 0 stays. -/
theorem zero_bZ_charge
    (t : Spec.Tier) (b : Ecbs.Board)
    (baseX baseY px py xP yP zP : List Nat) (done : Nat)
    (hAt : FformAt t b baseX baseY px py done)
    (hsh : TierShape t) (hOk : BoardOk t) (sat : TierSat t)
    (hs2 : 2 < t.script)
    (hxL : xP.length = t.n) (hyL : yP.length = t.n) (hzL : zP.length = t.n)
    (hxT : allTritList xP) (hyT : allTritList yP) (hzT : allTritList zP)
    (hszH : b.sudo_5Board_4home.size = 8) (hszD : b.sudo_5Board_4held.size = 8)
    (h0 : b.sudo_5Board_4home[0]'(by rw [hszH]; decide) = embed xP)
    (h1 : b.sudo_5Board_4home[1]'(by rw [hszH]; decide) = embed yP)
    (h2 : b.sudo_5Board_4home[2]'(by rw [hszH]; decide) = embed zP)
    (hd0 : b.sudo_5Board_4held[0]'(by rw [hszD]; decide) = true)
    (hd1 : b.sudo_5Board_4held[1]'(by rw [hszD]; decide) = true)
    (hd2 : b.sudo_5Board_4held[2]'(by rw [hszD]; decide) = true)
    (hoff : b.sudo_5Board_8bench_on = false)
    (moves slides c0 mark mx pk peakS hole cOps : Nat)
    (hmv : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hsl : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hc0 : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat c0)
    (hmkN : b.sudo_5Board_6marker = Int.ofNat mark)
    (hmx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hpk : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk)
    (hstrict : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat peakS)
    (hhole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop1 : b.sudo_5Board_4cost.sudo_5Costs_3ops[1]'hops = (cOps : Int))
    (cMul : Nat)
    (hMul : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hopMul : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]'hMul = Int.ofNat cMul)
    (hCtrl : FitsLen (c0 + 6)) (hOps : FitsLen (cOps + 3))
    (hRoom : FitsLen (moves + cubeCharge t.n t.benchlen + 2 * t.n +
        3 * (t.benchlen - t.n)))
    (hSl : FitsLen (slides + slideCharge t.n))
    (cells : List Nat) (i : Nat)
    (hpos : 0 < t.cells) (hi : i ≤ t.cells - 1) (hlen : cells.length = t.cells)
    (hc : cells[i]'(by omega) = 0)
    (hfitI : FitsLen (i + 1)) :
    ∃ (bL : Ecbs.Board) (bZ : Ecbs.Board) (moves' slides' pk' peakS' hole' : Nat),
      Ecbs.marker_lift b = .ok bL ∧
      Ecbs.frobenius_point bL = .ok bZ ∧
      bZ.sudo_5Board_9marker_on = true ∧
      (∀ h : 0 < bZ.sudo_5Board_4held.size, bZ.sudo_5Board_4held[0] = true) ∧
      bZ.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves' ∧
      bZ.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides' ∧
      bZ.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (c0 + 6) ∧
      bZ.sudo_5Board_6marker = Int.ofNat 2 ∧
      bZ.sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
        Int.ofNat (max (max (max mx 1) 2) 3) ∧
      bZ.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk' ∧
      bZ.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat peakS' ∧
      bZ.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole' ∧
      1 < bZ.sudo_5Board_4cost.sudo_5Costs_3ops.size ∧
      bZ.sudo_5Board_4cost.sudo_5Costs_3ops[1]? = some ((cOps + 3 : Nat) : Int) ∧
      bZ.sudo_5Board_4cost.sudo_5Costs_3ops[0]? = some (Int.ofNat cMul) ∧
      moves' ≤ moves + cubeCharge t.n t.benchlen + 2 * t.n +
        3 * (t.benchlen - t.n) ∧
      slides' ≤ slides + 4 * t.n := by
  obtain ⟨bL, bZ, a, hlift, hfrob, _hH1, _hH2, hH0, hmvZ, hslZ, hctrlZ, hmarkZ,
      hmxZ, hpkZ, hstZ, hholeZ, hopZ, _hfr, hmon, _hbon, _hto, _hlane⟩ :=
    zero_bZ_frame t b baseX baseY px py xP yP zP done hAt hsh hOk sat hs2
      hxL hyL hzL hxT hyT hzT hszH hszD h0 h1 h2 hd0 hd1 hd2 hoff
      moves slides c0 mark mx pk peakS hole cOps hmv hsl hc0 hmkN hmx hpk hstrict
      hhole hops hop1 hCtrl hOps hRoom hSl cells i hpos hi hlen hc hfitI
  obtain ⟨bL2, bZ2, hlift2, hfrob2, hop0raw⟩ :=
    comb_ops0_board t b baseX baseY px py xP yP zP done cMul hAt hsh hOk sat hs2
      hxL hyL hzL hxT hyT hzT hszH hszD h0 h1 h2 hd0 hd1 hd2 hoff
      moves slides c0 mark mx pk peakS hole cOps hmv hsl hc0 hmkN hmx hpk hstrict
      hhole hops hop1 hMul hopMul hCtrl hOps hRoom hSl
  have hbL : bL2 = bL := Except.ok.inj (hlift2.symm.trans hlift)
  have hfrobL : Ecbs.frobenius_point bL = .ok bZ2 := by
    rw [← hbL]
    exact hfrob2
  have hbZ : bZ = bZ2 := Except.ok.inj (hfrob.symm.trans hfrobL)
  have hsz1 : 1 < bZ.sudo_5Board_4cost.sudo_5Costs_3ops.size := idx_of_some _ 1 _ hopZ
  have hop0 : bZ.sudo_5Board_4cost.sudo_5Costs_3ops[0]? = some (Int.ofNat cMul) :=
    (congrArg (fun brd => brd.sudo_5Board_4cost.sudo_5Costs_3ops[0]?) hbZ).trans hop0raw
  exact ⟨bL, bZ,
    cubeMoves (upMv2 a + 2 * pegCount ((upLane t.n t.k t.benchlen yP).take t.n))
      zP t.n t.k t.benchlen,
    upSl a + 2 * pegCount ((upLane t.n t.k t.benchlen yP).take t.n),
    raisedPeak
      (raisedPeak (upPk2 a)
        (countHeld ((pointFeed a).sudo_5Board_4held.set ⟨1, pointFeed_heldIx a⟩ true) 7))
      (countHeld ((seatAt a).sudo_5Board_4held.set ⟨2, seatAt_held2ix a⟩ false) 7),
    raisedPeak
      (raisedPeak a.peakS1 (countHeld (upSettled a).sudo_5Board_4held 7))
      (countHeld (seatAt a).sudo_5Board_4held 7),
    raisedHole (raisedHole a.hole1 (topIdx (combStrip t.n t.benchlen yP)))
      (topIdx (combStrip t.n t.benchlen zP)),
    hlift, hfrob, hmon, hH0, hmvZ, hslZ, hctrlZ, hmarkZ, hmxZ, hpkZ, hstZ, hholeZ,
    hsz1, hopZ, hop0, comb_moves_le a zP, comb_slides_le a⟩

end EcbsLink2.Link2
