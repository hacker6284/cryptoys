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

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

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
      FrameAt (bottomFlag a zP) t baseX baseY := by
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
  exact ⟨bL, a, hlift, hflag, hfr⟩

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
      bZ = bottomFlag a zP ∧
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
  obtain ⟨bL, a, hlift, hflag, hfr⟩ :=
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
  exact ⟨bL, bZ, a, hlift, hfrobL, hbZ,
    frame_cast t (bottomFlag a zP) bZ baseX baseY hbZ hfr, hmon, hbon, hto, hlane⟩

private theorem read_cell {α : Type} (a : Array α) (i : Nat) (v : α)
    (h : a[i]? = some v) : ∀ hlt : i < a.size, a[i]'hlt = v := by
  intro hlt
  have heq := Array.getElem?_eq_getElem hlt
  rw [h] at heq
  exact Option.some.inj heq.symm

/-- The zero cell cubes the projective point and leaves it in the `zBench` layout. -/
theorem zero_cell_proj
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
      bZ = bottomFlag a zP ∧
      FrameAt bZ t baseX baseY ∧
      ProjOn t bZ (fieldCube t.n t.k t.benchlen px) (fieldCube t.n t.k t.benchlen py) := by
  obtain ⟨bL, bZ, a, _hlift, _hfrob, hbZ, hfr, _hmon, hbon, hto,
      lane, hbench, htake, hzero, hhome0, hhome1⟩ :=
    zero_bZ_frame t b baseX baseY px py xP yP zP done hAt hsh hOk sat hs2
      hxL hyL hzL hxT hyT hzT hszH hszD h0 h1 h2 hd0 hd1 hd2 hoff
      moves slides c0 mark mx pk peakS hole cOps hmv hsl hc0 hmkN hmx hpk hstrict
      hhole hops hop1 hCtrl hOps hRoom hSl cells i hpos hi hlen hc hfitI
  rcases hAt with ⟨_, _, hpx, hpy, hpxT, hpyT, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      hproj, _⟩
  rcases hproj with ⟨xQ, yQ, zQ, lay, _hxQL, _hyQL, _hzQL, hxQT, hyQT, hzQT,
      hxQ, hyQ, _hzne, hQ0, hlay, wInv, hwL, hwT, hinv⟩
  have hnb : t.n ≤ t.benchlen := by
    have hspan : 3 * (t.n - 1) + t.combgap < t.benchlen := sat.cube_span
    omega
  have hk : t.k < t.n := by
    have hgap : 0 < t.n - t.k := by rw [hsh.gap]; exact Nat.mul_pos hsh.w0 hsh.r0
    omega
  have h3span : 3 * (t.n - 1) < t.benchlen := by
    have hspan : 3 * (t.n - 1) + t.combgap < t.benchlen := sat.cube_span
    omega
  have h2span : 2 * (t.n - 1) < t.benchlen := by omega
  have hxId : xQ = xP :=
    embed_inj ((hQ0 (by rw [hszH]; decide)).symm.trans h0)
  cases lay with
  | yBench =>
    rw [hoff] at hlay
    cases hlay.1
  | zBench =>
    have hfalse := hlay.2.2.2.2.2 (by rw [hszD]; decide)
    rw [hd2] at hfalse
    cases hfalse
  | homes =>
    have hyId : yQ = yP :=
      embed_inj ((hlay.2.1 (by rw [hszH]; decide)).symm.trans h1)
    have hzId : zQ = zP :=
      embed_inj ((hlay.2.2.1 (by rw [hszH]; decide)).symm.trans h2)
    have hcube := cube_point_inv t.n t.k t.benchlen px py zQ wInv hOk.n_pos hk hnb
      h2span h3span hpxT hpyT hzQT hwT (by rw [hzId]; exact hzL) hwL hinv
    have hzC : fieldCube t.n t.k t.benchlen zP ≠ List.replicate t.n 0 := by
      simpa [hzId] using hcube.2.2.2.1
    have hxHome : ∀ h : 0 < bZ.sudo_5Board_4home.size,
        bZ.sudo_5Board_4home[0] = embed
          (fieldMul t.n t.k t.benchlen (fieldCube t.n t.k t.benchlen px)
            (fieldCube t.n t.k t.benchlen zP)) := by
      intro h
      have hread := read_cell _ 0 _ hhome0 h
      have hmul := hcube.1
      rw [← hxQ, hxId, hzId] at hmul
      exact hread.trans (congrArg embed hmul.symm)
    have hyHome : ∀ h : 1 < bZ.sudo_5Board_4home.size,
        bZ.sudo_5Board_4home[1] = embed
          (fieldMul t.n t.k t.benchlen (fieldCube t.n t.k t.benchlen py)
            (fieldCube t.n t.k t.benchlen zP)) := by
      intro h
      have hread := read_cell _ 1 _ hhome1 h
      have hmul := hcube.2.1
      rw [← hyQ, hyId, hzId] at hmul
      exact hread.trans (congrArg embed hmul.symm)
    have hHeld1 : ∀ h : 1 < bZ.sudo_5Board_4held.size, bZ.sudo_5Board_4held[1] = true := by
      intro h
      have harr := congrArg (fun brd => brd.sudo_5Board_4held) hbZ
      exact (at_eq harr h (by rw [bottomFlag_szD a zP]; decide)).trans (bottomFlag_held1 a zP)
    have hHeld2 : ∀ h : 2 < bZ.sudo_5Board_4held.size, bZ.sudo_5Board_4held[2] = false := by
      intro h
      have harr := congrArg (fun brd => brd.sudo_5Board_4held) hbZ
      exact (at_eq harr h (by rw [bottomFlag_szD a zP]; decide)).trans (bottomFlag_held2 a zP)
    have hnle : t.n ≤ lane.length := by
      have hlenT : (lane.take t.n).length = min t.n lane.length := List.length_take _ _
      rw [htake, fieldCube_length t.n t.k t.benchlen zP hnb] at hlenT
      exact hlenT.symm ▸ Nat.min_le_right t.n lane.length
    refine ⟨bL, bZ, a, hbZ, hfr, ?_⟩
    refine ⟨fieldMul t.n t.k t.benchlen (fieldCube t.n t.k t.benchlen px)
        (fieldCube t.n t.k t.benchlen zP),
      fieldMul t.n t.k t.benchlen (fieldCube t.n t.k t.benchlen py)
        (fieldCube t.n t.k t.benchlen zP),
      fieldCube t.n t.k t.benchlen zP, .zBench, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, hzC,
      hxHome, ?_, fieldCube t.n t.k t.benchlen wInv, ?_, ?_, ?_⟩
    · rw [← hzId, hcube.1, ← hxQ, hxId, fieldCube_length t.n t.k t.benchlen xP hnb]
    · rw [← hzId, hcube.2.1, ← hyQ, hyId, fieldCube_length t.n t.k t.benchlen yP hnb]
    · exact fieldCube_length t.n t.k t.benchlen zP hnb
    · rw [← hzId, hcube.1, ← hxQ, hxId]
      exact fieldCube_trits t.n t.k t.benchlen xP hxT h3span hsh.k_le
    · rw [← hzId, hcube.2.1, ← hyQ, hyId]
      exact fieldCube_trits t.n t.k t.benchlen yP hyT h3span hsh.k_le
    · exact fieldCube_trits t.n t.k t.benchlen zP hzT h3span hsh.k_le
    · exact ⟨hbon, hto, ⟨lane, hbench, hnle, htake, hzero⟩, hyHome, hHeld1, hHeld2⟩
    · simpa [hzId] using hcube.2.2.2.2.1
    · simpa [hzId] using hcube.2.2.2.2.2
    · simpa [hzId] using hcube.2.2.1

end EcbsLink2.Link2
