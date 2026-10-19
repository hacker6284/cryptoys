/-
  A zero cell keeps the frame. The incoming `FformAt` is `FrameAt` on the
  board the cell entered. `b1On_base` carries homes 3 and 4 through the lift
  and the across cube, and `comb_frame` carries them onto the comb.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FformFrob
import EcbsLink2.Link2.FformFrame

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
    (hxL : xP.length = t.n) (hyL : yP.length = t.n)
    (hxT : allTritList xP) (hyT : allTritList yP)
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
      FrameAt (bottomFlag a zP) t baseX baseY := by
  obtain ⟨bL, a, hlift, _hhome?, _hheld?⟩ :=
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
  have hfr := comb_frame t b bL (bottomFlag a zP) baseX baseY xP yP zP a c0 mark peakS
    (frame_of_at t b baseX baseY px py done hAt) hmkN hc0
    (FitsLen.of_le hCtrl (by omega)) hlift hopsL hOn rfl
  exact ⟨bL, a, hlift, hfr⟩

end EcbsLink2.Link2
