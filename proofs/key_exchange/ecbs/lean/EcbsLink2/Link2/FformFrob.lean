/-
  `frobenius_point` on an `FformAt` board in the homes layout.
  The live cell lifts the marker first. The bench is off, so the across cube
  is `down_across`, and home 2 is still `Z`. `frobenius_bottom_field` then
  cubes that bottom onto the bench. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.BottomGlue
import EcbsLink2.Link2.WalkFformInd
import EcbsLink2.Link2.CellCube
import EcbsLink2.Link2.BenchDown

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- Two proofs that an index is in range read the same cell. -/
private theorem elem_cast {α : Type} (a : Array α) (i : Nat)
    (h1 h2 : i < a.size) {v : α} (h : a[i]'h1 = v) : a[i]'h2 = v := by
  cases proof_irrel h1 h2
  exact h

/-- The across cube clears home 0 and leaves every other home. -/
theorem across_kept
    (b : Ecbs.Board) (xs : List Nat) (i : Nat) (v : Array Int)
    (n k moves hole bench peak peakS cOps ctrl mx : Nat)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hF : 0 < b.sudo_5Board_4held.size)
    (hHome : 0 < b.sudo_5Board_4home.size)
    (hne : (0 : Nat) ≠ i)
    (hi : i < b.sudo_5Board_4home.size)
    (h : b.sudo_5Board_4home[i]'hi = v) :
    (acrossBoard b xs n k moves hole bench peak peakS cOps ctrl mx hops hF hHome).sudo_5Board_4home[i]? =
      some v := by
  rw [raw_home]
  rw [Array.getElem?_set_ne _ _ _ hne]
  rw [feed_home, Array.getElem?_eq_getElem hi]
  exact congrArg some h

/-- The across cube clears held 0 and leaves every other held flag. -/
theorem across_kept_held
    (b : Ecbs.Board) (xs : List Nat) (i : Nat)
    (n k moves hole bench peak peakS cOps ctrl mx : Nat)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hF : 0 < b.sudo_5Board_4held.size)
    (hHome : 0 < b.sudo_5Board_4home.size)
    (hne : (0 : Nat) ≠ i)
    (hi : i < b.sudo_5Board_4held.size)
    (h : b.sudo_5Board_4held[i]'hi = true) :
    (acrossBoard b xs n k moves hole bench peak peakS cOps ctrl mx hops hF hHome).sudo_5Board_4held[i]? =
      some true := by
  rw [raw_held]
  rw [Array.getElem?_set_ne _ _ _ hne]
  rw [feed_held, Array.getElem?_eq_getElem hi]
  exact congrArg some h

/-- Homes layout, marker lifted: the across cube, with home 2 and held 2 still
    the bottom the lift was given. -/
theorem fform_homes_across
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
    (hRoom : FitsLen (moves + cubeCharge t.n t.benchlen + 2 * t.n + 3 * (t.benchlen - t.n)))
    (hSl : FitsLen (slides + slideCharge t.n)) :
    ∃ (bL : Ecbs.Board)
      (a : DownAcross bL xP yP t.n t.k t.w t.h t.r t.benchlen t.combgap
            pk moves slides hole cOps (c0 + 1) mx t.script),
      Ecbs.marker_lift b = .ok bL ∧
      a.b1On.sudo_5Board_4home[2]? = some (embed zP) ∧
      a.b1On.sudo_5Board_4held[2]? = some true := by
  have htier : b.sudo_5Board_1t = embTier t := hAt.2.1
  let bL := { b with
    sudo_5Board_6marker := -1
    sudo_5Board_4cost := { b.sudo_5Board_4cost with
      sudo_5Costs_4ctrl := Int.ofNat (c0 + 1) } }
  have hlift : Ecbs.marker_lift b = .ok bL :=
    marker_lift_refines b mark c0 hmkN hc0 (FitsLen.of_le hCtrl (by omega))
  have hn0 : 0 < t.n := hOk.n_pos
  have hs1 : 1 < t.script := by have h := hsh.script_ge; omega
  have hspan : 3 * (t.n - 1) + t.combgap < t.benchlen := sat.cube_span
  have hsm := hsh.small
  have hnsm := hsh.n_small
  have hcapN := smallCap t.n t.benchlen
  have hnFit : FitsLen t.n := geomFit t.n t.benchlen t.n hnsm hsm.2.2.2 hcapN.1
  have hbenchFit : FitsLen t.benchlen :=
    geomFit t.n t.benchlen t.benchlen hnsm hsm.2.2.2 hcapN.2.1
  have h3 : FitsLen (3 * (t.n - 1)) :=
    geomFit t.n t.benchlen (3 * (t.n - 1)) hnsm hsm.2.2.2 hcapN.2.2
  have hMv : FitsLen (moves + cubeCharge t.n t.benchlen) :=
    FitsLen.of_le hRoom (by omega)
  have hfm : FitsLen (moves + 2 * t.n) := by
    apply FitsLen.of_le hMv
    unfold cubeCharge
    omega
  have hfold : FitsLen (moves + 2 * t.n + 3 * (t.benchlen - t.n)) := by
    apply FitsLen.of_le hMv
    unfold cubeCharge
    omega
  have hmNeg : bL.sudo_5Board_6marker < 0 := by
    have hmEq : bL.sudo_5Board_6marker = -1 := rfl
    rw [hmEq]
    decide
  have hc : bL.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (c0 + 1) := rfl
  have hte : bL.sudo_5Board_1t = embTier t := by
    rw [show bL.sudo_5Board_1t = b.sudo_5Board_1t from rfl]
    exact htier
  have hscript : bL.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat t.script := by
    rw [hte]; rfl
  have hn : bL.sudo_5Board_1t.sudo_4Tier_1n = (t.n : Int) := by
    rw [hte]
    simp [embTier, ofNat_eq_natCast]
  have hk : bL.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat t.k := by rw [hte]; rfl
  have hw : bL.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat t.w := by rw [hte]; rfl
  have hh : bL.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat t.h := by rw [hte]; rfl
  have hr : bL.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat t.r := by rw [hte]; rfl
  have hbl : bL.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat t.benchlen := by
    rw [hte]; rfl
  have hcg : bL.sudo_5Board_1t.sudo_4Tier_7combgap = Int.ofNat t.combgap := by
    rw [hte]; rfl
  have hmoves : bL.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves := hmv
  have hslides : bL.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides := hsl
  have hpeak : bL.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk := hpk
  have hstrictL : bL.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat peakS := hstrict
  have hholeL : bL.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole := hhole
  have hmxL : bL.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx := hmx
  have hopsL : 1 < bL.sudo_5Board_4cost.sudo_5Costs_3ops.size := hops
  have hopL : bL.sudo_5Board_4cost.sudo_5Costs_3ops[1]'hopsL = (cOps : Int) :=
    elem_cast _ 1 hops hopsL hop1
  have h0D : 0 < bL.sudo_5Board_4held.size := by
    rw [show bL.sudo_5Board_4held = b.sudo_5Board_4held from rfl, hszD]; decide
  have h0H : 0 < bL.sudo_5Board_4home.size := by
    rw [show bL.sudo_5Board_4home = b.sudo_5Board_4home from rfl, hszH]; decide
  have h1D : 1 < bL.sudo_5Board_4held.size := by
    rw [show bL.sudo_5Board_4held = b.sudo_5Board_4held from rfl, hszD]; decide
  have h1H : 1 < bL.sudo_5Board_4home.size := by
    rw [show bL.sudo_5Board_4home = b.sudo_5Board_4home from rfl, hszH]; decide
  have h2D : 2 < bL.sudo_5Board_4held.size := by
    rw [show bL.sudo_5Board_4held = b.sudo_5Board_4held from rfl, hszD]; decide
  have h2H : 2 < bL.sudo_5Board_4home.size := by
    rw [show bL.sudo_5Board_4home = b.sudo_5Board_4home from rfl, hszH]; decide
  have hheld0 : bL.sudo_5Board_4held[0]'h0D = true :=
    elem_cast _ 0 (by rw [hszD]; decide) h0D hd0
  have hhome0 : bL.sudo_5Board_4home[0]'h0H = embed xP :=
    elem_cast _ 0 (by rw [hszH]; decide) h0H h0
  have hheld1 : bL.sudo_5Board_4held[1]'h1D = true :=
    elem_cast _ 1 (by rw [hszD]; decide) h1D hd1
  have hhome1 : bL.sudo_5Board_4home[1]'h1H = embed yP :=
    elem_cast _ 1 (by rw [hszH]; decide) h1H h1
  have hheld2L : bL.sudo_5Board_4held[2]'h2D = true :=
    elem_cast _ 2 (by rw [hszD]; decide) h2D hd2
  have hhome2L : bL.sudo_5Board_4home[2]'h2H = embed zP :=
    elem_cast _ 2 (by rw [hszH]; decide) h2H h2
  have hmkL : bL.sudo_5Board_9marker_on = true := hAt.1
  have hoffL : bL.sudo_5Board_8bench_on = false := hoff
  have hmovesC : bL.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int) :=
    hmoves.trans (ofNat_eq_natCast moves)
  have hpeakC : bL.sudo_5Board_4cost.sudo_5Costs_4peak = (pk : Int) :=
    hpeak.trans (ofNat_eq_natCast pk)
  have hstrictC : bL.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int) :=
    hstrictL.trans (ofNat_eq_natCast peakS)
  let a := down_across bL xP yP t.w t.h t.r t.n t.k moves slides pk peakS hole cOps
    (c0 + 1) mx t.script hszH hszD hopsL hxL hyL hxT hyT hmkL hoffL hmNeg hc hmxL
    hscript hs1 (FitsLen.of_le hCtrl (by omega)) (FitsLen.of_le hCtrl (by omega))
    hopL (FitsLen.of_le hOps (by omega)) hheld0 hhome0 hheld1 hhome1 hn hk hw hh hr
    hbl hcg hmoves hslides hpeak hstrictL hholeL hsh.w0 hsh.h0 hsh.rlt hsh.r0 hn0
    hsh.n_eq hsh.k_le hsh.gap hspan hsm hnsm
    (by
      unfold cubeCharge at hMv
      simpa [Nat.add_assoc] using hMv)
    (by simpa [slideCharge] using hSl)
  have hdown := cube_down_eq bL 0 0 xP t.w t.h t.r t.n t.k moves hole t.benchlen pk peakS
    cOps t.combgap (c0 + 1) mx t.script hmkL hoffL hmNeg hc hmxL hscript
    (by have h := hsh.script_ge; omega) (FitsLen.of_le hCtrl (by omega)) hopsL hopL
    (FitsLen.of_le hOps (by omega)) h0D h0H hheld0 hhome0 (by rw [hszD]; decide)
    hstrictC hpeakC hn0 hn hxL hnFit hmovesC hbl hcg hspan h3 hfm hholeL hxT
    hsh.w0 hsh.h0 hsh.rlt hsh.r0 hsh.n_eq hsh.k_le hsh.gap hw hh hr hk hsm hnsm
    hbenchFit hfold
  have hOn : a.b1On = acrossBoard bL xP t.n t.k moves hole t.benchlen pk peakS cOps
      (c0 + 1) mx hopsL h0D h0H :=
    Except.ok.inj (a.hcube.symm.trans hdown)
  have hhomeK := across_kept bL xP 2 (embed zP) t.n t.k moves hole t.benchlen pk peakS
    cOps (c0 + 1) mx hopsL h0D h0H (by decide) h2H hhome2L
  have hheldK := across_kept_held bL xP 2 t.n t.k moves hole t.benchlen pk peakS
    cOps (c0 + 1) mx hopsL h0D h0H (by decide) h2D hheld2L
  refine ⟨bL, a, hlift, ?_, ?_⟩
  · exact (congrArg (fun brd => brd.sudo_5Board_4home[2]?) hOn).trans hhomeK
  · exact (congrArg (fun brd => brd.sudo_5Board_4held[2]?) hOn).trans hheldK

/-- Homes layout of `FformAt`. After the cell's `marker_lift`, `frobenius_point`
    leaves `fieldCube Z` on the bench, aimed at home 2. SPEC.md §3 R5 and R7. -/
theorem frobenius_fform_homes
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
    (hRoom : FitsLen (moves + cubeCharge t.n t.benchlen + 2 * t.n + 3 * (t.benchlen - t.n)))
    (hSl : FitsLen (slides + slideCharge t.n)) :
    ∃ bL bZ,
      Ecbs.marker_lift b = .ok bL ∧
      Ecbs.frobenius_point bL = .ok bZ ∧
      bZ.sudo_5Board_9marker_on = true ∧
      bZ.sudo_5Board_8bench_on = true ∧
      bZ.sudo_5Board_8bench_to = (2 : Int) ∧
      ∃ lane,
        bZ.sudo_5Board_5bench = embed lane ∧
        lane.take t.n = fieldCube t.n t.k t.benchlen zP := by
  obtain ⟨bL, a, hlift, hhome?, hheld?⟩ :=
    fform_homes_across t b baseX baseY px py xP yP zP done hAt hsh hOk sat
      hxL hyL hxT hyT hszH hszD h0 h1 h2 hd0 hd1 hd2 hoff moves slides c0 mark mx
      pk peakS hole cOps hmv hsl hc0 hmkN hmx hpk hstrict hhole hops hop1 hCtrl hOps
      hRoom hSl
  have hn0 : 0 < t.n := hOk.n_pos
  have hs1 : 1 < t.script := by have h := hsh.script_ge; omega
  have hspan : 3 * (t.n - 1) + t.combgap < t.benchlen := sat.cube_span
  have hnb : t.n ≤ t.benchlen := by omega
  have hnbL : t.n ≤ a.laneX.length := by rw [a.hlenX]; exact hnb
  have hgap0 : 0 < t.n - t.k := by rw [hsh.gap]; exact Nat.mul_pos hsh.w0 hsh.r0
  have hsm := hsh.small
  have hnsm := hsh.n_small
  have hcapN := smallCap t.n t.benchlen
  have hnFit : FitsLen t.n := geomFit t.n t.benchlen t.n hnsm hsm.2.2.2 hcapN.1
  have hbenchFit : FitsLen t.benchlen :=
    geomFit t.n t.benchlen t.benchlen hnsm hsm.2.2.2 hcapN.2.1
  have h3 : FitsLen (3 * (t.n - 1)) :=
    geomFit t.n t.benchlen (3 * (t.n - 1)) hnsm hsm.2.2.2 hcapN.2.2
  have hMv : FitsLen (moves + cubeCharge t.n t.benchlen) :=
    FitsLen.of_le hRoom (by omega)
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
  have hfm : FitsLen (upMv2 a + 2 * pegCount ((upLane t.n t.k t.benchlen yP).take t.n) +
      2 * t.n) := FitsLen.of_le hRoom hleM
  have hfold : FitsLen (upMv2 a + 2 * pegCount ((upLane t.n t.k t.benchlen yP).take t.n) +
      2 * t.n + 3 * (t.benchlen - t.n)) := FitsLen.of_le hRoom hleF
  have hhome2 : a.b1On.sudo_5Board_4home[2]'(by rw [a.hszHOn]; decide) = embed zP := by
    have hsz : 2 < a.b1On.sudo_5Board_4home.size := by rw [a.hszHOn]; decide
    have h := hhome?
    rw [Array.getElem?_eq_getElem hsz] at h
    exact elem_cast _ 2 hsz (by rw [a.hszHOn]; decide) (Option.some.inj h)
  have hheld2 : a.b1On.sudo_5Board_4held[2]'(by rw [a.hszDOn]; decide) = true := by
    have hsz : 2 < a.b1On.sudo_5Board_4held.size := by rw [a.hszDOn]; decide
    have h := hheld?
    rw [Array.getElem?_eq_getElem hsz] at h
    exact elem_cast _ 2 hsz (by rw [a.hszDOn]; decide) (Option.some.inj h)
  obtain ⟨bZ, hfrob, hmon, hbon, hto, hlane, htake⟩ :=
    frobenius_bottom_field a zP hyT hyL hheld2 hhome2 hzL hzT hn0 hnbL hnb hgap0
      hs1 hs2 (FitsLen.of_le hCtrl (by omega)) (FitsLen.of_le hOps (by omega))
      (FitsLen.of_le hCtrl (by omega)) hOps hspan h3 hnFit hbenchFit hpeg hfitMv hfitSl
      hfm hfold hsh.w0 hsh.h0 hsh.rlt hsh.r0 hsh.n_eq hsh.k_le hsh.gap hsm hnsm
  exact ⟨bL, bZ, hlift, hfrob, hmon, hbon, hto,
    ⟨laneFold t.n (t.n - t.k) (combStrip t.n t.benchlen zP), hlane, htake⟩⟩

/-- Homes layout, marker already lifted, bench off. `frobenius_point` leaves
    `fieldCube Z` on the bench, aimed at home 2. -/
theorem frobenius_on_lifted
    (t : Spec.Tier) (b : Ecbs.Board) (xP yP zP : List Nat)
    (hsh : TierShape t) (hOk : BoardOk t) (sat : TierSat t)
    (hs2 : 2 < t.script)
    (htier : b.sudo_5Board_1t = embTier t)
    (hxL : xP.length = t.n) (hyL : yP.length = t.n) (hzL : zP.length = t.n)
    (hxT : allTritList xP) (hyT : allTritList yP) (hzT : allTritList zP)
    (hszH : b.sudo_5Board_4home.size = 8) (hszD : b.sudo_5Board_4held.size = 8)
    (h0 : b.sudo_5Board_4home[0]'(by rw [hszH]; decide) = embed xP)
    (h1 : b.sudo_5Board_4home[1]'(by rw [hszH]; decide) = embed yP)
    (h2 : b.sudo_5Board_4home[2]'(by rw [hszH]; decide) = embed zP)
    (hd0 : b.sudo_5Board_4held[0]'(by rw [hszD]; decide) = true)
    (hd1 : b.sudo_5Board_4held[1]'(by rw [hszD]; decide) = true)
    (hd2 : b.sudo_5Board_4held[2]'(by rw [hszD]; decide) = true)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hoff : b.sudo_5Board_8bench_on = false)
    (hm : b.sudo_5Board_6marker < 0)
    (moves slides ctrl mx pk peakS hole cOps : Nat)
    (hmv : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hsl : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hmx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hpk : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk)
    (hstrict : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat peakS)
    (hhole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop1 : b.sudo_5Board_4cost.sudo_5Costs_3ops[1]'hops = (cOps : Int))
    (hCtrl : FitsLen (ctrl + 5)) (hOps : FitsLen (cOps + 3))
    (hRoom : FitsLen (moves + cubeCharge t.n t.benchlen + 2 * t.n + 3 * (t.benchlen - t.n)))
    (hSl : FitsLen (slides + slideCharge t.n)) :
    ∃ bZ,
      Ecbs.frobenius_point b = .ok bZ ∧
      bZ.sudo_5Board_9marker_on = true ∧
      bZ.sudo_5Board_8bench_on = true ∧
      bZ.sudo_5Board_8bench_to = (2 : Int) ∧
      ∃ lane,
        bZ.sudo_5Board_5bench = embed lane ∧
        lane.take t.n = fieldCube t.n t.k t.benchlen zP := by
  have hn0 : 0 < t.n := hOk.n_pos
  have hs1 : 1 < t.script := by have h := hsh.script_ge; omega
  have hspan : 3 * (t.n - 1) + t.combgap < t.benchlen := sat.cube_span
  have hsm := hsh.small
  have hnsm := hsh.n_small
  have hcapN := smallCap t.n t.benchlen
  have hnFit : FitsLen t.n := geomFit t.n t.benchlen t.n hnsm hsm.2.2.2 hcapN.1
  have hbenchFit : FitsLen t.benchlen :=
    geomFit t.n t.benchlen t.benchlen hnsm hsm.2.2.2 hcapN.2.1
  have h3 : FitsLen (3 * (t.n - 1)) :=
    geomFit t.n t.benchlen (3 * (t.n - 1)) hnsm hsm.2.2.2 hcapN.2.2
  have hMv : FitsLen (moves + cubeCharge t.n t.benchlen) :=
    FitsLen.of_le hRoom (by omega)
  have hfm : FitsLen (moves + 2 * t.n) := by
    apply FitsLen.of_le hMv
    unfold cubeCharge
    omega
  have hfold : FitsLen (moves + 2 * t.n + 3 * (t.benchlen - t.n)) := by
    apply FitsLen.of_le hMv
    unfold cubeCharge
    omega
  have hscript : b.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat t.script := by
    rw [htier]; rfl
  have hn : b.sudo_5Board_1t.sudo_4Tier_1n = (t.n : Int) := by
    rw [htier]; simp [embTier, ofNat_eq_natCast]
  have hk : b.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat t.k := by rw [htier]; rfl
  have hw : b.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat t.w := by rw [htier]; rfl
  have hh : b.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat t.h := by rw [htier]; rfl
  have hr : b.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat t.r := by rw [htier]; rfl
  have hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat t.benchlen := by
    rw [htier]; rfl
  have hcg : b.sudo_5Board_1t.sudo_4Tier_7combgap = Int.ofNat t.combgap := by
    rw [htier]; rfl
  have h0D : 0 < b.sudo_5Board_4held.size := by rw [hszD]; decide
  have h0H : 0 < b.sudo_5Board_4home.size := by rw [hszH]; decide
  have h2D : 2 < b.sudo_5Board_4held.size := by rw [hszD]; decide
  have h2H : 2 < b.sudo_5Board_4home.size := by rw [hszH]; decide
  have hmovesC : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int) :=
    hmv.trans (ofNat_eq_natCast moves)
  have hpeakC : b.sudo_5Board_4cost.sudo_5Costs_4peak = (pk : Int) :=
    hpk.trans (ofNat_eq_natCast pk)
  have hstrictC : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int) :=
    hstrict.trans (ofNat_eq_natCast peakS)
  let a := down_across b xP yP t.w t.h t.r t.n t.k moves slides pk peakS hole cOps
    ctrl mx t.script hszH hszD hops hxL hyL hxT hyT hmk hoff hm hc hmx hscript hs1
    (FitsLen.of_le hCtrl (by omega)) (FitsLen.of_le hCtrl (by omega)) hop1
    (FitsLen.of_le hOps (by omega)) hd0 h0 hd1 h1 hn hk hw hh hr hbl hcg hmv hsl hpk
    hstrict hhole hsh.w0 hsh.h0 hsh.rlt hsh.r0 hn0 hsh.n_eq hsh.k_le hsh.gap hspan hsm
    hnsm
    (by
      unfold cubeCharge at hMv
      simpa [Nat.add_assoc] using hMv)
    (by simpa [slideCharge] using hSl)
  have hdown := cube_down_eq b 0 0 xP t.w t.h t.r t.n t.k moves hole t.benchlen pk peakS
    cOps t.combgap ctrl mx t.script hmk hoff hm hc hmx hscript
    (by have h := hsh.script_ge; omega) (FitsLen.of_le hCtrl (by omega)) hops hop1
    (FitsLen.of_le hOps (by omega)) h0D h0H hd0 h0 (by rw [hszD]; decide)
    hstrictC hpeakC hn0 hn hxL hnFit hmovesC hbl hcg hspan h3 hfm hhole hxT
    hsh.w0 hsh.h0 hsh.rlt hsh.r0 hsh.n_eq hsh.k_le hsh.gap hw hh hr hk hsm hnsm
    hbenchFit hfold
  have hOn : a.b1On = acrossBoard b xP t.n t.k moves hole t.benchlen pk peakS cOps
      ctrl mx hops h0D h0H :=
    Except.ok.inj (a.hcube.symm.trans hdown)
  have hhomeK := across_kept b xP 2 (embed zP) t.n t.k moves hole t.benchlen pk peakS
    cOps ctrl mx hops h0D h0H (by decide) h2H h2
  have hheldK := across_kept_held b xP 2 t.n t.k moves hole t.benchlen pk peakS
    cOps ctrl mx hops h0D h0H (by decide) h2D hd2
  have hhome? : a.b1On.sudo_5Board_4home[2]? = some (embed zP) :=
    (congrArg (fun brd => brd.sudo_5Board_4home[2]?) hOn).trans hhomeK
  have hheld? : a.b1On.sudo_5Board_4held[2]? = some true :=
    (congrArg (fun brd => brd.sudo_5Board_4held[2]?) hOn).trans hheldK
  have hnb : t.n ≤ t.benchlen := by omega
  have hnbL : t.n ≤ a.laneX.length := by rw [a.hlenX]; exact hnb
  have hgap0 : 0 < t.n - t.k := by rw [hsh.gap]; exact Nat.mul_pos hsh.w0 hsh.r0
  obtain ⟨hpeg, hfitMv, hfitSlP⟩ := up_settle_fit a hMv hSl
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
  have hfmP : FitsLen (upMv2 a + 2 * pegCount ((upLane t.n t.k t.benchlen yP).take t.n) +
      2 * t.n) := FitsLen.of_le hRoom hleM
  have hfoldP : FitsLen (upMv2 a + 2 * pegCount ((upLane t.n t.k t.benchlen yP).take t.n) +
      2 * t.n + 3 * (t.benchlen - t.n)) := FitsLen.of_le hRoom hleF
  have hhome2 : a.b1On.sudo_5Board_4home[2]'(by rw [a.hszHOn]; decide) = embed zP := by
    have hsz : 2 < a.b1On.sudo_5Board_4home.size := by rw [a.hszHOn]; decide
    have h := hhome?
    rw [Array.getElem?_eq_getElem hsz] at h
    exact elem_cast _ 2 hsz (by rw [a.hszHOn]; decide) (Option.some.inj h)
  have hheld2 : a.b1On.sudo_5Board_4held[2]'(by rw [a.hszDOn]; decide) = true := by
    have hsz : 2 < a.b1On.sudo_5Board_4held.size := by rw [a.hszDOn]; decide
    have h := hheld?
    rw [Array.getElem?_eq_getElem hsz] at h
    exact elem_cast _ 2 hsz (by rw [a.hszDOn]; decide) (Option.some.inj h)
  obtain ⟨bZ, hfrob, hmon, hbon, hto, hlane, htake⟩ :=
    frobenius_bottom_field a zP hyT hyL hheld2 hhome2 hzL hzT hn0 hnbL hnb hgap0
      hs1 hs2 (FitsLen.of_le hCtrl (by omega)) (FitsLen.of_le hOps (by omega))
      hCtrl hOps hspan h3 hnFit hbenchFit hpeg hfitMv hfitSlP hfmP hfoldP
      hsh.w0 hsh.h0 hsh.rlt hsh.r0 hsh.n_eq hsh.k_le hsh.gap hsm hnsm
  exact ⟨bZ, hfrob, hmon, hbon, hto,
    ⟨laneFold t.n (t.n - t.k) (combStrip t.n t.benchlen zP), hlane, htake⟩⟩

/-- Marker lifted, bench on and aimed at `home`, which is not across.
    `frobenius_point` slides that bench first, so it is `frobenius_point` of the
    settled board. `yBench` settles into home 1 and `zBench` into home 2. -/
theorem frobenius_lifted_bench
    (b : Ecbs.Board) (home : Nat) (xs ys : List Nat)
    (w h r n k moves slides hole bench peak peakS cOps cg ctrl mx script : Nat)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hon : b.sudo_5Board_8bench_on = true)
    (hm : b.sudo_5Board_6marker < 0)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hs : b.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script)
    (hpos : 0 < script) (hfit : FitsLen (ctrl + 1))
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop1 : b.sudo_5Board_4cost.sudo_5Costs_3ops[1]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1))
    (hne : (0 : Nat) ≠ home)
    (hF : 0 < b.sudo_5Board_4held.size)
    (hHome : 0 < b.sudo_5Board_4home.size)
    (hHF : b.sudo_5Board_4held[0] = true)
    (hArr : b.sudo_5Board_4home[0] = embed xs)
    (hDh : home < b.sudo_5Board_4held.size)
    (hHh : home < b.sudo_5Board_4home.size)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hto : b.sudo_5Board_8bench_to = (home : Int))
    (hempty : b.sudo_5Board_4held[home] = false)
    (hbench : b.sudo_5Board_5bench = embed ys)
    (hp : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak)
    (hn0 : 0 < n)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hlenx : xs.length = n)
    (hposY : 0 < ys.length) (hnle : n ≤ ys.length)
    (hzero : ∀ i, n ≤ i → ∀ hi : i < ys.length, ys[i] = 0)
    (hf : FitsLen n) (hfitL : FitsLen ys.length)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hpeg : FitsLen (2 * pegCount (ys.take n)))
    (hfitMv : FitsLen (moves + 2 * pegCount (ys.take n)))
    (hfitSl : FitsLen (slides + 2 * pegCount (ys.take n)))
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (hcg : b.sudo_5Board_1t.sudo_4Tier_7combgap = Int.ofNat cg)
    (hspan : 3 * (n - 1) + cg < bench)
    (h3 : FitsLen (3 * (n - 1)))
    (hfm : FitsLen (moves + 2 * pegCount (ys.take n) + 2 * n))
    (hhole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole)
    (hxsT : allTritList xs)
    (hw0 : 0 < w) (hh0 : 0 < h) (hrR : r < h) (hrP : 0 < r)
    (hnE : n = w * h - 1) (hkLe : k ≤ n) (hgap : n - k = w * r)
    (hw : b.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w)
    (hh : b.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h)
    (hr : b.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r)
    (hk : b.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k)
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ bench ≤ 1000001)
    (hnsm : n ≤ 1000000)
    (hfitB : FitsLen bench)
    (hfold : FitsLen (moves + 2 * pegCount (ys.take n) + 2 * n + 3 * (bench - n))) :
    Ecbs.frobenius_point b =
      Ecbs.frobenius_point (settleBoard b home hHh hDh ys n moves slides peak) := by
  rw [frobenius_point_cubes,
    frobenius_point_cubes (settleBoard b home hHh hDh ys n moves slides peak)]
  rw [show Ecbs.across = ((0 : Nat) : Int) from rfl]
  rw [cube_lifted_bench b 0 0 home xs ys w h r n k moves slides hole bench peak peakS cOps cg
      ctrl mx script hmk hon hm hc hx hs hpos hfit hops hop1 hfops hne hF hHome hHF hArr hDh hHh
      h7 hto hempty hbench hp hpeak hn0 hn hlenx hposY hnle hzero hf hfitL hmoves hslides hpeg
      hfitMv hfitSl hbl hcg hspan h3 hfm hhole hxsT hw0 hh0 hrR hrP hnE hkLe hgap hw hh hr hk hsm
      hnsm hfitB hfold]

/-- `yBench`, marker already lifted. The bench holds `Y` and is aimed at home 1.
    `frobenius_point` settles that bench, then cubes as on the homes layout, and
    leaves `fieldCube Z` aimed at home 2. -/
theorem frobenius_ybench_lifted
    (t : Spec.Tier) (b : Ecbs.Board) (xP yP zP ys : List Nat)
    (hsh : TierShape t) (hOk : BoardOk t) (sat : TierSat t)
    (hs2 : 2 < t.script)
    (htier : b.sudo_5Board_1t = embTier t)
    (hxL : xP.length = t.n) (hyL : yP.length = t.n) (hzL : zP.length = t.n)
    (hxT : allTritList xP) (hyT : allTritList yP) (hzT : allTritList zP)
    (hszH : b.sudo_5Board_4home.size = 8) (hszD : b.sudo_5Board_4held.size = 8)
    (h0 : b.sudo_5Board_4home[0]'(by rw [hszH]; decide) = embed xP)
    (h2 : b.sudo_5Board_4home[2]'(by rw [hszH]; decide) = embed zP)
    (hd0 : b.sudo_5Board_4held[0]'(by rw [hszD]; decide) = true)
    (hd1 : b.sudo_5Board_4held[1]'(by rw [hszD]; decide) = false)
    (hd2 : b.sudo_5Board_4held[2]'(by rw [hszD]; decide) = true)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (1 : Int))
    (hm : b.sudo_5Board_6marker < 0)
    (hbench : b.sudo_5Board_5bench = embed ys)
    (htake : ys.take t.n = yP)
    (hposY : 0 < ys.length) (hnle : t.n ≤ ys.length)
    (hzero : ∀ i, t.n ≤ i → ∀ hi : i < ys.length, ys[i] = 0)
    (moves slides ctrl mx pk peakS hole cOps : Nat)
    (hmv : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hsl : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hmx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hpk : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk)
    (hstrict : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat peakS)
    (hhole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop1 : b.sudo_5Board_4cost.sudo_5Costs_3ops[1]'hops = (cOps : Int))
    (hCtrl : FitsLen (ctrl + 5)) (hOps : FitsLen (cOps + 3))
    (hpeg : FitsLen (2 * pegCount (ys.take t.n)))
    (hfitMv : FitsLen (moves + 2 * pegCount (ys.take t.n)))
    (hfitSl : FitsLen (slides + 2 * pegCount (ys.take t.n)))
    (hRoom : FitsLen (moves + 2 * pegCount (ys.take t.n) + cubeCharge t.n t.benchlen +
        2 * t.n + 3 * (t.benchlen - t.n)))
    (hSl : FitsLen (slides + 2 * pegCount (ys.take t.n) + slideCharge t.n))
    (hfitN : FitsLen t.n) (hfitY : FitsLen ys.length) :
    ∃ bZ,
      Ecbs.frobenius_point b = .ok bZ ∧
      bZ.sudo_5Board_9marker_on = true ∧
      bZ.sudo_5Board_8bench_on = true ∧
      bZ.sudo_5Board_8bench_to = (2 : Int) ∧
      ∃ lane,
        bZ.sudo_5Board_5bench = embed lane ∧
        lane.take t.n = fieldCube t.n t.k t.benchlen zP := by
  have hn0 : 0 < t.n := hOk.n_pos
  have hspan : 3 * (t.n - 1) + t.combgap < t.benchlen := sat.cube_span
  have hsm := hsh.small
  have hnsm := hsh.n_small
  have hcapN := smallCap t.n t.benchlen
  have h3 : FitsLen (3 * (t.n - 1)) :=
    geomFit t.n t.benchlen (3 * (t.n - 1)) hnsm hsm.2.2.2 hcapN.2.2
  have hbenchFit : FitsLen t.benchlen :=
    geomFit t.n t.benchlen t.benchlen hnsm hsm.2.2.2 hcapN.2.1
  have hscript : b.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat t.script := by
    rw [htier]; rfl
  have hn : b.sudo_5Board_1t.sudo_4Tier_1n = (t.n : Int) := by
    rw [htier]; simp [embTier, ofNat_eq_natCast]
  have hk : b.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat t.k := by rw [htier]; rfl
  have hw : b.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat t.w := by rw [htier]; rfl
  have hh : b.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat t.h := by rw [htier]; rfl
  have hr : b.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat t.r := by rw [htier]; rfl
  have hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat t.benchlen := by
    rw [htier]; rfl
  have hcg : b.sudo_5Board_1t.sudo_4Tier_7combgap = Int.ofNat t.combgap := by
    rw [htier]; rfl
  have h1H : 1 < b.sudo_5Board_4home.size := by rw [hszH]; decide
  have h1D : 1 < b.sudo_5Board_4held.size := by rw [hszD]; decide
  have h0H : 0 < b.sudo_5Board_4home.size := by rw [hszH]; decide
  have h0D : 0 < b.sudo_5Board_4held.size := by rw [hszD]; decide
  have h7 : 7 ≤ b.sudo_5Board_4held.size := by rw [hszD]; decide
  let movesS := moves + 2 * pegCount (ys.take t.n)
  let slidesS := slides + 2 * pegCount (ys.take t.n)
  let peakT :=
    if pk < countHeld (b.sudo_5Board_4held.set ⟨1, h1D⟩ true) 7
    then countHeld (b.sudo_5Board_4held.set ⟨1, h1D⟩ true) 7
    else pk
  let bS := settleBoard b 1 h1H h1D ys t.n moves slides pk
  have hfm : FitsLen (moves + 2 * pegCount (ys.take t.n) + 2 * t.n) := by
    apply FitsLen.of_le hRoom
    unfold cubeCharge
    omega
  have hfold : FitsLen (moves + 2 * pegCount (ys.take t.n) + 2 * t.n +
      3 * (t.benchlen - t.n)) := by
    apply FitsLen.of_le hRoom
    unfold cubeCharge
    omega
  have hfrobEq := frobenius_lifted_bench b 1 xP ys t.w t.h t.r t.n t.k
    moves slides hole t.benchlen pk peakS cOps t.combgap ctrl mx t.script
    hmk hon hm hc hmx hscript (by have h := hsh.script_ge; omega) (FitsLen.of_le hCtrl (by omega))
    hops hop1 (FitsLen.of_le hOps (by omega)) (by decide) h0D h0H hd0 h0 h1D h1H h7 hto hd1
    hbench hstrict hpk hn0 hn hxL hposY hnle hzero hfitN hfitY hmv hsl hpeg hfitMv hfitSl
    hbl hcg hspan h3 hfm hhole hxT hsh.w0 hsh.h0 hsh.rlt hsh.r0 hsh.n_eq hsh.k_le hsh.gap
    hw hh hr hk hsm hnsm hbenchFit hfold
  have hszHS : bS.sudo_5Board_4home.size = 8 := by
    rw [settle_home_eq b 1 ⟨h1H, h1D⟩ ys t.n moves slides pk, Array.size_set, hszH]
  have hszDS : bS.sudo_5Board_4held.size = 8 := by
    rw [settle_held_eq b 1 ⟨h1H, h1D⟩ ys t.n moves slides pk, Array.size_set, hszD]
  have h0S? : bS.sudo_5Board_4home[0]? = some (embed xP) := by
    rw [settle_home_eq b 1 ⟨h1H, h1D⟩ ys t.n moves slides pk]
    rw [Array.getElem?_set_ne _ _ _ (by decide : (1 : Nat) ≠ 0)]
    rw [Array.getElem?_eq_getElem (by rw [hszH]; decide)]
    exact congrArg some h0
  have h2S? : bS.sudo_5Board_4home[2]? = some (embed zP) := by
    rw [settle_home_eq b 1 ⟨h1H, h1D⟩ ys t.n moves slides pk]
    rw [Array.getElem?_set_ne _ _ _ (by decide : (1 : Nat) ≠ 2)]
    rw [Array.getElem?_eq_getElem (by rw [hszH]; decide)]
    exact congrArg some h2
  have h1S? : bS.sudo_5Board_4home[1]? = some (embed yP) := by
    rw [settle_home_eq b 1 ⟨h1H, h1D⟩ ys t.n moves slides pk]
    rw [Array.getElem?_set_eq]
    rw [htake]
  have hd0S? : bS.sudo_5Board_4held[0]? = some true := by
    rw [settle_held_eq b 1 ⟨h1H, h1D⟩ ys t.n moves slides pk]
    rw [Array.getElem?_set_ne _ _ _ (by decide : (1 : Nat) ≠ 0)]
    rw [Array.getElem?_eq_getElem (by rw [hszD]; decide)]
    exact congrArg some hd0
  have hd2S? : bS.sudo_5Board_4held[2]? = some true := by
    rw [settle_held_eq b 1 ⟨h1H, h1D⟩ ys t.n moves slides pk]
    rw [Array.getElem?_set_ne _ _ _ (by decide : (1 : Nat) ≠ 2)]
    rw [Array.getElem?_eq_getElem (by rw [hszD]; decide)]
    exact congrArg some hd2
  have hd1S? : bS.sudo_5Board_4held[1]? = some true := by
    rw [settle_held_eq b 1 ⟨h1H, h1D⟩ ys t.n moves slides pk]
    rw [Array.getElem?_set_eq]
  have h0S : bS.sudo_5Board_4home[0]'(by rw [hszHS]; decide) = embed xP := by
    have hsz : 0 < bS.sudo_5Board_4home.size := by rw [hszHS]; decide
    rw [Array.getElem?_eq_getElem hsz] at h0S?
    exact Option.some.inj h0S?
  have h1S : bS.sudo_5Board_4home[1]'(by rw [hszHS]; decide) = embed yP := by
    have hsz : 1 < bS.sudo_5Board_4home.size := by rw [hszHS]; decide
    rw [Array.getElem?_eq_getElem hsz] at h1S?
    exact Option.some.inj h1S?
  have h2S : bS.sudo_5Board_4home[2]'(by rw [hszHS]; decide) = embed zP := by
    have hsz : 2 < bS.sudo_5Board_4home.size := by rw [hszHS]; decide
    rw [Array.getElem?_eq_getElem hsz] at h2S?
    exact Option.some.inj h2S?
  have hd0S : bS.sudo_5Board_4held[0]'(by rw [hszDS]; decide) = true := by
    have hsz : 0 < bS.sudo_5Board_4held.size := by rw [hszDS]; decide
    rw [Array.getElem?_eq_getElem hsz] at hd0S?
    exact Option.some.inj hd0S?
  have hd1S : bS.sudo_5Board_4held[1]'(by rw [hszDS]; decide) = true := by
    have hsz : 1 < bS.sudo_5Board_4held.size := by rw [hszDS]; decide
    rw [Array.getElem?_eq_getElem hsz] at hd1S?
    exact Option.some.inj hd1S?
  have hd2S : bS.sudo_5Board_4held[2]'(by rw [hszDS]; decide) = true := by
    have hsz : 2 < bS.sudo_5Board_4held.size := by rw [hszDS]; decide
    rw [Array.getElem?_eq_getElem hsz] at hd2S?
    exact Option.some.inj hd2S?
  have hmvS : bS.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat movesS :=
    settle_moves_eq b 1 ⟨h1H, h1D⟩ ys t.n moves slides pk
  have hslS : bS.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slidesS :=
    settle_slides_eq b 1 ⟨h1H, h1D⟩ ys t.n moves slides pk
  have hpkS : bS.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peakT :=
    settle_peak_eq b 1 ⟨h1H, h1D⟩ ys t.n moves slides pk hpk
  have hcS : bS.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl := by
    rw [settle_ctrl_eq b 1 ⟨h1H, h1D⟩ ys t.n moves slides pk]; exact hc
  have hmxS : bS.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx := by
    rw [settle_mx_eq b 1 ⟨h1H, h1D⟩ ys t.n moves slides pk]; exact hmx
  have hstrictS : bS.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat peakS := by
    rw [settle_strict_eq b 1 ⟨h1H, h1D⟩ ys t.n moves slides pk]; exact hstrict
  have hholeS : bS.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole := by
    rw [settle_hole_eq b 1 ⟨h1H, h1D⟩ ys t.n moves slides pk]; exact hhole
  have hopsS : 1 < bS.sudo_5Board_4cost.sudo_5Costs_3ops.size :=
    settle_ops_lt b 1 1 hops ⟨h1H, h1D⟩ ys t.n moves slides pk
  have hopS : bS.sudo_5Board_4cost.sudo_5Costs_3ops[1]'hopsS = (cOps : Int) := by
    have h? : bS.sudo_5Board_4cost.sudo_5Costs_3ops[1]? = some (cOps : Int) := by
      rw [settle_ops b 1 ⟨h1H, h1D⟩ ys t.n moves slides pk]
      rw [Array.getElem?_eq_getElem hops]
      exact congrArg some hop1
    rw [Array.getElem?_eq_getElem hopsS] at h?
    exact Option.some.inj h?
  have htierS : bS.sudo_5Board_1t = embTier t := by
    rw [settle_tier_eq b 1 ⟨h1H, h1D⟩ ys t.n moves slides pk]; exact htier
  have hmkS : bS.sudo_5Board_9marker_on = true := by
    rw [settle_marker_eq b 1 ⟨h1H, h1D⟩ ys t.n moves slides pk]; exact hmk
  have hmS : bS.sudo_5Board_6marker < 0 := by
    rw [settle_ix_eq b 1 ⟨h1H, h1D⟩ ys t.n moves slides pk]; exact hm
  have hoffS : bS.sudo_5Board_8bench_on = false :=
    settle_bench_off b 1 ⟨h1H, h1D⟩ ys t.n moves slides pk
  have hRoomS : FitsLen (movesS + cubeCharge t.n t.benchlen + 2 * t.n +
      3 * (t.benchlen - t.n)) := by
    simpa [movesS, Nat.add_assoc] using hRoom
  have hSlS : FitsLen (slidesS + slideCharge t.n) := by
    simpa [slidesS, Nat.add_assoc] using hSl
  obtain ⟨bZ, hfrob, hmon, hbon, htoZ, hlane⟩ :=
    frobenius_on_lifted t bS xP yP zP hsh hOk sat hs2 htierS hxL hyL hzL hxT hyT hzT
      hszHS hszDS h0S h1S h2S hd0S hd1S hd2S hmkS hoffS hmS movesS slidesS ctrl mx peakT
      peakS hole cOps hmvS hslS hcS hmxS hpkS hstrictS hholeS hopsS hopS hCtrl hOps hRoomS hSlS
  rw [hfrobEq]
  exact ⟨bZ, hfrob, hmon, hbon, htoZ, hlane⟩

/-- `zBench`, marker already lifted. The bench holds `Z` and is aimed at home 2.
    `frobenius_point` settles that bench, then cubes as on the homes layout, and
    leaves `fieldCube Z` aimed at home 2. -/
theorem frobenius_zbench_lifted
    (t : Spec.Tier) (b : Ecbs.Board) (xP yP zP ys : List Nat)
    (hsh : TierShape t) (hOk : BoardOk t) (sat : TierSat t)
    (hs2 : 2 < t.script)
    (htier : b.sudo_5Board_1t = embTier t)
    (hxL : xP.length = t.n) (hyL : yP.length = t.n) (hzL : zP.length = t.n)
    (hxT : allTritList xP) (hyT : allTritList yP) (hzT : allTritList zP)
    (hszH : b.sudo_5Board_4home.size = 8) (hszD : b.sudo_5Board_4held.size = 8)
    (h0 : b.sudo_5Board_4home[0]'(by rw [hszH]; decide) = embed xP)
    (h1 : b.sudo_5Board_4home[1]'(by rw [hszH]; decide) = embed yP)
    (hd0 : b.sudo_5Board_4held[0]'(by rw [hszD]; decide) = true)
    (hd1 : b.sudo_5Board_4held[1]'(by rw [hszD]; decide) = true)
    (hd2 : b.sudo_5Board_4held[2]'(by rw [hszD]; decide) = false)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (2 : Int))
    (hm : b.sudo_5Board_6marker < 0)
    (hbench : b.sudo_5Board_5bench = embed ys)
    (htake : ys.take t.n = zP)
    (hposY : 0 < ys.length) (hnle : t.n ≤ ys.length)
    (hzero : ∀ i, t.n ≤ i → ∀ hi : i < ys.length, ys[i] = 0)
    (moves slides ctrl mx pk peakS hole cOps : Nat)
    (hmv : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hsl : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hmx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hpk : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk)
    (hstrict : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat peakS)
    (hhole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop1 : b.sudo_5Board_4cost.sudo_5Costs_3ops[1]'hops = (cOps : Int))
    (hCtrl : FitsLen (ctrl + 5)) (hOps : FitsLen (cOps + 3))
    (hpeg : FitsLen (2 * pegCount (ys.take t.n)))
    (hfitMv : FitsLen (moves + 2 * pegCount (ys.take t.n)))
    (hfitSl : FitsLen (slides + 2 * pegCount (ys.take t.n)))
    (hRoom : FitsLen (moves + 2 * pegCount (ys.take t.n) + cubeCharge t.n t.benchlen +
        2 * t.n + 3 * (t.benchlen - t.n)))
    (hSl : FitsLen (slides + 2 * pegCount (ys.take t.n) + slideCharge t.n))
    (hfitN : FitsLen t.n) (hfitY : FitsLen ys.length) :
    ∃ bZ,
      Ecbs.frobenius_point b = .ok bZ ∧
      bZ.sudo_5Board_9marker_on = true ∧
      bZ.sudo_5Board_8bench_on = true ∧
      bZ.sudo_5Board_8bench_to = (2 : Int) ∧
      ∃ lane,
        bZ.sudo_5Board_5bench = embed lane ∧
        lane.take t.n = fieldCube t.n t.k t.benchlen zP := by
  have hn0 : 0 < t.n := hOk.n_pos
  have hspan : 3 * (t.n - 1) + t.combgap < t.benchlen := sat.cube_span
  have hsm := hsh.small
  have hnsm := hsh.n_small
  have hcapN := smallCap t.n t.benchlen
  have h3 : FitsLen (3 * (t.n - 1)) :=
    geomFit t.n t.benchlen (3 * (t.n - 1)) hnsm hsm.2.2.2 hcapN.2.2
  have hbenchFit : FitsLen t.benchlen :=
    geomFit t.n t.benchlen t.benchlen hnsm hsm.2.2.2 hcapN.2.1
  have hscript : b.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat t.script := by
    rw [htier]; rfl
  have hn : b.sudo_5Board_1t.sudo_4Tier_1n = (t.n : Int) := by
    rw [htier]; simp [embTier, ofNat_eq_natCast]
  have hk : b.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat t.k := by rw [htier]; rfl
  have hw : b.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat t.w := by rw [htier]; rfl
  have hh : b.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat t.h := by rw [htier]; rfl
  have hr : b.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat t.r := by rw [htier]; rfl
  have hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat t.benchlen := by
    rw [htier]; rfl
  have hcg : b.sudo_5Board_1t.sudo_4Tier_7combgap = Int.ofNat t.combgap := by
    rw [htier]; rfl
  have h2H : 2 < b.sudo_5Board_4home.size := by rw [hszH]; decide
  have h2D : 2 < b.sudo_5Board_4held.size := by rw [hszD]; decide
  have h0H : 0 < b.sudo_5Board_4home.size := by rw [hszH]; decide
  have h0D : 0 < b.sudo_5Board_4held.size := by rw [hszD]; decide
  have h7 : 7 ≤ b.sudo_5Board_4held.size := by rw [hszD]; decide
  let movesS := moves + 2 * pegCount (ys.take t.n)
  let slidesS := slides + 2 * pegCount (ys.take t.n)
  let peakT :=
    if pk < countHeld (b.sudo_5Board_4held.set ⟨2, h2D⟩ true) 7
    then countHeld (b.sudo_5Board_4held.set ⟨2, h2D⟩ true) 7
    else pk
  let bS := settleBoard b 2 h2H h2D ys t.n moves slides pk
  have hfm : FitsLen (moves + 2 * pegCount (ys.take t.n) + 2 * t.n) := by
    apply FitsLen.of_le hRoom
    unfold cubeCharge
    omega
  have hfold : FitsLen (moves + 2 * pegCount (ys.take t.n) + 2 * t.n +
      3 * (t.benchlen - t.n)) := by
    apply FitsLen.of_le hRoom
    unfold cubeCharge
    omega
  have hfrobEq := frobenius_lifted_bench b 2 xP ys t.w t.h t.r t.n t.k
    moves slides hole t.benchlen pk peakS cOps t.combgap ctrl mx t.script
    hmk hon hm hc hmx hscript (by have h := hsh.script_ge; omega) (FitsLen.of_le hCtrl (by omega))
    hops hop1 (FitsLen.of_le hOps (by omega)) (by decide) h0D h0H hd0 h0 h2D h2H h7 hto hd2
    hbench hstrict hpk hn0 hn hxL hposY hnle hzero hfitN hfitY hmv hsl hpeg hfitMv hfitSl
    hbl hcg hspan h3 hfm hhole hxT hsh.w0 hsh.h0 hsh.rlt hsh.r0 hsh.n_eq hsh.k_le hsh.gap
    hw hh hr hk hsm hnsm hbenchFit hfold
  have hszHS : bS.sudo_5Board_4home.size = 8 := by
    rw [settle_home_eq b 2 ⟨h2H, h2D⟩ ys t.n moves slides pk, Array.size_set, hszH]
  have hszDS : bS.sudo_5Board_4held.size = 8 := by
    rw [settle_held_eq b 2 ⟨h2H, h2D⟩ ys t.n moves slides pk, Array.size_set, hszD]
  have h0S? : bS.sudo_5Board_4home[0]? = some (embed xP) := by
    rw [settle_home_eq b 2 ⟨h2H, h2D⟩ ys t.n moves slides pk]
    rw [Array.getElem?_set_ne _ _ _ (by decide : (2 : Nat) ≠ 0)]
    rw [Array.getElem?_eq_getElem (by rw [hszH]; decide)]
    exact congrArg some h0
  have h1S? : bS.sudo_5Board_4home[1]? = some (embed yP) := by
    rw [settle_home_eq b 2 ⟨h2H, h2D⟩ ys t.n moves slides pk]
    rw [Array.getElem?_set_ne _ _ _ (by decide : (2 : Nat) ≠ 1)]
    rw [Array.getElem?_eq_getElem (by rw [hszH]; decide)]
    exact congrArg some h1
  have h2S? : bS.sudo_5Board_4home[2]? = some (embed zP) := by
    rw [settle_home_eq b 2 ⟨h2H, h2D⟩ ys t.n moves slides pk]
    rw [Array.getElem?_set_eq]
    rw [htake]
  have hd0S? : bS.sudo_5Board_4held[0]? = some true := by
    rw [settle_held_eq b 2 ⟨h2H, h2D⟩ ys t.n moves slides pk]
    rw [Array.getElem?_set_ne _ _ _ (by decide : (2 : Nat) ≠ 0)]
    rw [Array.getElem?_eq_getElem (by rw [hszD]; decide)]
    exact congrArg some hd0
  have hd1S? : bS.sudo_5Board_4held[1]? = some true := by
    rw [settle_held_eq b 2 ⟨h2H, h2D⟩ ys t.n moves slides pk]
    rw [Array.getElem?_set_ne _ _ _ (by decide : (2 : Nat) ≠ 1)]
    rw [Array.getElem?_eq_getElem (by rw [hszD]; decide)]
    exact congrArg some hd1
  have hd2S? : bS.sudo_5Board_4held[2]? = some true := by
    rw [settle_held_eq b 2 ⟨h2H, h2D⟩ ys t.n moves slides pk]
    rw [Array.getElem?_set_eq]
  have h0S : bS.sudo_5Board_4home[0]'(by rw [hszHS]; decide) = embed xP := by
    have hsz : 0 < bS.sudo_5Board_4home.size := by rw [hszHS]; decide
    rw [Array.getElem?_eq_getElem hsz] at h0S?
    exact Option.some.inj h0S?
  have h1S : bS.sudo_5Board_4home[1]'(by rw [hszHS]; decide) = embed yP := by
    have hsz : 1 < bS.sudo_5Board_4home.size := by rw [hszHS]; decide
    rw [Array.getElem?_eq_getElem hsz] at h1S?
    exact Option.some.inj h1S?
  have h2S : bS.sudo_5Board_4home[2]'(by rw [hszHS]; decide) = embed zP := by
    have hsz : 2 < bS.sudo_5Board_4home.size := by rw [hszHS]; decide
    rw [Array.getElem?_eq_getElem hsz] at h2S?
    exact Option.some.inj h2S?
  have hd0S : bS.sudo_5Board_4held[0]'(by rw [hszDS]; decide) = true := by
    have hsz : 0 < bS.sudo_5Board_4held.size := by rw [hszDS]; decide
    rw [Array.getElem?_eq_getElem hsz] at hd0S?
    exact Option.some.inj hd0S?
  have hd1S : bS.sudo_5Board_4held[1]'(by rw [hszDS]; decide) = true := by
    have hsz : 1 < bS.sudo_5Board_4held.size := by rw [hszDS]; decide
    rw [Array.getElem?_eq_getElem hsz] at hd1S?
    exact Option.some.inj hd1S?
  have hd2S : bS.sudo_5Board_4held[2]'(by rw [hszDS]; decide) = true := by
    have hsz : 2 < bS.sudo_5Board_4held.size := by rw [hszDS]; decide
    rw [Array.getElem?_eq_getElem hsz] at hd2S?
    exact Option.some.inj hd2S?
  have hmvS : bS.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat movesS :=
    settle_moves_eq b 2 ⟨h2H, h2D⟩ ys t.n moves slides pk
  have hslS : bS.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slidesS :=
    settle_slides_eq b 2 ⟨h2H, h2D⟩ ys t.n moves slides pk
  have hpkS : bS.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peakT :=
    settle_peak_eq b 2 ⟨h2H, h2D⟩ ys t.n moves slides pk hpk
  have hcS : bS.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl := by
    rw [settle_ctrl_eq b 2 ⟨h2H, h2D⟩ ys t.n moves slides pk]; exact hc
  have hmxS : bS.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx := by
    rw [settle_mx_eq b 2 ⟨h2H, h2D⟩ ys t.n moves slides pk]; exact hmx
  have hstrictS : bS.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat peakS := by
    rw [settle_strict_eq b 2 ⟨h2H, h2D⟩ ys t.n moves slides pk]; exact hstrict
  have hholeS : bS.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole := by
    rw [settle_hole_eq b 2 ⟨h2H, h2D⟩ ys t.n moves slides pk]; exact hhole
  have hopsS : 1 < bS.sudo_5Board_4cost.sudo_5Costs_3ops.size :=
    settle_ops_lt b 1 2 hops ⟨h2H, h2D⟩ ys t.n moves slides pk
  have hopS : bS.sudo_5Board_4cost.sudo_5Costs_3ops[1]'hopsS = (cOps : Int) := by
    have h? : bS.sudo_5Board_4cost.sudo_5Costs_3ops[1]? = some (cOps : Int) := by
      rw [settle_ops b 2 ⟨h2H, h2D⟩ ys t.n moves slides pk]
      rw [Array.getElem?_eq_getElem hops]
      exact congrArg some hop1
    rw [Array.getElem?_eq_getElem hopsS] at h?
    exact Option.some.inj h?
  have htierS : bS.sudo_5Board_1t = embTier t := by
    rw [settle_tier_eq b 2 ⟨h2H, h2D⟩ ys t.n moves slides pk]; exact htier
  have hmkS : bS.sudo_5Board_9marker_on = true := by
    rw [settle_marker_eq b 2 ⟨h2H, h2D⟩ ys t.n moves slides pk]; exact hmk
  have hmS : bS.sudo_5Board_6marker < 0 := by
    rw [settle_ix_eq b 2 ⟨h2H, h2D⟩ ys t.n moves slides pk]; exact hm
  have hoffS : bS.sudo_5Board_8bench_on = false :=
    settle_bench_off b 2 ⟨h2H, h2D⟩ ys t.n moves slides pk
  have hRoomS : FitsLen (movesS + cubeCharge t.n t.benchlen + 2 * t.n +
      3 * (t.benchlen - t.n)) := by
    simpa [movesS, Nat.add_assoc] using hRoom
  have hSlS : FitsLen (slidesS + slideCharge t.n) := by
    simpa [slidesS, Nat.add_assoc] using hSl
  obtain ⟨bZ, hfrob, hmon, hbon, htoZ, hlane⟩ :=
    frobenius_on_lifted t bS xP yP zP hsh hOk sat hs2 htierS hxL hyL hzL hxT hyT hzT
      hszHS hszDS h0S h1S h2S hd0S hd1S hd2S hmkS hoffS hmS movesS slidesS ctrl mx peakT
      peakS hole cOps hmvS hslS hcS hmxS hpkS hstrictS hholeS hopsS hopS hCtrl hOps hRoomS hSlS
  rw [hfrobEq]
  exact ⟨bZ, hfrob, hmon, hbon, htoZ, hlane⟩

/-- `ProjLay.yBench` after the cell's `marker_lift`. The bench holds `Y`.
    `frobenius_point` settles it and leaves `fieldCube Z` aimed at home 2. -/
theorem frobenius_fform_ybench
    (t : Spec.Tier) (b : Ecbs.Board) (xP yP zP ys : List Nat)
    (hsh : TierShape t) (hOk : BoardOk t) (sat : TierSat t)
    (hs2 : 2 < t.script)
    (htier : b.sudo_5Board_1t = embTier t)
    (hxL : xP.length = t.n) (hyL : yP.length = t.n) (hzL : zP.length = t.n)
    (hxT : allTritList xP) (hyT : allTritList yP) (hzT : allTritList zP)
    (hszH : b.sudo_5Board_4home.size = 8) (hszD : b.sudo_5Board_4held.size = 8)
    (h0 : b.sudo_5Board_4home[0]'(by rw [hszH]; decide) = embed xP)
    (h2 : b.sudo_5Board_4home[2]'(by rw [hszH]; decide) = embed zP)
    (hd0 : b.sudo_5Board_4held[0]'(by rw [hszD]; decide) = true)
    (hd1 : b.sudo_5Board_4held[1]'(by rw [hszD]; decide) = false)
    (hd2 : b.sudo_5Board_4held[2]'(by rw [hszD]; decide) = true)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (1 : Int))
    (hbench : b.sudo_5Board_5bench = embed ys)
    (htake : ys.take t.n = yP)
    (hposY : 0 < ys.length) (hnle : t.n ≤ ys.length)
    (hzero : ∀ i, t.n ≤ i → ∀ hi : i < ys.length, ys[i] = 0)
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
    (hpeg : FitsLen (2 * pegCount (ys.take t.n)))
    (hfitMv : FitsLen (moves + 2 * pegCount (ys.take t.n)))
    (hfitSl : FitsLen (slides + 2 * pegCount (ys.take t.n)))
    (hRoom : FitsLen (moves + 2 * pegCount (ys.take t.n) + cubeCharge t.n t.benchlen +
        2 * t.n + 3 * (t.benchlen - t.n)))
    (hSl : FitsLen (slides + 2 * pegCount (ys.take t.n) + slideCharge t.n))
    (hfitN : FitsLen t.n) (hfitY : FitsLen ys.length) :
    ∃ bL bZ,
      Ecbs.marker_lift b = .ok bL ∧
      Ecbs.frobenius_point bL = .ok bZ ∧
      bZ.sudo_5Board_9marker_on = true ∧
      bZ.sudo_5Board_8bench_on = true ∧
      bZ.sudo_5Board_8bench_to = (2 : Int) ∧
      ∃ lane,
        bZ.sudo_5Board_5bench = embed lane ∧
        lane.take t.n = fieldCube t.n t.k t.benchlen zP := by
  let bL := { b with
    sudo_5Board_6marker := -1
    sudo_5Board_4cost := { b.sudo_5Board_4cost with
      sudo_5Costs_4ctrl := Int.ofNat (c0 + 1) } }
  have hlift := marker_lift_refines b mark c0 hmkN hc0 (FitsLen.of_le hCtrl (by omega))
  have hmL : bL.sudo_5Board_6marker < 0 := by
    have hmEq : bL.sudo_5Board_6marker = -1 := rfl
    rw [hmEq]
    decide
  have hcL : bL.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (c0 + 1) := rfl
  have htierL : bL.sudo_5Board_1t = embTier t := htier
  obtain ⟨bZ, hfrob, hmon, hbon, htoZ, hlane⟩ :=
    frobenius_ybench_lifted t bL xP yP zP ys hsh hOk sat hs2 htierL hxL hyL hzL hxT hyT hzT
      hszH hszD h0 h2 hd0 hd1 hd2 hmk hon hto hmL hbench htake hposY hnle hzero
      moves slides (c0 + 1) mx pk peakS hole cOps hmv hsl hcL hmx hpk hstrict hhole hops hop1
      (by simpa [Nat.add_assoc] using hCtrl) hOps hpeg hfitMv hfitSl hRoom hSl hfitN hfitY
  exact ⟨bL, bZ, hlift, hfrob, hmon, hbon, htoZ, hlane⟩

/-- `ProjLay.zBench` after the cell's `marker_lift`. The bench holds `Z`.
    `frobenius_point` settles it and leaves `fieldCube Z` aimed at home 2. -/
theorem frobenius_fform_zbench
    (t : Spec.Tier) (b : Ecbs.Board) (xP yP zP ys : List Nat)
    (hsh : TierShape t) (hOk : BoardOk t) (sat : TierSat t)
    (hs2 : 2 < t.script)
    (htier : b.sudo_5Board_1t = embTier t)
    (hxL : xP.length = t.n) (hyL : yP.length = t.n) (hzL : zP.length = t.n)
    (hxT : allTritList xP) (hyT : allTritList yP) (hzT : allTritList zP)
    (hszH : b.sudo_5Board_4home.size = 8) (hszD : b.sudo_5Board_4held.size = 8)
    (h0 : b.sudo_5Board_4home[0]'(by rw [hszH]; decide) = embed xP)
    (h1 : b.sudo_5Board_4home[1]'(by rw [hszH]; decide) = embed yP)
    (hd0 : b.sudo_5Board_4held[0]'(by rw [hszD]; decide) = true)
    (hd1 : b.sudo_5Board_4held[1]'(by rw [hszD]; decide) = true)
    (hd2 : b.sudo_5Board_4held[2]'(by rw [hszD]; decide) = false)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (2 : Int))
    (hbench : b.sudo_5Board_5bench = embed ys)
    (htake : ys.take t.n = zP)
    (hposY : 0 < ys.length) (hnle : t.n ≤ ys.length)
    (hzero : ∀ i, t.n ≤ i → ∀ hi : i < ys.length, ys[i] = 0)
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
    (hpeg : FitsLen (2 * pegCount (ys.take t.n)))
    (hfitMv : FitsLen (moves + 2 * pegCount (ys.take t.n)))
    (hfitSl : FitsLen (slides + 2 * pegCount (ys.take t.n)))
    (hRoom : FitsLen (moves + 2 * pegCount (ys.take t.n) + cubeCharge t.n t.benchlen +
        2 * t.n + 3 * (t.benchlen - t.n)))
    (hSl : FitsLen (slides + 2 * pegCount (ys.take t.n) + slideCharge t.n))
    (hfitN : FitsLen t.n) (hfitY : FitsLen ys.length) :
    ∃ bL bZ,
      Ecbs.marker_lift b = .ok bL ∧
      Ecbs.frobenius_point bL = .ok bZ ∧
      bZ.sudo_5Board_9marker_on = true ∧
      bZ.sudo_5Board_8bench_on = true ∧
      bZ.sudo_5Board_8bench_to = (2 : Int) ∧
      ∃ lane,
        bZ.sudo_5Board_5bench = embed lane ∧
        lane.take t.n = fieldCube t.n t.k t.benchlen zP := by
  let bL := { b with
    sudo_5Board_6marker := -1
    sudo_5Board_4cost := { b.sudo_5Board_4cost with
      sudo_5Costs_4ctrl := Int.ofNat (c0 + 1) } }
  have hlift := marker_lift_refines b mark c0 hmkN hc0 (FitsLen.of_le hCtrl (by omega))
  have hmL : bL.sudo_5Board_6marker < 0 := by
    have hmEq : bL.sudo_5Board_6marker = -1 := rfl
    rw [hmEq]
    decide
  have hcL : bL.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (c0 + 1) := rfl
  have htierL : bL.sudo_5Board_1t = embTier t := htier
  obtain ⟨bZ, hfrob, hmon, hbon, htoZ, hlane⟩ :=
    frobenius_zbench_lifted t bL xP yP zP ys hsh hOk sat hs2 htierL hxL hyL hzL hxT hyT hzT
      hszH hszD h0 h1 hd0 hd1 hd2 hmk hon hto hmL hbench htake hposY hnle hzero
      moves slides (c0 + 1) mx pk peakS hole cOps hmv hsl hcL hmx hpk hstrict hhole hops hop1
      (by simpa [Nat.add_assoc] using hCtrl) hOps hpeg hfitMv hfitSl hRoom hSl hfitN hfitY
  exact ⟨bL, bZ, hlift, hfrob, hmon, hbon, htoZ, hlane⟩

end EcbsLink2.Link2
