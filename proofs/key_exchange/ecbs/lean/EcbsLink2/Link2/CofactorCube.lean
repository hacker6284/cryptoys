/-
  The cofactor cell after the white copy. The accumulator is the root, the
  marker is still `-1`, and the flag is on. `down_across` cubes that board,
  and `frobenius_affine` writes the two field cubes.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FrobeniusRead
import EcbsLink2.Link2.CofactorKeep
import EcbsLink2.Link2.EntryInv
import EcbsLink2.Link2.WalkCopy
import EcbsLink2.Link2.WalkLoop
import EcbsLink2.Link2.OpenBoard
import EcbsLink2.Link2.Basic

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open Ecbs
open EcbsLink2.Spec

private theorem shape_n_pos (n w h r : Nat)
    (heq : n = w * h - 1) (hw : 0 < w) (hr : 0 < r) (hlt : r < h) : 0 < n := by
  have hh : 2 ≤ h := by omega
  have hw1 : 1 ≤ w := by omega
  have hprod : 2 ≤ w * h := Nat.mul_le_mul hw1 hh
  omega

private theorem script_one (script : Nat) (h : 2 ≤ script) : 1 < script := by
  omega

private theorem mv2_le (mv1 pegX moves n bench spent yPeg : Nat)
    (hmv : mv1 ≤ moves + 2 * n + 3 * (bench - n))
    (hpx : pegX ≤ n) (hy : yPeg ≤ n)
    (hspent : spent ≤ mv1 + 2 * pegX + 2 * n + 3 * (bench - n)) :
    spent + 2 * yPeg ≤ moves + 8 * n + 6 * (bench - n) := by
  omega

private theorem slide_add (slides pegX yPeg n : Nat) (hpx : pegX ≤ n) (hy : yPeg ≤ n) :
    slides + 2 * pegX + 2 * yPeg ≤ slides + 4 * n := by
  omega

/-- A copied root, marker still down, flag on. Frobenius cubes both homes. -/
theorem cofactor_frobenius (b : Board) (t : Spec.Tier) (x y : List Nat)
    (moves slides pk peakS holeN cOps ctrl mx : Nat)
    (hsh : TierShape t) (sat : TierSat t)
    (hszH : b.sudo_5Board_4home.size = 8) (hszD : b.sudo_5Board_4held.size = 8)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hx : x.length = t.n) (hy : y.length = t.n)
    (hxt : allTritList x) (hyt : allTritList y)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hoff : b.sudo_5Board_8bench_on = false)
    (hmark : b.sudo_5Board_6marker = -1)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hmx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hT : b.sudo_5Board_1t = embTier t)
    (hop1 : b.sudo_5Board_4cost.sudo_5Costs_3ops[1]'hops = (cOps : Int))
    (hfitC : FitsLen (cOps + 2))
    (hfitD : FitsLen (ctrl + 1))
    (hfitU : FitsLen ((ctrl + 1) + 2))
    (hheld0 : b.sudo_5Board_4held[0]'(by rw [hszD]; decide) = true)
    (hhome0 : b.sudo_5Board_4home[0]'(by rw [hszH]; decide) = embed x)
    (hheld1 : b.sudo_5Board_4held[1]'(by rw [hszD]; decide) = true)
    (hhome1 : b.sudo_5Board_4home[1]'(by rw [hszH]; decide) = embed y)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk)
    (hstrict : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat peakS)
    (hhole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat holeN)
    (hMv : FitsLen (moves + 8 * t.n + 6 * (t.benchlen - t.n)))
    (hSl : FitsLen (slides + 4 * t.n)) :
    ∃ bF,
      frobenius_affine b = .ok bF ∧
      bF.sudo_5Board_9marker_on = true ∧
      bF.sudo_5Board_8bench_on = false ∧
      (∀ h0 : 0 < bF.sudo_5Board_4home.size,
        bF.sudo_5Board_4home[0] = embed (fieldCube t.n t.k t.benchlen x)) ∧
      (∀ h1 : 1 < bF.sudo_5Board_4home.size,
        bF.sudo_5Board_4home[1] = embed (fieldCube t.n t.k t.benchlen y)) := by
  have hm : b.sudo_5Board_6marker < 0 := by rw [hmark]; decide
  have hn0 : 0 < t.n := shape_n_pos t.n t.w t.h t.r hsh.n_eq hsh.w0 hsh.r0 hsh.rlt
  have hs1 : 1 < t.script := by
    have h := hsh.script_ge
    omega
  have hspan : 3 * (t.n - 1) + t.combgap < t.benchlen := sat.cube_span
  have h3 : FitsLen (3 * (t.n - 1)) := FitsLen.of_le hMv (by omega)
  have hnFit : FitsLen t.n := FitsLen.of_le hMv (by omega)
  have hbenchFit : FitsLen t.benchlen := FitsLen.of_le hMv (by omega)
  have hnb : t.n ≤ t.benchlen := by
    have h := sat.cube_span
    omega
  let a := down_across b x y t.w t.h t.r t.n t.k moves slides pk peakS holeN cOps ctrl mx
      t.script hszH hszD hops hx hy hxt hyt hmk hoff hm hc hmx
      (by simp [hT, embTier]) hs1 hfitD hfitU hop1 hfitC hheld0 hhome0 hheld1 hhome1
      (by simp [hT, embTier]) (by simp [hT, embTier]) (by simp [hT, embTier])
      (by simp [hT, embTier]) (by simp [hT, embTier]) (by simp [hT, embTier])
      (by simp [hT, embTier]) hmoves hslides hpeak hstrict hhole
      hsh.w0 hsh.h0 hsh.rlt hsh.r0 hn0 hsh.n_eq hsh.k_le hsh.gap hspan
      hsh.small hsh.n_small hMv hSl
  have hpegY : pegCount ((upLane t.n t.k t.benchlen y).take t.n) ≤ t.n := by
    have htake : (upLane t.n t.k t.benchlen y).take t.n =
        fieldCube t.n t.k t.benchlen y := upLane_take t.n t.k t.benchlen y
    have hlen := fieldCube_length t.n t.k t.benchlen y hnb
    rw [htake]
    have hle := pegCount_le (fieldCube t.n t.k t.benchlen y)
    rwa [hlen] at hle
  have hpeg : FitsLen (2 * pegCount ((upLane t.n t.k t.benchlen y).take t.n)) :=
    FitsLen.of_le hMv (by omega)
  have hfitM : FitsLen (upMv2 a + 2 * pegCount ((upLane t.n t.k t.benchlen y).take t.n)) := by
    have hspent := cubeMoves_le (a.mv1 + 2 * a.pegX) y t.n t.k t.benchlen
    have hle := mv2_le a.mv1 a.pegX moves t.n t.benchlen (upMv2 a)
        (pegCount ((upLane t.n t.k t.benchlen y).take t.n)) a.hmv1le a.hpegX hpegY
        (by simpa [upMv2, upMv] using hspent)
    exact FitsLen.of_le hMv hle
  have hfitS : FitsLen (upSl a + 2 * pegCount ((upLane t.n t.k t.benchlen y).take t.n)) := by
    have hle := slide_add slides a.pegX
        (pegCount ((upLane t.n t.k t.benchlen y).take t.n)) t.n a.hpegX hpegY
    simp [upSl]
    exact FitsLen.of_le hSl (by omega)
  have hlenL : t.n ≤ a.laneX.length := by
    rw [a.hlenX]
    exact hnb
  exact frobenius_affine_marker a hyt hy hn0 hs1 hfitU hfitC hspan h3 hnFit hbenchFit
    hlenL hnb hsh.w0 hsh.h0 hsh.rlt hsh.r0 hsh.n_eq hsh.k_le hsh.gap hsh.small hsh.n_small
    hpeg hfitM hfitS

private theorem proj_twice {α : Type} (proj : Board → α)
    (hkeep : ∀ (b : Board) (home : Nat)
      (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
      (xs : List Nat) (moves peak : Nat),
      proj (placeBoard b home hH hD xs moves peak) = proj b)
    (b : Board) (x y : List Nat)
    (h0H : 0 < b.sudo_5Board_4home.size) (h0D : 0 < b.sudo_5Board_4held.size)
    (moves peak : Nat)
    (h1H : 1 < (placeBoard b 0 h0H h0D x moves peak).sudo_5Board_4home.size)
    (h1D : 1 < (placeBoard b 0 h0H h0D x moves peak).sudo_5Board_4held.size)
    (mv1 pk1 : Nat) :
    proj (placeBoard (placeBoard b 0 h0H h0D x moves peak) 1 h1H h1D y mv1 pk1) = proj b :=
  (hkeep _ 1 h1H h1D y mv1 pk1).trans (hkeep b 0 h0H h0D x moves peak)

/-- The seated root, flag turned on, then the white copy. Across and up hold the
    root, the marker stays `-1`, and the flag stays on. -/
theorem cofactor_copied (b : Board) (x y : List Nat) (n moves peak : Nat)
    (hszH : b.sudo_5Board_4home.size = 8) (hszD : b.sudo_5Board_4held.size = 8)
    (hx : x.length = n) (hy : y.length = n)
    (hf : FitsLen n)
    (hfitx : FitsLen (moves + pegCount x))
    (hfity : FitsLen (moves + pegCount x + pegCount y))
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak)
    (hm : b.sudo_5Board_6marker = -1)
    (hoff : b.sudo_5Board_8bench_on = false)
    (h0 : b.sudo_5Board_4held[0]'(by rw [hszD]; decide) = false)
    (h1 : b.sudo_5Board_4held[1]'(by rw [hszD]; decide) = false)
    (h3t : b.sudo_5Board_4held[3]'(by rw [hszD]; decide) = true)
    (h3a : b.sudo_5Board_4home[3]'(by rw [hszH]; decide) = embed x)
    (h4t : b.sudo_5Board_4held[4]'(by rw [hszD]; decide) = true)
    (h4a : b.sudo_5Board_4home[4]'(by rw [hszH]; decide) = embed y) :
    ∃ b2 mv2 pk2,
      (do
          let board ← copy_band (chordFlag b) across base_across false
          copy_band board up base_up false) = .ok b2 ∧
      b2.sudo_5Board_9marker_on = true ∧
      b2.sudo_5Board_8bench_on = false ∧
      b2.sudo_5Board_6marker = -1 ∧
      b2.sudo_5Board_4home.size = 8 ∧
      b2.sudo_5Board_4held.size = 8 ∧
      (∀ h : 0 < b2.sudo_5Board_4home.size, b2.sudo_5Board_4home[0] = embed x) ∧
      (∀ h : 1 < b2.sudo_5Board_4home.size, b2.sudo_5Board_4home[1] = embed y) ∧
      (∀ h : 0 < b2.sudo_5Board_4held.size, b2.sudo_5Board_4held[0] = true) ∧
      (∀ h : 1 < b2.sudo_5Board_4held.size, b2.sudo_5Board_4held[1] = true) ∧
      b2.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mv2 ∧
      mv2 = moves + pegCount x + pegCount y ∧
      b2.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk2 ∧
      b2.sudo_5Board_1t = b.sudo_5Board_1t ∧
      b2.sudo_5Board_4cost.sudo_5Costs_4ctrl = b.sudo_5Board_4cost.sudo_5Costs_4ctrl ∧
      b2.sudo_5Board_4cost.sudo_5Costs_6slides = b.sudo_5Board_4cost.sudo_5Costs_6slides ∧
      b2.sudo_5Board_4cost.sudo_5Costs_3ops = b.sudo_5Board_4cost.sudo_5Costs_3ops ∧
      b2.sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
        b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max ∧
      b2.sudo_5Board_4cost.sudo_5Costs_11peak_strict =
        b.sudo_5Board_4cost.sudo_5Costs_11peak_strict ∧
      b2.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
        b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole := by
  let bF := chordFlag b
  have hszHF : bF.sudo_5Board_4home.size = 8 := by simp [chordFlag, bF, hszH]
  have hszDF : bF.sudo_5Board_4held.size = 8 := by simp [chordFlag, bF, hszD]
  have hmF : bF.sudo_5Board_6marker = -1 := by simp [chordFlag, bF, hm]
  have hoffF : bF.sudo_5Board_8bench_on = false := by simp [chordFlag, bF, hoff]
  have hmkF : bF.sudo_5Board_9marker_on = true := by simp [chordFlag, bF]
  obtain ⟨b2, mv2, pk2, hcopy, hszH2, hszD2, hx0, hy1, h0t, h1t, _hx3, _hy4, hmv, hpk, hsum,
      hmark, _hst, _hho, _hctrl, _hsl, _, _⟩ :=
    walk_copy_white bF x y n moves peak hszHF hszDF hx hy hf hfitx hfity
      (by simp [chordFlag, bF, hn])
      (by simpa [chordFlag, bF, ofNat_eq_natCast] using hmoves)
      (by simpa [chordFlag, bF, ofNat_eq_natCast] using hpeak)
      (by simpa [chordFlag, bF] using h0) (by simpa [chordFlag, bF] using h1)
      (by simpa [chordFlag, bF] using h3t) (by simpa [chordFlag, bF] using h3a)
      (by simpa [chordFlag, bF] using h4t) (by simpa [chordFlag, bF] using h4a)
  -- homes 3 and 4 stay the root; the copy writes 0 and 1.
  have h0H : 0 < bF.sudo_5Board_4home.size := by rw [hszHF]; decide
  have h0D : 0 < bF.sudo_5Board_4held.size := by rw [hszDF]; decide
  have h1H : 1 < bF.sudo_5Board_4home.size := by rw [hszHF]; decide
  have h1D : 1 < bF.sudo_5Board_4held.size := by rw [hszDF]; decide
  have h3H : 3 < bF.sudo_5Board_4home.size := by rw [hszHF]; decide
  have h3D : 3 < bF.sudo_5Board_4held.size := by rw [hszDF]; decide
  have h4H : 4 < bF.sudo_5Board_4home.size := by rw [hszHF]; decide
  have h4D : 4 < bF.sudo_5Board_4held.size := by rw [hszDF]; decide
  have h7 : 7 ≤ bF.sudo_5Board_4held.size := by rw [hszDF]; decide
  have hmvI : bF.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int) := by
    simpa [chordFlag, bF, ofNat_eq_natCast] using hmoves
  have hpkI : bF.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int) := by
    simpa [chordFlag, bF, ofNat_eq_natCast] using hpeak
  have hcopy1 := copy_band_refines bF 0 3 x moves peak h0H h0D h3H h3D h7
      (by simpa [chordFlag, bF] using h3t) (by simpa [chordFlag, bF] using h3a)
      (by simpa [chordFlag, bF] using h0)
      (by simpa [chordFlag, bF, hx] using hn) (by simpa [hx] using hf)
      hmvI hpkI hfitx
  let b1 := placeBoard bF 0 h0H h0D x moves peak
  have hszD1 : b1.sudo_5Board_4held.size = 8 := by rw [place_held_eq, Array.size_set, hszDF]
  have hszH1 : b1.sudo_5Board_4home.size = 8 := by rw [place_home_eq, Array.size_set, hszHF]
  have h1D1 : 1 < b1.sudo_5Board_4held.size := by rw [hszD1]; decide
  have h1H1 : 1 < b1.sudo_5Board_4home.size := by rw [hszH1]; decide
  have h4D1 : 4 < b1.sudo_5Board_4held.size := by rw [hszD1]; decide
  have h4H1 : 4 < b1.sudo_5Board_4home.size := by rw [hszH1]; decide
  have h7_1 : 7 ≤ b1.sudo_5Board_4held.size := by rw [hszD1]; decide
  have hempty1 : b1.sudo_5Board_4held[1] = false := by
    have hget := get_eq_of_array (place_held_eq bF 0 h0H h0D x moves peak) 1 h1D1
    simp only [Array.getElem_set, (by decide : (0 : Nat) ≠ 1)] at hget
    exact hget.trans (by simpa [chordFlag, bF] using h1)
  have h4t1 : b1.sudo_5Board_4held[4] = true := by
    have hget := get_eq_of_array (place_held_eq bF 0 h0H h0D x moves peak) 4 h4D1
    simp only [Array.getElem_set, (by decide : (0 : Nat) ≠ 4)] at hget
    exact hget.trans (by simpa [chordFlag, bF] using h4t)
  have h4a1 : b1.sudo_5Board_4home[4] = embed y := by
    have hget := get_eq_of_array (place_home_eq bF 0 h0H h0D x moves peak) 4 h4H1
    simp only [Array.getElem_set, (by decide : (0 : Nat) ≠ 4)] at hget
    exact hget.trans (by simpa [chordFlag, bF] using h4a)
  let mv1 := moves + pegCount x
  let pk1 := if peak < countHeld (bF.sudo_5Board_4held.set ⟨0, h0D⟩ true) 7
      then countHeld (bF.sudo_5Board_4held.set ⟨0, h0D⟩ true) 7 else peak
  have hmv1 : b1.sudo_5Board_4cost.sudo_5Costs_5moves = (mv1 : Int) := by
    rw [place_moves_eq]; exact ofNat_eq_natCast _
  have hpk1 : b1.sudo_5Board_4cost.sudo_5Costs_4peak = (pk1 : Int) := by
    rw [place_peak_nat bF 0 h0H h0D x moves peak hpkI]
    exact ofNat_eq_natCast _
  have hcopy2 := copy_band_refines b1 1 4 y mv1 pk1 h1H1 h1D1 h4H1 h4D1 h7_1
      h4t1 h4a1 hempty1
      (by rw [place_tier_eq, show bF.sudo_5Board_1t = b.sudo_5Board_1t from by simp [chordFlag, bF], hn, hy])
      (by simpa [hy] using hf) hmv1 hpk1 hfity
  let bP := placeBoard b1 1 h1H1 h1D1 y mv1 pk1
  have hP : (do
      let board ← copy_band bF across base_across false
      copy_band board up base_up false) = .ok bP := by
    rw [show across = ((0 : Nat) : Int) from rfl, show base_across = ((3 : Nat) : Int) from rfl,
        show up = ((1 : Nat) : Int) from rfl, show base_up = ((4 : Nat) : Int) from rfl,
        hcopy1, ok_bind]
    simpa [b1, bP] using hcopy2
  have hb : b2 = bP := by
    have h := hcopy.symm.trans (by simpa [bF] using hP)
    injection h
  have hflag : bP.sudo_5Board_9marker_on = true := by
    rw [proj_twice (fun b => b.sudo_5Board_9marker_on) place_flag bF x y h0H h0D moves peak
      h1H1 h1D1 mv1 pk1]
    exact hmkF
  have hbench : bP.sudo_5Board_8bench_on = false := by
    rw [proj_twice (fun b => b.sudo_5Board_8bench_on) place_bench bF x y h0H h0D moves peak
      h1H1 h1D1 mv1 pk1]
    exact hoffF
  have htier : bP.sudo_5Board_1t = b.sudo_5Board_1t := by
    rw [proj_twice (fun b => b.sudo_5Board_1t) place_tier_eq bF x y h0H h0D moves peak
      h1H1 h1D1 mv1 pk1]
    simp [chordFlag, bF]
  have hctrlP : bP.sudo_5Board_4cost.sudo_5Costs_4ctrl =
      b.sudo_5Board_4cost.sudo_5Costs_4ctrl := by
    rw [proj_twice (fun b => b.sudo_5Board_4cost.sudo_5Costs_4ctrl) place_ctrl_eq
      bF x y h0H h0D moves peak h1H1 h1D1 mv1 pk1]
    simp [chordFlag, bF]
  have hslP : bP.sudo_5Board_4cost.sudo_5Costs_6slides =
      b.sudo_5Board_4cost.sudo_5Costs_6slides := by
    rw [proj_twice (fun b => b.sudo_5Board_4cost.sudo_5Costs_6slides) place_slides_eq
      bF x y h0H h0D moves peak h1H1 h1D1 mv1 pk1]
    simp [chordFlag, bF]
  have hopsP : bP.sudo_5Board_4cost.sudo_5Costs_3ops =
      b.sudo_5Board_4cost.sudo_5Costs_3ops := by
    rw [proj_twice (fun b => b.sudo_5Board_4cost.sudo_5Costs_3ops) place_ops_eq
      bF x y h0H h0D moves peak h1H1 h1D1 mv1 pk1]
    simp [chordFlag, bF]
  have hmxP : bP.sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
      b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max := by
    rw [proj_twice (fun b => b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max) place_mx_eq
      bF x y h0H h0D moves peak h1H1 h1D1 mv1 pk1]
    simp [chordFlag, bF]
  have hstP : bP.sudo_5Board_4cost.sudo_5Costs_11peak_strict =
      b.sudo_5Board_4cost.sudo_5Costs_11peak_strict := by
    rw [proj_twice (fun b => b.sudo_5Board_4cost.sudo_5Costs_11peak_strict) place_strict_eq
      bF x y h0H h0D moves peak h1H1 h1D1 mv1 pk1]
    simp [chordFlag, bF]
  have hhoP : bP.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole := by
    rw [proj_twice (fun b => b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole) place_hole_eq
      bF x y h0H h0D moves peak h1H1 h1D1 mv1 pk1]
    simp [chordFlag, bF]
  refine ⟨b2, mv2, pk2, by simpa [bF] using hcopy, ?_, ?_, ?_, hszH2, hszD2, hx0, hy1, h0t, h1t,
      hmv, hsum, hpk, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hb]; exact hflag
  · rw [hb]; exact hbench
  · exact hmark.trans hmF
  · rw [hb]; exact htier
  · rw [hb]; exact hctrlP
  · rw [hb]; exact hslP
  · rw [hb]; exact hopsP
  · rw [hb]; exact hmxP
  · rw [hb]; exact hstP
  · rw [hb]; exact hhoP

/-- The seated root, copied, then cubed. Across and up become the field cubes. -/
theorem cofactor_copied_frobenius (b : Board) (t : Spec.Tier) (x y : List Nat)
    (moves slides pk peakS holeN cOps ctrl mx : Nat)
    (hsh : TierShape t) (sat : TierSat t)
    (hszH : b.sudo_5Board_4home.size = 8) (hszD : b.sudo_5Board_4held.size = 8)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hx : x.length = t.n) (hy : y.length = t.n)
    (hxt : allTritList x) (hyt : allTritList y)
    (hoff : b.sudo_5Board_8bench_on = false)
    (hmark : b.sudo_5Board_6marker = -1)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hmx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hT : b.sudo_5Board_1t = embTier t)
    (hop1 : b.sudo_5Board_4cost.sudo_5Costs_3ops[1]'hops = (cOps : Int))
    (hfitC : FitsLen (cOps + 2))
    (hfitD : FitsLen (ctrl + 1))
    (hfitU : FitsLen ((ctrl + 1) + 2))
    (h0 : b.sudo_5Board_4held[0]'(by rw [hszD]; decide) = false)
    (h1 : b.sudo_5Board_4held[1]'(by rw [hszD]; decide) = false)
    (h3t : b.sudo_5Board_4held[3]'(by rw [hszD]; decide) = true)
    (h3a : b.sudo_5Board_4home[3]'(by rw [hszH]; decide) = embed x)
    (h4t : b.sudo_5Board_4held[4]'(by rw [hszD]; decide) = true)
    (h4a : b.sudo_5Board_4home[4]'(by rw [hszH]; decide) = embed y)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk)
    (hstrict : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat peakS)
    (hhole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat holeN)
    (hf : FitsLen t.n)
    (hfitx : FitsLen (moves + pegCount x))
    (hfity : FitsLen (moves + pegCount x + pegCount y))
    (hMv : FitsLen (moves + pegCount x + pegCount y + 8 * t.n + 6 * (t.benchlen - t.n)))
    (hSl : FitsLen (slides + 4 * t.n)) :
    ∃ b2 bF,
      (do
          let board ← copy_band (chordFlag b) across base_across false
          copy_band board up base_up false) = .ok b2 ∧
      frobenius_affine b2 = .ok bF ∧
      (∀ h0 : 0 < bF.sudo_5Board_4home.size,
        bF.sudo_5Board_4home[0] = embed (fieldCube t.n t.k t.benchlen x)) ∧
      (∀ h1 : 1 < bF.sudo_5Board_4home.size,
        bF.sudo_5Board_4home[1] = embed (fieldCube t.n t.k t.benchlen y)) := by
  obtain ⟨b2, mv2, pk2, hcopy, hmk, hoff2, hmark2, hszH2, hszD2, hx0, hy1, h0t, h1t,
      hmv, hsum, hpk2, htier, hctrl, hsl2, hops2, hmx2, hst, hho⟩ :=
    cofactor_copied b x y t.n moves pk hszH hszD hx hy hf hfitx hfity
      (by simp [hT, embTier]) hmoves hpeak hmark hoff h0 h1 h3t h3a h4t h4a
  have hopsB : 1 < b2.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [hops2]; exact hops
  have hopB : b2.sudo_5Board_4cost.sudo_5Costs_3ops[1]'hopsB = (cOps : Int) := by
    have hget := get_eq_of_array hops2.symm 1 hops
    simpa [hopsB] using hget.symm.trans hop1
  have h0e : b2.sudo_5Board_4held[0]'(by rw [hszD2]; decide) = true := h0t _
  have h1e : b2.sudo_5Board_4held[1]'(by rw [hszD2]; decide) = true := h1t _
  have hx0e : b2.sudo_5Board_4home[0]'(by rw [hszH2]; decide) = embed x := hx0 _
  have hy1e : b2.sudo_5Board_4home[1]'(by rw [hszH2]; decide) = embed y := hy1 _
  have hMv2 : FitsLen (mv2 + 8 * t.n + 6 * (t.benchlen - t.n)) := by
    rw [hsum]; exact hMv
  obtain ⟨bF, hfrob, _, _, hxF, hyF⟩ :=
    cofactor_frobenius b2 t x y mv2 slides pk2 peakS holeN cOps ctrl mx hsh sat
      hszH2 hszD2 hopsB hx hy hxt hyt hmk hoff2 hmark2
      (hctrl.trans hc) (hmx2.trans hmx) (htier.trans hT) hopB hfitC hfitD hfitU
      h0e hx0e h1e hy1e hmv (hsl2.trans hslides) hpk2 (hst.trans hstrict)
      (hho.trans hhole) hMv2 hSl
  exact ⟨b2, bF, hcopy, hfrob, hxF, hyF⟩

/-- The across cube of a copied cofactor root. Its own declaration, so the
    move-count proof does not rebuild it. -/
noncomputable def cofactorDown (b : Board) (t : Spec.Tier) (x y : List Nat)
    (moves slides pk peakS holeN cOps ctrl mx : Nat)
    (hsh : TierShape t) (sat : TierSat t)
    (hszH : b.sudo_5Board_4home.size = 8) (hszD : b.sudo_5Board_4held.size = 8)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hx : x.length = t.n) (hy : y.length = t.n)
    (hxt : allTritList x) (hyt : allTritList y)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hoff : b.sudo_5Board_8bench_on = false)
    (hmark : b.sudo_5Board_6marker = -1)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hmx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hT : b.sudo_5Board_1t = embTier t)
    (hop1 : b.sudo_5Board_4cost.sudo_5Costs_3ops[1]'hops = (cOps : Int))
    (hfitC : FitsLen (cOps + 2))
    (hfitD : FitsLen (ctrl + 1))
    (hfitU : FitsLen ((ctrl + 1) + 2))
    (hheld0 : b.sudo_5Board_4held[0]'(by rw [hszD]; decide) = true)
    (hhome0 : b.sudo_5Board_4home[0]'(by rw [hszH]; decide) = embed x)
    (hheld1 : b.sudo_5Board_4held[1]'(by rw [hszD]; decide) = true)
    (hhome1 : b.sudo_5Board_4home[1]'(by rw [hszH]; decide) = embed y)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk)
    (hstrict : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat peakS)
    (hhole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat holeN)
    (hMv : FitsLen (moves + 8 * t.n + 6 * (t.benchlen - t.n)))
    (hSl : FitsLen (slides + 4 * t.n)) :
    DownAcross b x y t.n t.k t.w t.h t.r t.benchlen t.combgap pk moves slides
      holeN cOps ctrl mx t.script :=
  down_across b x y t.w t.h t.r t.n t.k moves slides pk peakS holeN cOps ctrl mx
      t.script hszH hszD hops hx hy hxt hyt hmk hoff (by rw [hmark]; decide) hc hmx
      (by simp [hT, embTier]) (script_one t.script hsh.script_ge) hfitD hfitU hop1 hfitC
      hheld0 hhome0 hheld1 hhome1
      (by simp [hT, embTier]) (by simp [hT, embTier]) (by simp [hT, embTier])
      (by simp [hT, embTier]) (by simp [hT, embTier]) (by simp [hT, embTier])
      (by simp [hT, embTier]) hmoves hslides hpeak hstrict hhole
      hsh.w0 hsh.h0 hsh.rlt hsh.r0
      (shape_n_pos t.n t.w t.h t.r hsh.n_eq hsh.w0 hsh.r0 hsh.rlt)
      hsh.n_eq hsh.k_le hsh.gap sat.cube_span
      hsh.small hsh.n_small hMv hSl

/-- The cubed copy keeps an empty bottom, ops slot 3, and a natural move count.
    Slot 1 is the cube counter; the chord counter is slot 3. The bottom is
    home 2, which neither cube writes. -/
theorem cofactor_cube_keep (b : Board) (t : Spec.Tier) (x y : List Nat)
    (moves slides pk peakS holeN cOps ctrl mx c3 : Nat)
    (hsh : TierShape t) (sat : TierSat t)
    (hszH : b.sudo_5Board_4home.size = 8) (hszD : b.sudo_5Board_4held.size = 8)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hops3 : 3 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hx : x.length = t.n) (hy : y.length = t.n)
    (hxt : allTritList x) (hyt : allTritList y)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hoff : b.sudo_5Board_8bench_on = false)
    (hmark : b.sudo_5Board_6marker = -1)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hmx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hT : b.sudo_5Board_1t = embTier t)
    (hop1 : b.sudo_5Board_4cost.sudo_5Costs_3ops[1]'hops = (cOps : Int))
    (hop3 : b.sudo_5Board_4cost.sudo_5Costs_3ops[3]'hops3 = (c3 : Int))
    (hfitC : FitsLen (cOps + 2))
    (hfitD : FitsLen (ctrl + 1))
    (hfitU : FitsLen ((ctrl + 1) + 2))
    (hheld0 : b.sudo_5Board_4held[0]'(by rw [hszD]; decide) = true)
    (hhome0 : b.sudo_5Board_4home[0]'(by rw [hszH]; decide) = embed x)
    (hheld1 : b.sudo_5Board_4held[1]'(by rw [hszD]; decide) = true)
    (hhome1 : b.sudo_5Board_4home[1]'(by rw [hszH]; decide) = embed y)
    (h2 : b.sudo_5Board_4held[2]'(by rw [hszD]; decide) = false)
    (h3t : b.sudo_5Board_4held[3]'(by rw [hszD]; decide) = true)
    (h3a : b.sudo_5Board_4home[3]'(by rw [hszH]; decide) = embed x)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk)
    (hstrict : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat peakS)
    (hhole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat holeN)
    (hMv : FitsLen (moves + 8 * t.n + 6 * (t.benchlen - t.n)))
    (hSl : FitsLen (slides + 4 * t.n))
    (hChord : FitsLen (moves + 10 * t.n + 6 * (t.benchlen - t.n))) :
    ∃ (bF : Board) (mvF pkF : Nat),
      frobenius_affine b = .ok bF ∧
      bF.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mvF ∧
      FitsLen (mvF + 2 * t.n) ∧
      bF.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pkF ∧
      bF.sudo_5Board_4held.size = 8 ∧
      bF.sudo_5Board_4home.size = 8 ∧
      (∀ h : 2 < bF.sudo_5Board_4held.size, bF.sudo_5Board_4held[2] = false) ∧
      (∀ h : 0 < bF.sudo_5Board_4held.size, bF.sudo_5Board_4held[0] = true) ∧
      (∀ h : 0 < bF.sudo_5Board_4home.size,
        bF.sudo_5Board_4home[0] = embed (fieldCube t.n t.k t.benchlen x)) ∧
      (∀ h : 3 < bF.sudo_5Board_4held.size, bF.sudo_5Board_4held[3] = true) ∧
      (∀ h : 3 < bF.sudo_5Board_4home.size, bF.sudo_5Board_4home[3] = embed x) ∧
      3 < bF.sudo_5Board_4cost.sudo_5Costs_3ops.size ∧
      (∀ h : 3 < bF.sudo_5Board_4cost.sudo_5Costs_3ops.size,
        bF.sudo_5Board_4cost.sudo_5Costs_3ops[3] = (c3 : Int)) ∧
      bF.sudo_5Board_1t.sudo_4Tier_1n = (t.n : Int) := by
  let a := cofactorDown b t x y moves slides pk peakS holeN cOps ctrl mx hsh sat
      hszH hszD hops hx hy hxt hyt hmk hoff hmark hc hmx hT hop1 hfitC hfitD hfitU
      hheld0 hhome0 hheld1 hhome1 hmoves hslides hpeak hstrict hhole hMv hSl
  obtain ⟨mvF, pkF, hrun, hmv, _, hfit, hpk, hszD2, hszH2, h2o, h0o, hhome0o, h3o, hhome3,
      hopsO, hopO, hnO⟩ :=
    cube_keep_of b x y t.n t.k t.w t.h t.r t.benchlen t.combgap pk moves slides holeN
      cOps ctrl mx t.script peakS c3 a hszH hszD hops hops3 hx hy hxt hyt hmk hoff hmark
      hc hmx (by simp [hT, embTier]) (by simp [hT, embTier]) (by simp [hT, embTier])
      (by simp [hT, embTier]) (by simp [hT, embTier]) (by simp [hT, embTier])
      (by simp [hT, embTier]) (by simp [hT, embTier]) hsh.script_ge hfitD hfitU hop1 hfitC
      hheld0 hhome0 hmoves hpeak hstrict hhole hsh.w0 hsh.h0 hsh.rlt hsh.r0 hsh.n_eq
      hsh.k_le hsh.gap sat.cube_span hsh.small hsh.n_small hMv hSl hChord h2 h3t h3a hop3
  refine ⟨frobeniusOut a, mvF, pkF, hrun, hmv, hfit, hpk, hszD2, hszH2, h2o, h0o, hhome0o,
      h3o, hhome3, hopsO, hopO, hnO⟩

end EcbsLink2.Link2
