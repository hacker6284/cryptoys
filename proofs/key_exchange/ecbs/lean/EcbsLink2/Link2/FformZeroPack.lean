/-
  A zero cell, packed as the next `FformAt`. The cube counter steps by 3.
  The multiply counter stays. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FformZeroAt
import EcbsLink2.Link2.FformZeroProj
import EcbsLink2.Link2.FformAtPack

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- One cell still to run, and the three cubes it spends. -/
theorem zero_cell_cube_slack (c1 cells done : Nat)
    (h : FitsLen (c1 + 3 * (cells - done))) (hpos : done < cells) :
    FitsLen (c1 + 3) ∧ FitsLen (c1 + 3 + 3 * (cells - (done + 1))) :=
  ⟨cube_slack_cell c1 cells done h hpos, cube_slack_next c1 cells done h hpos⟩

private theorem get_of_some {α : Type} (a : Array α) (i : Nat) (v : α)
    (h : a[i]? = some v) (hlt : i < a.size) : a[i]'hlt = v := by
  have heq := Array.getElem?_eq_getElem hlt
  rw [h] at heq
  exact Option.some.inj heq.symm

private theorem proj_cast (t : Spec.Tier) (b1 b2 : Ecbs.Board) (px py : List Nat)
    (h : b2 = b1) (hp : ProjOn t b1 px py) : ProjOn t b2 px py := by
  rw [h]
  exact hp

private theorem step_fit (t : Spec.Tier) (tw : TierWalk t) (i : Nat) (hi : i ≤ t.cells) :
    FitsLen (i + 1) := by
  apply FitsLen.of_le tw.roomO
  have hpos : 0 < cellOpsCharge t := by
    unfold cellOpsCharge
    omega
  have hle : i + 1 ≤ t.cells + 1 := by omega
  have hone : 1 ≤ cellOpsCharge t := hpos
  exact Nat.le_trans hle (by simpa using Nat.mul_le_mul_left (t.cells + 1) hone)

private theorem six_le_cube (n : Nat) : 6 * n ≤ 8 * n * (n + 1) := by
  have h : 6 ≤ 8 * (n + 1) := by omega
  calc
    6 * n = n * 6 := Nat.mul_comm _ _
    _ ≤ n * (8 * (n + 1)) := Nat.mul_le_mul_left n h
    _ = 8 * n * (n + 1) := by
      rw [← Nat.mul_assoc, Nat.mul_comm n 8, Nat.mul_assoc]

private theorem two_cube_le (n bench : Nat) :
    2 * (cubeCharge n bench + 2 * n + 3 * (bench - n)) + 2 * n ≤
      8 * stepBudget n bench := by
  unfold cubeCharge stepBudget
  generalize hd : bench - n = d
  have h6 : 6 * n ≤ 8 * (n * (n + 1)) := by
    simpa [Nat.mul_assoc] using six_le_cube n
  have hmain : 22 * n + 18 * d ≤ 16 * n + 8 * (n * (n + 1)) + 24 * d := by
    omega
  have hL : 2 * (8 * n + 6 * d + 2 * n + 3 * d) + 2 * n = 22 * n + 18 * d := by omega
  have hR : 8 * (2 * n + n * (n + 1) + 3 * d) =
      16 * n + 8 * (n * (n + 1)) + 24 * d := by omega
  rw [hL, hR]
  exact hmain

private theorem next_move_le (moves moves' spend extra budget : Nat)
    (hm : moves' ≤ moves + spend) (h2 : 2 * spend + extra ≤ budget) :
    moves' + spend + extra ≤ moves + budget := by
  omega

private theorem group_spend (moves moves' c n d : Nat)
    (h : moves' ≤ moves + c + 2 * n + 3 * d) :
    moves' ≤ moves + (c + 2 * n + 3 * d) := by
  omega

private theorem spend_of_two (spend extra budget : Nat)
    (h : 2 * spend + extra ≤ budget) : spend ≤ budget := by
  omega

private theorem move_goal_exp (moves' n c d moves budget : Nat)
    (h : moves' + (c + 2 * n + 3 * d) + 2 * n ≤ moves + budget) :
    moves' + 2 * n + c + 2 * n + 3 * d ≤ moves + budget := by
  omega

private theorem slide_fit_le (slides slides' n : Nat) (h : slides' ≤ slides + 4 * n) :
    slides' + 6 * n ≤ slides + 12 * n := by
  omega

private theorem slide_split (slides slides' n : Nat)
    (h : slides' + 6 * n ≤ slides + 12 * n) :
    slides' + 2 * n + 4 * n ≤ slides + 12 * n := by
  omega

private theorem ctrl_fit_le (ctrl : Nat) : (ctrl + 6) + 6 ≤ (ctrl + 6) + 40 := by
  omega

private theorem four_of_twelve (n S : Nat) (h : 12 * n ≤ S) : 4 * n ≤ S := by
  omega

private theorem six_of_fortysix (S : Nat) (h : 46 ≤ S) : 6 ≤ S := by
  omega

/-- The comparisons a shipped tier gives the zero cell's next room. -/
theorem zero_cell_room (t : Spec.Tier)
    (h : t = demo ∨ t = toy ∨ t = hobby ∨ t = serious) :
    TierWalk t ∧
    8 * stepBudget t.n t.benchlen ≤ walkCharge t + (6 * t.benchlen + 2 * t.n) ∧
    12 * t.n ≤ cellSlideCharge t + slideCharge t.n ∧
    46 ≤ cellCtrlCharge t + 4 := by
  rcases h with rfl | rfl | rfl | rfl
  · exact ⟨demo_tier_walk, demo_tail_moves, demo_slide12, demo_sum_ctrl⟩
  · exact ⟨toy_tier_walk, toy_tail_moves, toy_slide12, toy_sum_ctrl⟩
  · exact ⟨hobby_tier_walk, hobby_tail_moves, hobby_slide12, hobby_sum_ctrl⟩
  · exact ⟨serious_tier_walk, serious_tail_moves, serious_slide12, serious_sum_ctrl⟩

/-- Homes layout, colour 0. The board `frobenius_point` leaves is the next
    `FformAt`, and slot 1 has grown by exactly 3. -/
theorem zero_cell_at
    (t : Spec.Tier) (b : Ecbs.Board)
    (baseX baseY px py xP yP zP : List Nat) (i : Nat)
    (hAt : FformAt t b baseX baseY px py i)
    (hsh : TierShape t) (hOk : BoardOk t) (sat : TierSat t)
    (tw : TierWalk t)
    (hstep : 8 * stepBudget t.n t.benchlen ≤
      walkCharge t + (6 * t.benchlen + 2 * t.n))
    (h12 : 12 * t.n ≤ cellSlideCharge t + slideCharge t.n)
    (h46 : 46 ≤ cellCtrlCharge t + 4)
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
    (cells : List Nat)
    (hpos0 : 0 < t.cells) (hi : i ≤ t.cells - 1) (hlen : cells.length = t.cells)
    (hc : cells[i]'(by omega) = 0) :
    ∃ bL bZ,
      Ecbs.marker_lift b = .ok bL ∧
      Ecbs.frobenius_point bL = .ok bZ ∧
      FformAt t bZ baseX baseY
        (fieldCube t.n t.k t.benchlen px) (fieldCube t.n t.k t.benchlen py) (i + 1) := by
  have hAt0 := hAt
  rcases hAt with ⟨_, _, hpx, hpy, hpxT, hpyT, hbx, hby, hbxT, hbyT, _, _, _, _, _, _,
      _, hscript, _, _, _, hrest⟩
  rcases hrest with ⟨moves, slides, ctrl, mark, mx, pk, peakS, hole, c1, cMul,
      hmv, hsl, hcCtrl, hmark, hmxEq, hpk, hstrict, hhole, hops, hop1?, hop0?,
      hfitCtrl, hc1, hfitMul, hfitMv, hfitSl, hmvLe, hslLe, hcLe⟩
  have hpos : i < t.cells := by omega
  have hnb : t.n ≤ t.benchlen := tw.nLe
  have h3span : 3 * (t.n - 1) < t.benchlen := by
    have hspan : 3 * (t.n - 1) + t.combgap < t.benchlen := sat.cube_span
    omega
  have hMul : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size :=
    Nat.lt_trans Nat.zero_lt_one hops
  have hop1 := get_of_some _ 1 _ hop1? hops
  have hopMul := get_of_some _ 0 _ hop0? hMul
  have hpair := zero_cell_cube_slack c1 t.cells i hc1 hpos
  have hOps3 : FitsLen (c1 + 3) := hpair.1
  have hRoom : FitsLen (moves + cubeCharge t.n t.benchlen + 2 * t.n +
      3 * (t.benchlen - t.n)) := FitsLen.of_le hfitMv (by omega)
  have hSlF : FitsLen (slides + slideCharge t.n) := FitsLen.of_le hfitSl (by omega)
  have hfitI := step_fit t tw i (by omega)
  obtain ⟨bLp, bZp, hliftP, hfrobP, hfr, hp⟩ :=
    zero_cell_proj t b baseX baseY px py xP yP zP i hAt0 hsh hOk sat hs2
      hxL hyL hzL hxT hyT hzT hszH hszD h0 h1 h2 hd0 hd1 hd2 hoff
      moves slides ctrl mark mx pk peakS hole c1 hmv hsl hcCtrl hmark hmxEq hpk
      hstrict hhole hops hop1 hfitCtrl hOps3 hRoom hSlF
      cells i hpos0 hi hlen hc hfitI
  obtain ⟨bLc, bZc, moves', slides', pk', peakS', hole', hliftC, hfrobC, hmon, hH0,
      hmv', hsl', hctrl', hmark', hmx', hpk', hst', hhole', hsz1, hop1', hop0c,
      hleM, hleS⟩ :=

    zero_bZ_charge t b baseX baseY px py xP yP zP i hAt0 hsh hOk sat hs2
      hxL hyL hzL hxT hyT hzT hszH hszD h0 h1 h2 hd0 hd1 hd2 hoff
      moves slides ctrl mark mx pk peakS hole c1 hmv hsl hcCtrl hmark hmxEq hpk
      hstrict hhole hops hop1 cMul hMul hopMul hfitCtrl hOps3 hRoom hSlF
      cells i hpos0 hi hlen hc hfitI
  have hbL : bLp = bLc := Except.ok.inj (hliftP.symm.trans hliftC)
  have hfrobP' : Ecbs.frobenius_point bLc = .ok bZp := by
    rw [← hbL]
    exact hfrobP
  have hbZ : bZp = bZc := Except.ok.inj (hfrobP'.symm.trans hfrobC)
  have hfrC := frame_cast t bZp bZc baseX baseY hbZ.symm hfr
  have hpC := proj_cast t bZp bZc
    (fieldCube t.n t.k t.benchlen px) (fieldCube t.n t.k t.benchlen py) hbZ.symm hp
  have hpxC : (fieldCube t.n t.k t.benchlen px).length = t.n :=
    fieldCube_length t.n t.k t.benchlen px hnb
  have hpyC : (fieldCube t.n t.k t.benchlen py).length = t.n :=
    fieldCube_length t.n t.k t.benchlen py hnb
  have hpxCT := fieldCube_trits t.n t.k t.benchlen px hpxT h3span hsh.k_le
  have hpyCT := fieldCube_trits t.n t.k t.benchlen py hpyT h3span hsh.k_le
  have hfitC : FitsLen ((ctrl + 6) + 6) :=
    FitsLen.of_le (comb_ctrl_fit t ctrl i (ctrl + 6) tw hcLe hpos rfl h46) (ctrl_fit_le ctrl)
  have hc1' : FitsLen ((c1 + 3) + 3 * (t.cells - (i + 1))) := hpair.2
  have hc0' : FitsLen (cMul + 13 * (t.cells - (i + 1))) := by
    have hnext := mul_slack_next cMul 0 t.cells i hfitMul (by omega) hpos
    simpa [Nat.add_zero] using hnext
  have hbig := cell_big_room t moves i tw hmvLe hpos hstep
  have htwo := two_cube_le t.n t.benchlen
  let spend := cubeCharge t.n t.benchlen + 2 * t.n + 3 * (t.benchlen - t.n)
  have hspendLe : moves' ≤ moves + spend :=
    group_spend moves moves' (cubeCharge t.n t.benchlen) t.n (t.benchlen - t.n) hleM
  have hfitM' : FitsLen (moves' + 2 * t.n + cubeCharge t.n t.benchlen + 2 * t.n +
      3 * (t.benchlen - t.n)) := by
    refine FitsLen.of_le hbig ?_
    exact move_goal_exp moves' t.n (cubeCharge t.n t.benchlen) (t.benchlen - t.n)
      moves (8 * stepBudget t.n t.benchlen)
      (next_move_le moves moves' spend (2 * t.n) (8 * stepBudget t.n t.benchlen)
        hspendLe htwo)
  have hslide := cell_slide_room t slides i tw hslLe hpos h12
  have hfitS' : FitsLen (slides' + 2 * t.n + slideCharge t.n) := by
    refine FitsLen.of_le hslide ?_
    rw [slideCharge]
    exact slide_split slides slides' t.n (slide_fit_le slides slides' t.n hleS)
  let B := walkCharge t + (6 * t.benchlen + 2 * t.n)
  have hspB : spend ≤ B :=
    Nat.le_trans (spend_of_two spend (2 * t.n) (8 * stepBudget t.n t.benchlen) htwo) hstep
  have hsumM := ledger_next i B spend moves hmvLe hspB
  have hmvLe' : moves' ≤ (i + 1) * B := Nat.le_trans hspendLe hsumM
  have h4n := four_of_twelve t.n (cellSlideCharge t + slideCharge t.n) h12
  have hsumS := ledger_next i (cellSlideCharge t + slideCharge t.n) (4 * t.n) slides hslLe h4n
  have hslLe' : slides' ≤ (i + 1) * (cellSlideCharge t + slideCharge t.n) :=
    Nat.le_trans hleS hsumS
  have h6 := six_of_fortysix (cellCtrlCharge t + 4) h46
  have hcLe' := ledger_next i (cellCtrlCharge t + 4) 6 ctrl hcLe h6
  have hops0 : 0 < bZc.sudo_5Board_4cost.sudo_5Costs_3ops.size :=
    Nat.lt_trans Nat.zero_lt_one hsz1
  have hop0e := get_of_some _ 0 _ hop0c hops0
  have ch : TailCharge bZc moves' slides' (ctrl + 6) 2
      (max (max (max mx 1) 2) 3) pk' peakS' hole' cMul := {
    movesEq := hmv'
    slidesEq := hsl'
    ctrlEq := hctrl'
    markEq := hmark'
    mxEq := hmx'
    peakEq := hpk'
    strictEq := hst'
    holeEq := hhole'
    opsSz := hops0
    ops0 := hop0e
  }
  have hAt' := fform_at_pack t bZc baseX baseY
    (fieldCube t.n t.k t.benchlen px) (fieldCube t.n t.k t.benchlen py) (i + 1)
    hmon hpxC hpyC hpxCT hpyCT hbx hby hbxT hbyT hH0 hscript hfrC hpC
    moves' slides' (ctrl + 6) 2 (max (max (max mx 1) 2) 3) pk' peakS' hole'
    (c1 + 3) cMul ch hsz1 hop1' hfitC hc1' hc0' hfitM' hfitS' hmvLe' hslLe' hcLe'
  exact ⟨bLc, bZc, hliftC, hfrobC, hAt'⟩

end EcbsLink2.Link2
