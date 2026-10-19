/-
  A `yBench` zero cell, packed as the next `FformAt`. The comb is the
  `zBench` layout, slot 0 stays, and slot 1 grows by 3.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FformYZero
import EcbsLink2.Link2.FformAtPack
import EcbsLink2.Link2.FformCellInv

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open Ecbs
open EcbsLink2.Spec

attribute [local irreducible] fieldCube fieldMul Ecbs.frobenius_point Ecbs.marker_lift

private theorem embed_inj {xs ys : List Nat} (h : embed xs = embed ys) : xs = ys := by
  have hxs := embed_beq xs ys
  rw [h] at hxs
  rw [embed_beq ys ys] at hxs
  exact of_decide_eq_true (by simpa using hxs)

private theorem read_cell {α : Type} (a : Array α) (i : Nat) (v : α)
    (h : a[i]? = some v) : ∀ hlt : i < a.size, a[i]'hlt = v := by
  intro hlt
  have heq := Array.getElem?_eq_getElem hlt
  rw [h] at heq
  exact Option.some.inj heq.symm

private theorem peg_le (ys : List Nat) (n : Nat) (hn : n ≤ ys.length) :
    pegCount (ys.take n) ≤ n := by
  refine Nat.le_trans (pegCount_le _) ?_
  rw [List.length_take]
  exact Nat.min_le_left _ _

private theorem y_room (moves slides peg n cube d slide : Nat)
    (hpeg : peg ≤ n)
    (hm : FitsLen (moves + 2 * n + cube + 2 * n + 3 * d))
    (hs : FitsLen (slides + 2 * n + slide)) :
    FitsLen (2 * peg) ∧
      FitsLen (moves + 2 * peg) ∧
      FitsLen (slides + 2 * peg) ∧
      FitsLen (moves + 2 * peg + cube + 2 * n + 3 * d) ∧
      FitsLen (slides + 2 * peg + slide) := by
  have h2 : 2 * peg ≤ 2 * n := Nat.mul_le_mul_left 2 hpeg
  refine ⟨FitsLen.of_le hm ?_, FitsLen.of_le hm ?_, FitsLen.of_le hs ?_,
      FitsLen.of_le hm ?_, FitsLen.of_le hs ?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega

private theorem group_spend (m p c n d : Nat) :
    m + 2 * p + c + 2 * n + 3 * d = m + 2 * p + (c + 2 * n + 3 * d) := by
  omega

private theorem ungroup_move (m' c n d m b : Nat)
    (h : m' + (c + 2 * n + 3 * d) + 2 * n ≤ m + b) :
    m' + 2 * n + c + 2 * n + 3 * d ≤ m + b := by
  omega

private theorem ungroup_sum (m p s bound : Nat)
    (h : m + (2 * p + s) ≤ bound) : m + 2 * p + s ≤ bound := by
  omega

private theorem y_next (moves moves' peg spend n budget : Nat)
    (hpeg : peg ≤ n)
    (hm : moves' ≤ moves + 2 * peg + spend)
    (hroom : 2 * spend + 4 * n ≤ budget) :
    moves' + spend + 2 * n ≤ moves + budget := by
  have h2 : 2 * peg ≤ 2 * n := Nat.mul_le_mul_left 2 hpeg
  omega

private theorem spend_le (peg spend n budget : Nat)
    (hpeg : peg ≤ n) (hroom : 2 * spend + 4 * n ≤ budget) :
    2 * peg + spend ≤ budget := by
  have h2 : 2 * peg ≤ 2 * n := Nat.mul_le_mul_left 2 hpeg
  omega

private theorem six_of_twelve (n S : Nat) (h : 12 * n ≤ S) : 6 * n ≤ S := by
  omega

private theorem six_of_fortysix (S : Nat) (h : 46 ≤ S) : 6 ≤ S := by
  omega

/-- The projective point on a `yBench` board, read off home 0, the bench, and home 2. -/
private theorem ybench_ids
    (t : Spec.Tier) (b : Ecbs.Board) (px py xP yP zP ys : List Nat)
    (hszH : b.sudo_5Board_4home.size = 8) (hszD : b.sudo_5Board_4held.size = 8)
    (h0 : b.sudo_5Board_4home[0]'(by rw [hszH]; decide) = embed xP)
    (h2 : b.sudo_5Board_4home[2]'(by rw [hszH]; decide) = embed zP)
    (hd1 : b.sudo_5Board_4held[1]'(by rw [hszD]; decide) = false)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (1 : Int))
    (hbench : b.sudo_5Board_5bench = embed ys)
    (htake : ys.take t.n = yP)
    (hproj : ProjOn t b px py) :
    ∃ zQ wInv,
      zQ = zP ∧ allTritList zQ ∧
      xP = fieldMul t.n t.k t.benchlen px zQ ∧
      yP = fieldMul t.n t.k t.benchlen py zQ ∧
      wInv.length = t.n ∧ allTritList wInv ∧
      fieldMul t.n t.k t.benchlen zQ wInv = onePeg t.n := by
  rcases hproj with ⟨xQ, yQ, zQ, lay, _, _, _, _, _, hzQT, hxQ, hyQ, _, hQ0, hlay, wInv, hwL, hwT, hinv⟩
  have hxId : xQ = xP := embed_inj ((hQ0 (by rw [hszH]; decide)).symm.trans h0)
  cases lay with
  | homes =>
    rw [hon] at hlay
    cases hlay.1
  | zBench =>
    have htoZ := hlay.2.1
    rw [hto] at htoZ
    cases htoZ
  | yBench =>
    rcases hlay with ⟨_, htoY, ⟨lane, hlane, _, hpre, _⟩, hd1Y, h2Y, _⟩
    have hyId : yQ = yP := by
      have hbenchQ : b.sudo_5Board_5bench = embed lane := hlane
      have hys : ys = lane := embed_inj (hbench.symm.trans hbenchQ)
      rw [hys] at htake
      exact embed_inj (congrArg embed (hpre.symm.trans htake))
    have hzId : zQ = zP := embed_inj ((h2Y (by rw [hszH]; decide)).symm.trans h2)
    have _hd := hd1Y (by rw [hszD]; decide)
    have _hto := htoY
    exact ⟨zQ, wInv, hzId, hzQT, hxId ▸ hxQ, hyId ▸ hyQ, hwL, hwT, hinv⟩

/-- Cubing a `yBench` point leaves `Z³` on the bench. -/
theorem ybench_zproj
    (t : Spec.Tier) (b bZ : Ecbs.Board)
    (baseX baseY px py xP yP zP ys : List Nat)
    (done : Nat)
    (hAt : FformAt t b baseX baseY px py done)
    (hsh : TierShape t) (hOk : BoardOk t) (sat : TierSat t)
    (hszH : b.sudo_5Board_4home.size = 8) (hszD : b.sudo_5Board_4held.size = 8)
    (h0 : b.sudo_5Board_4home[0]'(by rw [hszH]; decide) = embed xP)
    (h2 : b.sudo_5Board_4home[2]'(by rw [hszH]; decide) = embed zP)
    (hd1 : b.sudo_5Board_4held[1]'(by rw [hszD]; decide) = false)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (1 : Int))
    (hbench : b.sudo_5Board_5bench = embed ys)
    (htake : ys.take t.n = yP)
    (hxL : xP.length = t.n) (hyL : yP.length = t.n) (hzL : zP.length = t.n)
    (hxT : allTritList xP) (hyT : allTritList yP) (hzT : allTritList zP)
    (hH1 : ∀ h : 1 < bZ.sudo_5Board_4held.size, bZ.sudo_5Board_4held[1] = true)
    (hH2 : ∀ h : 2 < bZ.sudo_5Board_4held.size, bZ.sudo_5Board_4held[2] = false)
    (hbon : bZ.sudo_5Board_8bench_on = true)
    (htoZ : bZ.sudo_5Board_8bench_to = (2 : Int))
    (lane : List Nat)
    (hbenchZ : bZ.sudo_5Board_5bench = embed lane)
    (htakeZ : lane.take t.n = fieldCube t.n t.k t.benchlen zP)
    (hzero : ∀ j, t.n ≤ j → ∀ hj : j < lane.length, lane[j] = 0)
    (hhome0 : bZ.sudo_5Board_4home[0]? = some (embed (fieldCube t.n t.k t.benchlen xP)))
    (hhome1 : bZ.sudo_5Board_4home[1]? = some (embed (fieldCube t.n t.k t.benchlen yP))) :
    ProjOn t bZ (fieldCube t.n t.k t.benchlen px) (fieldCube t.n t.k t.benchlen py) := by
  rcases hAt with ⟨_, _, _, _, hpxT, hpyT, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hproj, _⟩
  obtain ⟨zQ, wInv, hzId, hzQT, hxQ, hyQ, hwL, hwT, hinv⟩ :=
    ybench_ids t b px py xP yP zP ys hszH hszD h0 h2 hd1 hon hto hbench htake hproj
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
  have hcube := cube_point_inv t.n t.k t.benchlen px py zQ wInv hOk.n_pos hk hnb
    h2span h3span hpxT hpyT hzQT hwT (by rw [hzId]; exact hzL) hwL hinv
  have hxMul : fieldMul t.n t.k t.benchlen (fieldCube t.n t.k t.benchlen px)
      (fieldCube t.n t.k t.benchlen zP) = fieldCube t.n t.k t.benchlen xP := by
    rw [← hzId, hcube.1, hxQ]
  have hyMul : fieldMul t.n t.k t.benchlen (fieldCube t.n t.k t.benchlen py)
      (fieldCube t.n t.k t.benchlen zP) = fieldCube t.n t.k t.benchlen yP := by
    rw [← hzId, hcube.2.1, hyQ]
  have hzNe : fieldCube t.n t.k t.benchlen zP ≠ List.replicate t.n 0 := by
    rw [← hzId]
    exact hcube.2.2.2.1
  have hzw : fieldMul t.n t.k t.benchlen (fieldCube t.n t.k t.benchlen zP)
      (fieldCube t.n t.k t.benchlen wInv) = onePeg t.n := by
    rw [← hzId]
    exact hcube.2.2.1
  have hxLen := fieldCube_length t.n t.k t.benchlen xP hnb
  have hyLen := fieldCube_length t.n t.k t.benchlen yP hnb
  have hzLen := fieldCube_length t.n t.k t.benchlen zP hnb
  have hxTri := fieldCube_trits t.n t.k t.benchlen xP hxT h3span hsh.k_le
  have hyTri := fieldCube_trits t.n t.k t.benchlen yP hyT h3span hsh.k_le
  have hzTri := fieldCube_trits t.n t.k t.benchlen zP hzT h3span hsh.k_le
  have hxHome : ∀ h : 0 < bZ.sudo_5Board_4home.size,
      bZ.sudo_5Board_4home[0] = embed
        (fieldMul t.n t.k t.benchlen (fieldCube t.n t.k t.benchlen px)
          (fieldCube t.n t.k t.benchlen zP)) := by
    intro h
    exact (read_cell _ 0 _ hhome0 h).trans (congrArg embed hxMul.symm)
  have hyHome : ∀ h : 1 < bZ.sudo_5Board_4home.size,
      bZ.sudo_5Board_4home[1] = embed
        (fieldMul t.n t.k t.benchlen (fieldCube t.n t.k t.benchlen py)
          (fieldCube t.n t.k t.benchlen zP)) := by
    intro h
    exact (read_cell _ 1 _ hhome1 h).trans (congrArg embed hyMul.symm)
  have hnle : t.n ≤ lane.length := by
    have hlenT : (lane.take t.n).length = min t.n lane.length := List.length_take _ _
    rw [htakeZ, fieldCube_length t.n t.k t.benchlen zP hnb] at hlenT
    exact hlenT.symm ▸ Nat.min_le_right t.n lane.length
  exact ⟨fieldMul t.n t.k t.benchlen (fieldCube t.n t.k t.benchlen px)
      (fieldCube t.n t.k t.benchlen zP),
    fieldMul t.n t.k t.benchlen (fieldCube t.n t.k t.benchlen py)
      (fieldCube t.n t.k t.benchlen zP),
    fieldCube t.n t.k t.benchlen zP, .zBench,
    by rw [hxMul]; exact hxLen, by rw [hyMul]; exact hyLen, hzLen,
    by rw [hxMul]; exact hxTri, by rw [hyMul]; exact hyTri, hzTri,
    rfl, rfl, hzNe, hxHome,
    ⟨hbon, htoZ, ⟨lane, hbenchZ, hnle, htakeZ, hzero⟩, hyHome, hH1, hH2⟩,
    fieldCube t.n t.k t.benchlen wInv, hcube.2.2.2.2.1, hcube.2.2.2.2.2, hzw⟩

/-- `yBench`, colour still unread. The board `frobenius_point` leaves is the
    next `FformAt` in the `zBench` layout, and slot 1 has grown by exactly 3. -/
theorem ybench_zero_cell_at
    (t : Spec.Tier) (b : Ecbs.Board)
    (baseX baseY px py xP yP zP ys : List Nat) (i : Nat)
    (hAt : FformAt t b baseX baseY px py i)
    (hsh : TierShape t) (hOk : BoardOk t) (sat : TierSat t)
    (tw : TierWalk t)
    (hstep : 8 * stepBudget t.n t.benchlen ≤
      walkCharge t + (6 * t.benchlen + 2 * t.n))
    (h12 : 12 * t.n ≤ cellSlideCharge t + slideCharge t.n)
    (h46 : 46 ≤ cellCtrlCharge t + 4)
    (hxL : xP.length = t.n) (hyL : yP.length = t.n) (hzL : zP.length = t.n)
    (hxT : allTritList xP) (hyT : allTritList yP) (hzT : allTritList zP)
    (hszH : b.sudo_5Board_4home.size = 8) (hszD : b.sudo_5Board_4held.size = 8)
    (h0 : b.sudo_5Board_4home[0]'(by rw [hszH]; decide) = embed xP)
    (h2 : b.sudo_5Board_4home[2]'(by rw [hszH]; decide) = embed zP)
    (hd0 : b.sudo_5Board_4held[0]'(by rw [hszD]; decide) = true)
    (hd1 : b.sudo_5Board_4held[1]'(by rw [hszD]; decide) = false)
    (hd2 : b.sudo_5Board_4held[2]'(by rw [hszD]; decide) = true)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (1 : Int))
    (hbench : b.sudo_5Board_5bench = embed ys)
    (htake : ys.take t.n = yP)
    (hnle : t.n ≤ ys.length)
    (hzero : ∀ j, t.n ≤ j → ∀ hj : j < ys.length, ys[j] = 0)
    (hfitY : FitsLen ys.length)
    (hpos : i < t.cells) :
    ∃ bL bZ,
      Ecbs.marker_lift b = .ok bL ∧
      Ecbs.frobenius_point bL = .ok bZ ∧
      FformAt t bZ baseX baseY
        (fieldCube t.n t.k t.benchlen px) (fieldCube t.n t.k t.benchlen py) (i + 1) := by
  have hAt0 := hAt
  rcases hAt with ⟨hmk, _, hpx, hpy, hpxT, hpyT, hbx, hby, hbxT, hbyT, _, _, _, _, _, _,
      _, hscript, _, _, _, hrest⟩
  rcases hrest with ⟨moves0, slides0, ctrl0, mark, mx0, pk, peakS, hole, c10, c00,
      hmv0, hsl0, hc00, hmark, hmx0, hpk, hstrict, hhole, hops, hop1?, hop0?,
      hfitCtrl, hc1, hfitMul, hfitMv, hfitSl, hmvLe, hslLe, hcLe⟩
  have hpegN := peg_le ys t.n hnle
  obtain ⟨hpeg, hfitMvS, hfitSlS, hRoom, hSl⟩ :=
    y_room moves0 slides0 (pegCount (ys.take t.n)) t.n
      (cubeCharge t.n t.benchlen) (t.benchlen - t.n) (slideCharge t.n)
      hpegN hfitMv hfitSl
  have hOps := cube_slack_cell c10 t.cells i hc1 hpos
  have hop1 := by
    have h := hop1?
    exact h
  obtain ⟨bL, bZ, hlift, hfrob, hmon, hbon, htoZ, hlane⟩ :=
    frobenius_fform_ybench t b xP yP zP ys hsh hOk sat hscript hAt0.2.1
      hxL hyL hzL hxT hyT hzT hszH hszD h0 h2 hd0 hd1 hd2 hmk hon hto hbench htake
      (Nat.lt_of_lt_of_le hOk.n_pos hnle) hnle hzero
      moves0 slides0 ctrl0 mark mx0 pk peakS hole c10
      hmv0 hsl0 hc00 hmark hmx0 hpk hstrict hhole hops
      (by
        have hsz : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size := hops
        have heq := Array.getElem?_eq_getElem hsz
        rw [hop1?] at heq
        exact Option.some.inj heq.symm)
      hfitCtrl hOps hpeg hfitMvS hfitSlS hRoom hSl
      (geomFit t.n t.benchlen t.n hsh.n_small hsh.small.2.2.2 (smallCap t.n t.benchlen).1)
      hfitY
  rcases hlane with ⟨lane, hbenchZ, htakeZ, hzeroZ, hhome0, hhome1⟩
  have hfr := ybench_zero_frame t b bL bZ baseX baseY px py xP yP zP ys i hAt0
    hsh hOk sat hxL hyL hzL hxT hyT hzT hszH hszD h0 h2 hd0 hd1 hd2 hon hto hbench
    htake hnle hzero hfitY hpos hlift hfrob
  obtain ⟨moves, slides, ctrl, mx, c1, c0, moves', slides', pk', peakS', hole',
      hmv, hsl, hc0, hmx, hopIn, hop0in, hmonC, hH0, hmv', hsl', hctrl', hmark', hmx',
      hpk', hst', hhole', hsz1, hop1', hop0', hleM, hleS⟩ :=
    ybench_zero_counts t b bL bZ baseX baseY px py xP yP zP ys i hAt0
      hsh hOk sat hxL hyL hzL hxT hyT hzT hszH hszD h0 h2 hd0 hd1 hd2 hon hto
      hbench htake hnle hzero hfitY hpos hlift hfrob
  have hmvN : moves = moves0 :=
    Int.ofNat.inj (by simpa [ofNat_eq_natCast] using hmv.symm.trans hmv0)
  have hslN : slides = slides0 :=
    Int.ofNat.inj (by simpa [ofNat_eq_natCast] using hsl.symm.trans hsl0)
  have hcN : ctrl = ctrl0 :=
    Int.ofNat.inj (by simpa [ofNat_eq_natCast] using hc0.symm.trans hc00)
  have hmxN : mx = mx0 :=
    Int.ofNat.inj (by simpa [ofNat_eq_natCast] using hmx.symm.trans hmx0)
  have hc1N : c1 = c10 := by
    have h := Option.some.inj (hopIn.symm.trans hop1?)
    exact Int.ofNat.inj (by simpa [ofNat_eq_natCast] using h)
  have hc0N : c0 = c00 := by
    have h := Option.some.inj (hop0in.symm.trans hop0?)
    exact Int.ofNat.inj (by simpa [ofNat_eq_natCast] using h)
  let o := ybench_open t b bL bZ baseX baseY px py xP yP zP ys i hAt0
    hsh hOk sat hxL hyL hzL hxT hyT hzT hszH hszD h0 h2 hd0 hd1 hd2 hon hto hbench
    htake hnle hzero hfitY hpos hlift hfrob
  have hH1 : ∀ h : 1 < bZ.sudo_5Board_4held.size, bZ.sudo_5Board_4held[1] = true := by
    intro h
    have hheld := congrArg (fun brd => brd.sudo_5Board_4held) o.hZ
    exact (at_eq hheld h (by rw [bottomFlag_szD o.pack.seen.a zP]; decide)).trans
      (bottomFlag_held1 o.pack.seen.a zP)
  have hH2 : ∀ h : 2 < bZ.sudo_5Board_4held.size, bZ.sudo_5Board_4held[2] = false := by
    intro h
    have hheld := congrArg (fun brd => brd.sudo_5Board_4held) o.hZ
    exact (at_eq hheld h (by rw [bottomFlag_szD o.pack.seen.a zP]; decide)).trans
      (bottomFlag_held2 o.pack.seen.a zP)
  have hp := ybench_zproj t b bZ baseX baseY px py xP yP zP ys i hAt0 hsh hOk sat
    hszH hszD h0 h2 hd1 hon hto hbench htake hxL hyL hzL hxT hyT hzT
    hH1 hH2 hbon htoZ lane hbenchZ htakeZ hzeroZ hhome0 hhome1
  have hpair := cube_slack_next c10 t.cells i hc1 hpos
  have hc1' : FitsLen ((c1 + 3) + 3 * (t.cells - (i + 1))) := by
    rw [hc1N]
    exact hpair
  have hc0' : FitsLen (c0 + 13 * (t.cells - (i + 1))) := by
    rw [hc0N]
    simpa [Nat.add_zero] using mul_slack_next c00 0 t.cells i hfitMul (by omega) hpos
  have hfitC : FitsLen ((ctrl + 6) + 6) := by
    refine FitsLen.of_le (comb_ctrl_fit t ctrl i (ctrl + 6) tw (by simpa [hcN] using hcLe)
      hpos rfl h46) ?_
    omega
  let spend := cubeCharge t.n t.benchlen + 2 * t.n + 3 * (t.benchlen - t.n)
  have hspend : moves' + spend + 2 * t.n ≤ moves + 8 * stepBudget t.n t.benchlen := by
    have hm : moves' ≤ moves + 2 * pegCount (ys.take t.n) + spend := by
      rw [← group_spend]
      exact hleM
    exact y_next moves moves' (pegCount (ys.take t.n)) spend t.n
      (8 * stepBudget t.n t.benchlen) hpegN hm (ybench_move_room t.n t.benchlen)
  have hfitM' : FitsLen (moves' + 2 * t.n + cubeCharge t.n t.benchlen + 2 * t.n +
      3 * (t.benchlen - t.n)) := by
    refine FitsLen.of_le (cell_big_room t moves i tw (by simpa [hmvN] using hmvLe) hpos hstep) ?_
    exact ungroup_move _ _ _ _ _ _ hspend
  have hfitS' : FitsLen (slides' + 2 * t.n + slideCharge t.n) := by
    refine FitsLen.of_le (cell_slide_room t slides i tw (by simpa [hslN] using hslLe) hpos h12) ?_
    rw [slideCharge]
    omega
  have hB : 2 * pegCount (ys.take t.n) + spend ≤
      walkCharge t + (6 * t.benchlen + 2 * t.n) :=
    Nat.le_trans (spend_le (pegCount (ys.take t.n)) spend t.n
      (8 * stepBudget t.n t.benchlen) hpegN (ybench_move_room t.n t.benchlen)) hstep
  have hsumM := ledger_next i (walkCharge t + (6 * t.benchlen + 2 * t.n))
    (2 * pegCount (ys.take t.n) + spend) moves (by simpa [hmvN] using hmvLe) hB
  have hmvLe' : moves' ≤ (i + 1) * (walkCharge t + (6 * t.benchlen + 2 * t.n)) := by
    have hm : moves' ≤ moves + 2 * pegCount (ys.take t.n) + spend := by
      rw [← group_spend]
      exact hleM
    exact Nat.le_trans hm (ungroup_sum _ _ _ _ hsumM)
  have h6n := six_of_twelve t.n (cellSlideCharge t + slideCharge t.n) h12
  have hsumS := ledger_next i (cellSlideCharge t + slideCharge t.n) (6 * t.n) slides
    (by simpa [hslN] using hslLe) h6n
  have hslLe' : slides' ≤ (i + 1) * (cellSlideCharge t + slideCharge t.n) :=
    Nat.le_trans hleS hsumS
  have h6 := six_of_fortysix (cellCtrlCharge t + 4) h46
  have hcLe' := ledger_next i (cellCtrlCharge t + 4) 6 ctrl (by simpa [hcN] using hcLe) h6
  have hnb : t.n ≤ t.benchlen := tw.nLe
  have h3span : 3 * (t.n - 1) < t.benchlen := by
    have hspan : 3 * (t.n - 1) + t.combgap < t.benchlen := sat.cube_span
    omega
  have hpxC := fieldCube_length t.n t.k t.benchlen px hnb
  have hpyC := fieldCube_length t.n t.k t.benchlen py hnb
  have hpxCT := fieldCube_trits t.n t.k t.benchlen px hpxT h3span hsh.k_le
  have hpyCT := fieldCube_trits t.n t.k t.benchlen py hpyT h3span hsh.k_le
  have hops0 : 0 < bZ.sudo_5Board_4cost.sudo_5Costs_3ops.size :=
    Nat.lt_trans Nat.zero_lt_one hsz1
  have hop0e : bZ.sudo_5Board_4cost.sudo_5Costs_3ops[0]'hops0 = Int.ofNat c0 := by
    have h := hop0'
    rw [Array.getElem?_eq_getElem hops0] at h
    exact Option.some.inj h
  have ch : TailCharge bZ moves' slides' (ctrl + 6) 2
      (max (max (max mx 1) 2) 3) pk' peakS' hole' c0 := {
    movesEq := hmv'
    slidesEq := hsl'
    ctrlEq := hctrl'
    markEq := hmark'
    mxEq := by simpa [hmxN] using hmx'
    peakEq := hpk'
    strictEq := hst'
    holeEq := hhole'
    opsSz := hops0
    ops0 := hop0e
  }
  have hAt' := fform_at_pack t bZ baseX baseY
    (fieldCube t.n t.k t.benchlen px) (fieldCube t.n t.k t.benchlen py) (i + 1)
    hmonC hpxC hpyC hpxCT hpyCT hbx hby hbxT hbyT hH0 hscript hfr hp
    moves' slides' (ctrl + 6) 2 (max (max (max mx 1) 2) 3) pk' peakS' hole'
    (c1 + 3) c0 ch hsz1 hop1' hfitC hc1' hc0' hfitM' hfitS' hmvLe' hslLe' hcLe'
  exact ⟨bL, bZ, hlift, hfrob, hAt'⟩

end EcbsLink2.Link2
