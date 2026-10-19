/-
  The comb a live cell reads. `homes_layout_comb`, `ybench_layout_comb`, and
  `zbench_layout_comb` each start from `FformAt` in that layout. Each one
  returns the frame, the counters, ops slot 0, the marker at 2, and the
  cubed homes. The y and z proofs reuse `ybench_zero_frame`,
  `ybench_zero_counts`, and the zBench copies.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FformZZero
import EcbsLink2.Link2.FformZeroAt

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open Ecbs
open EcbsLink2.Spec

attribute [local irreducible] fieldCube fieldMul Ecbs.frobenius_point Ecbs.marker_lift
  bottomFlag

private theorem drop_front (moves n cube d : Nat)
    (h : FitsLen (moves + 2 * n + cube + 2 * n + 3 * d)) :
    FitsLen (moves + cube + 2 * n + 3 * d) :=
  FitsLen.of_le h (by omega)

private theorem drop_slide (slides n s : Nat)
    (h : FitsLen (slides + 2 * n + s)) : FitsLen (slides + s) :=
  FitsLen.of_le h (by omega)

private theorem cube_le_settle (out m n cube d : Nat)
    (h : out ≤ m + cube + 2 * n + 3 * d) :
    out ≤ m + 2 * n + cube + 2 * n + 3 * d := by
  omega

private theorem four_to_six (out s n : Nat) (h : out ≤ s + 4 * n) :
    out ≤ s + 6 * n := by
  omega

private theorem peg_le (ys : List Nat) (n : Nat) (hn : n ≤ ys.length) :
    pegCount (ys.take n) ≤ n := by
  have hlen : (ys.take n).length = n := by
    rw [List.length_take, Nat.min_eq_left hn]
  have hp := pegCount_le (ys.take n)
  rw [hlen] at hp
  exact hp

private theorem peg_bound (out m peg cube n d : Nat) (hpeg : peg ≤ n)
    (h : out ≤ m + 2 * peg + cube + 2 * n + 3 * d) :
    out ≤ m + 2 * n + cube + 2 * n + 3 * d := by
  have h2 : 2 * peg ≤ 2 * n := Nat.mul_le_mul_left 2 hpeg
  omega

private theorem bench_room (moves slides peg n cube d slide : Nat)
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

private theorem slot1_nat (ops : Array Int) (c : Nat)
    (hops : 1 < ops.size) (hop : ops[1]? = some (c : Int)) :
    ops[1]'hops = (c : Int) := by
  have heq := Array.getElem?_eq_getElem hops
  rw [hop] at heq
  exact Option.some.inj heq.symm

private theorem slot0_nat (ops : Array Int) (c : Nat)
    (hops : 0 < ops.size) (hop : ops[0]? = some (Int.ofNat c)) :
    ops[0]'hops = Int.ofNat c := by
  have heq := Array.getElem?_eq_getElem hops
  rw [hop] at heq
  exact Option.some.inj heq.symm

/-- Homes layout. The comb is `FrameAt`, the counters cover a bench settle,
    slot 0 is the multiply counter the cell entered with, the marker is 2,
    and homes 0 and 1 are the cubes. -/
theorem homes_layout_comb
    (t : Spec.Tier) (b : Ecbs.Board)
    (baseX baseY px py xP yP zP : List Nat) (done : Nat)
    (hAt : FformAt t b baseX baseY px py done)
    (hsh : TierShape t) (hOk : BoardOk t) (sat : TierSat t)
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
    (hpos : done < t.cells) :
    ∃ (bL bZ : Ecbs.Board)
      (moves slides ctrl c0 moves' slides' : Nat) (lane : List Nat),
      Ecbs.marker_lift b = .ok bL ∧
      Ecbs.frobenius_point bL = .ok bZ ∧
      b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves ∧
      b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides ∧
      b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl ∧
      b.sudo_5Board_4cost.sudo_5Costs_3ops[0]? = some (Int.ofNat c0) ∧
      FrameAt bZ t baseX baseY ∧
      bZ.sudo_5Board_9marker_on = true ∧
      bZ.sudo_5Board_6marker = Int.ofNat 2 ∧
      bZ.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (ctrl + 6) ∧
      bZ.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves' ∧
      bZ.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides' ∧
      bZ.sudo_5Board_4cost.sudo_5Costs_3ops[0]? = some (Int.ofNat c0) ∧
      moves' ≤ moves + 2 * t.n + cubeCharge t.n t.benchlen + 2 * t.n +
        3 * (t.benchlen - t.n) ∧
      slides' ≤ slides + 6 * t.n ∧
      bZ.sudo_5Board_8bench_on = true ∧
      bZ.sudo_5Board_8bench_to = (2 : Int) ∧
      bZ.sudo_5Board_5bench = embed lane ∧
      lane.take t.n = fieldCube t.n t.k t.benchlen zP ∧
      (∀ j, t.n ≤ j → ∀ hj : j < lane.length, lane[j] = 0) ∧
      bZ.sudo_5Board_4home[0]? = some (embed (fieldCube t.n t.k t.benchlen xP)) ∧
      bZ.sudo_5Board_4home[1]? = some (embed (fieldCube t.n t.k t.benchlen yP)) := by
  have hAt0 := hAt
  rcases hAt with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hscript, _, _, _, hrest⟩
  rcases hrest with ⟨moves, slides, ctrl, mark, mx, pk, peakS, hole, c1, c0,
      hmv, hsl, hcCtrl, hmark, hmx, hpk, hstrict, hhole, hops, hop1?, hop0?,
      hfitCtrl, hc1, _, hfitMv, hfitSl, _, _, _⟩
  have hOps := cube_slack_cell c1 t.cells done hc1 hpos
  have hop1 := slot1_nat _ c1 hops hop1?
  have hMul : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size :=
    Nat.lt_trans Nat.zero_lt_one hops
  have hopMul := slot0_nat _ c0 hMul hop0?
  have hRoom := drop_front moves t.n (cubeCharge t.n t.benchlen) (t.benchlen - t.n) hfitMv
  have hSl := drop_slide slides t.n (slideCharge t.n) hfitSl
  obtain ⟨bL, bZ, hlift, hfrob, hmon, hbon, hto, hlane⟩ :=
    frobenius_fform_homes t b baseX baseY px py xP yP zP done hAt0 hsh hOk sat hscript
      hxL hyL hzL hxT hyT hzT hszH hszD h0 h1 h2 hd0 hd1 hd2 hoff
      moves slides ctrl mark mx pk peakS hole c1
      hmv hsl hcCtrl hmark hmx hpk hstrict hhole hops hop1
      hfitCtrl hOps hRoom hSl
  obtain ⟨bLF, a, hliftF, hflag, hfr⟩ :=
    zero_comb_frame t b baseX baseY px py xP yP zP done hAt0 hsh hOk sat hscript
      hxL hyL hzL hxT hyT hzT hszH hszD h0 h1 h2 hd0 hd1 hd2 hoff
      moves slides ctrl mark mx pk peakS hole c1
      hmv hsl hcCtrl hmark hmx hpk hstrict hhole hops hop1
      hfitCtrl hOps hRoom hSl
  have hLF : bLF = bL := Except.ok.inj (hliftF.symm.trans hlift)
  have hflagL : Ecbs.frobenius_point bL = .ok (bottomFlag a zP) :=
    (congrArg Ecbs.frobenius_point hLF).symm.trans hflag
  have hZ : bZ = bottomFlag a zP := Except.ok.inj (hfrob.symm.trans hflagL)
  have hfrZ := frame_cast t (bottomFlag a zP) bZ baseX baseY hZ hfr
  have hmarkZ :=
    (congrArg (fun brd => brd.sudo_5Board_6marker) hZ).trans (bottomFlag_mark a zP)
  have hctrlRaw :=
    (congrArg (fun brd => brd.sudo_5Board_4cost.sudo_5Costs_4ctrl) hZ).trans
      (bottomFlag_ctrl a zP)
  have hnat : (ctrl + 1) + 5 = ctrl + 6 := by omega
  have hctrlZ : bZ.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (ctrl + 6) := by
    rw [hnat] at hctrlRaw
    exact hctrlRaw
  have hmvZ :=
    (congrArg (fun brd => brd.sudo_5Board_4cost.sudo_5Costs_5moves) hZ).trans
      (bottomFlag_moves a zP)
  have hslZ :=
    (congrArg (fun brd => brd.sudo_5Board_4cost.sudo_5Costs_6slides) hZ).trans
      (bottomFlag_slides a zP)
  have hleM := cube_le_settle _ moves t.n (cubeCharge t.n t.benchlen)
    (t.benchlen - t.n) (comb_moves_le a zP)
  have hleS := four_to_six _ slides t.n (comb_slides_le a)
  obtain ⟨bL3, bZ3, hlift3, hfrob3, hop0⟩ :=
    comb_ops0_board t b baseX baseY px py xP yP zP done c0 hAt0 hsh hOk sat hscript
      hxL hyL hzL hxT hyT hzT hszH hszD h0 h1 h2 hd0 hd1 hd2 hoff
      moves slides ctrl mark mx pk peakS hole c1
      hmv hsl hcCtrl hmark hmx hpk hstrict hhole hops hop1 hMul hopMul
      hfitCtrl hOps hRoom hSl
  have hL3 : bL3 = bL := Except.ok.inj (hlift3.symm.trans hlift)
  have hf3 : Ecbs.frobenius_point bL = .ok bZ3 :=
    (congrArg Ecbs.frobenius_point hL3).symm.trans hfrob3
  have hZZ : bZ = bZ3 := Except.ok.inj (hfrob.symm.trans hf3)
  have hop0Z :=
    (congrArg (fun brd => brd.sudo_5Board_4cost.sudo_5Costs_3ops[0]?) hZZ).trans hop0
  rcases hlane with ⟨lane, hbench, htake, hzero, hhome0, hhome1⟩
  exact ⟨bL, bZ, moves, slides, ctrl, c0,
    cubeMoves (upMv2 a + 2 * pegCount ((upLane t.n t.k t.benchlen yP).take t.n))
      zP t.n t.k t.benchlen,
    upSl a + 2 * pegCount ((upLane t.n t.k t.benchlen yP).take t.n),
    lane, hlift, hfrob, hmv, hsl, hcCtrl, hop0?, hfrZ, hmon, hmarkZ, hctrlZ,
    hmvZ, hslZ, hop0Z, hleM, hleS, hbon, hto, hbench, htake, hzero, hhome0, hhome1⟩

/-- `yBench`. The frame and the counters are `ybench_zero_frame` and
    `ybench_zero_counts`. The cubed homes are the same comb. -/
theorem ybench_layout_comb
    (t : Spec.Tier) (b : Ecbs.Board)
    (baseX baseY px py xP yP zP ys : List Nat) (done : Nat)
    (hAt : FformAt t b baseX baseY px py done)
    (hsh : TierShape t) (hOk : BoardOk t) (sat : TierSat t)
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
    (hpos : done < t.cells) :
    ∃ (bL bZ : Ecbs.Board)
      (moves slides ctrl c0 moves' slides' : Nat) (lane : List Nat),
      Ecbs.marker_lift b = .ok bL ∧
      Ecbs.frobenius_point bL = .ok bZ ∧
      b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves ∧
      b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides ∧
      b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl ∧
      b.sudo_5Board_4cost.sudo_5Costs_3ops[0]? = some (Int.ofNat c0) ∧
      FrameAt bZ t baseX baseY ∧
      bZ.sudo_5Board_9marker_on = true ∧
      bZ.sudo_5Board_6marker = Int.ofNat 2 ∧
      bZ.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (ctrl + 6) ∧
      bZ.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves' ∧
      bZ.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides' ∧
      bZ.sudo_5Board_4cost.sudo_5Costs_3ops[0]? = some (Int.ofNat c0) ∧
      moves' ≤ moves + 2 * t.n + cubeCharge t.n t.benchlen + 2 * t.n +
        3 * (t.benchlen - t.n) ∧
      slides' ≤ slides + 6 * t.n ∧
      bZ.sudo_5Board_8bench_on = true ∧
      bZ.sudo_5Board_8bench_to = (2 : Int) ∧
      bZ.sudo_5Board_5bench = embed lane ∧
      lane.take t.n = fieldCube t.n t.k t.benchlen zP ∧
      (∀ j, t.n ≤ j → ∀ hj : j < lane.length, lane[j] = 0) ∧
      bZ.sudo_5Board_4home[0]? = some (embed (fieldCube t.n t.k t.benchlen xP)) ∧
      bZ.sudo_5Board_4home[1]? = some (embed (fieldCube t.n t.k t.benchlen yP)) := by
  have hAt0 := hAt
  rcases hAt with ⟨hmk, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hscript, _, _, _, hrest⟩
  rcases hrest with ⟨moves0, slides0, ctrl0, mark, mx0, pk, peakS, hole, c10, c00,
      hmv0, hsl0, hc00, hmark, hmx0, hpk, hstrict, hhole, hops, hop1?, hop0?,
      hfitCtrl, hc1, _, hfitMv, hfitSl, _, _, _⟩
  have hpegN := peg_le ys t.n hnle
  obtain ⟨hpeg, hfitMvS, hfitSlS, hRoom, hSl⟩ :=
    bench_room moves0 slides0 (pegCount (ys.take t.n)) t.n
      (cubeCharge t.n t.benchlen) (t.benchlen - t.n) (slideCharge t.n)
      hpegN hfitMv hfitSl
  have hOps := cube_slack_cell c10 t.cells done hc1 hpos
  obtain ⟨bL, bZ, hlift, hfrob, hmon, hbon, htoZ, hlane⟩ :=
    frobenius_fform_ybench t b xP yP zP ys hsh hOk sat hscript hAt0.2.1
      hxL hyL hzL hxT hyT hzT hszH hszD h0 h2 hd0 hd1 hd2 hmk hon hto hbench htake
      (Nat.lt_of_lt_of_le hOk.n_pos hnle) hnle hzero
      moves0 slides0 ctrl0 mark mx0 pk peakS hole c10
      hmv0 hsl0 hc00 hmark hmx0 hpk hstrict hhole hops
      (slot1_nat _ c10 hops hop1?)
      hfitCtrl hOps hpeg hfitMvS hfitSlS hRoom hSl
      (geomFit t.n t.benchlen t.n hsh.n_small hsh.small.2.2.2 (smallCap t.n t.benchlen).1)
      hfitY
  have hfr := ybench_zero_frame t b bL bZ baseX baseY px py xP yP zP ys done hAt0
    hsh hOk sat hxL hyL hzL hxT hyT hzT hszH hszD h0 h2 hd0 hd1 hd2 hon hto hbench
    htake hnle hzero hfitY hpos hlift hfrob
  obtain ⟨moves, slides, ctrl, _, _, c0, moves', slides', _, _, _,
      hmv, hsl, hc0, _, _, hop0in, _, _, hmv', hsl', hctrl', hmark', _,
      _, _, _, _, _, hop0', hleM, hleS⟩ :=
    ybench_zero_counts t b bL bZ baseX baseY px py xP yP zP ys done hAt0
      hsh hOk sat hxL hyL hzL hxT hyT hzT hszH hszD h0 h2 hd0 hd1 hd2 hon hto
      hbench htake hnle hzero hfitY hpos hlift hfrob
  have hleM' := peg_bound moves' moves (pegCount (ys.take t.n))
    (cubeCharge t.n t.benchlen) t.n (t.benchlen - t.n) hpegN hleM
  rcases hlane with ⟨lane, hbenchZ, htakeZ, hzeroZ, hhome0, hhome1⟩
  exact ⟨bL, bZ, moves, slides, ctrl, c0, moves', slides', lane,
    hlift, hfrob, hmv, hsl, hc0, hop0in, hfr, hmon, hmark', hctrl', hmv', hsl',
    hop0', hleM', hleS, hbon, htoZ, hbenchZ, htakeZ, hzeroZ, hhome0, hhome1⟩

/-- `zBench`. The same frame, counters, and cubed homes, with the settle
    aimed at home 2. -/
theorem zbench_layout_comb
    (t : Spec.Tier) (b : Ecbs.Board)
    (baseX baseY px py xP yP zP ys : List Nat) (done : Nat)
    (hAt : FformAt t b baseX baseY px py done)
    (hsh : TierShape t) (hOk : BoardOk t) (sat : TierSat t)
    (hxL : xP.length = t.n) (hyL : yP.length = t.n) (hzL : zP.length = t.n)
    (hxT : allTritList xP) (hyT : allTritList yP) (hzT : allTritList zP)
    (hszH : b.sudo_5Board_4home.size = 8) (hszD : b.sudo_5Board_4held.size = 8)
    (h0 : b.sudo_5Board_4home[0]'(by rw [hszH]; decide) = embed xP)
    (h1 : b.sudo_5Board_4home[1]'(by rw [hszH]; decide) = embed yP)
    (hd0 : b.sudo_5Board_4held[0]'(by rw [hszD]; decide) = true)
    (hd1 : b.sudo_5Board_4held[1]'(by rw [hszD]; decide) = true)
    (hd2 : b.sudo_5Board_4held[2]'(by rw [hszD]; decide) = false)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (2 : Int))
    (hbench : b.sudo_5Board_5bench = embed ys)
    (htake : ys.take t.n = zP)
    (hnle : t.n ≤ ys.length)
    (hzero : ∀ j, t.n ≤ j → ∀ hj : j < ys.length, ys[j] = 0)
    (hfitY : FitsLen ys.length)
    (hpos : done < t.cells) :
    ∃ (bL bZ : Ecbs.Board)
      (moves slides ctrl c0 moves' slides' : Nat) (lane : List Nat),
      Ecbs.marker_lift b = .ok bL ∧
      Ecbs.frobenius_point bL = .ok bZ ∧
      b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves ∧
      b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides ∧
      b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl ∧
      b.sudo_5Board_4cost.sudo_5Costs_3ops[0]? = some (Int.ofNat c0) ∧
      FrameAt bZ t baseX baseY ∧
      bZ.sudo_5Board_9marker_on = true ∧
      bZ.sudo_5Board_6marker = Int.ofNat 2 ∧
      bZ.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (ctrl + 6) ∧
      bZ.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves' ∧
      bZ.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides' ∧
      bZ.sudo_5Board_4cost.sudo_5Costs_3ops[0]? = some (Int.ofNat c0) ∧
      moves' ≤ moves + 2 * t.n + cubeCharge t.n t.benchlen + 2 * t.n +
        3 * (t.benchlen - t.n) ∧
      slides' ≤ slides + 6 * t.n ∧
      bZ.sudo_5Board_8bench_on = true ∧
      bZ.sudo_5Board_8bench_to = (2 : Int) ∧
      bZ.sudo_5Board_5bench = embed lane ∧
      lane.take t.n = fieldCube t.n t.k t.benchlen zP ∧
      (∀ j, t.n ≤ j → ∀ hj : j < lane.length, lane[j] = 0) ∧
      bZ.sudo_5Board_4home[0]? = some (embed (fieldCube t.n t.k t.benchlen xP)) ∧
      bZ.sudo_5Board_4home[1]? = some (embed (fieldCube t.n t.k t.benchlen yP)) := by
  have hAt0 := hAt
  rcases hAt with ⟨hmk, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hscript, _, _, _, hrest⟩
  rcases hrest with ⟨moves0, slides0, ctrl0, mark, mx0, pk, peakS, hole, c10, c00,
      hmv0, hsl0, hc00, hmark, hmx0, hpk, hstrict, hhole, hops, hop1?, hop0?,
      hfitCtrl, hc1, _, hfitMv, hfitSl, _, _, _⟩
  have hpegN := peg_le ys t.n hnle
  obtain ⟨hpeg, hfitMvS, hfitSlS, hRoom, hSl⟩ :=
    bench_room moves0 slides0 (pegCount (ys.take t.n)) t.n
      (cubeCharge t.n t.benchlen) (t.benchlen - t.n) (slideCharge t.n)
      hpegN hfitMv hfitSl
  have hOps := cube_slack_cell c10 t.cells done hc1 hpos
  obtain ⟨bL, bZ, hlift, hfrob, hmon, hbon, htoZ, hlane⟩ :=
    frobenius_fform_zbench t b xP yP zP ys hsh hOk sat hscript hAt0.2.1
      hxL hyL hzL hxT hyT hzT hszH hszD h0 h1 hd0 hd1 hd2 hmk hon hto hbench htake
      (Nat.lt_of_lt_of_le hOk.n_pos hnle) hnle hzero
      moves0 slides0 ctrl0 mark mx0 pk peakS hole c10
      hmv0 hsl0 hc00 hmark hmx0 hpk hstrict hhole hops
      (slot1_nat _ c10 hops hop1?)
      hfitCtrl hOps hpeg hfitMvS hfitSlS hRoom hSl
      (geomFit t.n t.benchlen t.n hsh.n_small hsh.small.2.2.2 (smallCap t.n t.benchlen).1)
      hfitY
  have hfr := zbench_zero_frame t b bL bZ baseX baseY px py xP yP zP ys done hAt0
    hsh hOk sat hxL hyL hzL hxT hyT hzT hszH hszD h0 h1 hd0 hd1 hd2 hon hto hbench
    htake hnle hzero hfitY hpos hlift hfrob
  obtain ⟨moves, slides, ctrl, _, _, c0, moves', slides', _, _, _,
      hmv, hsl, hc0, _, _, hop0in, _, _, hmv', hsl', hctrl', hmark', _,
      _, _, _, _, _, hop0', hleM, hleS⟩ :=
    zbench_zero_counts t b bL bZ baseX baseY px py xP yP zP ys done hAt0
      hsh hOk sat hxL hyL hzL hxT hyT hzT hszH hszD h0 h1 hd0 hd1 hd2 hon hto
      hbench htake hnle hzero hfitY hpos hlift hfrob
  have hleM' := peg_bound moves' moves (pegCount (ys.take t.n))
    (cubeCharge t.n t.benchlen) t.n (t.benchlen - t.n) hpegN hleM
  rcases hlane with ⟨lane, hbenchZ, htakeZ, hzeroZ, hhome0, hhome1⟩
  exact ⟨bL, bZ, moves, slides, ctrl, c0, moves', slides', lane,
    hlift, hfrob, hmv, hsl, hc0, hop0in, hfr, hmon, hmark', hctrl', hmv', hsl',
    hop0', hleM', hleS, hbon, htoZ, hbenchZ, htakeZ, hzeroZ, hhome0, hhome1⟩

end EcbsLink2.Link2
