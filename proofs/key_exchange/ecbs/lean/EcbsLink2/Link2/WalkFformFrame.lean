/-
  One cell of `hframe`, split on layout and colour. Colour 0 is
  `homes_zero_frame`, `ybench_zero_step`, or `zbench_zero_step`.
  White and red are `close_live` on the comb `run` returns, and
  `oncomb_chord` is the point `walkStep` produced.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.OnCombChord
import EcbsLink2.Link2.WalkFformZero

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open Ecbs
open EcbsLink2.Spec

attribute [local irreducible] fieldCube fieldMul Ecbs.frobenius_point Ecbs.marker_lift
  Ecbs.fform_add

private theorem step_fit (t : Spec.Tier) (tw : TierWalk t) (i : Nat) (hi : i ≤ t.cells) :
    FitsLen (i + 1) := by
  apply FitsLen.of_le tw.roomO
  have hpos : 0 < cellOpsCharge t := by
    unfold cellOpsCharge
    omega
  have hle : i + 1 ≤ t.cells + 1 := by omega
  have hone : 1 ≤ cellOpsCharge t := hpos
  exact Nat.le_trans hle (by simpa using Nat.mul_le_mul_left (t.cells + 1) hone)

private theorem idx_at {α : Type} (a : Array α) (i : Nat) (v : α)
    (hsz : a.size = 8) (hi : i < 8)
    (h : ∀ hlt : i < a.size, a[i] = v) :
    a[i]'(by rw [hsz]; exact hi) = v :=
  h (by rw [hsz]; exact hi)

private theorem span2 (n bench gap : Nat) (h : 3 * (n - 1) + gap < bench) :
    2 * (n - 1) < bench := by
  omega

/-- Colour 0. The layout picks the zero-cell step. -/
theorem zero_fform_cell
    (t : Spec.Tier) (b : Ecbs.Board)
    (baseX baseY px py ax' ay' : List Nat) (i : Nat) (cells : List Nat)
    (hAt : FformAt t b baseX baseY px py i)
    (hsh : TierShape t) (hOk : BoardOk t) (sat : TierSat t) (tw : TierWalk t)
    (h8 : 8 * stepBudget t.n t.benchlen ≤
      walkCharge t + (6 * t.benchlen + 2 * t.n))
    (h12 : 12 * t.n ≤ cellSlideCharge t + slideCharge t.n)
    (h46 : 46 ≤ cellCtrlCharge t + 4)
    (hfitY : ∀ ys, b.sudo_5Board_5bench = embed ys → FitsLen ys.length)
    (hpos : 0 < t.cells) (hi : i ≤ t.cells - 1) (hlen : cells.length = t.cells)
    (hc : cells[i]'(by omega) = 0)
    (hwalk : walkStep t.n t.k t.benchlen (baseX, baseY) true (px, py)
        (cells[i]'(by omega)) = some (true, (ax', ay'))) :
    ∃ sb',
      fformStep (embed cells) (Int.ofNat (t.cells - 1)) (Int.ofNat i, (b, true)) =
        (if i = t.cells - 1 then .ok (SudoRt.Flow.brk (Int.ofNat i, (sb', true)))
          else .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), (sb', true)))) ∧
      FformAt t sb' baseX baseY ax' ay' (i + 1) := by
  have hAt0 := hAt
  rcases hAt with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      hH0, hscript, hszH, hszD, hproj, _⟩
  rcases hproj with ⟨xP, yP, zP, lay, hxL, hyL, hzL, hxT, hyT, hzT, hXP, hYP, _,
      h0, hlay, _⟩
  have hd0 := idx_at b.sudo_5Board_4held 0 true hszD (by decide) hH0
  have h0i := idx_at b.sudo_5Board_4home 0 (embed xP) hszH (by decide) h0
  cases lay with
  | homes =>
    rcases hlay with ⟨hoff, h1, h2, hd1, hd2⟩
    have h1i := idx_at b.sudo_5Board_4home 1 (embed yP) hszH (by decide) h1
    have h2i := idx_at b.sudo_5Board_4home 2 (embed zP) hszH (by decide) h2
    have hd1i := idx_at b.sudo_5Board_4held 1 true hszD (by decide) hd1
    have hd2i := idx_at b.sudo_5Board_4held 2 true hszD (by decide) hd2
    exact homes_zero_frame t b baseX baseY px py xP yP zP i ax' ay' hAt0 hsh hOk sat
      tw h8 h12 h46 hscript hxL hyL hzL hxT hyT hzT hszH hszD h0i h1i h2i hd0 hd1i
      hd2i hoff cells hpos hi hlen hc hwalk
  | yBench =>
    rcases hlay with ⟨hon, hto, ⟨ys, hbench, hnle, htake, hzero⟩, hd1, h2, hd2⟩
    have h2i := idx_at b.sudo_5Board_4home 2 (embed zP) hszH (by decide) h2
    have hd1i := idx_at b.sudo_5Board_4held 1 false hszD (by decide) hd1
    have hd2i := idx_at b.sudo_5Board_4held 2 true hszD (by decide) hd2
    exact ybench_zero_step t b baseX baseY px py xP yP zP ys i ax' ay' hAt0 hsh hOk
      sat tw h8 h12 h46 hxL hyL hzL hxT hyT hzT hszH hszD h0i h2i hd0 hd1i hd2i hon
      hto hbench htake hnle hzero (hfitY ys hbench) cells hpos hi hlen hc hwalk
  | zBench =>
    rcases hlay with ⟨hon, hto, ⟨ys, hbench, hnle, htake, hzero⟩, h1, hd1, hd2⟩
    have h1i := idx_at b.sudo_5Board_4home 1 (embed yP) hszH (by decide) h1
    have hd1i := idx_at b.sudo_5Board_4held 1 true hszD (by decide) hd1
    have hd2i := idx_at b.sudo_5Board_4held 2 false hszD (by decide) hd2
    exact zbench_zero_step t b baseX baseY px py xP yP zP ys i ax' ay' hAt0 hsh hOk
      sat tw h8 h12 h46 hxL hyL hzL hxT hyT hzT hszH hszD h0i h1i hd0 hd1i hd2i hon
      hto hbench htake hnle hzero (hfitY ys hbench) cells hpos hi hlen hc hwalk

/-- The comb `run` returns, identified with the point `walkStep` produced. -/
private theorem live_from_run
    (t : Spec.Tier) (b bZ : Ecbs.Board) (red : Bool)
    (baseX baseY px py ax' ay' : List Nat) (i c : Nat)
    (cells : List Nat)
    (moves slides ctrl c0 moves' slides' c1 moves0 slides0 ctrl0 c00 : Nat)
    (xP yP zP : List Nat)
    (o : OnComb t bZ red baseX baseY moves' slides' (ctrl + 6) c0 c1)
    (bL : Ecbs.Board)
    (tw : TierWalk t) (hsh : TierShape t) (hOk : BoardOk t) (sat : TierSat t)
    (hlift : Ecbs.marker_lift b = .ok bL) (hfrob : Ecbs.frobenius_point bL = .ok bZ)
    (hmv : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hsl : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hcCtrl : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hop0 : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]? = some (Int.ofNat c0))
    (hmv0 : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves0)
    (hsl0 : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides0)
    (hc0 : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl0)
    (hop00 : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]? = some (Int.ofNat c00))
    (hc1 : FitsLen (c1 + 3 * (t.cells - i)))
    (hfitMul : FitsLen (c00 + 13 * (t.cells - i)))
    (hmvLe : moves0 ≤ i * (walkCharge t + (6 * t.benchlen + 2 * t.n)))
    (hslLe : slides0 ≤ i * (cellSlideCharge t + slideCharge t.n))
    (hcLe : ctrl0 ≤ i * (cellCtrlCharge t + 4))
    (hleM : moves' ≤ moves + 2 * t.n + cubeCharge t.n t.benchlen + 2 * t.n +
      3 * (t.benchlen - t.n))
    (hleS : slides' ≤ slides + 6 * t.n)
    (hwide : 32 * stepBudget t.n t.benchlen ≤
      walkCharge t + (6 * t.benchlen + 2 * t.n))
    (h32 : 32 * t.n ≤ cellSlideCharge t + slideCharge t.n)
    (h46 : 46 ≤ cellCtrlCharge t + 4)
    (hspan : 2 * (t.n - 1) < t.benchlen) (hnb : t.n ≤ t.benchlen)
    (hscript : 2 < t.script)
    (hbx : baseX.length = t.n) (hby : baseY.length = t.n)
    (hbxT : allTritList baseX) (hbyT : allTritList baseY)
    (hpxL : px.length = t.n) (hpyL : py.length = t.n)
    (hpxT : allTritList px) (hpyT : allTritList py)
    (hzL : zP.length = t.n) (hzT : allTritList zP)
    (hXP : xP = fieldMul t.n t.k t.benchlen px zP)
    (hYP : yP = fieldMul t.n t.k t.benchlen py zP)
    (hxPid : o.xP = xP) (hyPid : o.yP = yP) (hzPid : o.zP = zP)
    (hzC : o.z = fieldCube t.n t.k t.benchlen zP)
    (hc4 : FitsLen (o.c4 + (t.cells - i)))
    (hpos : 0 < t.cells) (hi : i ≤ t.cells - 1) (hlen : cells.length = t.cells)
    (hc : cells[i]'(by omega) = c) (hc12 : c = 1 ∨ c = 2)
    (hred : red = decide (c = 2))
    (hwalk : walkStep t.n t.k t.benchlen (baseX, baseY) true (px, py) c =
      some (true, (ax', ay'))) :
    ∃ sb',
      fformStep (embed cells) (Int.ofNat (t.cells - 1)) (Int.ofNat i, (b, true)) =
        (if i = t.cells - 1 then .ok (SudoRt.Flow.brk (Int.ofNat i, (sb', true)))
          else .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), (sb', true)))) ∧
      FformAt t sb' baseX baseY ax' ay' (i + 1) := by
  have hposI : i < t.cells := by omega
  obtain ⟨_, b', x3, yUp, _, hadd, hAt', hx3, hyUp⟩ :=
    close_live t b bZ red baseX baseY i moves slides ctrl c0 moves' slides' c1
      moves0 slides0 ctrl0 c00 o tw hposI hscript hbx hby hbxT hbyT
      hmv hsl hcCtrl hop0 hmv0 hsl0 hc0 hop00 hc1 hfitMul hmvLe hslLe hcLe
      hleM hleS hwide h32 h46 hspan hnb hc4
  have hXPo : o.xP = fieldMul t.n t.k t.benchlen px o.zP := by
    rw [hxPid, hzPid, hXP]
  have hYPo : o.yP = fieldMul t.n t.k t.benchlen py o.zP := by
    rw [hyPid, hzPid, hYP]
  have hzO : o.z = fieldCube t.n t.k t.benchlen o.zP :=
    hzC.trans (congrArg (fieldCube t.n t.k t.benchlen) hzPid.symm)
  have hzTo : allTritList o.zP := by rw [hzPid]; exact hzT
  have hzLo : o.zP.length = t.n := by rw [hzPid]; exact hzL
  have hchord :=
    oncomb_chord t bZ red baseX baseY px py ax' ay' moves' slides' (ctrl + 6) c0 c1 c o
      hsh sat hOk.n_pos hnb hpxT hpyT hzTo hbxT hbyT hpxL hpyL hzLo hbx hby
      hXPo hYPo hzO hc12 hred hwalk
  have hAtW : FformAt t b' baseX baseY ax' ay' (i + 1) := by
    rw [hx3, hyUp, hchord.1, hchord.2] at hAt'
    exact hAt'
  have hc0n : c ≠ 0 := by rcases hc12 with rfl | rfl <;> decide
  have hc2 : c ≤ 2 := by rcases hc12 with rfl | rfl <;> decide
  have haddB : Ecbs.fform_add bZ (SudoRt.SEq.beq (Int.ofNat c) (2 : Int)) =
      .ok (true, b') := by
    rw [cell_red_flag c, ← hred]
    exact hadd
  have hfit := step_fit t tw i (by omega)
  have hlen' : cells.length = (t.cells - 1) + 1 := by omega
  have hst := fformStep_add cells i (t.cells - 1) c b bL bZ b' hi hlen' hc hc0n hc2
    hlift hfrob haddB hfit
  exact ⟨b', hst, hAtW⟩

/-- White or red. `run` is the comb's add, and the point is `walkStep`'s. -/
theorem live_fform_cell
    (t : Spec.Tier) (b : Ecbs.Board) (red : Bool)
    (baseX baseY px py ax' ay' : List Nat) (i c : Nat) (cells : List Nat)
    (hAt : FformAt t b baseX baseY px py i)
    (hsh : TierShape t) (hOk : BoardOk t) (sat : TierSat t) (tw : TierWalk t)
    (hwide : 32 * stepBudget t.n t.benchlen ≤
      walkCharge t + (6 * t.benchlen + 2 * t.n))
    (h32 : 32 * t.n ≤ cellSlideCharge t + slideCharge t.n)
    (h46 : 46 ≤ cellCtrlCharge t + 4)
    (hfitY : ∀ ys, b.sudo_5Board_5bench = embed ys → FitsLen ys.length)
    (hpos : 0 < t.cells) (hi : i ≤ t.cells - 1) (hlen : cells.length = t.cells)
    (hc : cells[i]'(by omega) = c) (hc12 : c = 1 ∨ c = 2)
    (hred : red = decide (c = 2))
    (hwalk : walkStep t.n t.k t.benchlen (baseX, baseY) true (px, py) c =
      some (true, (ax', ay')))
    (run : ∀ (bZ : Ecbs.Board) (xP yP zP : List Nat)
      (moves slides ctrl c0 moves' slides' c1 : Nat) (lane : List Nat),
      FrameAt bZ t baseX baseY →
      bZ.sudo_5Board_9marker_on = true →
      bZ.sudo_5Board_6marker = Int.ofNat 2 →
      bZ.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (ctrl + 6) →
      bZ.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves' →
      bZ.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides' →
      bZ.sudo_5Board_4cost.sudo_5Costs_3ops[0]? = some (Int.ofNat c0) →
      b.sudo_5Board_4cost.sudo_5Costs_3ops[1]? = some (c1 : Int) →
      moves' ≤ moves + 2 * t.n + cubeCharge t.n t.benchlen + 2 * t.n +
        3 * (t.benchlen - t.n) →
      slides' ≤ slides + 6 * t.n →
      bZ.sudo_5Board_8bench_on = true →
      bZ.sudo_5Board_8bench_to = (2 : Int) →
      bZ.sudo_5Board_5bench = embed lane →
      lane.take t.n = fieldCube t.n t.k t.benchlen zP →
      (∀ j, t.n ≤ j → ∀ hj : j < lane.length, lane[j] = 0) →
      bZ.sudo_5Board_4home[0]? =
        some (embed (fieldCube t.n t.k t.benchlen xP)) →
      bZ.sudo_5Board_4home[1]? =
        some (embed (fieldCube t.n t.k t.benchlen yP)) →
      ∃ o : OnComb t bZ red baseX baseY moves' slides' (ctrl + 6) c0 c1,
        o.xP = xP ∧ o.yP = yP ∧ o.zP = zP ∧
          o.z = fieldCube t.n t.k t.benchlen zP ∧
            b.sudo_5Board_4cost.sudo_5Costs_3ops[4]? = some (Int.ofNat o.c4)) :
    ∃ sb',
      fformStep (embed cells) (Int.ofNat (t.cells - 1)) (Int.ofNat i, (b, true)) =
        (if i = t.cells - 1 then .ok (SudoRt.Flow.brk (Int.ofNat i, (sb', true)))
          else .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), (sb', true)))) ∧
      FformAt t sb' baseX baseY ax' ay' (i + 1) := by
  have hAt0 := hAt
  rcases hAt with ⟨_, _, hpxL, hpyL, hpxT, hpyT, hbx, hby, hbxT, hbyT, _, _, _, _, _, _,
      _, hscript, hszH, hszD, hproj, hrest⟩
  rcases hrest with ⟨moves0, slides0, ctrl0, _, _, _, _, _, c1, c00,
      hmv0, hsl0, hc00, _, _, _, _, _, _, hop1?, hop0?,
      _, hc1, hfitMul, _, _, hmvLe, hslLe, hcLe, _, _, _⟩
  rcases hproj with ⟨xP, yP, zP, lay, hxL, hyL, hzL, hxT, hyT, hzT, hXP, hYP, _,
      h0, hlay, _⟩
  have hspan := span2 t.n t.benchlen t.combgap sat.cube_span
  have hnb : t.n ≤ t.benchlen := tw.nLe
  have hposI : i < t.cells := by omega
  have hd0 := idx_at b.sudo_5Board_4held 0 true hszD (by decide) (by
    rcases hAt0 with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hH0, _⟩
    exact hH0)
  have h0i := idx_at b.sudo_5Board_4home 0 (embed xP) hszH (by decide) h0
  cases lay with
  | homes =>
    rcases hlay with ⟨hoff, h1, h2, hd1, hd2⟩
    have h1i := idx_at b.sudo_5Board_4home 1 (embed yP) hszH (by decide) h1
    have h2i := idx_at b.sudo_5Board_4home 2 (embed zP) hszH (by decide) h2
    have hd1i := idx_at b.sudo_5Board_4held 1 true hszD (by decide) hd1
    have hd2i := idx_at b.sudo_5Board_4held 2 true hszD (by decide) hd2
    obtain ⟨bL, bZ, moves, slides, ctrl, c0, moves', slides', lane, hlift, hfrob,
        hmv, hsl, hcCtrl, hopIn0, hfr, hmon, hmark, hctrl, hmv', hsl', hop0',
        hleM, hleS, hbon, hto, hbench, htake, hzero, hhome0, hhome1, _, _⟩ :=
      homes_layout_comb t b baseX baseY px py xP yP zP i hAt0 hsh hOk sat
        hxL hyL hzL hxT hyT hzT hszH hszD h0i h1i h2i hd0 hd1i hd2i hoff hXP hYP hposI
    obtain ⟨o, hxPid, hyPid, hzPid, hzC, hsrc⟩ :=
      run bZ xP yP zP moves slides ctrl c0 moves' slides' c1 lane
        hfr hmon hmark hctrl hmv' hsl' hop0' hop1? hleM hleS hbon hto hbench
        htake hzero hhome0 hhome1
    obtain ⟨cIn, hopIn, hcIn⟩ := fform_fadd t b baseX baseY px py i hAt0
    have hc4 := slot_room o.c4 cIn t.cells i _ hsrc hopIn hcIn
    exact live_from_run t b bZ red baseX baseY px py ax' ay' i c cells
      moves slides ctrl c0 moves' slides' c1 moves0 slides0 ctrl0 c00 xP yP zP o bL
      tw hsh hOk sat hlift hfrob hmv hsl hcCtrl hopIn0 hmv0 hsl0 hc00 hop0?
      hc1 hfitMul hmvLe hslLe hcLe hleM hleS hwide h32 h46 hspan hnb hscript
      hbx hby hbxT hbyT hpxL hpyL hpxT hpyT hzL hzT hXP hYP hxPid hyPid hzPid hzC hc4
      hpos hi hlen hc hc12 hred hwalk
  | yBench =>
    rcases hlay with ⟨hon, hto, ⟨ys, hbench, hnle, htake, hzero⟩, hd1, h2, hd2⟩
    have h2i := idx_at b.sudo_5Board_4home 2 (embed zP) hszH (by decide) h2
    have hd1i := idx_at b.sudo_5Board_4held 1 false hszD (by decide) hd1
    have hd2i := idx_at b.sudo_5Board_4held 2 true hszD (by decide) hd2
    obtain ⟨bL, bZ, moves, slides, ctrl, c0, moves', slides', lane, hlift, hfrob,
        hmv, hsl, hcCtrl, hopIn0, hfr, hmon, hmark, hctrl, hmv', hsl', hop0',
        hleM, hleS, hbon, htoZ, hbenchZ, htakeZ, hzeroZ, hhome0, hhome1, _, _⟩ :=
      ybench_layout_comb t b baseX baseY px py xP yP zP ys i hAt0 hsh hOk sat
        hxL hyL hzL hxT hyT hzT hszH hszD h0i h2i hd0 hd1i hd2i hon hto hbench
        htake hnle hzero (hfitY ys hbench) hXP hYP hposI
    obtain ⟨o, hxPid, hyPid, hzPid, hzC, hsrc⟩ :=
      run bZ xP yP zP moves slides ctrl c0 moves' slides' c1 lane
        hfr hmon hmark hctrl hmv' hsl' hop0' hop1? hleM hleS hbon htoZ hbenchZ
        htakeZ hzeroZ hhome0 hhome1
    obtain ⟨cIn, hopIn, hcIn⟩ := fform_fadd t b baseX baseY px py i hAt0
    have hc4 := slot_room o.c4 cIn t.cells i _ hsrc hopIn hcIn
    exact live_from_run t b bZ red baseX baseY px py ax' ay' i c cells
      moves slides ctrl c0 moves' slides' c1 moves0 slides0 ctrl0 c00 xP yP zP o bL
      tw hsh hOk sat hlift hfrob hmv hsl hcCtrl hopIn0 hmv0 hsl0 hc00 hop0?
      hc1 hfitMul hmvLe hslLe hcLe hleM hleS hwide h32 h46 hspan hnb hscript
      hbx hby hbxT hbyT hpxL hpyL hpxT hpyT hzL hzT hXP hYP hxPid hyPid hzPid hzC hc4
      hpos hi hlen hc hc12 hred hwalk
  | zBench =>
    rcases hlay with ⟨hon, hto, ⟨ys, hbench, hnle, htake, hzero⟩, h1, hd1, hd2⟩
    have h1i := idx_at b.sudo_5Board_4home 1 (embed yP) hszH (by decide) h1
    have hd1i := idx_at b.sudo_5Board_4held 1 true hszD (by decide) hd1
    have hd2i := idx_at b.sudo_5Board_4held 2 false hszD (by decide) hd2
    obtain ⟨bL, bZ, moves, slides, ctrl, c0, moves', slides', lane, hlift, hfrob,
        hmv, hsl, hcCtrl, hopIn0, hfr, hmon, hmark, hctrl, hmv', hsl', hop0',
        hleM, hleS, hbon, htoZ, hbenchZ, htakeZ, hzeroZ, hhome0, hhome1, _, _⟩ :=
      zbench_layout_comb t b baseX baseY px py xP yP zP ys i hAt0 hsh hOk sat
        hxL hyL hzL hxT hyT hzT hszH hszD h0i h1i hd0 hd1i hd2i hon hto hbench
        htake hnle hzero (hfitY ys hbench) hXP hYP hposI
    obtain ⟨o, hxPid, hyPid, hzPid, hzC, hsrc⟩ :=
      run bZ xP yP zP moves slides ctrl c0 moves' slides' c1 lane
        hfr hmon hmark hctrl hmv' hsl' hop0' hop1? hleM hleS hbon htoZ hbenchZ
        htakeZ hzeroZ hhome0 hhome1
    obtain ⟨cIn, hopIn, hcIn⟩ := fform_fadd t b baseX baseY px py i hAt0
    have hc4 := slot_room o.c4 cIn t.cells i _ hsrc hopIn hcIn
    exact live_from_run t b bZ red baseX baseY px py ax' ay' i c cells
      moves slides ctrl c0 moves' slides' c1 moves0 slides0 ctrl0 c00 xP yP zP o bL
      tw hsh hOk sat hlift hfrob hmv hsl hcCtrl hopIn0 hmv0 hsl0 hc00 hop0?
      hc1 hfitMul hmvLe hslLe hcLe hleM hleS hwide h32 h46 hspan hnb hscript
      hbx hby hbxT hbyT hpxL hpyL hpxT hpyT hzL hzT hXP hYP hxPid hyPid hzPid hzC hc4
      hpos hi hlen hc hc12 hred hwalk

/-- One cell. Colour 0 cubes. White and red add, with `red = (c = 2)`. -/
theorem fform_frame
    (t : Spec.Tier) (b : Ecbs.Board)
    (baseX baseY px py ax' ay' : List Nat) (i : Nat) (cells : List Nat)
    (hAt : FformAt t b baseX baseY px py i)
    (hsh : TierShape t) (hOk : BoardOk t) (sat : TierSat t) (tw : TierWalk t)
    (h8 : 8 * stepBudget t.n t.benchlen ≤
      walkCharge t + (6 * t.benchlen + 2 * t.n))
    (h12 : 12 * t.n ≤ cellSlideCharge t + slideCharge t.n)
    (hwide : 32 * stepBudget t.n t.benchlen ≤
      walkCharge t + (6 * t.benchlen + 2 * t.n))
    (h32 : 32 * t.n ≤ cellSlideCharge t + slideCharge t.n)
    (h46 : 46 ≤ cellCtrlCharge t + 4)
    (hfitY : ∀ ys, b.sudo_5Board_5bench = embed ys → FitsLen ys.length)
    (hpos : 0 < t.cells) (hi : i ≤ t.cells - 1) (hlen : cells.length = t.cells)
    (hwalk : walkStep t.n t.k t.benchlen (baseX, baseY) true (px, py)
        (cells[i]'(by omega)) = some (true, (ax', ay')))
    (run : ∀ (red : Bool) (bZ : Ecbs.Board) (xP yP zP : List Nat)
      (moves slides ctrl c0 moves' slides' c1 : Nat) (lane : List Nat),
      FrameAt bZ t baseX baseY →
      bZ.sudo_5Board_9marker_on = true →
      bZ.sudo_5Board_6marker = Int.ofNat 2 →
      bZ.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (ctrl + 6) →
      bZ.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves' →
      bZ.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides' →
      bZ.sudo_5Board_4cost.sudo_5Costs_3ops[0]? = some (Int.ofNat c0) →
      b.sudo_5Board_4cost.sudo_5Costs_3ops[1]? = some (c1 : Int) →
      moves' ≤ moves + 2 * t.n + cubeCharge t.n t.benchlen + 2 * t.n +
        3 * (t.benchlen - t.n) →
      slides' ≤ slides + 6 * t.n →
      bZ.sudo_5Board_8bench_on = true →
      bZ.sudo_5Board_8bench_to = (2 : Int) →
      bZ.sudo_5Board_5bench = embed lane →
      lane.take t.n = fieldCube t.n t.k t.benchlen zP →
      (∀ j, t.n ≤ j → ∀ hj : j < lane.length, lane[j] = 0) →
      bZ.sudo_5Board_4home[0]? =
        some (embed (fieldCube t.n t.k t.benchlen xP)) →
      bZ.sudo_5Board_4home[1]? =
        some (embed (fieldCube t.n t.k t.benchlen yP)) →
      ∃ o : OnComb t bZ red baseX baseY moves' slides' (ctrl + 6) c0 c1,
        o.xP = xP ∧ o.yP = yP ∧ o.zP = zP ∧
          o.z = fieldCube t.n t.k t.benchlen zP ∧
            b.sudo_5Board_4cost.sudo_5Costs_3ops[4]? = some (Int.ofNat o.c4)) :
    ∃ sb',
      fformStep (embed cells) (Int.ofNat (t.cells - 1)) (Int.ofNat i, (b, true)) =
        (if i = t.cells - 1 then .ok (SudoRt.Flow.brk (Int.ofNat i, (sb', true)))
          else .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), (sb', true)))) ∧
      FformAt t sb' baseX baseY ax' ay' (i + 1) := by
  have hiLen : i < cells.length := by omega
  have hcol := walk_step_colour t.n t.k t.benchlen (baseX, baseY) (px, py)
    (cells[i]'hiLen) _ hwalk
  rcases hcol with h0 | h1 | h2
  · exact zero_fform_cell t b baseX baseY px py ax' ay' i cells hAt hsh hOk sat tw
      h8 h12 h46 hfitY hpos hi hlen h0 hwalk
  · have hwalk1 : walkStep t.n t.k t.benchlen (baseX, baseY) true (px, py) 1 =
        some (true, (ax', ay')) := by simpa [h1] using hwalk
    exact live_fform_cell t b false baseX baseY px py ax' ay' i 1 cells hAt hsh hOk
      sat tw hwide h32 h46 hfitY hpos hi hlen h1 (Or.inl rfl) (by decide) hwalk1
      (fun bZ xP yP zP moves slides ctrl c0 moves' slides' c1 lane =>
        run false bZ xP yP zP moves slides ctrl c0 moves' slides' c1 lane)
  · have hwalk2 : walkStep t.n t.k t.benchlen (baseX, baseY) true (px, py) 2 =
        some (true, (ax', ay')) := by simpa [h2] using hwalk
    exact live_fform_cell t b true baseX baseY px py ax' ay' i 2 cells hAt hsh hOk
      sat tw hwide h32 h46 hfitY hpos hi hlen h2 (Or.inr rfl) (by decide) hwalk2
      (fun bZ xP yP zP moves slides ctrl c0 moves' slides' c1 lane =>
        run true bZ xP yP zP moves slides ctrl c0 moves' slides' c1 lane)

end EcbsLink2.Link2
