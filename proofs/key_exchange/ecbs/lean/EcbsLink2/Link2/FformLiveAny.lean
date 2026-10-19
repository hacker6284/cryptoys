/-
  One live cell, white or red, on any layout. The layout's comb is
  `homes_layout_comb`, `ybench_layout_comb`, or `zbench_layout_comb`.
  `live_cell_at` reads that comb, and `red` is the colour.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FformLayout
import EcbsLink2.Link2.FformLivePack

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open Ecbs
open EcbsLink2.Spec

attribute [local irreducible] fieldCube fieldMul Ecbs.frobenius_point Ecbs.marker_lift
  Ecbs.fform_add

/-- The add `live_cell_at` reads off the comb. `moves'`, `slides'`, and
    `ctrl'` are that comb's counters. -/
structure OnComb (t : Spec.Tier) (bZ : Ecbs.Board) (red : Bool)
    (baseX baseY : List Nat) (moves' slides' ctrl' cMul c1 : Nat) : Type where
  t0 : Int
  t1 : Int
  ops : Array Int
  b2 : Ecbs.Board
  b3 : Ecbs.Board
  b4 : Ecbs.Board
  b5 : Ecbs.Board
  b6 : Ecbs.Board
  b7 : Ecbs.Board
  b8 : Ecbs.Board
  b9 : Ecbs.Board
  b10 : Ecbs.Board
  b11 : Ecbs.Board
  hAtL : SudoRt.atL bZ.sudo_5Board_4cost.sudo_5Costs_3ops op_fadd = .ok t0
  hInc : SudoRt.addI t0 (1 : Int) = .ok t1
  hPut : SudoRt.putL bZ.sudo_5Board_4cost.sudo_5Costs_3ops op_fadd t1 = .ok ops
  hMir : mirror ({ bZ with sudo_5Board_4cost :=
      { bZ.sudo_5Board_4cost with sudo_5Costs_3ops := ops } } : Ecbs.Board) across = .ok b2
  hRun : mul b2 across base_across bottom true true false = .ok b3
  hZ : is_zero b3 across = .ok false
  hMirU : mirror b3 up = .ok b4
  hRise : mul b4 up base_up bottom true true red = .ok b5
  hU : mul b5 gap up up true false false = .ok b6
  hUZ : mul b6 gap bottom gap false false false = .ok b7
  hV : mul b7 spare across across true false false = .ok b8
  hVZ : mul b8 bottom spare bottom false false false = .ok b9
  hSum : mul b9 gap across spare false true false = .ok b10
  hAdd : add b10 gap bottom false = .ok b11
  lane : List Nat
  u : List Nat
  v : List Nat
  z : List Nat
  x2 : List Nat
  y2 : List Nat
  script : Nat
  w : Nat
  ht : Nat
  r : Nat
  m : Nat
  mx : Nat
  cOps : Nat
  hole : Nat
  peak : Nat
  peakS : Nat
  x3 : List Nat
  yUp : List Nat
  s : AddAt b11 lane t.n t.k t.benchlen u v z x2 y2 script w ht r
    m ctrl' mx cOps moves' slides' hole peak peakS
  hbound : m + 5 < script
  hfitM6 : FitsLen (m + 6)
  hfitC6 : FitsLen (ctrl' + 12)
  hfops6 : FitsLen (cOps + 6)
  hf : FitsLen t.n
  hBig : FitsLen (moves' + 8 * stepBudget t.n t.benchlen)
  hSlide : FitsLen (slides' + 8 * t.n)
  hw0 : 0 < w
  hh0 : 0 < ht
  hrR : r < ht
  hrP : 0 < r
  hnE : t.n = w * ht - 1
  hkLe : t.k ≤ t.n
  hgapN : t.n - t.k = w * r
  hsm : w ≤ 1000000 ∧ ht ≤ 1000000 ∧ r ≤ 1000000 ∧ t.benchlen ≤ 1000001
  hnsm : t.n ≤ 1000000
  hfitB : FitsLen t.benchlen
  hx : fformAcross t.n t.k t.benchlen x2 u v z =
    fieldMul t.n t.k t.benchlen x3 (fformBottom t.n t.k t.benchlen v z)
  hy : addUp t.n t.k t.benchlen red y2 u v z =
    fieldMul t.n t.k t.benchlen yUp (fformBottom t.n t.k t.benchlen v z)
  hpx : x3.length = t.n
  hpy : yUp.length = t.n
  hpxT : allTritList x3
  hpyT : allTritList yUp
  hx2 : x2 = baseX
  hy2 : y2 = baseY
  htier : b11.sudo_5Board_1t = embTier t
  hszH : b11.sudo_5Board_4home.size = 8
  hszD : b11.sudo_5Board_4held.size = 8
  hopIn : 1 < b11.sudo_5Board_4cost.sudo_5Costs_3ops.size
  hop1 : b11.sudo_5Board_4cost.sudo_5Costs_3ops[1]? = some ((c1 + 3 : Nat) : Int)
  hcOps : cOps = cMul + 7
  hne : fformBottom t.n t.k t.benchlen v z ≠ List.replicate t.n 0
  hinv : ∃ w, w.length = t.n ∧ allTritList w ∧
    fieldMul t.n t.k t.benchlen (fformBottom t.n t.k t.benchlen v z) w = onePeg t.n
  xP : List Nat
  yP : List Nat
  zP : List Nat
  hv : v = fformRun t.n t.k t.benchlen baseX
    (fieldCube t.n t.k t.benchlen zP) (fieldCube t.n t.k t.benchlen xP)
  hu : u = fformRise t.n t.k t.benchlen
    (if red then mirrorTrits baseY else baseY)
    (fieldCube t.n t.k t.benchlen zP) (fieldCube t.n t.k t.benchlen yP)
  hopsN : b11.sudo_5Board_4cost.sudo_5Costs_3ops.size = 5
  c4 : Nat
  hop4 : b11.sudo_5Board_4cost.sudo_5Costs_3ops[4]? = some (Int.ofNat (c4 + 1))

private theorem same_nat (a b : Nat) (p : Int)
    (h1 : p = Int.ofNat a) (h2 : p = Int.ofNat b) : a = b :=
  Int.ofNat.inj (by simpa [ofNat_eq_natCast] using h1.symm.trans h2)

theorem slot_room (c4 cIn cells done : Nat) (slot : Option Int)
    (h4 : slot = some (Int.ofNat c4)) (hIn : slot = some (Int.ofNat cIn))
    (hc : FitsLen (cIn + (cells - done))) :
    FitsLen (c4 + (cells - done)) := by
  have he : c4 = cIn :=
    Int.ofNat.inj (by simpa [ofNat_eq_natCast] using Option.some.inj (h4.symm.trans hIn))
  simpa [he] using hc

private theorem span2 (n bench gap : Nat) (h : 3 * (n - 1) + gap < bench) :
    2 * (n - 1) < bench := by
  omega

private theorem idx_at {α : Type} (a : Array α) (i : Nat) (v : α)
    (hsz : a.size = 8) (hi : i < 8)
    (h : ∀ hlt : i < a.size, a[i] = v) :
    a[i]'(by rw [hsz]; exact hi) = v :=
  h (by rw [hsz]; exact hi)

/-- The comb's counters are the bounds `live_cell_at` uses. -/
private theorem live_on
    (t : Spec.Tier) (bZ : Ecbs.Board) (red : Bool)
    (baseX baseY : List Nat) (done : Nat)
    (moves slides ctrl c0 moves' slides' c1 : Nat)
    (o : OnComb t bZ red baseX baseY moves' slides' (ctrl + 6) c0 c1)
    (tw : TierWalk t)
    (hpos : done < t.cells)
    (hscript : 2 < t.script)
    (hbx : baseX.length = t.n) (hby : baseY.length = t.n)
    (hbxT : allTritList baseX) (hbyT : allTritList baseY)
    (hfitC1 : FitsLen (c1 + 3 * (t.cells - done)))
    (hfitMul : FitsLen (c0 + 13 * (t.cells - done)))
    (hmvLe : moves ≤ done * (walkCharge t + (6 * t.benchlen + 2 * t.n)))
    (hslLe : slides ≤ done * (cellSlideCharge t + slideCharge t.n))
    (hcLe : ctrl ≤ done * (cellCtrlCharge t + 4))
    (hleM : moves' ≤ moves + 2 * t.n + cubeCharge t.n t.benchlen + 2 * t.n +
      3 * (t.benchlen - t.n))
    (hleS : slides' ≤ slides + 6 * t.n)
    (hwide : 32 * stepBudget t.n t.benchlen ≤
      walkCharge t + (6 * t.benchlen + 2 * t.n))
    (h32 : 32 * t.n ≤ cellSlideCharge t + slideCharge t.n)
    (h46 : 46 ≤ cellCtrlCharge t + 4)
    (hspan : 2 * (t.n - 1) < t.benchlen) (hnb : t.n ≤ t.benchlen)
    (hc4 : FitsLen (o.c4 + (t.cells - done))) :
    ∃ b',
      Ecbs.fform_add bZ red = .ok (true, b') ∧
      FformAt t b' baseX baseY o.x3 o.yUp (done + 1) := by
  exact live_cell_at t bZ red o.t0 o.t1 o.ops o.b2 o.b3 o.b4 o.b5 o.b6 o.b7 o.b8
    o.b9 o.b10 o.b11 o.hAtL o.hInc o.hPut o.hMir o.hRun o.hZ o.hMirU o.hRise
    o.hU o.hUZ o.hV o.hVZ o.hSum o.hAdd o.lane t.n t.k t.benchlen o.u o.v o.z
    o.x2 o.y2 o.script o.w o.ht o.r o.m (ctrl + 6) o.mx o.cOps moves' slides'
    o.hole o.peak o.peakS o.x3 o.yUp o.s o.hbound o.hfitM6 o.hfitC6 o.hfops6
    o.hf o.hBig o.hSlide o.hw0 o.hh0 o.hrR o.hrP o.hnE o.hkLe o.hgapN o.hsm
    o.hnsm o.hfitB o.hx o.hy baseX baseY done c0 c1 moves slides ctrl tw hpos
    hscript o.hpx o.hpy o.hpxT o.hpyT hbx hby hbxT hbyT o.hx2 o.hy2 o.htier
    o.hszH o.hszD rfl rfl rfl o.hopIn o.hop1 o.hcOps hleM hleS rfl hfitC1
    hfitMul hmvLe hslLe hcLe hwide h32 h46 hspan hnb o.hne o.hinv o.hopsN
    o.c4 o.hop4 hc4

theorem close_live
    (t : Spec.Tier) (b bZ : Ecbs.Board) (red : Bool)
    (baseX baseY : List Nat) (done : Nat)
    (moves slides ctrl c0 moves' slides' c1 moves0 slides0 ctrl0 c00 : Nat)
    (o : OnComb t bZ red baseX baseY moves' slides' (ctrl + 6) c0 c1)
    (tw : TierWalk t)
    (hpos : done < t.cells) (hscript : 2 < t.script)
    (hbx : baseX.length = t.n) (hby : baseY.length = t.n)
    (hbxT : allTritList baseX) (hbyT : allTritList baseY)
    (hmv : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hsl : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hop0 : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]? = some (Int.ofNat c0))
    (hmv0 : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves0)
    (hsl0 : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides0)
    (hc0 : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl0)
    (hop00 : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]? = some (Int.ofNat c00))
    (hc1 : FitsLen (c1 + 3 * (t.cells - done)))
    (hfitMul : FitsLen (c00 + 13 * (t.cells - done)))
    (hmvLe : moves0 ≤ done * (walkCharge t + (6 * t.benchlen + 2 * t.n)))
    (hslLe : slides0 ≤ done * (cellSlideCharge t + slideCharge t.n))
    (hcLe : ctrl0 ≤ done * (cellCtrlCharge t + 4))
    (hleM : moves' ≤ moves + 2 * t.n + cubeCharge t.n t.benchlen + 2 * t.n +
      3 * (t.benchlen - t.n))
    (hleS : slides' ≤ slides + 6 * t.n)
    (hwide : 32 * stepBudget t.n t.benchlen ≤
      walkCharge t + (6 * t.benchlen + 2 * t.n))
    (h32 : 32 * t.n ≤ cellSlideCharge t + slideCharge t.n)
    (h46 : 46 ≤ cellCtrlCharge t + 4)
    (hspan : 2 * (t.n - 1) < t.benchlen) (hnb : t.n ≤ t.benchlen)
    (hc4 : FitsLen (o.c4 + (t.cells - done))) :
    ∃ bZ' b' x3 yUp,
      bZ' = bZ ∧
      Ecbs.fform_add bZ red = .ok (true, b') ∧
      FformAt t b' baseX baseY x3 yUp (done + 1) ∧
      x3 = o.x3 ∧ yUp = o.yUp := by
  have hm := same_nat moves moves0 _ hmv hmv0
  have hs := same_nat slides slides0 _ hsl hsl0
  have hce := same_nat ctrl ctrl0 _ hc hc0
  have hmul : c0 = c00 := by
    have h := Option.some.inj (hop0.symm.trans hop00)
    exact Int.ofNat.inj (by simpa [ofNat_eq_natCast] using h)
  have hmvLe' : moves ≤ done * (walkCharge t + (6 * t.benchlen + 2 * t.n)) := by
    rw [hm]; exact hmvLe
  have hslLe' : slides ≤ done * (cellSlideCharge t + slideCharge t.n) := by
    rw [hs]; exact hslLe
  have hcLe' : ctrl ≤ done * (cellCtrlCharge t + 4) := by
    rw [hce]; exact hcLe
  have hfitMul' : FitsLen (c0 + 13 * (t.cells - done)) := by
    rw [hmul]; exact hfitMul
  obtain ⟨b', hadd, hAt'⟩ :=
    live_on t bZ red baseX baseY done moves slides ctrl c0 moves' slides' c1 o
      tw hpos hscript hbx hby hbxT hbyT hc1 hfitMul' hmvLe' hslLe' hcLe'
      hleM hleS hwide h32 h46 hspan hnb hc4
  exact ⟨bZ, b', o.x3, o.yUp, rfl, hadd, hAt', rfl, rfl⟩

/-- White or red, on homes, `yBench`, or `zBench`. The layout picks the comb
    and `red` picks the colour. -/
theorem live_any
    (t : Spec.Tier) (b : Ecbs.Board) (red : Bool)
    (baseX baseY px py : List Nat) (done : Nat)
    (hAt : FformAt t b baseX baseY px py done)
    (hsh : TierShape t) (hOk : BoardOk t) (sat : TierSat t)
    (tw : TierWalk t)
    (hwide : 32 * stepBudget t.n t.benchlen ≤
      walkCharge t + (6 * t.benchlen + 2 * t.n))
    (h32 : 32 * t.n ≤ cellSlideCharge t + slideCharge t.n)
    (h46 : 46 ≤ cellCtrlCharge t + 4)
    (hship : t = demo ∨ t = toy ∨ t = hobby ∨ t = serious)
    (hpos : done < t.cells)
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
    ∃ bL bZ b' x3 yUp,
      Ecbs.marker_lift b = .ok bL ∧
      Ecbs.frobenius_point bL = .ok bZ ∧
      Ecbs.fform_add bZ red = .ok (true, b') ∧
      FformAt t b' baseX baseY x3 yUp (done + 1) := by
  have hAt0 := hAt
  rcases hAt with ⟨_, _, _, _, _, _, hbx, hby, hbxT, hbyT, _, _, _, _, _, _,
      hH0, hscript, hszH, hszD, hproj, hrest⟩
  rcases hrest with ⟨moves0, slides0, ctrl0, _, _, _, _, _, c1, c00,
      hmv0, hsl0, hc00, _, _, _, _, _, _, hop1?, hop0?,
      _, hc1, hfitMul, _, _, hmvLe, hslLe, hcLe, _, _, _⟩
  rcases hproj with ⟨xP, yP, zP, lay, hxL, hyL, hzL, hxT, hyT, hzT, hXP, hYP, _,
      h0, hlay, _⟩
  have hspan := span2 t.n t.benchlen t.combgap sat.cube_span
  have hnb : t.n ≤ t.benchlen := tw.nLe
  have hd0 :=
    idx_at b.sudo_5Board_4held 0 true hszD (by decide) hH0
  have h0i :=
    idx_at b.sudo_5Board_4home 0 (embed xP) hszH (by decide) h0
  cases lay with
  | homes =>
    rcases hlay with ⟨hoff, h1, h2, hd1, hd2⟩
    have h1i := idx_at b.sudo_5Board_4home 1 (embed yP) hszH (by decide) h1
    have h2i := idx_at b.sudo_5Board_4home 2 (embed zP) hszH (by decide) h2
    have hd1i := idx_at b.sudo_5Board_4held 1 true hszD (by decide) hd1
    have hd2i := idx_at b.sudo_5Board_4held 2 true hszD (by decide) hd2
    obtain ⟨bL, bZ, moves, slides, ctrl, c0, moves', slides', lane, hlift, hfrob,
        hmv, hsl, hc, hopIn0, hfr, hmon, hmark, hctrl, hmv', hsl', hop0',
        hleM, hleS, hbon, hto, hbench, htake, hzero, hhome0, hhome1, _, _⟩ :=
      homes_layout_comb t b baseX baseY px py xP yP zP done hAt0 hsh hOk sat
        hxL hyL hzL hxT hyT hzT hszH hszD h0i h1i h2i hd0 hd1i hd2i hoff hXP hYP hpos
    obtain ⟨cIn, hopIn, hcIn⟩ := fform_fadd t b baseX baseY px py done hAt0
    obtain ⟨o, _, _, _, _, hsrc⟩ := run bZ xP yP zP moves slides ctrl c0 moves' slides' c1 lane
      hfr hmon hmark hctrl hmv' hsl' hop0' hop1? hleM hleS hbon hto hbench
      htake hzero hhome0 hhome1
    have hc4 := slot_room o.c4 cIn t.cells done _ hsrc hopIn hcIn
    obtain ⟨_, b', x3, yUp, _, hadd, hAt', _, _⟩ :=
      close_live t b bZ red baseX baseY done moves slides ctrl c0 moves' slides'
        c1 moves0 slides0 ctrl0 c00 o tw hpos hscript hbx hby hbxT hbyT
        hmv hsl hc hopIn0 hmv0 hsl0 hc00 hop0? hc1 hfitMul hmvLe hslLe hcLe
        hleM hleS hwide h32 h46 hspan hnb hc4
    exact ⟨bL, bZ, b', x3, yUp, hlift, hfrob, hadd, hAt'⟩
  | yBench =>
    rcases hlay with ⟨hon, hto, ⟨ys, hbench, hnle, htake, hzero, hcap⟩, hd1, h2, hd2⟩
    have h2i := idx_at b.sudo_5Board_4home 2 (embed zP) hszH (by decide) h2
    have hd1i := idx_at b.sudo_5Board_4held 1 false hszD (by decide) hd1
    have hd2i := idx_at b.sudo_5Board_4held 2 true hszD (by decide) hd2
    obtain ⟨bL, bZ, moves, slides, ctrl, c0, moves', slides', lane, hlift, hfrob,
        hmv, hsl, hc, hopIn0, hfr, hmon, hmark, hctrl, hmv', hsl', hop0',
        hleM, hleS, hbon, htoZ, hbenchZ, htakeZ, hzeroZ, hhome0, hhome1, _, _⟩ :=
      ybench_layout_comb t b baseX baseY px py xP yP zP ys done hAt0 hsh hOk sat
        hxL hyL hzL hxT hyT hzT hszH hszD h0i h2i hd0 hd1i hd2i hon hto hbench
        htake hnle hzero hcap hship hXP hYP hpos
    obtain ⟨cIn, hopIn, hcIn⟩ := fform_fadd t b baseX baseY px py done hAt0
    obtain ⟨o, _, _, _, _, hsrc⟩ := run bZ xP yP zP moves slides ctrl c0 moves' slides' c1 lane
      hfr hmon hmark hctrl hmv' hsl' hop0' hop1? hleM hleS hbon htoZ hbenchZ
      htakeZ hzeroZ hhome0 hhome1
    have hc4 := slot_room o.c4 cIn t.cells done _ hsrc hopIn hcIn
    obtain ⟨_, b', x3, yUp, _, hadd, hAt', _, _⟩ :=
      close_live t b bZ red baseX baseY done moves slides ctrl c0 moves' slides'
        c1 moves0 slides0 ctrl0 c00 o tw hpos hscript hbx hby hbxT hbyT
        hmv hsl hc hopIn0 hmv0 hsl0 hc00 hop0? hc1 hfitMul hmvLe hslLe hcLe
        hleM hleS hwide h32 h46 hspan hnb hc4
    exact ⟨bL, bZ, b', x3, yUp, hlift, hfrob, hadd, hAt'⟩
  | zBench =>
    rcases hlay with ⟨hon, hto, ⟨ys, hbench, hnle, htake, hzero, hcap⟩, h1, hd1, hd2⟩
    have h1i := idx_at b.sudo_5Board_4home 1 (embed yP) hszH (by decide) h1
    have hd1i := idx_at b.sudo_5Board_4held 1 true hszD (by decide) hd1
    have hd2i := idx_at b.sudo_5Board_4held 2 false hszD (by decide) hd2
    obtain ⟨bL, bZ, moves, slides, ctrl, c0, moves', slides', lane, hlift, hfrob,
        hmv, hsl, hc, hopIn0, hfr, hmon, hmark, hctrl, hmv', hsl', hop0',
        hleM, hleS, hbon, htoZ, hbenchZ, htakeZ, hzeroZ, hhome0, hhome1, _, _⟩ :=
      zbench_layout_comb t b baseX baseY px py xP yP zP ys done hAt0 hsh hOk sat
        hxL hyL hzL hxT hyT hzT hszH hszD h0i h1i hd0 hd1i hd2i hon hto hbench
        htake hnle hzero hcap hship hXP hYP hpos
    obtain ⟨cIn, hopIn, hcIn⟩ := fform_fadd t b baseX baseY px py done hAt0
    obtain ⟨o, _, _, _, _, hsrc⟩ := run bZ xP yP zP moves slides ctrl c0 moves' slides' c1 lane
      hfr hmon hmark hctrl hmv' hsl' hop0' hop1? hleM hleS hbon htoZ hbenchZ
      htakeZ hzeroZ hhome0 hhome1
    have hc4 := slot_room o.c4 cIn t.cells done _ hsrc hopIn hcIn
    obtain ⟨_, b', x3, yUp, _, hadd, hAt', _, _⟩ :=
      close_live t b bZ red baseX baseY done moves slides ctrl c0 moves' slides'
        c1 moves0 slides0 ctrl0 c00 o tw hpos hscript hbx hby hbxT hbyT
        hmv hsl hc hopIn0 hmv0 hsl0 hc00 hop0? hc1 hfitMul hmvLe hslLe hcLe
        hleM hleS hwide h32 h46 hspan hnb hc4
    exact ⟨bL, bZ, b', x3, yUp, hlift, hfrob, hadd, hAt'⟩

end EcbsLink2.Link2
