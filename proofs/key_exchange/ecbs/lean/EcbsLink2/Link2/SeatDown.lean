/-
  The first live cell when the marker is still `-1`. A board with the same
  homes and a natural marker one control step earlier lifts to that board, so
  `cell_run_frame` seats the marker at 1 and hands the next cell a `RunFrame`.
  That earlier board is a proof device. The seat theorems do not name it.
  The red opening, whose up home is negated, has its own device and its own
  seat. Strict stays at most 7 and the hole stays under the bench.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.OpenBoard
import EcbsLink2.Link2.WalkInd

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- The opening board with the marker seated one step early, so `marker_lift`
    returns the real opening board. Private: a seat theorem does not name it. -/
private def seatFake (t : Spec.Tier) (x y : List Nat) : Ecbs.Board :=
  { whiteRec t x y with
    sudo_5Board_6marker := 0
    sudo_5Board_4cost := { (whiteRec t x y).sudo_5Board_4cost with
      sudo_5Costs_4ctrl := Int.ofNat (tierR t - 1) } }

private theorem fake_szH (t : Spec.Tier) (x y : List Nat) :
    (seatFake t x y).sudo_5Board_4home.size = 8 := by
  simp [seatFake, open_szH]

private theorem fake_szD (t : Spec.Tier) (x y : List Nat) :
    (seatFake t x y).sudo_5Board_4held.size = 8 := by
  simp [seatFake, open_szD]

private theorem fake_marker (t : Spec.Tier) (x y : List Nat) :
    (seatFake t x y).sudo_5Board_6marker = 0 := by
  simp [seatFake]

private theorem fake_ctrl (t : Spec.Tier) (x y : List Nat) :
    (seatFake t x y).sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (tierR t - 1) := by
  simp [seatFake]

private theorem fake_flag (t : Spec.Tier) (x y : List Nat) :
    (seatFake t x y).sudo_5Board_9marker_on = true := by
  simp [seatFake, open_flag]

private theorem fake_bench (t : Spec.Tier) (x y : List Nat) :
    (seatFake t x y).sudo_5Board_8bench_on = false := by
  simp [seatFake, open_bench]

private theorem fake_strict (t : Spec.Tier) (x y : List Nat) :
    (seatFake t x y).sudo_5Board_4cost.sudo_5Costs_11peak_strict = 0 := by
  simp [seatFake, open_strict]

private theorem fake_hole (t : Spec.Tier) (x y : List Nat) :
    (seatFake t x y).sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = 0 := by
  simp [seatFake, open_hole]

private theorem fake_slides (t : Spec.Tier) (x y : List Nat) :
    (seatFake t x y).sudo_5Board_4cost.sudo_5Costs_6slides = 0 := by
  simp [seatFake, open_slides]

private theorem fake_moves (t : Spec.Tier) (x y : List Nat) :
    (seatFake t x y).sudo_5Board_4cost.sudo_5Costs_5moves =
      Int.ofNat (pegCount x + pegCount y + pegCount x + pegCount y) := by
  simp [seatFake, open_moves]

private theorem fake_peak (t : Spec.Tier) (x y : List Nat) :
    (seatFake t x y).sudo_5Board_4cost.sudo_5Costs_4peak = 4 := by
  simp [seatFake, open_peak]

private theorem fake_mx (t : Spec.Tier) (x y : List Nat) :
    (seatFake t x y).sudo_5Board_4cost.sudo_5Costs_17script_marker_max = 0 := by
  simp [seatFake, open_mx]

private theorem fake_tier (t : Spec.Tier) (x y : List Nat) :
    (seatFake t x y).sudo_5Board_1t = embTier t := by
  simp [seatFake, open_tier]

private theorem fake_row (t : Spec.Tier) (x y : List Nat) :
    (seatFake t x y).sudo_5Board_3row = embed (paintedRow t) := by
  simp [seatFake, open_row]

private theorem fake_ladder (t : Spec.Tier) (x y : List Nat) :
    (seatFake t x y).sudo_5Board_6ladder = embed (tierClimb t) := by
  simp [seatFake, open_ladder]

private theorem fake_l0 (t : Spec.Tier) (x y : List Nat) :
    (seatFake t x y).sudo_5Board_7ladder0 = Int.ofNat (t.script + 2) := by
  simp [seatFake, open_l0]

private theorem fake_nr (t : Spec.Tier) (x y : List Nat) :
    (seatFake t x y).sudo_5Board_6nrungs = Int.ofNat (tierR t) := by
  simp [seatFake, open_nr]

private theorem fake_park (t : Spec.Tier) (x y : List Nat) :
    (seatFake t x y).sudo_5Board_9park_hole = Int.ofNat (t.script + 2 + tierR t) := by
  simp [seatFake, open_park]

private theorem fake_from (t : Spec.Tier) (x y : List Nat) :
    (seatFake t x y).sudo_5Board_11parked_from = -1 := by
  simp [seatFake, open_from]

private theorem fake_ridx (t : Spec.Tier) (x y : List Nat) :
    (seatFake t x y).sudo_5Board_8rung_idx = 0 := by
  simp [seatFake, open_ridx]

private theorem fake_tally (t : Spec.Tier) (x y : List Nat) :
    (seatFake t x y).sudo_5Board_9tally_len = 0 := by
  simp [seatFake, white_tally]

private theorem fake_t0 (t : Spec.Tier) (x y : List Nat) :
    (seatFake t x y).sudo_5Board_6tally0 = Int.ofNat (tallyOrigin t) := by
  simp [seatFake, open_t0]

private theorem fake_high (t : Spec.Tier) (x y : List Nat) (hR : 0 < tierR t) :
    (seatFake t x y).sudo_5Board_4cost.sudo_5Costs_15control_highest =
      Int.ofNat (t.script + tierR t + 1) := by
  simp [seatFake, open_high t x y hR]

private theorem fake_tmax (t : Spec.Tier) (x y : List Nat) :
    (seatFake t x y).sudo_5Board_4cost.sudo_5Costs_9tally_max = 0 := by
  simp [seatFake, open_tmax]

private theorem fake_ops (t : Spec.Tier) (x y : List Nat) :
    (seatFake t x y).sudo_5Board_4cost.sudo_5Costs_3ops =
      Array.mkArray 5 0 := by
  simp [seatFake, open_ops, built_ops_arr]

private theorem fake_home0 (t : Spec.Tier) (x y : List Nat) :
    (seatFake t x y).sudo_5Board_4home[0]'(by rw [fake_szH]; decide) = embed x := by
  simpa [seatFake] using rec_home0 t x y

private theorem fake_home1 (t : Spec.Tier) (x y : List Nat) :
    (seatFake t x y).sudo_5Board_4home[1]'(by rw [fake_szH]; decide) = embed y := by
  simpa [seatFake] using rec_home1 t x y

private theorem fake_home3 (t : Spec.Tier) (x y : List Nat) :
    (seatFake t x y).sudo_5Board_4home[3]'(by rw [fake_szH]; decide) = embed x := by
  simpa [seatFake] using rec_home3 t x y

private theorem fake_home4 (t : Spec.Tier) (x y : List Nat) :
    (seatFake t x y).sudo_5Board_4home[4]'(by rw [fake_szH]; decide) = embed y := by
  simpa [seatFake] using rec_home4 t x y

private theorem fake_held0 (t : Spec.Tier) (x y : List Nat) :
    (seatFake t x y).sudo_5Board_4held[0]'(by rw [fake_szD]; decide) = true := by
  simpa [seatFake] using rec_held0 t x y

private theorem fake_held1 (t : Spec.Tier) (x y : List Nat) :
    (seatFake t x y).sudo_5Board_4held[1]'(by rw [fake_szD]; decide) = true := by
  simpa [seatFake] using rec_held1 t x y

private theorem fake_held2 (t : Spec.Tier) (x y : List Nat) :
    (seatFake t x y).sudo_5Board_4held[2]'(by rw [fake_szD]; decide) = false := by
  simpa [seatFake] using rec_held2 t x y

private theorem fake_held3 (t : Spec.Tier) (x y : List Nat) :
    (seatFake t x y).sudo_5Board_4held[3]'(by rw [fake_szD]; decide) = true := by
  simpa [seatFake] using rec_held3 t x y

private theorem fake_held4 (t : Spec.Tier) (x y : List Nat) :
    (seatFake t x y).sudo_5Board_4held[4]'(by rw [fake_szD]; decide) = true := by
  simpa [seatFake] using rec_held4 t x y

private theorem fake_held5 (t : Spec.Tier) (x y : List Nat) :
    (seatFake t x y).sudo_5Board_4held[5]'(by rw [fake_szD]; decide) = false := by
  simpa [seatFake] using rec_held5 t x y

private theorem fake_held6 (t : Spec.Tier) (x y : List Nat) :
    (seatFake t x y).sudo_5Board_4held[6]'(by rw [fake_szD]; decide) = false := by
  simpa [seatFake] using rec_held6 t x y

private theorem fake_ops_sz (t : Spec.Tier) (x y : List Nat) :
    (seatFake t x y).sudo_5Board_4cost.sudo_5Costs_3ops.size = 5 := by
  rw [fake_ops]
  simp [Array.size_mkArray]

private theorem ops_at_eq {a b : Array Int} (h : a = b) {i : Nat}
    {ha : i < a.size} {hb : i < b.size} (hv : b[i] = (0 : Int)) : a[i] = 0 := by
  subst h
  have : (⟨i, ha⟩ : Fin a.size) = ⟨i, hb⟩ := Fin.ext rfl
  simpa [this] using hv

private theorem fake_ops_at (t : Spec.Tier) (x y : List Nat) (i : Nat)
    (hi : i < (seatFake t x y).sudo_5Board_4cost.sudo_5Costs_3ops.size) :
    (seatFake t x y).sudo_5Board_4cost.sudo_5Costs_3ops[i] = 0 := by
  have h := fake_ops t x y
  have hb : i < (Array.mkArray 5 (0 : Int)).size := by
    rw [← h]
    exact hi
  exact ops_at_eq h (ha := hi) (hb := hb) (by simp [Array.getElem_mkArray])

private theorem small_fit (n : Nat) (hn : n ≤ 10) : FitsLen n := by
  unfold FitsLen i64MaxNat
  omega

/-- The early-marker board is a `RunFrame` for the copied base point.
    Control is `tierR − 1`, so the lift restores `tierR`. Strict and hole are 0. -/
private def whiteFakeFrame (t : Spec.Tier) (x y : List Nat) (tw : TierWalk t) (hOk : BoardOk t)
    (hR : 0 < tierR t) (hx : x.length = t.n) (hy : y.length = t.n)
    (htriX : allTritList x) (hcells : 0 < t.cells) :
    RunFrame (seatFake t x y) t x x :=
  let mv := pegCount x + pegCount y + pegCount x + pegCount y
  { szH := fake_szH t x y
    szD := fake_szD t x y
    bench := fake_bench t x y
    held5 := fake_held5 t x y
    held6 := fake_held6 t x y
    held2 := fake_held2 t x y
    held0 := fake_held0 t x y
    home0 := fake_home0 t x y
    held3 := fake_held3 t x y
    home3 := fake_home3 t x y
    y1 := y
    y4 := y
    flag1 := true
    flag4 := true
    home1 := fake_home1 t x y
    held1 := fake_held1 t x y
    home4 := fake_home4 t x y
    held4 := fake_held4 t x y
    mark := 0
    mx := 0
    hmark := fake_marker t x y
    hmx := fake_mx t x y
    lenX := hx
    lenA := hx
    triX := htriX
    triA := htriX
    tier := fake_tier t x y
    moves := mv
    slides := 0
    peak := 4
    ctrl := tierR t - 1
    high := t.script + tierR t + 1
    cOps := 0
    chordOps := 0
    opsCap := 1
    peakS := 0
    hole := 0
    hmoves := fake_moves t x y
    hslides := fake_slides t x y
    hpeak := fake_peak t x y
    hctrl := fake_ctrl t x y
    hhigh := fake_high t x y hR
    tmax := 0
    htally := fake_tally t x y
    ht0 := fake_t0 t x y
    hrow := fake_row t x y
    htmax := fake_tmax t x y
    hStart := Or.inl ⟨built_high_lt t, rfl⟩
    hlad := fake_ladder t x y
    hl0 := fake_l0 t x y
    hnr := fake_nr t x y
    hpark := fake_park t x y
    hfrom := fake_from t x y
    hridx := fake_ridx t x y
    hstrict := fake_strict t x y
    hhole := fake_hole t x y
    ops2 := by rw [fake_ops_sz]; decide
    ops3 := by rw [fake_ops_sz]; decide
    hop2 := fake_ops_at t x y 2 (by rw [fake_ops_sz]; decide)
    hop3 := fake_ops_at t x y 3 (by rw [fake_ops_sz]; decide)
    fitInv := small_fit 1 (by decide)
    fitChord := small_fit 1 (by decide)
    fitCtrl := by
      have he : (tierR t - 1) + 1 = tierR t := by omega
      simpa [he] using tierR_fit t hOk
    fitRoom := by
      apply FitsLen.of_le tw.roomM
      have hpx : pegCount x ≤ t.n := by rw [← hx]; exact pegCount_le x
      have hpy : pegCount y ≤ t.n := by rw [← hy]; exact pegCount_le y
      have hone : 1 ≤ t.cells + 1 := by omega
      have hwalk : 7 * t.n ≤ walkCharge t := by
        unfold walkCharge cellMoveCharge
        omega
      have hmul : walkCharge t ≤ (t.cells + 1) * walkCharge t :=
        Nat.le_mul_of_pos_left (walkCharge t) hone
      omega
    opsRoom := by
      intro i hi
      refine ⟨0, fake_ops_at t x y i hi, ?_⟩
      by_cases h2 : i = 2
      · simp [h2]
      · by_cases h3 : i = 3
        · simp [h2, h3]
        · simp [h2, h3] }

private theorem lift_white (t : Spec.Tier) (x y : List Nat) (hOk : BoardOk t) (hR : 0 < tierR t) :
    Ecbs.marker_lift (seatFake t x y) = .ok (whiteRec t x y) := by
  have hm0 : (seatFake t x y).sudo_5Board_6marker = Int.ofNat 0 := fake_marker t x y
  have hc0 : (seatFake t x y).sudo_5Board_4cost.sudo_5Costs_4ctrl =
      Int.ofNat (tierR t - 1) := fake_ctrl t x y
  have hfit : FitsLen ((tierR t - 1) + 1) := by
    have he : (tierR t - 1) + 1 = tierR t := by omega
    simpa [he] using tierR_fit t hOk
  rw [marker_lift_refines (seatFake t x y) 0 (tierR t - 1) hm0 hc0 hfit]
  have hsum : (tierR t - 1) + 1 = tierR t := by omega
  simp [seatFake, hsum]
  rw [← open_marker t x y]
  have hc : (whiteRec t x y).sudo_5Board_4cost.sudo_5Costs_4ctrl = ↑(tierR t) := by
    simpa [ofNat_eq_natCast] using open_ctrl t x y
  rw [← hc]

/-- Frobenius on the white opening board. The marker was `-1`; the cube seats it
    at 1 and the output is a `RunFrame` for the cubed across. -/
theorem seat_white (t : Spec.Tier) (x y : List Nat) (tw : TierWalk t) (hOk : BoardOk t)
    (sat : TierSat t) (hsh : TierShape t) (hR : 0 < tierR t)
    (hx : x.length = t.n) (hy : y.length = t.n)
    (htriX : allTritList x) (htriY : allTritList y) (hcells : 0 < t.cells) :
    ∃ bL bF, ∃ fr' : RunFrame bF t x (fieldCube t.n t.k t.benchlen x),
      Ecbs.marker_lift (whiteRec t x y) = .ok (whiteRec t x y) ∧
      Ecbs.frobenius_affine (whiteRec t x y) = .ok bF ∧
      bL = whiteRec t x y ∧
      bF.sudo_5Board_9marker_on = true ∧
      fr'.y1 = fieldCube t.n t.k t.benchlen y ∧
      fr'.y4 = y ∧
      fr'.mark = 1 ∧
      fr'.ctrl = tierR t - 1 + 4 ∧
      fr'.peakS ≤ 7 ∧
      fr'.hole ≤ t.benchlen ∧
      fr'.moves ≤ pegCount x + pegCount y + pegCount x + pegCount y +
        cubeCharge t.n t.benchlen ∧
      fr'.slides ≤ 4 * t.n ∧
      fr'.opsCap = 3 ∧
      fr'.flag1 = true ∧
      fr'.flag4 = true := by
  let fr := whiteFakeFrame t x y tw hOk hR hx hy htriX hcells
  have hgeom : ∀ m, m ≤ 15 * t.n + 6 * t.benchlen → FitsLen m := by
    intro m hm
    apply geomFit t.n t.benchlen m hsh.n_small hsh.small.2.2.2
    omega
  have hMove : FitsLen (fr.moves + cubeCharge t.n t.benchlen + 3 * t.n) := by
    apply hgeom
    have hpx : pegCount x ≤ t.n := by rw [← hx]; exact pegCount_le x
    have hpy : pegCount y ≤ t.n := by rw [← hy]; exact pegCount_le y
    have hmv : fr.moves = pegCount x + pegCount y + pegCount x + pegCount y := rfl
    rw [hmv]
    unfold cubeCharge
    omega
  have hSlide : FitsLen (fr.slides + slideCharge t.n) := by
    apply hgeom
    rw [show fr.slides = 0 from rfl, slideCharge, Nat.zero_add]
    omega
  have hCtrl : FitsLen (fr.ctrl + 5) := by
    apply hgeom
    rw [show fr.ctrl = tierR t - 1 from rfl]
    have hlen := rungList_length_le (t.n - 1)
    have hle : tierR t ≤ t.n := by
      unfold tierR
      exact Nat.le_trans hlen (Nat.sub_le _ _)
    omega
  have hOps : FitsLen (fr.opsCap + 2) := by
    apply FitsLen.of_le tw.roomO
    have ho : fr.opsCap = 1 := rfl
    rw [ho]
    exact Nat.le_trans (by decide) tw.sevenLe
  obtain ⟨bL, bF, fr', hml, hfrob, hmk, hy1, hy4, hf1, hf4, hctrl, hmark,
      _cOps, _chord, hmv, hsl, hops, hheld, ⟨occU, hocc, hpeak⟩, hhole, htopX, htopY⟩ :=
    cell_run_frame (seatFake t x y) t x x y y fr hOk sat hsh (fake_flag t x y)
      rfl rfl rfl rfl hy htriY hMove hSlide hCtrl hOps
  have hlift := lift_white t x y hOk hR
  have hbL : bL = whiteRec t x y := Except.ok.inj (hml.symm.trans hlift)
  have hst : fr'.peakS ≤ 7 := by
    rw [hpeak]
    exact strict_out_le fr.peakS (countHeld (seatFake t x y).sudo_5Board_4held 7) occU
      (by rw [show fr.peakS = 0 from rfl]; decide) hheld hocc
  have hho : fr'.hole ≤ t.benchlen := by
    rw [hhole]
    exact hole_out_le fr.hole (topIdx (combStrip t.n t.benchlen x))
      (topIdx (combStrip t.n t.benchlen y)) t.benchlen
      (by rw [show fr.hole = 0 from rfl]; exact Nat.zero_le _) htopX htopY
  refine ⟨bL, bF, fr', marker_lift_down (whiteRec t x y) (open_marker t x y), ?_,
    hbL, hmk, hy1, hy4, hmark, ?_, hst, hho, ?_, ?_, ?_, hf1, hf4⟩
  · rw [← hbL]
    exact hfrob
  · rw [hctrl, show fr.ctrl = tierR t - 1 from rfl]
  · have hpre : fr.moves = pegCount x + pegCount y + pegCount x + pegCount y := rfl
    rw [hpre] at hmv
    exact hmv
  · have hpre : fr.slides = 0 := rfl
    rw [hpre, slideCharge, Nat.zero_add] at hsl
    exact hsl
  · have hpre : fr.opsCap = 1 := rfl
    rw [hpre] at hops
    exact hops

/-- The board after that Frobenius is a `LiveAt` frame `walk_chord_from` can start
    from. One cell has been spent, so the counters sit under a single charge.
    The accumulator is the cube; a nonzero seat cell still has its chord to run. -/
theorem seat_white_at (t : Spec.Tier) (x y : List Nat) (tw : TierWalk t) (hOk : BoardOk t)
    (sat : TierSat t) (hsh : TierShape t) (hR : 0 < tierR t)
    (hx : x.length = t.n) (hy : y.length = t.n)
    (htriX : allTritList x) (htriY : allTritList y) (hcells : 0 < t.cells) :
    ∃ bF, ∃ _fr : RunFrame bF t x (fieldCube t.n t.k t.benchlen x),
      Ecbs.frobenius_affine (whiteRec t x y) = .ok bF ∧
      LiveAt t bF x y (fieldCube t.n t.k t.benchlen x) (fieldCube t.n t.k t.benchlen y) 1 := by
  obtain ⟨_bL, bF, fr', _hlift, hfrob, _hbL, hmk, hy1, hy4, _hmark, hctrlS, hst, hho,
      hmv, hsl, hops, hf1, hf4⟩ :=
    seat_white t x y tw hOk sat hsh hR hx hy htriX htriY hcells
  refine ⟨bF, fr', hfrob, fr', hmk, hy4, hy1, hf4, hf1, hst, hho, ?_, ?_, ?_, ?_,
    hy, htriY, fieldCube_length t.n t.k t.benchlen y tw.nLe, ?_⟩
  · have hpeg : pegCount x + pegCount y + pegCount x + pegCount y ≤ walkCharge t := by
      unfold walkCharge cellMoveCharge
      have hpx : pegCount x ≤ t.n := by rw [← hx]; exact pegCount_le x
      have hpy : pegCount y ≤ t.n := by rw [← hy]; exact pegCount_le y
      omega
    have hcube : cubeCharge t.n t.benchlen = 6 * t.benchlen + 2 * t.n := cube_over _ _ tw.nLe
    calc
      fr'.moves ≤ pegCount x + pegCount y + pegCount x + pegCount y +
          cubeCharge t.n t.benchlen := hmv
      _ ≤ walkCharge t + (6 * t.benchlen + 2 * t.n) := by rw [hcube]; omega
      _ = 1 * (walkCharge t + (6 * t.benchlen + 2 * t.n)) := by omega
  · calc
      fr'.slides ≤ 4 * t.n := hsl
      _ ≤ cellSlideCharge t + slideCharge t.n := by
        rw [slideCharge]
        omega
      _ = 1 * (cellSlideCharge t + slideCharge t.n) := by omega
  · have hctrl : fr'.ctrl = tierR t + 3 := by
      rw [hctrlS]
      omega
    rw [hctrl, Nat.one_mul]
    have h5 : 5 ≤ 3 * rowRoom t + 5 := by omega
    have hmul : (tierR t + 1) * 5 ≤ (tierR t + 1) * (3 * rowRoom t + 5) :=
      Nat.mul_le_mul_left _ h5
    have hchg : cellCtrlCharge t = 1 + (tierR t + 1) * (3 * rowRoom t + 5) + 6 := by
      unfold cellCtrlCharge
      rfl
    rw [hchg]
    omega
  · rw [hops, Nat.one_mul]
    unfold cellOpsCharge
    omega
  · apply fieldCube_trits t.n t.k t.benchlen y htriY
    · have h := sat.cube_span
      omega
    · exact hsh.k_le

/-- The red opening with the marker seated one step early. Private, as `seatFake` is. -/
private def redFake (t : Spec.Tier) (x y : List Nat) : Ecbs.Board :=
  { redRec t x y with
    sudo_5Board_6marker := 0
    sudo_5Board_4cost := { (redRec t x y).sudo_5Board_4cost with
      sudo_5Costs_4ctrl := Int.ofNat (tierR t - 1) } }

private theorem redF_szH (t : Spec.Tier) (x y : List Nat) :
    (redFake t x y).sudo_5Board_4home.size = 8 := by
  simpa [redFake] using red_szH t x y

private theorem redF_szD (t : Spec.Tier) (x y : List Nat) :
    (redFake t x y).sudo_5Board_4held.size = 8 := by
  simpa [redFake] using red_szD t x y

private theorem redF_marker (t : Spec.Tier) (x y : List Nat) :
    (redFake t x y).sudo_5Board_6marker = 0 := by
  simp [redFake]

private theorem redF_ctrl (t : Spec.Tier) (x y : List Nat) :
    (redFake t x y).sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (tierR t - 1) := by
  simp [redFake]

private theorem redF_flag (t : Spec.Tier) (x y : List Nat) :
    (redFake t x y).sudo_5Board_9marker_on = true := by
  simpa [redFake] using red_flag t x y

private theorem redF_bench (t : Spec.Tier) (x y : List Nat) :
    (redFake t x y).sudo_5Board_8bench_on = false := by
  simpa [redFake] using red_bench t x y

private theorem redF_strict (t : Spec.Tier) (x y : List Nat) :
    (redFake t x y).sudo_5Board_4cost.sudo_5Costs_11peak_strict = 0 := by
  simpa [redFake] using red_strict t x y

private theorem redF_hole (t : Spec.Tier) (x y : List Nat) :
    (redFake t x y).sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = 0 := by
  simpa [redFake] using red_hole t x y

private theorem redF_slides (t : Spec.Tier) (x y : List Nat) :
    (redFake t x y).sudo_5Board_4cost.sudo_5Costs_6slides = 0 := by
  simpa [redFake] using red_slides t x y

private theorem redF_moves (t : Spec.Tier) (x y : List Nat) :
    (redFake t x y).sudo_5Board_4cost.sudo_5Costs_5moves =
      Int.ofNat (pegCount x + pegCount y + pegCount x + pegCount y) := by
  simpa [redFake] using red_moves t x y

private theorem redF_peak (t : Spec.Tier) (x y : List Nat) :
    (redFake t x y).sudo_5Board_4cost.sudo_5Costs_4peak = 4 := by
  simpa [redFake] using red_peak t x y

private theorem redF_mx (t : Spec.Tier) (x y : List Nat) :
    (redFake t x y).sudo_5Board_4cost.sudo_5Costs_17script_marker_max = 0 := by
  simpa [redFake] using red_mx t x y

private theorem redF_tier (t : Spec.Tier) (x y : List Nat) :
    (redFake t x y).sudo_5Board_1t = embTier t := by
  simpa [redFake] using red_tier t x y

private theorem redF_row (t : Spec.Tier) (x y : List Nat) :
    (redFake t x y).sudo_5Board_3row = embed (paintedRow t) := by
  simpa [redFake] using red_row t x y

private theorem redF_ladder (t : Spec.Tier) (x y : List Nat) :
    (redFake t x y).sudo_5Board_6ladder = embed (tierClimb t) := by
  simpa [redFake] using red_ladder t x y

private theorem redF_l0 (t : Spec.Tier) (x y : List Nat) :
    (redFake t x y).sudo_5Board_7ladder0 = Int.ofNat (t.script + 2) := by
  simpa [redFake] using red_l0 t x y

private theorem redF_nr (t : Spec.Tier) (x y : List Nat) :
    (redFake t x y).sudo_5Board_6nrungs = Int.ofNat (tierR t) := by
  simpa [redFake] using red_nr t x y

private theorem redF_park (t : Spec.Tier) (x y : List Nat) :
    (redFake t x y).sudo_5Board_9park_hole = Int.ofNat (t.script + 2 + tierR t) := by
  simpa [redFake] using red_park t x y

private theorem redF_from (t : Spec.Tier) (x y : List Nat) :
    (redFake t x y).sudo_5Board_11parked_from = -1 := by
  simpa [redFake] using red_from t x y

private theorem redF_ridx (t : Spec.Tier) (x y : List Nat) :
    (redFake t x y).sudo_5Board_8rung_idx = 0 := by
  simpa [redFake] using red_ridx t x y

private theorem redF_tally (t : Spec.Tier) (x y : List Nat) :
    (redFake t x y).sudo_5Board_9tally_len = 0 := by
  simpa [redFake] using red_tally t x y

private theorem redF_t0 (t : Spec.Tier) (x y : List Nat) :
    (redFake t x y).sudo_5Board_6tally0 = Int.ofNat (tallyOrigin t) := by
  simpa [redFake] using red_t0 t x y

private theorem redF_high (t : Spec.Tier) (x y : List Nat) (hR : 0 < tierR t) :
    (redFake t x y).sudo_5Board_4cost.sudo_5Costs_15control_highest =
      Int.ofNat (t.script + tierR t + 1) := by
  simpa [redFake] using red_high t x y hR

private theorem redF_tmax (t : Spec.Tier) (x y : List Nat) :
    (redFake t x y).sudo_5Board_4cost.sudo_5Costs_9tally_max = 0 := by
  simpa [redFake] using red_tmax t x y

private theorem redF_ops (t : Spec.Tier) (x y : List Nat) :
    (redFake t x y).sudo_5Board_4cost.sudo_5Costs_3ops = Array.mkArray 5 0 := by
  simpa [redFake] using red_ops t x y

private theorem redF_home0 (t : Spec.Tier) (x y : List Nat) :
    (redFake t x y).sudo_5Board_4home[0]'(by rw [redF_szH]; decide) = embed x := by
  simpa [redFake] using red_home0 t x y

private theorem redF_home1 (t : Spec.Tier) (x y : List Nat) :
    (redFake t x y).sudo_5Board_4home[1]'(by rw [redF_szH]; decide) =
      embed (mirrorTrits y) := by
  simpa [redFake] using red_home1 t x y

private theorem redF_home3 (t : Spec.Tier) (x y : List Nat) :
    (redFake t x y).sudo_5Board_4home[3]'(by rw [redF_szH]; decide) = embed x := by
  simpa [redFake] using red_home3 t x y

private theorem redF_home4 (t : Spec.Tier) (x y : List Nat) :
    (redFake t x y).sudo_5Board_4home[4]'(by rw [redF_szH]; decide) = embed y := by
  simpa [redFake] using red_home4 t x y

private theorem redF_held0 (t : Spec.Tier) (x y : List Nat) :
    (redFake t x y).sudo_5Board_4held[0]'(by rw [redF_szD]; decide) = true := by
  simpa [redFake] using red_held0 t x y

private theorem redF_held1 (t : Spec.Tier) (x y : List Nat) :
    (redFake t x y).sudo_5Board_4held[1]'(by rw [redF_szD]; decide) = true := by
  simpa [redFake] using red_held1 t x y

private theorem redF_held2 (t : Spec.Tier) (x y : List Nat) :
    (redFake t x y).sudo_5Board_4held[2]'(by rw [redF_szD]; decide) = false := by
  simpa [redFake] using red_held2 t x y

private theorem redF_held3 (t : Spec.Tier) (x y : List Nat) :
    (redFake t x y).sudo_5Board_4held[3]'(by rw [redF_szD]; decide) = true := by
  simpa [redFake] using red_held3 t x y

private theorem redF_held4 (t : Spec.Tier) (x y : List Nat) :
    (redFake t x y).sudo_5Board_4held[4]'(by rw [redF_szD]; decide) = true := by
  simpa [redFake] using red_held4 t x y

private theorem redF_held5 (t : Spec.Tier) (x y : List Nat) :
    (redFake t x y).sudo_5Board_4held[5]'(by rw [redF_szD]; decide) = false := by
  simpa [redFake] using red_held5 t x y

private theorem redF_held6 (t : Spec.Tier) (x y : List Nat) :
    (redFake t x y).sudo_5Board_4held[6]'(by rw [redF_szD]; decide) = false := by
  simpa [redFake] using red_held6 t x y

private theorem redF_ops_sz (t : Spec.Tier) (x y : List Nat) :
    (redFake t x y).sudo_5Board_4cost.sudo_5Costs_3ops.size = 5 := by
  rw [redF_ops]
  simp [Array.size_mkArray]

private theorem redF_ops_at (t : Spec.Tier) (x y : List Nat) (i : Nat)
    (hi : i < (redFake t x y).sudo_5Board_4cost.sudo_5Costs_3ops.size) :
    (redFake t x y).sudo_5Board_4cost.sudo_5Costs_3ops[i] = 0 := by
  have h := redF_ops t x y
  have hb : i < (Array.mkArray 5 (0 : Int)).size := by
    rw [← h]
    exact hi
  exact ops_at_eq h (ha := hi) (hb := hb) (by simp [Array.getElem_mkArray])

/-- The early-marker red board is a `RunFrame` for the copied base across
    and the negated base up. -/
private def redFakeFrame (t : Spec.Tier) (x y : List Nat) (tw : TierWalk t) (hOk : BoardOk t)
    (hR : 0 < tierR t) (hx : x.length = t.n) (hy : y.length = t.n)
    (htriX : allTritList x) (hcells : 0 < t.cells) :
    RunFrame (redFake t x y) t x x :=
  let mv := pegCount x + pegCount y + pegCount x + pegCount y
  { szH := redF_szH t x y
    szD := redF_szD t x y
    bench := redF_bench t x y
    held5 := redF_held5 t x y
    held6 := redF_held6 t x y
    held2 := redF_held2 t x y
    held0 := redF_held0 t x y
    home0 := redF_home0 t x y
    held3 := redF_held3 t x y
    home3 := redF_home3 t x y
    y1 := mirrorTrits y
    y4 := y
    flag1 := true
    flag4 := true
    home1 := redF_home1 t x y
    held1 := redF_held1 t x y
    home4 := redF_home4 t x y
    held4 := redF_held4 t x y
    mark := 0
    mx := 0
    hmark := redF_marker t x y
    hmx := redF_mx t x y
    lenX := hx
    lenA := hx
    triX := htriX
    triA := htriX
    tier := redF_tier t x y
    moves := mv
    slides := 0
    peak := 4
    ctrl := tierR t - 1
    high := t.script + tierR t + 1
    cOps := 0
    chordOps := 0
    opsCap := 1
    peakS := 0
    hole := 0
    hmoves := redF_moves t x y
    hslides := redF_slides t x y
    hpeak := redF_peak t x y
    hctrl := redF_ctrl t x y
    hhigh := redF_high t x y hR
    tmax := 0
    htally := redF_tally t x y
    ht0 := redF_t0 t x y
    hrow := redF_row t x y
    htmax := redF_tmax t x y
    hStart := Or.inl ⟨built_high_lt t, rfl⟩
    hlad := redF_ladder t x y
    hl0 := redF_l0 t x y
    hnr := redF_nr t x y
    hpark := redF_park t x y
    hfrom := redF_from t x y
    hridx := redF_ridx t x y
    hstrict := redF_strict t x y
    hhole := redF_hole t x y
    ops2 := by rw [redF_ops_sz]; decide
    ops3 := by rw [redF_ops_sz]; decide
    hop2 := redF_ops_at t x y 2 (by rw [redF_ops_sz]; decide)
    hop3 := redF_ops_at t x y 3 (by rw [redF_ops_sz]; decide)
    fitInv := small_fit 1 (by decide)
    fitChord := small_fit 1 (by decide)
    fitCtrl := by
      have he : (tierR t - 1) + 1 = tierR t := by omega
      simpa [he] using tierR_fit t hOk
    fitRoom := by
      apply FitsLen.of_le tw.roomM
      have hpx : pegCount x ≤ t.n := by rw [← hx]; exact pegCount_le x
      have hpy : pegCount y ≤ t.n := by rw [← hy]; exact pegCount_le y
      have hone : 1 ≤ t.cells + 1 := by omega
      have hwalk : 7 * t.n ≤ walkCharge t := by
        unfold walkCharge cellMoveCharge
        omega
      have hmul : walkCharge t ≤ (t.cells + 1) * walkCharge t :=
        Nat.le_mul_of_pos_left (walkCharge t) hone
      omega
    opsRoom := by
      intro i hi
      refine ⟨0, redF_ops_at t x y i hi, ?_⟩
      by_cases h2 : i = 2
      · simp [h2]
      · by_cases h3 : i = 3
        · simp [h2, h3]
        · simp [h2, h3] }

private theorem lift_red (t : Spec.Tier) (x y : List Nat) (hOk : BoardOk t) (hR : 0 < tierR t) :
    Ecbs.marker_lift (redFake t x y) = .ok (redRec t x y) := by
  have hm0 : (redFake t x y).sudo_5Board_6marker = Int.ofNat 0 := redF_marker t x y
  have hc0 : (redFake t x y).sudo_5Board_4cost.sudo_5Costs_4ctrl =
      Int.ofNat (tierR t - 1) := redF_ctrl t x y
  have hfit : FitsLen ((tierR t - 1) + 1) := by
    have he : (tierR t - 1) + 1 = tierR t := by omega
    simpa [he] using tierR_fit t hOk
  rw [marker_lift_refines (redFake t x y) 0 (tierR t - 1) hm0 hc0 hfit]
  have hsum : (tierR t - 1) + 1 = tierR t := by omega
  simp [redFake, hsum]
  rw [← red_marker t x y]
  have hc : (redRec t x y).sudo_5Board_4cost.sudo_5Costs_4ctrl = ↑(tierR t) := by
    simpa [ofNat_eq_natCast] using red_ctrl t x y
  rw [← hc]

/-- Frobenius on the red opening board. The up home is the negated base up,
    so the cube seats that negation. The marker was `-1`. -/
theorem seat_red (t : Spec.Tier) (x y : List Nat) (tw : TierWalk t) (hOk : BoardOk t)
    (sat : TierSat t) (hsh : TierShape t) (hR : 0 < tierR t)
    (hx : x.length = t.n) (hy : y.length = t.n)
    (htriX : allTritList x) (htriY : allTritList y) (hcells : 0 < t.cells) :
    ∃ bL bF, ∃ fr' : RunFrame bF t x (fieldCube t.n t.k t.benchlen x),
      Ecbs.marker_lift (redRec t x y) = .ok (redRec t x y) ∧
      Ecbs.frobenius_affine (redRec t x y) = .ok bF ∧
      bL = redRec t x y ∧
      bF.sudo_5Board_9marker_on = true ∧
      fr'.y1 = fieldCube t.n t.k t.benchlen (mirrorTrits y) ∧
      fr'.y4 = y ∧
      fr'.mark = 1 ∧
      fr'.ctrl = tierR t - 1 + 4 ∧
      fr'.peakS ≤ 7 ∧
      fr'.hole ≤ t.benchlen ∧
      fr'.moves ≤ pegCount x + pegCount (mirrorTrits y) + pegCount x +
        pegCount (mirrorTrits y) + cubeCharge t.n t.benchlen ∧
      fr'.slides ≤ 4 * t.n ∧
      fr'.opsCap = 3 ∧
      fr'.flag1 = true ∧
      fr'.flag4 = true := by
  let fr := redFakeFrame t x y tw hOk hR hx hy htriX hcells
  have hgeom : ∀ m, m ≤ 15 * t.n + 6 * t.benchlen → FitsLen m := by
    intro m hm
    apply geomFit t.n t.benchlen m hsh.n_small hsh.small.2.2.2
    omega
  have hMove : FitsLen (fr.moves + cubeCharge t.n t.benchlen + 3 * t.n) := by
    apply hgeom
    have hpx : pegCount x ≤ t.n := by rw [← hx]; exact pegCount_le x
    have hpy : pegCount y ≤ t.n := by rw [← hy]; exact pegCount_le y
    have hmv : fr.moves = pegCount x + pegCount y + pegCount x + pegCount y := rfl
    rw [hmv]
    unfold cubeCharge
    omega
  have hSlide : FitsLen (fr.slides + slideCharge t.n) := by
    apply hgeom
    rw [show fr.slides = 0 from rfl, slideCharge, Nat.zero_add]
    omega
  have hCtrl : FitsLen (fr.ctrl + 5) := by
    apply hgeom
    rw [show fr.ctrl = tierR t - 1 from rfl]
    have hlen := rungList_length_le (t.n - 1)
    have hle : tierR t ≤ t.n := by
      unfold tierR
      exact Nat.le_trans hlen (Nat.sub_le _ _)
    omega
  have hOps : FitsLen (fr.opsCap + 2) := by
    apply FitsLen.of_le tw.roomO
    have ho : fr.opsCap = 1 := rfl
    rw [ho]
    exact Nat.le_trans (by decide) tw.sevenLe
  obtain ⟨bL, bF, fr', hml, hfrob, hmk, hy1, hy4, hf1, hf4, hctrl, hmark,
      _cOps, _chord, hmv, hsl, hops, hheld, ⟨occU, hocc, hpeak⟩, hhole, htopX, htopY⟩ :=
    cell_run_frame (redFake t x y) t x x y (mirrorTrits y) fr hOk sat hsh
      (redF_flag t x y) rfl rfl rfl rfl
      (by rw [mirror_length]; exact hy) (mirrorTrits_allTrit htriY)
      hMove hSlide hCtrl hOps
  have hlift := lift_red t x y hOk hR
  have hbL : bL = redRec t x y := Except.ok.inj (hml.symm.trans hlift)
  have hst : fr'.peakS ≤ 7 := by
    rw [hpeak]
    exact strict_out_le fr.peakS (countHeld (redFake t x y).sudo_5Board_4held 7) occU
      (by rw [show fr.peakS = 0 from rfl]; decide) hheld hocc
  have hho : fr'.hole ≤ t.benchlen := by
    rw [hhole]
    exact hole_out_le fr.hole (topIdx (combStrip t.n t.benchlen x))
      (topIdx (combStrip t.n t.benchlen (mirrorTrits y))) t.benchlen
      (by rw [show fr.hole = 0 from rfl]; exact Nat.zero_le _) htopX htopY
  refine ⟨bL, bF, fr', marker_lift_down (redRec t x y) (red_marker t x y), ?_,
    hbL, hmk, hy1, hy4, hmark, ?_, hst, hho, ?_, ?_, ?_, hf1, hf4⟩
  · rw [← hbL]
    exact hfrob
  · rw [hctrl, show fr.ctrl = tierR t - 1 from rfl]
  · have hpre : fr.moves = pegCount x + pegCount y + pegCount x + pegCount y := rfl
    rw [hpre] at hmv
    rw [pegCount_mirror y htriY]
    exact hmv
  · have hpre : fr.slides = 0 := rfl
    rw [hpre, slideCharge, Nat.zero_add] at hsl
    exact hsl
  · have hpre : fr.opsCap = 1 := rfl
    rw [hpre] at hops
    exact hops

/-- The board after that Frobenius is a `LiveAt` frame at one cell.
    The accumulator up is the cube of the negated base up. -/
theorem seat_red_at (t : Spec.Tier) (x y : List Nat) (tw : TierWalk t) (hOk : BoardOk t)
    (sat : TierSat t) (hsh : TierShape t) (hR : 0 < tierR t)
    (hx : x.length = t.n) (hy : y.length = t.n)
    (htriX : allTritList x) (htriY : allTritList y) (hcells : 0 < t.cells) :
    ∃ bF, ∃ _fr : RunFrame bF t x (fieldCube t.n t.k t.benchlen x),
      Ecbs.frobenius_affine (redRec t x y) = .ok bF ∧
      LiveAt t bF x y (fieldCube t.n t.k t.benchlen x)
        (fieldCube t.n t.k t.benchlen (mirrorTrits y)) 1 := by
  obtain ⟨_bL, bF, fr', _hlift, hfrob, _hbL, hmk, hy1, hy4, _hmark, hctrlS, hst, hho,
      hmv, hsl, hops, hf1, hf4⟩ :=
    seat_red t x y tw hOk sat hsh hR hx hy htriX htriY hcells
  have hmirr : pegCount (mirrorTrits y) = pegCount y := pegCount_mirror y htriY
  rw [hmirr] at hmv
  refine ⟨bF, fr', hfrob, fr', hmk, hy4, hy1, hf4, hf1, hst, hho, ?_, ?_, ?_, ?_,
    hy, htriY, fieldCube_length t.n t.k t.benchlen (mirrorTrits y) tw.nLe, ?_⟩
  · have hpeg : pegCount x + pegCount y + pegCount x + pegCount y ≤ walkCharge t := by
      unfold walkCharge cellMoveCharge
      have hpx : pegCount x ≤ t.n := by rw [← hx]; exact pegCount_le x
      have hpy : pegCount y ≤ t.n := by rw [← hy]; exact pegCount_le y
      omega
    have hcube : cubeCharge t.n t.benchlen = 6 * t.benchlen + 2 * t.n := cube_over _ _ tw.nLe
    calc
      fr'.moves ≤ pegCount x + pegCount y + pegCount x + pegCount y +
          cubeCharge t.n t.benchlen := hmv
      _ ≤ walkCharge t + (6 * t.benchlen + 2 * t.n) := by rw [hcube]; omega
      _ = 1 * (walkCharge t + (6 * t.benchlen + 2 * t.n)) := by omega
  · calc
      fr'.slides ≤ 4 * t.n := hsl
      _ ≤ cellSlideCharge t + slideCharge t.n := by
        rw [slideCharge]
        omega
      _ = 1 * (cellSlideCharge t + slideCharge t.n) := by omega
  · have hctrl : fr'.ctrl = tierR t + 3 := by
      rw [hctrlS]
      omega
    rw [hctrl, Nat.one_mul]
    have h5 : 5 ≤ 3 * rowRoom t + 5 := by omega
    have hmul : (tierR t + 1) * 5 ≤ (tierR t + 1) * (3 * rowRoom t + 5) :=
      Nat.mul_le_mul_left _ h5
    have hchg : cellCtrlCharge t = 1 + (tierR t + 1) * (3 * rowRoom t + 5) + 6 := by
      unfold cellCtrlCharge
      rfl
    rw [hchg]
    omega
  · rw [hops, Nat.one_mul]
    unfold cellOpsCharge
    omega
  · apply fieldCube_trits t.n t.k t.benchlen (mirrorTrits y) (mirrorTrits_allTrit htriY)
    · have h := sat.cube_span
      omega
    · exact hsh.k_le

end EcbsLink2.Link2
