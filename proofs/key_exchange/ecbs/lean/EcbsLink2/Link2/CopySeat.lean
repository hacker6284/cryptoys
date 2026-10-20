/-
  The seat on the board `white_copy_kept` returns. The early marker is private.
  `place_*` already carried the control frame, so this file only reads `OutLay`.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.CopyKeep
import EcbsLink2.Link2.SeatChord

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- Marker seated one step early, so `marker_lift` returns the copied board. -/
private def early (b : Ecbs.Board) (t : Spec.Tier) : Ecbs.Board :=
  { b with
    sudo_5Board_6marker := 0
    sudo_5Board_4cost := { b.sudo_5Board_4cost with
      sudo_5Costs_4ctrl := Int.ofNat (tierR t - 1) } }

private theorem early_szH (b : Ecbs.Board) (t : Spec.Tier) (h : b.sudo_5Board_4home.size = 8) :
    (early b t).sudo_5Board_4home.size = 8 := by
  simpa [early] using h

private theorem early_szD (b : Ecbs.Board) (t : Spec.Tier) (h : b.sudo_5Board_4held.size = 8) :
    (early b t).sudo_5Board_4held.size = 8 := by
  simpa [early] using h

private theorem early_marker (b : Ecbs.Board) (t : Spec.Tier) :
    (early b t).sudo_5Board_6marker = 0 := by
  simp [early]

private theorem early_ctrl (b : Ecbs.Board) (t : Spec.Tier) :
    (early b t).sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (tierR t - 1) := by
  simp [early]

private theorem early_ops (b : Ecbs.Board) (t : Spec.Tier)
    (h : b.sudo_5Board_4cost.sudo_5Costs_3ops = Array.mkArray 5 0) :
    (early b t).sudo_5Board_4cost.sudo_5Costs_3ops = Array.mkArray 5 0 := by
  simpa [early] using h

private theorem slot_zero {a : Array Int} (h : a = Array.mkArray 5 0) {i : Nat}
    (hi : i < a.size) : a[i] = 0 := by
  subst h
  simp [Array.getElem_mkArray]

private theorem lift_early (b : Ecbs.Board) (t : Spec.Tier) (hOk : BoardOk t) (hR : 0 < tierR t)
    (hmark : b.sudo_5Board_6marker = -1)
    (hctrl : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (tierR t)) :
    Ecbs.marker_lift (early b t) = .ok b := by
  have hm0 : (early b t).sudo_5Board_6marker = Int.ofNat 0 := early_marker b t
  have hc0 : (early b t).sudo_5Board_4cost.sudo_5Costs_4ctrl =
      Int.ofNat (tierR t - 1) := early_ctrl b t
  have hfit : FitsLen ((tierR t - 1) + 1) := by
    have he : (tierR t - 1) + 1 = tierR t := by omega
    simpa [he] using tierR_fit t hOk
  rw [marker_lift_refines (early b t) 0 (tierR t - 1) hm0 hc0 hfit]
  have hsum : (tierR t - 1) + 1 = tierR t := by omega
  simp [early, hsum]
  rw [← hmark]
  have hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = ↑(tierR t) := by
    simpa [ofNat_eq_natCast] using hctrl
  rw [← hc]

private theorem small_fit (n : Nat) (hn : n ≤ 10) : FitsLen n := by
  unfold FitsLen i64MaxNat
  omega

/-- Frobenius of a copied board. The control frame is `OutLay`, which `place_*`
    carried off the board the copy started from. -/
theorem seat_out (t : Spec.Tier) (b : Ecbs.Board) (x y1 y4 : List Nat) (mv pk : Nat)
    (lay : OutLay t b x y1 y4 mv pk)
    (tw : TierWalk t) (hOk : BoardOk t) (sat : TierSat t) (hsh : TierShape t)
    (hR : 0 < tierR t)
    (hx : x.length = t.n) (hy1 : y1.length = t.n)
    (htriX : allTritList x) (htri1 : allTritList y1)
    (hmvN : mv ≤ 4 * t.n) (hcells : 0 < t.cells)
    (hfresh : lay.sl0 = 0 ∧ lay.ops0 = 0 ∧ lay.strict0 = 0 ∧ lay.hole0 = 0 ∧
      lay.mx0 = 0 ∧ lay.tmax0 = 0 ∧ lay.ctrl0 = tierR t ∧
      lay.high0 = t.script + tierR t + 1) :
    ∃ bF, ∃ fr' : RunFrame bF t x (fieldCube t.n t.k t.benchlen x),
      Ecbs.marker_lift b = .ok b ∧
      Ecbs.frobenius_affine b = .ok bF ∧
      bF.sudo_5Board_9marker_on = true ∧
      fr'.y1 = fieldCube t.n t.k t.benchlen y1 ∧
      fr'.y4 = y4 ∧
      fr'.mark = 1 ∧
      fr'.ctrl = tierR t - 1 + 4 ∧
      fr'.peakS ≤ 7 ∧
      fr'.hole ≤ t.benchlen ∧
      fr'.moves ≤ mv + cubeCharge t.n t.benchlen ∧
      fr'.slides ≤ 4 * t.n ∧
      fr'.opsCap = 3 ∧
      fr'.flag1 = true ∧
      fr'.flag4 = true := by
  rcases hfresh with ⟨hsl0, hops0, hstrict0, hhole0, hmx0, htmax0, hctrl0, hhigh0⟩
  let eb := early b t
  have hszH := early_szH b t lay.szH
  have hszD := early_szD b t lay.szD
  let fr : RunFrame eb t x x :=
    { szH := hszH
      szD := hszD
      bench := by simpa [eb, early] using lay.bench
      held5 := by simpa [eb, early] using lay.held5
      held6 := by simpa [eb, early] using lay.held6
      held2 := by simpa [eb, early] using lay.held2
      held0 := by simpa [eb, early] using lay.held0
      home0 := by simpa [eb, early] using lay.home0
      held3 := by simpa [eb, early] using lay.held3
      home3 := by simpa [eb, early] using lay.home3
      y1 := y1
      y4 := y4
      flag1 := true
      flag4 := true
      home1 := by simpa [eb, early] using lay.home1
      held1 := by simpa [eb, early] using lay.held1
      home4 := by simpa [eb, early] using lay.home4
      held4 := by simpa [eb, early] using lay.held4
      mark := 0
      mx := 0
      hmark := early_marker b t
      hmx := by simpa [eb, early, hmx0, ofNat_eq_natCast] using lay.mx
      lenX := hx
      lenA := hx
      triX := htriX
      triA := htriX
      tier := by simpa [eb, early] using lay.tier
      moves := mv
      slides := 0
      peak := pk
      ctrl := tierR t - 1
      high := t.script + tierR t + 1
      cOps := 0
      chordOps := 0
      opsCap := 1
      peakS := 0
      hole := 0
      hmoves := by simpa [eb, early] using lay.moves
      hslides := by simpa [eb, early, hsl0, ofNat_eq_natCast] using lay.slides
      hpeak := by simpa [eb, early] using lay.peak
      hctrl := early_ctrl b t
      hhigh := by simpa [eb, early, hhigh0, ofNat_eq_natCast] using lay.high
      tmax := 0
      htally := by simpa [eb, early] using lay.tally
      ht0 := by simpa [eb, early] using lay.t0
      hrow := by simpa [eb, early] using lay.row
      htmax := by simpa [eb, early, htmax0, ofNat_eq_natCast] using lay.tmax
      hStart := Or.inl ⟨built_high_lt t, rfl⟩
      hlad := by simpa [eb, early] using lay.ladder
      hl0 := by simpa [eb, early] using lay.l0
      hnr := by simpa [eb, early] using lay.nr
      hpark := by simpa [eb, early] using lay.park
      hfrom := by simpa [eb, early] using lay.parked
      hridx := by simpa [eb, early] using lay.ridx
      hstrict := by simpa [eb, early, hstrict0, ofNat_eq_natCast] using lay.strict
      hhole := by simpa [eb, early, hhole0, ofNat_eq_natCast] using lay.hole
      ops2 := by
        have hsz : (eb).sudo_5Board_4cost.sudo_5Costs_3ops.size = 5 := by
          simpa [eb, early] using lay.opsSz
        rw [hsz]; decide
      ops3 := by
        have hsz : (eb).sudo_5Board_4cost.sudo_5Costs_3ops.size = 5 := by
          simpa [eb, early] using lay.opsSz
        rw [hsz]; decide
      hop2 := by
        have hi : 2 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
          rw [lay.opsSz]; decide
        obtain ⟨c, hc, hle⟩ := lay.opsBound 2 hi
        have hc0 : c = 0 := by rw [hops0] at hle; omega
        simpa [eb, early, hc0] using hc
      hop3 := by
        have hi : 3 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
          rw [lay.opsSz]; decide
        obtain ⟨c, hc, hle⟩ := lay.opsBound 3 hi
        have hc0 : c = 0 := by rw [hops0] at hle; omega
        simpa [eb, early, hc0] using hc
      fitInv := small_fit 1 (by decide)
      fitChord := small_fit 1 (by decide)
      fitCtrl := by
        have he : (tierR t - 1) + 1 = tierR t := by omega
        simpa [he] using tierR_fit t hOk
      fitRoom := by
        apply FitsLen.of_le tw.roomM
        have hone : 1 ≤ t.cells + 1 := by omega
        have hwalk : 7 * t.n ≤ walkCharge t := by
          unfold walkCharge cellMoveCharge
          omega
        have hmul : walkCharge t ≤ (t.cells + 1) * walkCharge t :=
          Nat.le_mul_of_pos_left (walkCharge t) hone
        omega
      opsRoom := by
        intro i hi
        have hiB : i < b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
          simpa [eb, early] using hi
        obtain ⟨c, hc, hle⟩ := lay.opsBound i hiB
        have hc0 : c = 0 := by rw [hops0] at hle; omega
        refine ⟨0, by simpa [eb, early, hc0] using hc, ?_⟩
        by_cases h2 : i = 2
        · simp [h2]
        · by_cases h3 : i = 3
          · simp [h2, h3]
          · simp [h2, h3] }
  have hgeom : ∀ m, m ≤ 15 * t.n + 6 * t.benchlen → FitsLen m := by
    intro m hm
    apply geomFit t.n t.benchlen m hsh.n_small hsh.small.2.2.2
    omega
  have hMove : FitsLen (fr.moves + cubeCharge t.n t.benchlen + 3 * t.n) := by
    apply hgeom
    rw [show fr.moves = mv from rfl]
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
  obtain ⟨bL, bF, fr', hml, hfrob, hmk, hy1c, hy4c, hf1, hf4, hctrl, hmark,
      _cOps, _chord, hmv, hsl, hops, hheld, ⟨occU, hocc, hpeak⟩, hhole, htopX, htopY⟩ :=
    cell_run_frame eb t x x y4 y1 fr hOk sat hsh
      (by simpa [eb, early] using lay.flag) rfl rfl rfl rfl hy1 htri1
      hMove hSlide hCtrl hOps
  have hctrlI : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (tierR t) := by
    simpa [hctrl0, ofNat_eq_natCast] using lay.ctrl
  have hlift := lift_early b t hOk hR lay.marker hctrlI
  have hbL : bL = b := Except.ok.inj (hml.symm.trans hlift)
  have hst : fr'.peakS ≤ 7 := by
    rw [hpeak]
    exact strict_out_le fr.peakS (countHeld eb.sudo_5Board_4held 7) occU
      (by rw [show fr.peakS = 0 from rfl]; decide) hheld hocc
  have hho : fr'.hole ≤ t.benchlen := by
    rw [hhole]
    exact hole_out_le fr.hole (topIdx (combStrip t.n t.benchlen x))
      (topIdx (combStrip t.n t.benchlen y1)) t.benchlen
      (by rw [show fr.hole = 0 from rfl]; exact Nat.zero_le _) htopX htopY
  refine ⟨bF, fr', marker_lift_down b lay.marker, ?_, hmk, hy1c, hy4c, hmark, ?_,
    hst, hho, ?_, ?_, ?_, hf1, hf4⟩
  · rw [← hbL]
    exact hfrob
  · rw [hctrl, show fr.ctrl = tierR t - 1 from rfl]
  · have hpre : fr.moves = mv := rfl
    rw [hpre] at hmv
    exact hmv
  · have hpre : fr.slides = 0 := rfl
    rw [hpre, slideCharge, Nat.zero_add] at hsl
    exact hsl
  · have hpre : fr.opsCap = 1 := rfl
    rw [hpre] at hops
    exact hops

/-- The white copy of a board that already has `InLay`, then the seat. -/
theorem seat_copy_white (t : Spec.Tier) (b : Ecbs.Board) (x y : List Nat) (mv pk : Nat)
    (lay : InLay t b x y mv pk)
    (tw : TierWalk t) (hOk : BoardOk t) (sat : TierSat t) (hsh : TierShape t)
    (hR : 0 < tierR t)
    (hx : x.length = t.n) (hy : y.length = t.n)
    (htriX : allTritList x) (htriY : allTritList y)
    (hf : FitsLen t.n) (hfitx : FitsLen (mv + pegCount x))
    (hfity : FitsLen (mv + pegCount x + pegCount y))
    (hmvN : mv + pegCount x + pegCount y ≤ 4 * t.n) (hcells : 0 < t.cells)
    (hfresh : lay.sl0 = 0 ∧ lay.ops0 = 0 ∧ lay.strict0 = 0 ∧ lay.hole0 = 0 ∧
      lay.mx0 = 0 ∧ lay.tmax0 = 0 ∧ lay.ctrl0 = tierR t ∧
      lay.high0 = t.script + tierR t + 1) :
    ∃ b2 bF, ∃ _fr : RunFrame bF t x (fieldCube t.n t.k t.benchlen x),
      (do
          let board ← Ecbs.copy_band b Ecbs.across Ecbs.base_across false
          Ecbs.copy_band board Ecbs.up Ecbs.base_up false) = .ok b2 ∧
      Ecbs.frobenius_affine b2 = .ok bF ∧
      LiveAt t bF x y (fieldCube t.n t.k t.benchlen x)
        (fieldCube t.n t.k t.benchlen y) 1 := by
  obtain ⟨b2, _pk2, out, hsl0, hctrl0, hops0, hstrict0, hhole0, hmx0, hhigh0, htmax0, hcopy⟩ :=
    white_copy_kept t b x y mv pk lay hx hy hf hfitx hfity
  rcases hfresh with ⟨hsl, hopsZ, hstrict, hhole, hmx, htmax, hctrlZ, hhigh⟩
  have hfreshOut : out.sl0 = 0 ∧ out.ops0 = 0 ∧ out.strict0 = 0 ∧ out.hole0 = 0 ∧
      out.mx0 = 0 ∧ out.tmax0 = 0 ∧ out.ctrl0 = tierR t ∧
      out.high0 = t.script + tierR t + 1 :=
    ⟨hsl0.trans hsl, hops0.trans hopsZ, hstrict0.trans hstrict, hhole0.trans hhole,
      hmx0.trans hmx, htmax0.trans htmax, hctrl0.trans hctrlZ, hhigh0.trans hhigh⟩
  obtain ⟨bF, fr', _hlift, hfrob, hmk, hy1, hy4, _hmark, hctrlS, hst, hho, hmv, hsl, hops,
      hf1, hf4⟩ :=
    seat_out t b2 x y y (mv + pegCount x + pegCount y) _pk2 out tw hOk sat hsh hR
      hx hy htriX htriY hmvN hcells hfreshOut
  refine ⟨b2, bF, fr', hcopy, hfrob, fr', hmk, hy4, hy1, hf4, hf1, hst, hho, ?_, ?_, ?_, ?_,
    hy, htriY, fieldCube_length t.n t.k t.benchlen y tw.nLe, ?_⟩
  · have hpeg : mv + pegCount x + pegCount y ≤ walkCharge t := by
      have hpx : pegCount x ≤ t.n := by rw [← hx]; exact pegCount_le x
      have hpy : pegCount y ≤ t.n := by rw [← hy]; exact pegCount_le y
      unfold walkCharge cellMoveCharge
      omega
    have hcube : cubeCharge t.n t.benchlen = 6 * t.benchlen + 2 * t.n := cube_over _ _ tw.nLe
    calc
      fr'.moves ≤ mv + pegCount x + pegCount y + cubeCharge t.n t.benchlen := hmv
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

/-- A live white or red cell that returns is an invertible run. The final
    `walk_chord` reads the inverse off `walkRun = some`, not as an extra hypothesis. -/
theorem live_chord_inv (n k bench : Nat) (base acc : List Nat × List Nat) (c : Nat)
    (q : Bool × (List Nat × List Nat))
    (hc : c = 1 ∨ c = 2)
    (h : walkStep n k bench base true acc c = some q) :
    ∃ inv, fieldInv n k bench (fieldSub n base.1 (fieldCube n k bench acc.1)) = some inv := by
  have hc0 : c ≠ 0 := by rcases hc with rfl | rfl <;> decide
  have hcol : ¬ (c ≠ 1 ∧ c ≠ 2) := by
    rcases hc with rfl | rfl <;> decide
  unfold walkStep at h
  simp only [ite_true] at h
  rw [if_neg hc0, if_neg hcol] at h
  unfold chordAdd pointCube at h
  simp only [Prod.fst, Prod.snd] at h
  revert h
  generalize hrun :
    specInv n k bench (fieldSub n base.1 (fieldCube n k bench acc.1)) = s
  intro h
  cases s with
  | none => simp [hrun] at h
  | some inv =>
    rw [specInv_eq] at hrun
    exact ⟨inv, hrun⟩

private theorem flag_szH (t : Spec.Tier) (x y : List Nat) :
    (chordFlag (baseBoard t x y)).sudo_5Board_4home.size = 8 := by
  simp [chordFlag, base_szH]

private theorem flag_szD (t : Spec.Tier) (x y : List Nat) :
    (chordFlag (baseBoard t x y)).sudo_5Board_4held.size = 8 := by
  simp [chordFlag, base_szD]

private theorem flag_held {v : Bool} (t : Spec.Tier) (x y : List Nat) (i : Nat) (hi : i < 8)
    (h : (baseBoard t x y).sudo_5Board_4held[i]'(by rw [base_szD]; exact hi) = v) :
    (chordFlag (baseBoard t x y)).sudo_5Board_4held[i]'(by rw [flag_szD]; exact hi) = v := by
  simpa [chordFlag] using h

private theorem flag_home {v : Array Int} (t : Spec.Tier) (x y : List Nat) (i : Nat) (hi : i < 8)
    (h : (baseBoard t x y).sudo_5Board_4home[i]'(by rw [base_szH]; exact hi) = v) :
    (chordFlag (baseBoard t x y)).sudo_5Board_4home[i]'(by rw [flag_szH]; exact hi) = v := by
  simpa [chordFlag] using h

/-- The flagged base board is the board the opening copy reads. -/
noncomputable def base_in_lay (t : Spec.Tier) (x y : List Nat) (hR : 0 < tierR t) :
    InLay t (chordFlag (baseBoard t x y)) x y (pegCount x + pegCount y) 2 := by
  have h0 : (baseBoard t x y).sudo_5Board_4held[0]'(by rw [base_szD]; decide) = false := by
    simp [baseBoard, putAcross, Array.getElem_set, built_held_arr, Array.getElem_mkArray]
  have h1 : (baseBoard t x y).sudo_5Board_4held[1]'(by rw [base_szD]; decide) = false := by
    simp [baseBoard, putAcross, Array.getElem_set, built_held_arr, Array.getElem_mkArray]
  have h2 : (baseBoard t x y).sudo_5Board_4held[2]'(by rw [base_szD]; decide) = false := by
    simp [baseBoard, putAcross, Array.getElem_set, built_held_arr, Array.getElem_mkArray]
  have h3 : (baseBoard t x y).sudo_5Board_4held[3]'(by rw [base_szD]; decide) = true := by
    simp [baseBoard, putAcross, Array.getElem_set, built_held_arr, Array.getElem_mkArray]
  have h4 : (baseBoard t x y).sudo_5Board_4held[4]'(by rw [base_szD]; decide) = true := by
    simp [baseBoard, putAcross, Array.getElem_set]
  have h5 : (baseBoard t x y).sudo_5Board_4held[5]'(by rw [base_szD]; decide) = false := by
    simp [baseBoard, putAcross, Array.getElem_set, built_held_arr, Array.getElem_mkArray]
  have h6 : (baseBoard t x y).sudo_5Board_4held[6]'(by rw [base_szD]; decide) = false := by
    simp [baseBoard, putAcross, Array.getElem_set, built_held_arr, Array.getElem_mkArray]
  have hx3 : (baseBoard t x y).sudo_5Board_4home[3]'(by rw [base_szH]; decide) = embed x := by
    simp [baseBoard, putAcross, Array.getElem_set]
  have hy4 : (baseBoard t x y).sudo_5Board_4home[4]'(by rw [base_szH]; decide) = embed y := by
    simp [baseBoard, putAcross, Array.getElem_set]
  exact
    { szH := flag_szH t x y
      szD := flag_szD t x y
      bench := by simp [chordFlag, baseBoard, putAcross, built_bench_off]
      marker := by simp [chordFlag, baseBoard, putAcross, built_marker_down]
      flag := by simp [chordFlag]
      strict0 := 0
      hole0 := 0
      sl0 := 0
      ctrl0 := tierR t
      mx0 := 0
      high0 := t.script + tierR t + 1
      tmax0 := 0
      ops0 := 0
      strict := by simp [chordFlag, baseBoard, putAcross, builtBoard, midBoard, placed, blankOf]
      hole := by simp [chordFlag, baseBoard, putAcross, builtBoard, midBoard, placed, blankOf]
      slides := by simp [chordFlag, baseBoard, putAcross, built_slides0]
      mx := by simp [chordFlag, baseBoard, putAcross, built_mx0]
      ctrl := by simpa [ofNat_eq_natCast] using
        (by simp [chordFlag, baseBoard, putAcross, built_ctrl_eq] :
          (chordFlag (baseBoard t x y)).sudo_5Board_4cost.sudo_5Costs_4ctrl =
            Int.ofNat (tierR t))
      high := by simpa [ofNat_eq_natCast] using
        (by simp [chordFlag, baseBoard, putAcross, built_high_eq t hR] :
          (chordFlag (baseBoard t x y)).sudo_5Board_4cost.sudo_5Costs_15control_highest =
            Int.ofNat (t.script + tierR t + 1))
      tmax := by simp [chordFlag, baseBoard, putAcross, built_tmax0]
      opsSz := by simp [chordFlag, baseBoard, putAcross, built_ops_arr, Array.size_mkArray]
      opsBound := by
        intro i hi
        have harr : (chordFlag (baseBoard t x y)).sudo_5Board_4cost.sudo_5Costs_3ops =
            Array.mkArray 5 (0 : Int) := by
          simp [chordFlag, baseBoard, putAcross, built_ops_arr]
        refine ⟨0, ?_, Nat.le_refl 0⟩
        simp [harr, Array.getElem_mkArray]
      hStart := Or.inl ⟨built_high_lt t, rfl⟩
      tier := by simp [chordFlag, baseBoard, putAcross, built_tier_eq]
      row := by simp [chordFlag, baseBoard, putAcross, built_row_eq]
      ladder := by simp [chordFlag, baseBoard, putAcross, built_ladder_eq]
      l0 := by simp [chordFlag, baseBoard, putAcross, built_l0_eq]
      nr := by simp [chordFlag, baseBoard, putAcross, built_nr_eq]
      park := by simp [chordFlag, baseBoard, putAcross, built_park_eq]
      parked := by simp [chordFlag, baseBoard, putAcross, built_from_eq]
      ridx := by simp [chordFlag, baseBoard, putAcross, built_ridx_eq]
      tally := by simp [chordFlag, baseBoard, putAcross, built_tally0]
      t0 := by simp [chordFlag, baseBoard, putAcross, built_t0_eq]
      held0 := flag_held t x y 0 (by decide) h0
      held1 := flag_held t x y 1 (by decide) h1
      held2 := flag_held t x y 2 (by decide) h2
      held3 := flag_held t x y 3 (by decide) h3
      held4 := flag_held t x y 4 (by decide) h4
      held5 := flag_held t x y 5 (by decide) h5
      held6 := flag_held t x y 6 (by decide) h6
      home3 := flag_home t x y 3 (by decide) hx3
      home4 := flag_home t x y 4 (by decide) hy4
      moves := by simp [chordFlag, baseBoard, ofNat_eq_natCast]
      peak := by simp [chordFlag, baseBoard, ofNat_eq_natCast]
      tierN := by simp [chordFlag, baseBoard, putAcross, built_tier_eq, embTier, ofNat_eq_natCast] }

/-- The fresh board's counters are the zeros, with control and high painted. -/
theorem base_lay_fresh (t : Spec.Tier) (x y : List Nat) (hR : 0 < tierR t) :
    let lay := base_in_lay t x y hR
    lay.sl0 = 0 ∧ lay.ops0 = 0 ∧ lay.strict0 = 0 ∧ lay.hole0 = 0 ∧
      lay.mx0 = 0 ∧ lay.tmax0 = 0 ∧ lay.ctrl0 = tierR t ∧
      lay.high0 = t.script + tierR t + 1 := by
  rw [base_in_lay.eq_def]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The opening white copy on `baseBoard`, then the seat. -/
theorem seat_base_white (t : Spec.Tier) (x y : List Nat)
    (tw : TierWalk t) (hOk : BoardOk t) (sat : TierSat t) (hsh : TierShape t)
    (hR : 0 < tierR t)
    (hx : x.length = t.n) (hy : y.length = t.n)
    (htriX : allTritList x) (htriY : allTritList y) (hcells : 0 < t.cells) :
    ∃ b2 bF, ∃ _fr : RunFrame bF t x (fieldCube t.n t.k t.benchlen x),
      (do
          let board ← Ecbs.copy_band (chordFlag (baseBoard t x y)) Ecbs.across
            Ecbs.base_across false
          Ecbs.copy_band board Ecbs.up Ecbs.base_up false) = .ok b2 ∧
      Ecbs.frobenius_affine b2 = .ok bF ∧
      LiveAt t bF x y (fieldCube t.n t.k t.benchlen x)
        (fieldCube t.n t.k t.benchlen y) 1 := by
  have hpx : pegCount x ≤ t.n := by rw [← hx]; exact pegCount_le x
  have hpy : pegCount y ≤ t.n := by rw [← hy]; exact pegCount_le y
  have hf : FitsLen t.n := by
    apply geomFit t.n t.benchlen t.n hsh.n_small hsh.small.2.2.2
    omega
  have hfitx : FitsLen (pegCount x + pegCount y + pegCount x) := by
    apply geomFit t.n t.benchlen _ hsh.n_small hsh.small.2.2.2
    omega
  have hfity : FitsLen (pegCount x + pegCount y + pegCount x + pegCount y) := by
    apply geomFit t.n t.benchlen _ hsh.n_small hsh.small.2.2.2
    omega
  exact seat_copy_white t (chordFlag (baseBoard t x y)) x y (pegCount x + pegCount y) 2
    (base_in_lay t x y hR) tw hOk sat hsh hR hx hy htriX htriY hf hfitx hfity
    (by omega) hcells (base_lay_fresh t x y hR)

private theorem base_copy_ready (t : Spec.Tier) (x y : List Nat)
    (hsh : TierShape t) (hR : 0 < tierR t)
    (hx : x.length = t.n) (hy : y.length = t.n) :
    ∃ b2 pk2, ∃ out : OutLay t b2 x y y
        (pegCount x + pegCount y + pegCount x + pegCount y) pk2,
      (do
          let board ← Ecbs.copy_band (chordFlag (baseBoard t x y)) Ecbs.across
            Ecbs.base_across false
          Ecbs.copy_band board Ecbs.up Ecbs.base_up false) = .ok b2 ∧
      (out.sl0 = 0 ∧ out.ops0 = 0 ∧ out.strict0 = 0 ∧ out.hole0 = 0 ∧
        out.mx0 = 0 ∧ out.tmax0 = 0 ∧ out.ctrl0 = tierR t ∧
        out.high0 = t.script + tierR t + 1) := by
  have hpx : pegCount x ≤ t.n := by rw [← hx]; exact pegCount_le x
  have hpy : pegCount y ≤ t.n := by rw [← hy]; exact pegCount_le y
  have hf : FitsLen t.n := by
    apply geomFit t.n t.benchlen t.n hsh.n_small hsh.small.2.2.2
    omega
  have hfitx : FitsLen (pegCount x + pegCount y + pegCount x) := by
    apply geomFit t.n t.benchlen _ hsh.n_small hsh.small.2.2.2
    omega
  have hfity : FitsLen (pegCount x + pegCount y + pegCount x + pegCount y) := by
    apply geomFit t.n t.benchlen _ hsh.n_small hsh.small.2.2.2
    omega
  obtain ⟨b2, pk2, out, hsl0, hctrl0, hops0, hstrict0, hhole0, hmx0, hhigh0, htmax0, hcopy⟩ :=
    white_copy_kept t (chordFlag (baseBoard t x y)) x y (pegCount x + pegCount y) 2
      (base_in_lay t x y hR) hx hy hf hfitx hfity
  rcases base_lay_fresh t x y hR with ⟨hsl, hopsZ, hstrict, hhole, hmx, htmax, hctrlZ, hhigh⟩
  exact ⟨b2, pk2, out, hcopy,
    ⟨hsl0.trans hsl, hops0.trans hopsZ, hstrict0.trans hstrict, hhole0.trans hhole,
      hmx0.trans hmx, htmax0.trans htmax, hctrl0.trans hctrlZ, hhigh0.trans hhigh⟩⟩

/-- The white opening copy, the seat, and the chord. The inverse is the run this
    cell reaches. `walk_chord` reads it off a successful `walkRun`. -/
theorem seat_base_chord (t : Spec.Tier) (x y : List Nat) (c done left fuel : Nat)
    (inv : List Nat) (tw : TierWalk t) (hOk : BoardOk t) (sat : TierSat t)
    (hR : 0 < tierR t) (hsh : TierShape t)
    (hx : x.length = t.n) (hy : y.length = t.n)
    (htriX : allTritList x) (htriY : allTritList y) (hcells : 0 < t.cells)
    (hc : c = 1 ∨ c = 2)
    (hacc : fieldInv t.n t.k t.benchlen
      (fieldSub t.n x (fieldCube t.n t.k t.benchlen x)) = some inv)
    (hge : 1 ≤ done) (hFuel : 1 ≤ fuel) (hleftEq : fuel + 1 = left)
    (hsum : done + left = t.cells) :
    ∃ b2 bF b' x3 y3,
      (do
          let board ← Ecbs.copy_band (chordFlag (baseBoard t x y)) Ecbs.across
            Ecbs.base_across false
          Ecbs.copy_band board Ecbs.up Ecbs.base_up false) = .ok b2 ∧
      Ecbs.frobenius_affine b2 = .ok bF ∧
      Ecbs.chord_add_demo bF (decide (c = 2)) = .ok (true, b') ∧
      walkStep t.n t.k t.benchlen (x, y) true (x, y) c = some (true, (x3, y3)) ∧
      LiveAt t b' x y x3 y3 (done + 1) := by
  have hpx : pegCount x ≤ t.n := by rw [← hx]; exact pegCount_le x
  have hpy : pegCount y ≤ t.n := by rw [← hy]; exact pegCount_le y
  obtain ⟨b2, pk2, out, hcopy, hfresh⟩ := base_copy_ready t x y hsh hR hx hy
  obtain ⟨bF, fr, _hlift, hfrob, hmk, hy1, hy4, hmark, hctrl, hst, hho, hmv, hsl, hops,
      hf1, hf4⟩ :=
    seat_out t b2 x y y (pegCount x + pegCount y + pegCount x + pegCount y) pk2 out
      tw hOk sat hsh hR hx hy htriX htriY (by omega) hcells hfresh
  obtain ⟨b', x3, y3, hdemo, hwalk, hAt⟩ :=
    seat_cell_chord t bF x y y c done left fuel inv fr tw hOk sat hR hsh
      hmk hy4 hy1 hf4 hf1 hy htriY htriY hmv hsl hctrl hops hmark hst hho
      hc hacc hge hFuel hleftEq hsum
  exact ⟨b2, bF, b', x3, y3, hcopy, hfrob, hdemo, hwalk, hAt⟩

/-- The white opening copy when the seat cell is the last cell. -/
theorem seat_base_last (t : Spec.Tier) (x y : List Nat) (c done left : Nat)
    (inv : List Nat) (tw : TierWalk t) (hOk : BoardOk t) (sat : TierSat t)
    (hR : 0 < tierR t) (hsh : TierShape t)
    (hx : x.length = t.n) (hy : y.length = t.n)
    (htriX : allTritList x) (htriY : allTritList y) (hcells : 0 < t.cells)
    (hc : c = 1 ∨ c = 2)
    (hacc : fieldInv t.n t.k t.benchlen
      (fieldSub t.n x (fieldCube t.n t.k t.benchlen x)) = some inv)
    (hge : 1 ≤ done) (hleft : left = 1) (hsum : done + left = t.cells) :
    ∃ b2 bF b' x3 y3,
      (do
          let board ← Ecbs.copy_band (chordFlag (baseBoard t x y)) Ecbs.across
            Ecbs.base_across false
          Ecbs.copy_band board Ecbs.up Ecbs.base_up false) = .ok b2 ∧
      Ecbs.frobenius_affine b2 = .ok bF ∧
      Ecbs.chord_add_demo bF (decide (c = 2)) = .ok (true, b') ∧
      walkStep t.n t.k t.benchlen (x, y) true (x, y) c = some (true, (x3, y3)) ∧
      (∀ h : 0 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[0] = embed x3) ∧
      (∀ h : 1 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[1] = embed y3) := by
  have hpx : pegCount x ≤ t.n := by rw [← hx]; exact pegCount_le x
  have hpy : pegCount y ≤ t.n := by rw [← hy]; exact pegCount_le y
  obtain ⟨b2, pk2, out, hcopy, hfresh⟩ := base_copy_ready t x y hsh hR hx hy
  obtain ⟨bF, fr, _hlift, hfrob, hmk, hy1, hy4, hmark, hctrl, hst, hho, hmv, hsl, hops,
      hf1, hf4⟩ :=
    seat_out t b2 x y y (pegCount x + pegCount y + pegCount x + pegCount y) pk2 out
      tw hOk sat hsh hR hx hy htriX htriY (by omega) hcells hfresh
  obtain ⟨b', x3, y3, hdemo, hwalk, hx0, hy0, _hlift⟩ :=
    seat_cell_last t bF x y y c done left inv fr tw hOk sat hR hsh
      hmk hy4 hy1 hf4 hf1 hy htriY htriY hmv hsl hctrl hops hmark hho
      hc hacc hge hleft hsum
  exact ⟨b2, bF, b', x3, y3, hcopy, hfrob, hdemo, hwalk, hx0, hy0⟩

end EcbsLink2.Link2
