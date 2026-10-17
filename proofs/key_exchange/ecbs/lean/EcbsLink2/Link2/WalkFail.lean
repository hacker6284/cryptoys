/-
  The other two outcomes of `walk_chord`. No live cell leaves the homes and
  returns not live. A live cell whose run does not invert is either the
  reroll `.ok` (the run is `n` zeros) or the `AssertFailed` trap from
  `invert_checked` (lines 728 and 730). Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.WalkSeat

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- `walkRun` stayed not live, so every cell was empty and the accumulator
    is the one the walk started with. -/
theorem walkStep_true_bit (n k bench : Nat) (base acc : List Nat × List Nat)
    (c : Nat) (q : Bool × (List Nat × List Nat))
    (h : walkStep n k bench base true acc c = some q) : q.1 = true := by
  unfold walkStep at h
  simp only [ite_true] at h
  by_cases h0 : c = 0
  · rw [if_pos h0] at h
    exact (congrArg Prod.fst (Option.some.inj h)).symm
  · rw [if_neg h0] at h
    by_cases hbad : c ≠ 1 ∧ c ≠ 2
    · rw [if_pos hbad] at h
      cases h
    · rw [if_neg hbad] at h
      split at h
      · cases h
      · exact (congrArg Prod.fst (Option.some.inj h)).symm

theorem walkStep_copy_bit (n k bench : Nat) (base acc : List Nat × List Nat)
    (c : Nat) (q : Bool × (List Nat × List Nat))
    (h : walkStep n k bench base false acc c = some q) (h0 : c ≠ 0) : q.1 = true := by
  unfold walkStep at h
  rw [if_neg h0] at h
  by_cases hbad : c ≠ 1 ∧ c ≠ 2
  · rw [if_pos hbad] at h
    cases h
  · rw [if_neg hbad] at h
    simp only [ite_false] at h
    exact (congrArg Prod.fst (Option.some.inj h)).symm

theorem walkRun_stays (n k bench : Nat) (base acc acc' : List Nat × List Nat)
    (cells : List Nat) (b : Bool)
    (h : walkRun n k bench base true acc cells = some (b, acc')) :
    b = true := by
  induction cells generalizing acc with
  | nil =>
    exact (congrArg Prod.fst (Option.some.inj h)).symm
  | cons c cs ih =>
    simp only [walkRun] at h
    cases hstep : walkStep n k bench base true acc c with
    | none => simp [hstep] at h
    | some q =>
      simp only [hstep] at h
      have hq := walkStep_true_bit n k bench base acc c q hstep
      rw [hq] at h
      exact ih q.2 h

theorem walkRun_idle (n k bench : Nat) (base acc acc' : List Nat × List Nat)
    (cells : List Nat)
    (h : walkRun n k bench base false acc cells = some (false, acc')) :
    (∀ c ∈ cells, c = 0) ∧ acc' = acc := by
  induction cells generalizing acc with
  | nil =>
    have hpair := Option.some.inj h
    exact ⟨by simp, (congrArg Prod.snd hpair).symm⟩
  | cons c cs ih =>
    simp only [walkRun] at h
    cases hstep : walkStep n k bench base false acc c with
    | none => simp [hstep] at h
    | some q =>
      simp only [hstep] at h
      have hc0 : c = 0 := by
        by_cases h0 : c = 0
        · exact h0
        · exfalso
          have hq := walkStep_copy_bit n k bench base acc c q hstep h0
          rw [hq] at h
          exact Bool.false_ne_true (walkRun_stays n k bench base q.2 acc' cs false h)
      have hq : q = (false, acc) := by
        unfold walkStep at hstep
        rw [if_pos hc0] at hstep
        exact (Option.some.inj hstep).symm
      rw [hq] at h
      obtain ⟨hz, heq⟩ := ih acc h
      refine ⟨?_, heq⟩
      intro z hz'
      simp at hz'
      rcases hz' with rfl | hz'
      · exact hc0
      · exact hz z hz'

/-- No live cell. The homes are the board the walk started from. -/
theorem walk_chord_idle (t : Spec.Tier) (x y : List Nat) (acc : List Nat × List Nat)
    (cells : List Nat) (tw : TierWalk t)
    (hlen : cells.length = t.cells)
    (h : walkRun t.n t.k t.benchlen (x, y) false acc cells = some (false, acc)) :
    Ecbs.walk_chord (baseBoard t x y) (embed cells) =
      .ok ((false, true),
        { baseBoard t x y with sudo_5Board_9marker_on := false }) := by
  obtain ⟨hz, _⟩ := walkRun_idle t.n t.k t.benchlen (x, y) acc acc cells h
  exact (walk_chord_base_zeros t x y cells tw acc hlen hz).1

/-- A step `walkStep` refuses, on a cell in `{0, 1, 2}`, is a live white or
    red cell whose run does not invert. -/
theorem step_none_inv (n k bench : Nat) (base acc : List Nat × List Nat)
    (c : Nat) (h : walkStep n k bench base true acc c = none) (hc : c ≤ 2) :
    (c = 1 ∨ c = 2) ∧
      fieldInv n k bench (fieldSub n base.1 (fieldCube n k bench acc.1)) = none := by
  have hc12 : c = 1 ∨ c = 2 := by
    by_cases h0 : c = 0
    · unfold walkStep at h
      simp [h0] at h
    · omega
  refine ⟨hc12, ?_⟩
  have h0 : c ≠ 0 := by rcases hc12 with rfl | rfl <;> decide
  have hbad : ¬ (c ≠ 1 ∧ c ≠ 2) := by rcases hc12 with rfl | rfl <;> decide
  unfold walkStep at h
  simp only [ite_true] at h
  rw [if_neg h0, if_neg hbad] at h
  unfold chordAdd pointCube at h
  simp only [Prod.fst, Prod.snd] at h
  rw [specInv_eq] at h
  cases hfi : fieldInv n k bench (fieldSub n base.1 (fieldCube n k bench acc.1)) with
  | none => rfl
  | some inv =>
    rw [hfi] at h
    cases h

theorem step_none_live (n k bench : Nat) (base acc : List Nat × List Nat)
    (live : Bool) (c : Nat)
    (h : walkStep n k bench base live acc c = none) (hc : c ≤ 2) :
    live = true := by
  cases live
  · by_cases h0 : c = 0
    · unfold walkStep at h
      simp [h0] at h
    · have hc12 : c = 1 ∨ c = 2 := by omega
      unfold walkStep at h
      rw [if_neg h0] at h
      have hbad : ¬ (c ≠ 1 ∧ c ≠ 2) := by rcases hc12 with rfl | rfl <;> decide
      rw [if_neg hbad] at h
      simp only [ite_false] at h
      cases h
  · rfl

/-- The first cell a failing run refuses. -/
theorem first_fail (n k bench : Nat) (base : List Nat × List Nat)
    (live : Bool) (acc : List Nat × List Nat) (cells : List Nat)
    (hc2 : ∀ i (hi : i < cells.length), cells[i] ≤ 2)
    (h : walkRun n k bench base live acc cells = none) :
    ∃ (i : Nat) (hi : i < cells.length) (liveI : Bool) (accI : List Nat × List Nat),
      walkRun n k bench base live acc (cells.take i) = some (liveI, accI) ∧
      walkStep n k bench base liveI accI (cells[i]'hi) = none := by
  induction cells generalizing live acc with
  | nil =>
    rw [walkRun.eq_def] at h
    cases h
  | cons c cs ih =>
    cases hstep : walkStep n k bench base live acc c with
    | none =>
      exact ⟨0, by simp, live, acc, by simp [walkRun], by simp [hstep]⟩
    | some q =>
      have htail : walkRun n k bench base q.1 q.2 cs = none := by
        simp only [walkRun] at h
        rw [hstep] at h
        exact h
      have hc2' : ∀ i (hi : i < cs.length), cs[i] ≤ 2 := by
        intro i hi
        have hget := hc2 (i + 1) (by simp; omega)
        simpa [List.getElem_cons_succ] using hget
      obtain ⟨i, hi, liveI, accI, hpre, hcell⟩ := ih q.1 q.2 hc2' htail
      refine ⟨i + 1, by simp; omega, liveI, accI, ?_, ?_⟩
      · simp only [List.take_succ_cons, walkRun, hstep]
        exact hpre
      · rw [List.getElem_cons_succ]
        exact hcell

private theorem getD_eq_get (xs : List Nat) (j : Nat) (hj : j < xs.length) :
    xs.getD j 0 = xs[j] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]

/-- The check product is not a peg in hole 0. `invert_checked` is the
    `AssertFailed` trap at line 728, or at line 730 on the first later hole. -/
theorem invert_checked_lay_none (b : Ecbs.Board) (t : Spec.Tier) (xs : List Nat)
    (lay : OpenLay b t xs) (hOk : BoardOk t) (sat : TierSat t) (hR : 0 < tierR t)
    (hsh : TierShape t) (base : ClimbBudget) (hm : OpenMatch lay base)
    (hhole : lay.hole ≤ t.benchlen)
    (hrej : fieldInv t.n t.k t.benchlen xs = none) :
    ∃ e, Ecbs.invert_checked b ((2 : Nat) : Int) = .error e ∧
      e.kind = "AssertFailed" ∧
      (e.detail = s!"line {728}" ∨
        ∃ c, c ≠ 0 ∧
          e.detail = s!"line {730}: {SudoRt.Canon.canon (Int.ofNat c)} != {SudoRt.Canon.canon (0 : Int)}") := by
  have hpos : 0 < t.n := hOk.n_pos
  have hnbench := mul_span_n t.n t.benchlen hpos sat.mul_span
  let g := invGap t.n t.k t.benchlen xs
  let P := fieldMul t.n t.k t.benchlen g xs
  have hlenP : P.length = t.n := fieldMul_length _ _ _ _ _ hnbench
  have hP0 : 0 < P.length := by rw [hlenP]; exact hpos
  have hne := fieldInv_none_shape t.n t.k t.benchlen xs hrej
  obtain ⟨bZ, bM, bR, v, _h5, hpack⟩ :=
    open_check_mul b t xs lay hOk sat hR hsh base hm hhole
  have hinv := hpack.1
  have hmul := hpack.2.1
  have hread := hpack.2.2.1
  have hv := hpack.2.2.2.1
  have hframe := hpack.2.2.2.2.2.2.1
  obtain ⟨_h5D, mv, _hheld, _hmv, hfit, _hnT⟩ := hframe
  have hfitn : FitsLen t.n := FitsLen.of_le hfit (Nat.le_add_left t.n mv)
  unfold Ecbs.invert_checked
  rw [hinv, ok_bind]
  conv => zeta
  rw [hmul, ok_bind]
  conv => zeta
  rw [hread, ok_bind]
  dsimp
  have hvP : v = embed P := by simpa [P, g] using hv
  rw [hvP, show (0 : Int) = Int.ofNat 0 from rfl, atL_embed P 0 hP0, ok_bind,
    sEq_ofNat (P[0]'(hP0)) 0]
  by_cases hhead : (P[0]'(hP0)) = 0
  · rw [hhead]
    rw [show decide ((0 : Nat) = 0) = true from rfl, Bool.not_true]
    unfold SudoRt.sudoAssert SudoRt.fail
    simp only [Bool.false_eq_true, if_false, bind, Except.bind, error_bind]
    exact ⟨{ kind := "AssertFailed", detail := s!"line {728}" }, rfl, rfl, Or.inl rfl⟩
  · rw [decide_eq_false hhead, Bool.not_false, sudoAssert_true, ok_bind]
    have htriP : allTritList P := by
      have h := fieldMul_trits t.n t.k t.benchlen g xs
        (cube_span_le _ _ _ sat.cube_span) hnbench
      simpa [P, g, show xs.take t.n = xs from by rw [← lay.len, List.take_length]] using h
    have hnot : ¬ ∀ j, 1 ≤ j → ∀ hj : j < t.n, P[j]'(by rw [hlenP]; exact hj) = 0 := by
      intro hall
      have hlist := eq_pegList P t.n (P[0]'(hP0)) hpos hlenP rfl hall
      have hc := trit_nz_one_two _ (trit_get htriP hP0) hhead
      rcases hc with hc | hc
      · exact hne.1 (by simpa [P, g, hc] using hlist)
      · exact hne.2 (by simpa [P, g, hc] using hlist)
    have hex : ∃ j, 1 ≤ j ∧ j < t.n ∧ P.getD j 0 ≠ 0 :=
      exists_nz_tail P t.n (by
        intro hall
        apply hnot
        intro j hj1 hj
        have h0 := hall j hj1 hj
        rw [getD_eq_get P j (by rw [hlenP]; exact hj)] at h0
        exact h0)
    obtain ⟨j, hj1, hjn, hbad, hpre⟩ :=
      first_tail P t.n 1 (Nat.le_refl _) (Nat.succ_le_of_lt hpos) hex
    have hjL : j < P.length := by rw [hlenP]; exact hjn
    rw [listLen_embed, hlenP, subI_ofNat_one t.n hpos hfitn, ok_bind]
    conv => zeta
    rw [show (1 : Int) = Int.ofNat 1 from rfl, fuelRange_eq, except_bind_pure]
    rw [zeroScan_err_of P t.n j hlenP ?hstep hP0 hj1 hjL (by rwa [hlenP])
        (by rw [getD_eq_get P j hjL] at hbad; exact hbad) ?hpre]
    · let e730 : SudoRt.Trap :=
        { kind := "AssertFailed"
          detail := s!"line {730}: {SudoRt.Canon.canon (Int.ofNat (P[j]'hjL))} != {SudoRt.Canon.canon (0 : Int)}" }
      have hnz : P[j]'hjL ≠ 0 := by
        rw [getD_eq_get P j hjL] at hbad
        exact hbad
      exact ⟨e730, rfl, rfl, Or.inr ⟨P[j]'hjL, hnz, rfl⟩⟩
    · intro k; rfl
    · intro k hk1 hk
      have hkL : k < P.length := Nat.lt_trans hk hjL
      have h0 := hpre k hk1 hk
      rw [getD_eq_get P k hkL] at h0
      exact h0

private theorem fuel_as_succ (i toN : Nat) (hi : i ≤ toN) :
    fuelRange (Int.ofNat i) (Int.ofNat toN) = (toN - i) + 1 :=
  fuelRange_le hi

private theorem ret_from (i toN : Nat) (b : Ecbs.Board) (cells : List Nat)
    (r : (Bool × Bool) × Ecbs.Board) (hi : i ≤ toN)
    (hstep : chordStep (embed cells) (Int.ofNat toN) (Int.ofNat i, (b, true)) =
      .ok (SudoRt.Flow.ret r)) :
    SudoRt.runLoopOn (Int.ofNat i, (b, true))
        (fuelRange (Int.ofNat i) (Int.ofNat toN))
        (chordStep (embed cells) (Int.ofNat toN)) chordAfter (fun r => pure r) =
      .ok r := by
  rw [fuel_as_succ i toN hi, runLoopOn_succ, hstep]
  simp [pure_eq_ok]

private theorem err_from (i toN : Nat) (b : Ecbs.Board) (cells : List Nat)
    (e : SudoRt.Trap) (hi : i ≤ toN)
    (hstep : chordStep (embed cells) (Int.ofNat toN) (Int.ofNat i, (b, true)) =
      .error e) :
    SudoRt.runLoopOn (Int.ofNat i, (b, true))
        (fuelRange (Int.ofNat i) (Int.ofNat toN))
        (chordStep (embed cells) (Int.ofNat toN)) chordAfter (fun r => pure r) =
      .error e := by
  rw [fuel_as_succ i toN hi, runLoopOn_succ, hstep]

private theorem cont_from (k toN : Nat) (b b' : Ecbs.Board) (cells : List Nat)
    (hlt : k < toN)
    (hstep : chordStep (embed cells) (Int.ofNat toN) (Int.ofNat k, (b, true)) =
      .ok (SudoRt.Flow.cont (Int.ofNat (k + 1), (b', true)))) :
    SudoRt.runLoopOn (Int.ofNat k, (b, true))
        (fuelRange (Int.ofNat k) (Int.ofNat toN))
        (chordStep (embed cells) (Int.ofNat toN)) chordAfter (fun r => pure r) =
      SudoRt.runLoopOn (Int.ofNat (k + 1), (b', true))
        (fuelRange (Int.ofNat (k + 1)) (Int.ofNat toN))
        (chordStep (embed cells) (Int.ofNat toN)) chordAfter (fun r => pure r) := by
  have hfuel : fuelRange (Int.ofNat k) (Int.ofNat toN) =
      fuelRange (Int.ofNat (k + 1)) (Int.ofNat toN) + 1 := by
    rw [fuelRange_le (by omega : k ≤ toN), fuelRange_le (by omega : k + 1 ≤ toN)]
    omega
  rw [hfuel, runLoopOn_succ, hstep]

private theorem flag_beq (c : Nat) (hc : c = 1 ∨ c = 2) :
    SudoRt.SEq.beq (Int.ofNat c) (2 : Int) = decide (c = 2) := by
  rcases hc with rfl | rfl <;> decide

/-- `chord_add_demo` returning an error is the cell returning that error. -/
theorem chordStep_trap (cells : List Nat) (i toN c : Nat)
    (b0 b bF : Ecbs.Board) (e : SudoRt.Trap)
    (hi : i ≤ toN) (hlen : cells.length = toN + 1)
    (hc : cells[i]'(by omega) = c) (hc0 : c ≠ 0) (hc2 : c ≤ 2)
    (hml : Ecbs.marker_lift b0 = .ok b)
    (hfrob : Ecbs.frobenius_affine b = .ok bF)
    (hadd : Ecbs.chord_add_demo bF (SudoRt.SEq.beq (Int.ofNat c) (2 : Int)) = .error e) :
    chordStep (embed cells) (Int.ofNat toN) (Int.ofNat i, (b0, true)) = .error e := by
  unfold chordStep
  dsimp only
  have hng : ¬ (Int.ofNat i > Int.ofNat toN) := ofNat_not_gt hi
  rw [if_neg hng]
  unfold chordBody
  have hix : i < cells.length := by omega
  rw [atL_embed cells i hix, ok_bind, hc]
  have hge : decide (Int.ofNat c ≥ (0 : Int)) = true := by
    rw [decide_eq_true_eq]
    exact Int.ofNat_nonneg c
  have hle : decide (Int.ofNat c ≤ (2 : Int)) = true := by
    rw [decide_eq_true_eq, show (2 : Int) = Int.ofNat 2 from rfl, ofNat_le_iff]
    exact hc2
  rw [hge, if_pos rfl, hle, pure_eq_ok, ok_bind, sudoAssert_true, ok_bind]
  rw [hml, ok_bind]
  simp only [if_true]
  rw [hfrob, ok_bind]
  rw [show (0 : Int) = Int.ofNat 0 from rfl, sEq_ofNat c 0, decide_eq_false hc0]
  simp only [Bool.not_false, if_true, Bool.not_true]
  rw [if_neg (by decide : ¬ ((false : Bool) = true))]
  rw [hadd]
  simp [error_bind, bind, Except.bind]

private theorem copy_rooms (t : Spec.Tier) (b : Ecbs.Board) (baseX accX : List Nat)
    (fr : RunFrame b t baseX accX) (_hOk : BoardOk t)
    (hMove : FitsLen (liveMoveRoom t fr.moves baseX accX))
    (hSlide : FitsLen (liveSlideRoom t fr.slides))
    (hCtrl : FitsLen (liveCtrlRoom t fr.ctrl))
    (hOps : FitsLen (liveOpsRoom t fr.opsCap)) :
    FitsLen ((fr.moves + pegCount baseX + pegCount accX) +
        pegCount (fieldSub t.n baseX accX) +
        tierR t * rungCharge t.n t.benchlen (rowRoom t)) ∧
      FitsLen (fr.slides + tierR t * rungSlideCharge t.n (rowRoom t)) ∧
      FitsLen (fr.opsCap + tierR t * (rowRoom t + 3)) ∧
      FitsLen ((fr.moves + pegCount baseX + pegCount accX) +
        pegCount (fieldSub t.n baseX accX) +
        tierR t * rungCharge t.n t.benchlen (rowRoom t) +
        pegCharge t.n t.benchlen) ∧
      FitsLen (fr.slides + tierR t * rungSlideCharge t.n (rowRoom t) + 2 * t.n) ∧
      FitsLen ((fr.moves + pegCount baseX + pegCount accX) +
        pegCount (fieldSub t.n baseX accX) +
        tierR t * rungCharge t.n t.benchlen (rowRoom t) +
        pegCharge t.n t.benchlen + t.n + t.n * (t.n + 1) +
        3 * (t.benchlen - t.n) + 2 * t.n) ∧
      FitsLen ((fr.ctrl + 1) + (tierR t + 1) * (3 * rowRoom t + 5)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact FitsLen.of_le hMove (by unfold liveMoveRoom runMoves; omega)
  · exact FitsLen.of_le hSlide (by unfold liveSlideRoom; omega)
  · exact FitsLen.of_le hOps (by unfold liveOpsRoom; omega)
  · exact FitsLen.of_le hMove (by unfold liveMoveRoom runMoves; omega)
  · exact FitsLen.of_le hSlide (by unfold liveSlideRoom; omega)
  · exact FitsLen.of_le hMove (by unfold liveMoveRoom runMoves; omega)
  · exact FitsLen.of_le hCtrl (by unfold liveCtrlRoom; omega)

private theorem frame_tier_n (t : Spec.Tier) (b : Ecbs.Board) (baseX accX : List Nat)
    (fr : RunFrame b t baseX accX) :
    b.sudo_5Board_1t.sudo_4Tier_1n = (t.n : Int) := by
  simp [fr.tier, embTier]

/-- A nonempty run that does not invert. The chord is the check's trap.
    The colour is not read: the trap is raised before the rise. -/
theorem chord_add_trap (b : Ecbs.Board) (t : Spec.Tier) (baseX accX : List Nat)
    (red : Bool) (fr : RunFrame b t baseX accX) (hOk : BoardOk t) (sat : TierSat t)
    (hR : 0 < tierR t) (hsh : TierShape t)
    (hMove : FitsLen (liveMoveRoom t fr.moves baseX accX))
    (hSlide : FitsLen (liveSlideRoom t fr.slides))
    (hCtrl : FitsLen (liveCtrlRoom t fr.ctrl))
    (hOps : FitsLen (liveOpsRoom t fr.opsCap))
    (hhole : fr.hole ≤ t.benchlen)
    (hne : fieldSub t.n baseX accX ≠ List.replicate t.n 0)
    (hrej : fieldInv t.n t.k t.benchlen (fieldSub t.n baseX accX) = none) :
    ∃ e, Ecbs.chord_add_demo b red = .error e ∧
      e.kind = "AssertFailed" ∧
      (e.detail = s!"line {728}" ∨
        ∃ c, c ≠ 0 ∧
          e.detail = s!"line {730}: {SudoRt.Canon.canon (Int.ofNat c)} != {SudoRt.Canon.canon (0 : Int)}") := by
  obtain ⟨hM, hS, hO, hTailM, hTailS, hCheck, hCtrlC⟩ :=
    copy_rooms t b baseX accX fr hOk hMove hSlide hCtrl hOps
  obtain ⟨bA, hcopy, _hflag, lay, bud, hmatch, _hmv, _hsl, _hctrl, _hc, _ho,
      _hmk, _hmx, _hs1, _hf1, _hs4, _hf4, _hs0, _hf0, _hb3, _hf3, _hsz, _hp,
      hholeLay⟩ :=
    copy_add_open b t baseX accX fr hOk sat hM hS hO hTailM hTailS hCheck hCtrlC
  have hhole' : lay.hole ≤ t.benchlen := by rw [hholeLay]; exact hhole
  let run := fieldSub t.n baseX accX
  obtain ⟨e, hinv, hk, hd⟩ :=
    invert_checked_lay_none { bA with sudo_5Board_9marker_on := false } t run lay
      hOk sat hR hsh bud hmatch hhole' hrej
  have hfitn : FitsLen t.n := FitsLen.of_le hMove (by unfold liveMoveRoom; omega)
  let bOff := { bA with sudo_5Board_9marker_on := false }
  have hszH : bA.sudo_5Board_4home.size = 8 := lay.szH
  have hszD : bA.sudo_5Board_4held.size = 8 := lay.szD
  have h2H : 2 < bA.sudo_5Board_4home.size := by rw [hszH]; decide
  have h2D : 2 < bA.sudo_5Board_4held.size := by rw [hszD]; decide
  have hhomeEq : bA.sudo_5Board_4home =
      ({ bA with sudo_5Board_9marker_on := false } : Ecbs.Board).sudo_5Board_4home := rfl
  have hheldEq : bA.sudo_5Board_4held =
      ({ bA with sudo_5Board_9marker_on := false } : Ecbs.Board).sudo_5Board_4held := rfl
  have hheld : bA.sudo_5Board_4held[2]'h2D = true := cell_eq_of hheldEq lay.held2
  have harr : bA.sudo_5Board_4home[2]'h2H = embed run := cell_eq_of hhomeEq lay.home2
  have hn : bA.sudo_5Board_1t.sudo_4Tier_1n = (t.n : Int) := by
    rw [show bA.sudo_5Board_1t =
      ({ bA with sudo_5Board_9marker_on := false } : Ecbs.Board).sudo_5Board_1t from rfl,
      lay.tier]
    simp [embTier]
  have hlen : run.length = t.n := fieldSub_length t.n baseX accX
  rw [chord_add_eq]
  unfold chordAddGo
  rw [hcopy, ok_bind]
  rw [show Ecbs.bottom = ((2 : Nat) : Int) from rfl,
    is_zero_embed bA 2 t.n run h2D h2H hheld harr hn hlen hfitn, ok_bind]
  rw [decide_eq_false hne]
  simp only [Bool.false_eq_true, if_false]
  unfold chordAddTail
  dsimp only
  rw [show Ecbs.bottom = ((2 : Nat) : Int) from rfl, hinv, error_bind]
  exact ⟨e, rfl, hk, hd⟩

private theorem take_succ_cell (cells : List Nat) (i : Nat) (hi : i < cells.length) :
    cells.take (i + 1) = cells.take i ++ [cells[i]] := by
  rw [List.take_succ, List.getElem?_eq_getElem hi]
  simp

private theorem walkRun_snoc (n k bench : Nat) (base acc p p' : List Nat × List Nat)
    (cells : List Nat) (c : Nat) (live : Bool)
    (h : walkRun n k bench base live acc cells = some (true, p))
    (hstep : walkStep n k bench base true p c = some (true, p')) :
    walkRun n k bench base live acc (cells ++ [c]) = some (true, p') := by
  induction cells generalizing live acc with
  | nil =>
    simp only [walkRun] at h
    cases h
    simp [walkRun, hstep]
  | cons d ds ih =>
    simp only [walkRun] at h
    cases hgo : walkStep n k bench base live acc d with
    | none => simp [hgo] at h
    | some q =>
      simp only [hgo] at h
      have hrec := ih q.2 q.1 h
      simp [walkRun, hgo, hrec]

/-- Shorter prefixes of a successful run succeed. -/
theorem walkRun_take_some (n k bench : Nat) (base : List Nat × List Nat)
    (live : Bool) (acc : List Nat × List Nat) (cells : List Nat)
    (q : Bool × (List Nat × List Nat)) (j : Nat)
    (h : walkRun n k bench base live acc cells = some q) (hj : j ≤ cells.length) :
    ∃ q', walkRun n k bench base live acc (cells.take j) = some q' := by
  induction cells generalizing live acc j with
  | nil =>
    simp at hj
    subst hj
    exact ⟨q, by simpa [walkRun] using h⟩
  | cons c cs ih =>
    cases j with
    | zero => exact ⟨(live, acc), by simp [walkRun]⟩
    | succ j =>
      simp only [walkRun] at h
      cases hstep : walkStep n k bench base live acc c with
      | none => simp [hstep] at h
      | some s =>
        simp only [hstep] at h
        have hj' : j ≤ cs.length := by simp at hj; omega
        obtain ⟨q', hq⟩ := ih s.1 s.2 j h hj'
        exact ⟨q', by simpa [walkRun, hstep, List.take_succ_cons] using hq⟩

/-- A run that returns `some` is either still not live, with the homes left
    as the base board, or live at the spec point. -/
theorem walk_chord_some (t : Spec.Tier) (x y : List Nat)
    (acc acc' : List Nat × List Nat) (cells : List Nat) (live : Bool)
    (tw : TierWalk t) (hOk : BoardOk t) (sat : TierSat t)
    (hR : 0 < tierR t) (hsh : TierShape t)
    (hx : x.length = t.n) (hy : y.length = t.n)
    (htriX : allTritList x) (htriY : allTritList y)
    (hlen : cells.length = t.cells)
    (h : walkRun t.n t.k t.benchlen (x, y) false acc cells = some (live, acc')) :
    (live = false ∧ acc' = acc ∧
        Ecbs.walk_chord (baseBoard t x y) (embed cells) =
          .ok ((false, true),
            { baseBoard t x y with sudo_5Board_9marker_on := false })) ∨
      (live = true ∧
        ∃ px py b', acc' = (px, py) ∧
          Ecbs.walk_chord (baseBoard t x y) (embed cells) = .ok ((true, true), b') ∧
          (∀ h0 : 0 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[0] = embed px) ∧
          (∀ h1 : 1 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[1] = embed py)) := by
  cases live
  · have hidle := walkRun_idle t.n t.k t.benchlen (x, y) acc acc' cells h
    have hrun : walkRun t.n t.k t.benchlen (x, y) false acc cells = some (false, acc) := by
      simpa [hidle.2] using h
    exact Or.inl ⟨rfl, hidle.2, walk_chord_idle t x y acc cells tw hlen hrun⟩
  · cases acc' with
    | mk px py =>
      obtain ⟨b', hch, hx0, hy1⟩ :=
        walk_chord_success t x y px py acc cells tw hOk sat hR hsh hx hy
          htriX htriY hlen h
      exact Or.inr ⟨rfl, px, py, b', rfl, hch, hx0, hy1⟩

private theorem one_mul_le (left a : Nat) (h : 0 < left) : a ≤ left * a :=
  Nat.le_mul_of_pos_left a h

private theorem ctrl_one (t : Spec.Tier) : tierR t + 3 ≤ cellCtrlCharge t + 4 := by
  have h5 : 5 ≤ 3 * rowRoom t + 5 := by omega
  have hmul : (tierR t + 1) * 5 ≤ (tierR t + 1) * (3 * rowRoom t + 5) :=
    Nat.mul_le_mul_left _ h5
  unfold cellCtrlCharge
  omega

/-- The seat cell is the one `walkRun` refuses. The loop there is the reroll
    or the check trap. -/
theorem seat_is_fail (t : Spec.Tier) (b2 bF : Ecbs.Board) (x y up : List Nat)
    (cells : List Nat) (k c : Nat) (fr : RunFrame bF t x (fieldCube t.n t.k t.benchlen x))
    (tw : TierWalk t) (hOk : BoardOk t) (sat : TierSat t) (hR : 0 < tierR t)
    (hsh : TierShape t)
    (hx : x.length = t.n) (hy : y.length = t.n)
    (hml : Ecbs.marker_lift b2 = .ok b2)
    (hfrob : Ecbs.frobenius_affine b2 = .ok bF)
    (hctrl : fr.ctrl = tierR t - 1 + 4)
    (hops : fr.opsCap = 3)
    (hmv : fr.moves ≤ pegCount x + pegCount y + pegCount x + pegCount y +
      cubeCharge t.n t.benchlen)
    (hsl : fr.slides ≤ 4 * t.n)
    (hho : fr.hole ≤ t.benchlen)
    (hlen : cells.length = t.cells) (hk : k ≤ t.cells - 1) (hk1 : 1 ≤ k)
    (hcAt : cells[k]'(by omega) = c) (hc : c = 1 ∨ c = 2)
    (hinv : fieldInv t.n t.k t.benchlen
      (fieldSub t.n x (fieldCube t.n t.k t.benchlen x)) = none) :
    (∃ bA : Ecbs.Board, SudoRt.runLoopOn (Int.ofNat k, (b2, true))
        (fuelRange (Int.ofNat k) (Int.ofNat (t.cells - 1)))
        (chordStep (embed cells) (Int.ofNat (t.cells - 1))) chordAfter (fun r => pure r) =
        .ok ((true, false), { bA with sudo_5Board_9marker_on := false })) ∨
      (∃ e, SudoRt.runLoopOn (Int.ofNat k, (b2, true))
        (fuelRange (Int.ofNat k) (Int.ofNat (t.cells - 1)))
        (chordStep (embed cells) (Int.ofNat (t.cells - 1))) chordAfter (fun r => pure r) =
        .error e ∧ e.kind = "AssertFailed" ∧
        (e.detail = s!"line {728}" ∨
          ∃ d, d ≠ 0 ∧
            e.detail = s!"line {730}: {SudoRt.Canon.canon (Int.ofNat d)} != {SudoRt.Canon.canon (0 : Int)}")) := by
  let toN := t.cells - 1
  have hto : toN = t.cells - 1 := rfl
  have hlenC : cells.length = toN + 1 := by omega
  have hiK : k < cells.length := by omega
  have hfitM : FitsLen (fr.moves + 2 * t.n) :=
    FitsLen.of_le fr.fitRoom (by omega)
  have hn : bF.sudo_5Board_1t.sudo_4Tier_1n = (t.n : Int) := by
    simp [fr.tier, embTier]
  by_cases hzero : fieldSub t.n x (fieldCube t.n t.k t.benchlen x) = List.replicate t.n 0
  · obtain ⟨bA, hstep, _hw⟩ :=
      chordStep_empty_run cells k toN c b2 b2 bF t.n t.k t.benchlen fr.moves fr.peak
        fr.chordOps (x, y) (x, up) hk hlenC hcAt hc hml hfrob fr.szH fr.szD fr.ops3
        fr.hop3 fr.fitChord hx fr.triX fr.triA hn fr.hmoves fr.hpeak hfitM fr.held2
        fr.held0 fr.home0 fr.held3 fr.home3 hzero hOk.n_pos tw.nLe
    have hret := ret_from k toN b2 cells
      ((true, false), { bA with sudo_5Board_9marker_on := false }) hk hstep
    exact Or.inl ⟨bA, by simpa [hto] using hret⟩
  · let left := t.cells - k
    have hleft : 0 < left := by omega
    have hsum : k + left = t.cells := by omega
    have hpreM : pegCount x + pegCount y + pegCount x + pegCount y ≤
        k * (walkCharge t + (6 * t.benchlen + 2 * t.n)) := by
      have hpx : pegCount x ≤ t.n := by rw [← hx]; exact pegCount_le x
      have hpy : pegCount y ≤ t.n := by rw [← hy]; exact pegCount_le y
      have hpeg : pegCount x + pegCount y + pegCount x + pegCount y ≤ walkCharge t := by
        unfold walkCharge cellMoveCharge
        omega
      exact Nat.le_trans (Nat.le_trans hpeg (Nat.le_add_right _ _))
        (Nat.le_mul_of_pos_left _ hk1)
    have hpreC : tierR t - 1 ≤ k * (cellCtrlCharge t + 4) := by
      exact Nat.le_trans (by
        have h := ctrl_one t
        omega) (Nat.le_mul_of_pos_left _ hk1)
    have hpreO : 1 ≤ k * (cellOpsCharge t + 2) := by
      have h1 : 1 ≤ cellOpsCharge t + 2 := by unfold cellOpsCharge; omega
      exact Nat.le_trans h1 (Nat.le_mul_of_pos_left _ hk1)
    have hrooms := chord_rooms t tw
      (pegCount x + pegCount y + pegCount x + pegCount y) 0 (tierR t - 1) 1
      fr.moves fr.slides fr.ctrl fr.opsCap k left hsum hleft hpreM (Nat.zero_le _)
      hpreC hpreO hmv (by rw [slideCharge, Nat.zero_add]; exact hsl)
      (by rw [hctrl]; omega) (by rw [hops]; omega)
    have hMove : FitsLen (liveMoveRoom t fr.moves x (fieldCube t.n t.k t.benchlen x)) := by
      apply FitsLen.of_le hrooms.1
      have hlive := live_move_le t fr.moves x (fieldCube t.n t.k t.benchlen x) hx
        (fieldCube_length t.n t.k t.benchlen x tw.nLe)
      have hmul := one_mul_le left (cellMoveCharge t) hleft
      omega
    have hSlide : FitsLen (liveSlideRoom t fr.slides) := by
      apply FitsLen.of_le hrooms.2.1
      rw [live_slide_eq]
      exact Nat.add_le_add_left (one_mul_le left _ hleft) _
    have hCtrl : FitsLen (liveCtrlRoom t fr.ctrl) := by
      apply FitsLen.of_le hrooms.2.2.1
      rw [live_ctrl_eq]
      exact Nat.add_le_add_left (one_mul_le left _ hleft) _
    have hOps : FitsLen (liveOpsRoom t fr.opsCap) := by
      apply FitsLen.of_le hrooms.2.2.2
      rw [live_ops_eq]
      exact Nat.add_le_add_left (one_mul_le left _ hleft) _
    obtain ⟨e, hadd, hknd, hd⟩ :=
      chord_add_trap bF t x (fieldCube t.n t.k t.benchlen x)
        (SudoRt.SEq.beq (Int.ofNat c) (2 : Int)) fr hOk sat hR hsh
        hMove hSlide hCtrl hOps hho hzero hinv
    have hstep := chordStep_trap cells k toN c b2 b2 bF e hk hlenC hcAt
      (by rcases hc with rfl | rfl <;> decide) (by rcases hc with rfl | rfl <;> decide)
      hml hfrob hadd
    have herr := err_from k toN b2 cells e hk hstep
    exact Or.inr ⟨e, by simpa [hto] using herr, hknd, hd⟩

