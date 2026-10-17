/-
  `walk_chord` on the domain: a live success, a walk that never goes live,
  or a refusal. The refusal is the reroll when the run is `n` zeros, and the
  `AssertFailed` trap at line 728 or 730 otherwise.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.WalkFail

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

private theorem step_fit (t : Spec.Tier) (tw : TierWalk t) (i : Nat) (hi : i ≤ t.cells) :
    FitsLen (i + 1) := by
  apply FitsLen.of_le tw.roomO
  have hpos : 0 < cellOpsCharge t := by
    have h := tw.opsOver
    omega
  exact Nat.le_trans (by omega : i + 1 ≤ t.cells + 1)
    (Nat.le_mul_of_pos_right (t.cells + 1) hpos)

private theorem cells_fit (t : Spec.Tier) (tw : TierWalk t) : FitsLen t.cells := by
  apply FitsLen.of_le tw.roomO
  have hpos : 0 < cellOpsCharge t := by
    unfold cellOpsCharge
    omega
  calc
    t.cells ≤ t.cells * cellOpsCharge t := Nat.le_mul_of_pos_right t.cells hpos
    _ ≤ t.cells * cellOpsCharge t + cellOpsCharge t := Nat.le_add_right _ _
    _ = (t.cells + 1) * cellOpsCharge t := by rw [Nat.succ_mul]

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

/-- One successful live cell, strictly before the refusal. -/
theorem live_step_ok (t : Spec.Tier) (tw : TierWalk t) (b : Ecbs.Board)
    (x y ax ay : List Nat) (acc0 : List Nat × List Nat) (accI : List Nat × List Nat)
    (cells : List Nat) (j i : Nat)
    (hOk : BoardOk t) (sat : TierSat t) (hR : 0 < tierR t) (hsh : TierShape t)
    (hAt : LiveAt t b x y ax ay j)
    (hlen : cells.length = t.cells)
    (hc2 : ∀ n (hn : n < cells.length), cells[n] ≤ 2)
    (hj : j < i) (hi : i < cells.length)
    (hpre : walkRun t.n t.k t.benchlen (x, y) false acc0 (cells.take j) =
      some (true, (ax, ay)))
    (hfull : walkRun t.n t.k t.benchlen (x, y) false acc0 (cells.take i) =
      some (true, accI)) :
    ∃ b' ax' ay',
      chordStep (embed cells) (Int.ofNat (t.cells - 1)) (Int.ofNat j, (b, true)) =
        .ok (SudoRt.Flow.cont (Int.ofNat (j + 1), (b', true))) ∧
      LiveAt t b' x y ax' ay' (j + 1) ∧
      walkRun t.n t.k t.benchlen (x, y) false acc0 (cells.take (j + 1)) =
        some (true, (ax', ay')) := by
  let toN := t.cells - 1
  have hto : toN + 1 = t.cells := by omega
  have hjN : j ≤ toN := by omega
  have hlenC : cells.length = toN + 1 := by omega
  have hjLen : j < cells.length := by omega
  have hfit := step_fit t tw j (by omega)
  have hinv : cells[j]'(by omega) ≠ 0 →
      ∃ inv, fieldInv t.n t.k t.benchlen
        (fieldSub t.n x (fieldCube t.n t.k t.benchlen ax)) = some inv := by
    intro hnz
    have hle := hc2 j hjLen
    have hc : cells[j]'(by omega) = 1 ∨ cells[j]'(by omega) = 2 := by omega
    have hlenI : (cells.take i).length = i := by
      rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
    have hjI : j < (cells.take i).length := by rw [hlenI]; exact hj
    obtain ⟨liveJ, accJ, step, hpreJ, hstepJ, _⟩ :=
      walkRun_at t.n t.k t.benchlen (x, y) false acc0 (cells.take i) j (true, accI)
        hjI hfull
    have hpreJ' : walkRun t.n t.k t.benchlen (x, y) false acc0 (cells.take j) =
        some (liveJ, accJ) := by
      simpa [List.take_take, Nat.min_eq_left (Nat.le_of_lt hj)] using hpreJ
    have hs := Option.some.inj (hpreJ'.symm.trans hpre)
    have hliveJ : liveJ = true := congrArg Prod.fst hs
    have haccJ : accJ = (ax, ay) := congrArg Prod.snd hs
    rw [hliveJ, haccJ] at hstepJ
    have hcellEq : (cells.take i)[j]'hjI = cells[j]'hjLen := by
      rw [List.getElem_take]
    rw [hcellEq] at hstepJ
    exact live_chord_inv t.n t.k t.benchlen (x, y) (ax, ay) (cells[j]'hjLen) step hc hstepJ
  obtain ⟨b', ax', ay', hstep, hwalk, hnext, _⟩ :=
    live_cell t tw b x y ax ay j cells j toN hOk sat hR hsh hAt rfl hto
      (by omega) (by omega) hjN hlenC (hc2 j hjLen) hfit hinv
  have hlt : j < toN := by omega
  have hne : j ≠ toN := by omega
  rw [if_neg hne] at hstep
  have hAt' := hnext hlt
  have htake := take_succ_cell cells j hjLen
  have hrun := walkRun_snoc t.n t.k t.benchlen (x, y) acc0 (ax, ay) (ax', ay')
    (cells.take j) (cells[j]) false hpre hwalk
  refine ⟨b', ax', ay', hstep, hAt', by simpa [htake] using hrun⟩

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

/-- Successful live cells from `start` up to the refusal at `i`. -/
theorem live_until (t : Spec.Tier) (tw : TierWalk t) (b : Ecbs.Board)
    (x y ax ay : List Nat) (acc0 accI : List Nat × List Nat)
    (cells : List Nat) (start i : Nat)
    (hOk : BoardOk t) (sat : TierSat t) (hR : 0 < tierR t) (hsh : TierShape t)
    (hAt : LiveAt t b x y ax ay start)
    (hlen : cells.length = t.cells)
    (hc2 : ∀ n (hn : n < cells.length), cells[n] ≤ 2)
    (hs : start ≤ i) (hi : i < cells.length)
    (hpre : walkRun t.n t.k t.benchlen (x, y) false acc0 (cells.take start) =
      some (true, (ax, ay)))
    (hfull : walkRun t.n t.k t.benchlen (x, y) false acc0 (cells.take i) =
      some (true, accI)) :
    ∃ b' ax' ay',
      LiveAt t b' x y ax' ay' i ∧
      walkRun t.n t.k t.benchlen (x, y) false acc0 (cells.take i) =
        some (true, (ax', ay')) ∧
      SudoRt.runLoopOn (Int.ofNat start, (b, true))
          (fuelRange (Int.ofNat start) (Int.ofNat (t.cells - 1)))
          (chordStep (embed cells) (Int.ofNat (t.cells - 1))) chordAfter (fun r => pure r) =
        SudoRt.runLoopOn (Int.ofNat i, (b', true))
          (fuelRange (Int.ofNat i) (Int.ofNat (t.cells - 1)))
          (chordStep (embed cells) (Int.ofNat (t.cells - 1))) chordAfter (fun r => pure r) := by
  suffices ∀ d start b ax ay,
      start ≤ i →
      i - start = d →
      LiveAt t b x y ax ay start →
      walkRun t.n t.k t.benchlen (x, y) false acc0 (cells.take start) =
        some (true, (ax, ay)) →
      ∃ b' ax' ay',
        LiveAt t b' x y ax' ay' i ∧
        walkRun t.n t.k t.benchlen (x, y) false acc0 (cells.take i) =
          some (true, (ax', ay')) ∧
        SudoRt.runLoopOn (Int.ofNat start, (b, true))
            (fuelRange (Int.ofNat start) (Int.ofNat (t.cells - 1)))
            (chordStep (embed cells) (Int.ofNat (t.cells - 1))) chordAfter (fun r => pure r) =
          SudoRt.runLoopOn (Int.ofNat i, (b', true))
            (fuelRange (Int.ofNat i) (Int.ofNat (t.cells - 1)))
            (chordStep (embed cells) (Int.ofNat (t.cells - 1))) chordAfter (fun r => pure r) by
    exact this (i - start) start b ax ay hs rfl hAt hpre
  intro d
  induction d with
  | zero =>
    intro start b ax ay hs hd hAt hpre
    have heq : start = i := by omega
    subst heq
    exact ⟨b, ax, ay, hAt, hpre, rfl⟩
  | succ d ih =>
    intro start b ax ay hs hd hAt hpre
    have hlt : start < i := by omega
    obtain ⟨b', ax', ay', hstep, hAt', hrun'⟩ :=
      live_step_ok t tw b x y ax ay acc0 accI cells start i hOk sat hR hsh hAt
        hlen hc2 hlt hi hpre hfull
    have hcont := cont_from start (t.cells - 1) b b' cells
      (by
        have hlenI : i < t.cells := by
          rw [← hlen]
          exact hi
        omega)
      hstep
    obtain ⟨b2, ax2, ay2, hAt2, hrun2, hloop⟩ :=
      ih (start + 1) b' ax' ay' (by omega) (by omega) hAt' hrun'
    exact ⟨b2, ax2, ay2, hAt2, hrun2, hcont.trans hloop⟩

private theorem one_mul_le (left a : Nat) (h : 0 < left) : a ≤ left * a :=
  Nat.le_mul_of_pos_left a h

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

private theorem frame_tier_n (t : Spec.Tier) (b : Ecbs.Board) (baseX accX : List Nat)
    (fr : RunFrame b t baseX accX) :
    b.sudo_5Board_1t.sudo_4Tier_1n = (t.n : Int) := by
  simp [fr.tier, embTier]

private theorem flag_beq (c : Nat) (hc : c = 1 ∨ c = 2) :
    SudoRt.SEq.beq (Int.ofNat c) (2 : Int) = decide (c = 2) := by
  rcases hc with rfl | rfl <;> decide

private theorem take_open (zs rest : List Nat) (c : Nat) :
    (zs ++ (c :: rest)).take (zs.length + 1) = zs ++ [c] := by
  induction zs with
  | nil => simp
  | cons z zs ih =>
    simp [List.take_succ_cons, ih]

/-- A live board at the cell `walkRun` refuses. The loop there is the reroll
    when that run is `n` zeros, and the check trap otherwise. -/
theorem frame_is_fail (t : Spec.Tier) (b : Ecbs.Board)
    (baseX baseY accX accY : List Nat) (cells : List Nat) (i c : Nat)
    (tw : TierWalk t) (hOk : BoardOk t) (sat : TierSat t)
    (hR : 0 < tierR t) (hsh : TierShape t)
    (hAt : LiveAt t b baseX baseY accX accY i)
    (hlen : cells.length = t.cells) (hi : i < t.cells)
    (hcAt : cells[i]'(by omega) = c) (hc : c = 1 ∨ c = 2)
    (hinv : fieldInv t.n t.k t.benchlen
      (fieldSub t.n baseX (fieldCube t.n t.k t.benchlen accX)) = none) :
    (∃ bA : Ecbs.Board, SudoRt.runLoopOn (Int.ofNat i, (b, true))
        (fuelRange (Int.ofNat i) (Int.ofNat (t.cells - 1)))
        (chordStep (embed cells) (Int.ofNat (t.cells - 1))) chordAfter (fun r => pure r) =
        .ok ((true, false), { bA with sudo_5Board_9marker_on := false })) ∨
      (∃ e, SudoRt.runLoopOn (Int.ofNat i, (b, true))
        (fuelRange (Int.ofNat i) (Int.ofNat (t.cells - 1)))
        (chordStep (embed cells) (Int.ofNat (t.cells - 1))) chordAfter (fun r => pure r) =
        .error e ∧ e.kind = "AssertFailed" ∧
        (e.detail = s!"line {728}" ∨
          ∃ d, d ≠ 0 ∧
            e.detail = s!"line {730}: {SudoRt.Canon.canon (Int.ofNat d)} != {SudoRt.Canon.canon (0 : Int)}")) := by
  let toN := t.cells - 1
  have hk : i ≤ toN := by omega
  have hlenC : cells.length = toN + 1 := by omega
  obtain ⟨fr, hmk, hY, hA, hf4, hf1, hst, hhole, hm, hs, hctrl, ho, _hyB, _htriY, hyA, htriA⟩ := hAt
  let left := t.cells - i
  have hleft : 0 < left := by omega
  have hsum : i + left = t.cells := by omega
  have hs4 : fr.slides ≤ i * (cellSlideCharge t + 4 * t.n) := by
    rw [slideCharge] at hs
    exact hs
  obtain ⟨bL, bF, frF, hml, hfrob, _hmkF, _hy1F, _hy4F, hctrlF, _hmarkF, hopsF, hmvF, hslF,
      _hstF, hhoF, _hfitS, _hfitH, _hopsN, _hocc, _hholeEq, _hf1F, _hf4F⟩ :=
    tier_cell_frob t b baseX accX baseY accY fr i left tw hOk sat hsh
      hmk hY hA hf4 hf1 hyA htriA hsum hleft hm hs4 hctrl ho hst hhole
  by_cases hzero : fieldSub t.n baseX (fieldCube t.n t.k t.benchlen accX) =
      List.replicate t.n 0
  · have hfitM : FitsLen (frF.moves + 2 * t.n) :=
      FitsLen.of_le frF.fitRoom (by omega)
    have hn := frame_tier_n t bF baseX (fieldCube t.n t.k t.benchlen accX) frF
    obtain ⟨bA, hstep, _⟩ :=
      chordStep_empty_run cells i toN c b bL bF t.n t.k t.benchlen frF.moves frF.peak
        frF.chordOps (baseX, baseY) (accX, accY) hk hlenC hcAt hc hml hfrob frF.szH
        frF.szD frF.ops3 frF.hop3 frF.fitChord frF.lenX frF.triX frF.triA hn frF.hmoves
        frF.hpeak hfitM frF.held2 frF.held0 frF.home0 frF.held3 frF.home3 hzero
        hOk.n_pos tw.nLe
    have hret := ret_from i toN b cells
      ((true, false), { bA with sudo_5Board_9marker_on := false }) hk hstep
    exact Or.inl ⟨bA, hret⟩
  · have hrooms := chord_rooms t tw fr.moves fr.slides fr.ctrl fr.opsCap
      frF.moves frF.slides frF.ctrl frF.opsCap i left hsum hleft hm hs4 hctrl ho
      hmvF hslF (Nat.le_of_eq hctrlF) (Nat.le_of_eq hopsF)
    have hMove : FitsLen (liveMoveRoom t frF.moves baseX
        (fieldCube t.n t.k t.benchlen accX)) := by
      apply FitsLen.of_le hrooms.1
      have hlive := live_move_le t frF.moves baseX (fieldCube t.n t.k t.benchlen accX)
        frF.lenX (fieldCube_length t.n t.k t.benchlen accX tw.nLe)
      have hmul := one_mul_le left (cellMoveCharge t) hleft
      omega
    have hSlide : FitsLen (liveSlideRoom t frF.slides) := by
      apply FitsLen.of_le hrooms.2.1
      rw [live_slide_eq]
      exact Nat.add_le_add_left (one_mul_le left _ hleft) _
    have hCtrl : FitsLen (liveCtrlRoom t frF.ctrl) := by
      apply FitsLen.of_le hrooms.2.2.1
      rw [live_ctrl_eq]
      exact Nat.add_le_add_left (one_mul_le left _ hleft) _
    have hOps : FitsLen (liveOpsRoom t frF.opsCap) := by
      apply FitsLen.of_le hrooms.2.2.2
      rw [live_ops_eq]
      exact Nat.add_le_add_left (one_mul_le left _ hleft) _
    obtain ⟨e, hadd, hknd, hd⟩ :=
      chord_add_trap bF t baseX (fieldCube t.n t.k t.benchlen accX)
        (SudoRt.SEq.beq (Int.ofNat c) (2 : Int)) frF hOk sat hR hsh
        hMove hSlide hCtrl hOps hhoF hzero hinv
    have hstep := chordStep_trap cells i toN c b bL bF e hk hlenC hcAt
      (by rcases hc with rfl | rfl <;> decide) (by rcases hc with rfl | rfl <;> decide)
      hml hfrob hadd
    have herr := err_from i toN b cells e hk hstep
    exact Or.inr ⟨e, herr, hknd, hd⟩

/-- The cell after the opening copy succeeds. The board it leaves is `LiveAt`
    at the next index, and the loop takes one `cont` step. -/
theorem land_seat (t : Spec.Tier) (b2 : Ecbs.Board)
    (x y up : List Nat) (mv pk : Nat)
    (acc accI : List Nat × List Nat) (cells : List Nat) (k i : Nat)
    (out : OutLay t b2 x up y mv pk)
    (tw : TierWalk t) (hOk : BoardOk t) (sat : TierSat t)
    (hR : 0 < tierR t) (hsh : TierShape t)
    (hx : x.length = t.n) (hy : y.length = t.n)
    (htriX : allTritList x) (htriY : allTritList y) (htriUp : allTritList up)
    (hup : up.length = t.n)
    (hmvEq : mv = pegCount x + pegCount y + pegCount x + pegCount y)
    (hmvN : mv ≤ 4 * t.n)
    (hlen : cells.length = t.cells)
    (hkLt : k < i) (hi : i < cells.length) (hk1 : 1 ≤ k)
    (hpre : walkRun t.n t.k t.benchlen (x, y) false acc (cells.take k) =
      some (true, (x, up)))
    (hfull : walkRun t.n t.k t.benchlen (x, y) false acc (cells.take i) =
      some (true, accI))
    (hc2 : ∀ n (hn : n < cells.length), cells[n] ≤ 2) :
    ∃ b' ax ay,
      chordStep (embed cells) (Int.ofNat (t.cells - 1)) (Int.ofNat k, (b2, true)) =
        .ok (SudoRt.Flow.cont (Int.ofNat (k + 1), (b', true))) ∧
      LiveAt t b' x y ax ay (k + 1) ∧
      walkRun t.n t.k t.benchlen (x, y) false acc (cells.take (k + 1)) =
        some (true, (ax, ay)) := by
  let toN := t.cells - 1
  have hkTo : k ≤ toN := by omega
  have hne : k ≠ toN := by omega
  have hlenC : cells.length = toN + 1 := by omega
  have hiK : k < cells.length := by omega
  have hfitk := step_fit t tw k (by omega)
  obtain ⟨bF, fr, hml, hfrob, hmk, hy1, hy4, hmark, hctrl, hst, hho, hmv, hsl, hops,
      hf1, hf4⟩ :=
    seat_out t b2 x up y mv pk out tw hOk sat hsh hR hx hup htriX htriUp hmvN
      (by omega : 0 < t.cells)
  by_cases hzero : cells[k]'hiK = 0
  · have hwalk := walkStep_cube t.n t.k t.benchlen (x, y) (x, up)
    have hstep0 := chordStep_cube cells k toN b2 b2 bF hkTo hlenC hzero hml hfrob hfitk
    rw [if_neg hne] at hstep0
    have hsnoc := walkRun_snoc t.n t.k t.benchlen (x, y) acc (x, up)
      (fieldCube t.n t.k t.benchlen x, fieldCube t.n t.k t.benchlen up)
      (cells.take k) 0 false hpre hwalk
    have htake := take_succ_cell cells k hiK
    have hAt := cubed_live t bF x y up mv fr (k + 1) tw sat hsh hR hx hy hmk hy4 hy1
      hf4 hf1 hmv hsl hctrl hops hst hho htriY htriUp hmvN (by omega)
    refine ⟨bF, fieldCube t.n t.k t.benchlen x, fieldCube t.n t.k t.benchlen up,
      hstep0, hAt, ?_⟩
    simpa [htake, hzero] using hsnoc
  · have hcS : cells[k]'hiK = 1 ∨ cells[k]'hiK = 2 := by
      have hle := hc2 k hiK
      omega
    have hlenI : (cells.take i).length = i := by
      rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
    have hkI : k < (cells.take i).length := by rw [hlenI]; exact hkLt
    have hpreI : walkRun t.n t.k t.benchlen (x, y) false acc ((cells.take i).take k) =
        some (true, (x, up)) := by
      simpa [List.take_take, Nat.min_eq_left (Nat.le_of_lt hkLt)] using hpre
    have hcTake : (cells.take i)[k]'hkI = cells[k]'hiK := by
      rw [List.getElem_take]
    obtain ⟨inv, hinv⟩ :=
      walkRun_live_inv t.n t.k t.benchlen (x, y) acc (x, up) (cells.take i) k
        (true, accI) hkI (by rw [hcTake]; exact hcS) hpreI hfull
    let left := t.cells - k
    let fuel := left - 1
    have hfuel : 1 ≤ fuel := by omega
    have hleftEq : fuel + 1 = left := by omega
    have hsum : k + left = t.cells := by omega
    have hmvP : fr.moves ≤ pegCount x + pegCount y + pegCount x + pegCount y +
        cubeCharge t.n t.benchlen := by
      simpa [hmvEq] using hmv
    obtain ⟨b', x3, y3, hdemo, hwalk, hAt⟩ :=
      seat_cell_chord t bF x y up (cells[k]'hiK) k left fuel inv fr tw hOk sat hR hsh
        hmk hy4 hy1 hf4 hf1 hy htriY htriUp hmvP hsl hctrl hops hmark hst hho
        hcS hinv hk1 hfuel hleftEq hsum
    have hadd : Ecbs.chord_add_demo bF
        (SudoRt.SEq.beq (Int.ofNat (cells[k]'hiK)) (2 : Int)) = .ok (true, b') := by
      rw [flag_beq _ hcS]
      exact hdemo
    have hstep := chordStep_open cells k toN (cells[k]'hiK) b2 b2 bF b' hkTo hlenC
      rfl hzero (hc2 k hiK) hml hfrob hadd hfitk
    rw [if_neg hne] at hstep
    have hsnoc := walkRun_snoc t.n t.k t.benchlen (x, y) acc (x, up) (x3, y3)
      (cells.take k) (cells[k]'hiK) false hpre hwalk
    have htake := take_succ_cell cells k hiK
    exact ⟨b', x3, y3, hstep, hAt, by simpa [htake] using hsnoc⟩

/-- From the copied board, the rest of a refused walk is the reroll or the trap. -/
theorem suffix_is_fail (t : Spec.Tier) (b2 : Ecbs.Board)
    (x y up : List Nat) (mv pk : Nat)
    (acc accI : List Nat × List Nat) (cells : List Nat) (k i c : Nat)
    (out : OutLay t b2 x up y mv pk)
    (tw : TierWalk t) (hOk : BoardOk t) (sat : TierSat t)
    (hR : 0 < tierR t) (hsh : TierShape t)
    (hx : x.length = t.n) (hy : y.length = t.n)
    (htriX : allTritList x) (htriY : allTritList y) (htriUp : allTritList up)
    (hup : up.length = t.n)
    (hmvEq : mv = pegCount x + pegCount y + pegCount x + pegCount y)
    (hmvN : mv ≤ 4 * t.n)
    (hlen : cells.length = t.cells)
    (hkLe : k ≤ i) (hi : i < cells.length) (hk1 : 1 ≤ k)
    (hkTo : k ≤ t.cells - 1)
    (hpre : walkRun t.n t.k t.benchlen (x, y) false acc (cells.take k) =
      some (true, (x, up)))
    (hfull : walkRun t.n t.k t.benchlen (x, y) false acc (cells.take i) =
      some (true, accI))
    (hcAt : cells[i]'(hi) = c) (hc : c = 1 ∨ c = 2)
    (hinv : fieldInv t.n t.k t.benchlen
      (fieldSub t.n x (fieldCube t.n t.k t.benchlen accI.1)) = none)
    (hc2 : ∀ n (hn : n < cells.length), cells[n] ≤ 2) :
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
  by_cases hik : i = k
  · have hfullK : walkRun t.n t.k t.benchlen (x, y) false acc (cells.take k) =
        some (true, accI) := by
      rw [← hik]
      exact hfull
    have hpair := Option.some.inj (hfullK.symm.trans hpre)
    have hacc : accI = (x, up) := congrArg Prod.snd hpair
    have hinvX : fieldInv t.n t.k t.benchlen
        (fieldSub t.n x (fieldCube t.n t.k t.benchlen x)) = none := by
      rw [hacc] at hinv
      exact hinv
    have hcK : cells[k]'(by omega) = c := by
      have hik' : k = i := hik.symm
      subst hik'
      exact hcAt
    obtain ⟨bF, fr, hml, hfrob, _hmk, _hy1, _hy4, _hmark, hctrl, _hst, hho, hmv, hsl, hops,
        _hf1, _hf4⟩ :=
      seat_out t b2 x up y mv pk out tw hOk sat hsh hR hx hup htriX htriUp hmvN
        (by omega : 0 < t.cells)
    have hmvP : fr.moves ≤ pegCount x + pegCount y + pegCount x + pegCount y +
        cubeCharge t.n t.benchlen := by
      rw [hmvEq] at hmv
      exact hmv
    exact seat_is_fail t b2 bF x y up cells k c fr tw hOk sat hR hsh hx hy hml hfrob
      hctrl hops hmvP hsl hho hlen hkTo hk1 hcK hc hinvX
  · have hkLt : k < i := by omega
    obtain ⟨b', ax, ay, hstep, hAt, hrun1⟩ :=
      land_seat t b2 x y up mv pk acc accI cells k i out tw hOk sat hR hsh
        hx hy htriX htriY htriUp hup hmvEq hmvN hlen hkLt hi hk1 hpre hfull hc2
    have hcont := cont_from k (t.cells - 1) b2 b' cells (by omega) hstep
    obtain ⟨bI, axI, ayI, hAtI, hrunI, hloop⟩ :=
      live_until t tw b' x y ax ay acc accI cells (k + 1) i hOk sat hR hsh hAt
        hlen hc2 (by omega) hi hrun1 hfull
    have hpair := Option.some.inj (hrunI.symm.trans hfull)
    have hsnd : (axI, ayI) = accI := congrArg Prod.snd hpair
    have hinvI : fieldInv t.n t.k t.benchlen
        (fieldSub t.n x (fieldCube t.n t.k t.benchlen axI)) = none := by
      rw [← hsnd] at hinv
      exact hinv
    have hfail := frame_is_fail t bI x y axI ayI cells i c tw hOk sat hR hsh hAtI
      hlen (by omega) hcAt hc hinvI
    have hjoin :
        SudoRt.runLoopOn (Int.ofNat k, (b2, true))
            (fuelRange (Int.ofNat k) (Int.ofNat (t.cells - 1)))
            (chordStep (embed cells) (Int.ofNat (t.cells - 1))) chordAfter (fun r => pure r) =
          SudoRt.runLoopOn (Int.ofNat i, (bI, true))
            (fuelRange (Int.ofNat i) (Int.ofNat (t.cells - 1)))
            (chordStep (embed cells) (Int.ofNat (t.cells - 1))) chordAfter (fun r => pure r) :=
      hcont.trans hloop
    rcases hfail with ⟨bA, hok⟩ | ⟨e, herr, hknd, hd⟩
    · exact Or.inl ⟨bA, hjoin.trans hok⟩
    · exact Or.inr ⟨e, hjoin.trans herr, hknd, hd⟩

/-- `walkRun = none` on the domain. The emitted walk is the reroll, or the
    `AssertFailed` trap at line 728 or 730. -/
theorem walk_chord_none (t : Spec.Tier) (x y : List Nat)
    (acc : List Nat × List Nat) (cells : List Nat)
    (tw : TierWalk t) (hOk : BoardOk t) (sat : TierSat t)
    (hR : 0 < tierR t) (hsh : TierShape t)
    (hx : x.length = t.n) (hy : y.length = t.n)
    (htriX : allTritList x) (htriY : allTritList y)
    (hlen : cells.length = t.cells)
    (hc2 : ∀ n (hn : n < cells.length), cells[n] ≤ 2)
    (h : walkRun t.n t.k t.benchlen (x, y) false acc cells = none) :
    (∃ bA : Ecbs.Board, Ecbs.walk_chord (baseBoard t x y) (embed cells) =
        .ok ((true, false), { bA with sudo_5Board_9marker_on := false })) ∨
      (∃ e, Ecbs.walk_chord (baseBoard t x y) (embed cells) = .error e ∧
        e.kind = "AssertFailed" ∧
        (e.detail = s!"line {728}" ∨
          ∃ d, d ≠ 0 ∧
            e.detail = s!"line {730}: {SudoRt.Canon.canon (Int.ofNat d)} != {SudoRt.Canon.canon (0 : Int)}")) := by
  obtain ⟨i, hi, liveI, accI, hpre, hcell⟩ :=
    first_fail t.n t.k t.benchlen (x, y) false acc cells hc2 h
  have hlive : liveI = true :=
    step_none_live t.n t.k t.benchlen (x, y) accI liveI (cells[i]'hi) hcell (hc2 i hi)
  have hpreT : walkRun t.n t.k t.benchlen (x, y) false acc (cells.take i) =
      some (true, accI) := by
    simpa [hlive] using hpre
  have hcellT : walkStep t.n t.k t.benchlen (x, y) true accI (cells[i]'hi) = none := by
    simpa [hlive] using hcell
  obtain ⟨hcFail, hinv⟩ :=
    step_none_inv t.n t.k t.benchlen (x, y) accI (cells[i]'hi) hcellT (hc2 i hi)
  obtain ⟨zs, oc, mid, heqTake, hz, hoc⟩ :=
    walk_split_live t.n t.k t.benchlen (x, y) acc accI (cells.take i) hpreT
  have hcells : cells = zs ++ (oc :: (mid ++ cells.drop i)) := by
    calc
      cells = cells.take i ++ cells.drop i := (List.take_append_drop i cells).symm
      _ = (zs ++ (oc :: mid)) ++ cells.drop i := by rw [heqTake]
      _ = zs ++ ((oc :: mid) ++ cells.drop i) := by rw [List.append_assoc]
      _ = zs ++ (oc :: (mid ++ cells.drop i)) := by rw [List.cons_append]
  let rest := mid ++ cells.drop i
  have hrest : 0 < rest.length := by
    change 0 < (mid ++ cells.drop i).length
    rw [List.length_append, List.length_drop]
    omega
  let k := zs.length + 1
  have hlenTake : (cells.take i).length = i := by
    rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
  have hkSum : k + mid.length = i := by
    have hlenEq : i = (zs ++ (oc :: mid)).length := by
      rw [← hlenTake]
      exact congrArg List.length heqTake
    rw [List.length_append, List.length_cons] at hlenEq
    omega
  have hkLe : k ≤ i := by omega
  have hk1 : 1 ≤ k := by omega
  have hkTo : k ≤ t.cells - 1 := by
    have hlen' : (zs ++ (oc :: rest)).length = t.cells := by
      rw [← hcells]
      exact hlen
    rw [List.length_append, List.length_cons] at hlen'
    omega
  have htakeK : cells.take k = zs ++ [oc] := by
    rw [hcells]
    exact take_open zs rest oc
  have hpos : 0 < t.cells := by omega
  have hfit := cells_fit t tw
  have hmvN : pegCount x + pegCount y + pegCount x + pegCount y ≤ 4 * t.n := by
    have hpx : pegCount x ≤ t.n := by rw [← hx]; exact pegCount_le x
    have hpy : pegCount y ≤ t.n := by rw [← hy]; exact pegCount_le y
    omega
  rcases hoc with rfl | rfl
  · obtain ⟨b2, pk, out, _hcopy, hloop⟩ :=
      walk_reach_white t x y zs rest tw hsh hR hx hy hz
        (by rw [← hcells]; exact hlen) hrest
    have hpreK : walkRun t.n t.k t.benchlen (x, y) false acc (cells.take k) =
        some (true, (x, y)) := by
      rw [htakeK]
      exact walkRun_open_white t.n t.k t.benchlen (x, y) acc zs hz
    have hjoin :
        Ecbs.walk_chord (baseBoard t x y) (embed cells) =
          SudoRt.runLoopOn (Int.ofNat k, (b2, true))
            (fuelRange (Int.ofNat k) (Int.ofNat (t.cells - 1)))
            (chordStep (embed cells) (Int.ofNat (t.cells - 1)))
            chordAfter (fun r => pure r) := by
      rw [walk_chord_loop (baseBoard t x y) cells (by rw [hlen]; exact hpos)
        (by rw [hlen]; exact hfit)]
      rw [show cells.length - 1 = t.cells - 1 by rw [hlen]]
      rw [hcells]
      exact hloop
    have hsuf := suffix_is_fail t b2 x y y
      (pegCount x + pegCount y + pegCount x + pegCount y) pk acc accI cells k i
      (cells[i]'hi) out tw hOk sat hR hsh hx hy htriX htriY htriY hy rfl hmvN
      hlen hkLe hi hk1 hkTo hpreK hpreT rfl hcFail hinv hc2
    rcases hsuf with ⟨bA, hok⟩ | ⟨e, herr, hknd, hd⟩
    · exact Or.inl ⟨bA, hjoin.trans hok⟩
    · exact Or.inr ⟨e, hjoin.trans herr, hknd, hd⟩
  · obtain ⟨b2, pk, out, _hcopy, hloop⟩ :=
      walk_reach_red t x y zs rest tw hOk hsh hR hx hy htriY hz
        (by rw [← hcells]; exact hlen) hrest
    have hpreK : walkRun t.n t.k t.benchlen (x, y) false acc (cells.take k) =
        some (true, (x, mirrorTrits y)) := by
      rw [htakeK]
      exact walkRun_open_red t.n t.k t.benchlen x y acc zs hz
    have hjoin :
        Ecbs.walk_chord (baseBoard t x y) (embed cells) =
          SudoRt.runLoopOn (Int.ofNat k, (b2, true))
            (fuelRange (Int.ofNat k) (Int.ofNat (t.cells - 1)))
            (chordStep (embed cells) (Int.ofNat (t.cells - 1)))
            chordAfter (fun r => pure r) := by
      rw [walk_chord_loop (baseBoard t x y) cells (by rw [hlen]; exact hpos)
        (by rw [hlen]; exact hfit)]
      rw [show cells.length - 1 = t.cells - 1 by rw [hlen]]
      rw [hcells]
      exact hloop
    have hsuf := suffix_is_fail t b2 x y (mirrorTrits y)
      (pegCount x + pegCount y + pegCount x + pegCount y) pk acc accI cells k i
      (cells[i]'hi) out tw hOk sat hR hsh hx hy htriX htriY
      (mirrorTrits_allTrit htriY) (by rw [mirror_length, hy]) rfl hmvN
      hlen hkLe hi hk1 hkTo hpreK hpreT rfl hcFail hinv hc2
    rcases hsuf with ⟨bA, hok⟩ | ⟨e, herr, hknd, hd⟩
    · exact Or.inl ⟨bA, hjoin.trans hok⟩
    · exact Or.inr ⟨e, hjoin.trans herr, hknd, hd⟩

/-- The domain walk. A run that stays dead leaves the homes. A run that
    returns a point emits it. A run that returns `none` is the reroll or the
    check trap. -/
theorem walk_chord_cases (t : Spec.Tier) (x y : List Nat)
    (acc : List Nat × List Nat) (cells : List Nat)
    (tw : TierWalk t) (hOk : BoardOk t) (sat : TierSat t)
    (hR : 0 < tierR t) (hsh : TierShape t)
    (hx : x.length = t.n) (hy : y.length = t.n)
    (htriX : allTritList x) (htriY : allTritList y)
    (hlen : cells.length = t.cells)
    (hc2 : ∀ n (hn : n < cells.length), cells[n] ≤ 2) :
    (∃ acc', walkRun t.n t.k t.benchlen (x, y) false acc cells = some (false, acc') ∧
        acc' = acc ∧
        Ecbs.walk_chord (baseBoard t x y) (embed cells) =
          .ok ((false, true),
            { baseBoard t x y with sudo_5Board_9marker_on := false })) ∨
      (∃ px py b',
        walkRun t.n t.k t.benchlen (x, y) false acc cells = some (true, (px, py)) ∧
        Ecbs.walk_chord (baseBoard t x y) (embed cells) = .ok ((true, true), b') ∧
        (∀ h0 : 0 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[0] = embed px) ∧
        (∀ h1 : 1 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[1] = embed py)) ∨
      (walkRun t.n t.k t.benchlen (x, y) false acc cells = none ∧
        ((∃ bA : Ecbs.Board, Ecbs.walk_chord (baseBoard t x y) (embed cells) =
            .ok ((true, false), { bA with sudo_5Board_9marker_on := false })) ∨
          (∃ e, Ecbs.walk_chord (baseBoard t x y) (embed cells) = .error e ∧
            e.kind = "AssertFailed" ∧
            (e.detail = s!"line {728}" ∨
              ∃ d, d ≠ 0 ∧
                e.detail =
                  s!"line {730}: {SudoRt.Canon.canon (Int.ofNat d)} != {SudoRt.Canon.canon (0 : Int)}")))) := by
  cases hrun : walkRun t.n t.k t.benchlen (x, y) false acc cells with
  | some q =>
    rcases q with ⟨live, acc'⟩
    obtain hsome :=
      walk_chord_some t x y acc acc' cells live tw hOk sat hR hsh hx hy htriX htriY hlen hrun
    rcases hsome with ⟨hfalse, hacc, hch⟩ | ⟨htrue, px, py, b', hpt, hch, hx0, hy1⟩
    · exact Or.inl ⟨acc', by rw [hfalse], hacc, hch⟩
    · exact Or.inr (Or.inl ⟨px, py, b', by rw [htrue, hpt], hch, hx0, hy1⟩)
  | none =>
    exact Or.inr (Or.inr ⟨rfl, walk_chord_none t x y acc cells tw hOk sat hR hsh
      hx hy htriX htriY hlen hc2 hrun⟩)

end EcbsLink2.Link2
