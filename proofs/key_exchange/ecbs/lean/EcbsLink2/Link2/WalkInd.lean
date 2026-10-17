/-
  The live suffix of `walk_chord`. The first cell's frame reads `peakS` and the
  bench hole off the initial board, whose strict and hole are zero. Later cells
  keep both bounds; neither is a hypothesis of the walk. A nonzero cell needs
  the inverse of the run it actually reaches. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.BoardBuild
import EcbsLink2.Link2.WalkCell
import EcbsLink2.Link2.WalkLoop

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

theorem built_strict (t : Spec.Tier) :
    (builtBoard t).sudo_5Board_4cost.sudo_5Costs_11peak_strict = 0 := by
  simp [builtBoard, midBoard, placed, blankOf]

theorem built_hole (t : Spec.Tier) :
    (builtBoard t).sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = 0 := by
  simp [builtBoard, midBoard, placed, blankOf]

/-- A frame whose strict and hole are still the initial board's has `peakS = 0`
    and `hole = 0`, so both sit under the cell bounds. -/
theorem frame_from_initial (t : Spec.Tier) (b : Ecbs.Board) (baseX accX : List Nat)
    (fr : RunFrame b t baseX accX)
    (hs : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict =
      (builtBoard t).sudo_5Board_4cost.sudo_5Costs_11peak_strict)
    (hh : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      (builtBoard t).sudo_5Board_4cost.sudo_5Costs_14max_bench_hole) :
    fr.peakS = 0 ∧ fr.hole = 0 := by
  have hs0 : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = 0 := hs.trans (built_strict t)
  have hh0 : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = 0 := hh.trans (built_hole t)
  refine ⟨?_, ?_⟩
  · apply Int.ofNat.inj
    rw [← fr.hstrict, hs0]
    rfl
  · apply Int.ofNat.inj
    rw [← fr.hhole, hh0]
    rfl

private theorem succ_sum (done a : Nat) :
    (done + 1) * a = done * a + a := by
  rw [Nat.succ_mul]

private theorem next_le (done cap spent now next : Nat)
    (hnow : now ≤ done * cap) (hstep : next ≤ now + spent) (hspent : spent ≤ cap) :
    next ≤ (done + 1) * cap := by
  rw [succ_sum]
  exact Nat.le_trans hstep (Nat.add_le_add hnow hspent)

theorem walkStep_cube (n k bench : Nat) (base acc : List Nat × List Nat) :
    walkStep n k bench base true acc 0 =
      some (true, (fieldCube n k bench acc.1, fieldCube n k bench acc.2)) := by
  unfold walkStep pointCube
  simp

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

/-- The counters and the point on a live board, `done` cells already run. -/
def LiveAt (t : Spec.Tier) (b : Ecbs.Board) (baseX baseY accX accY : List Nat)
    (done : Nat) : Prop :=
  ∃ fr : RunFrame b t baseX accX,
    b.sudo_5Board_9marker_on = true ∧
    fr.y4 = baseY ∧ fr.y1 = accY ∧
    fr.flag4 = true ∧ fr.flag1 = true ∧
    fr.peakS ≤ 7 ∧ fr.hole ≤ t.benchlen ∧
    fr.moves ≤ done * (walkCharge t + (6 * t.benchlen + 2 * t.n)) ∧
    fr.slides ≤ done * (cellSlideCharge t + slideCharge t.n) ∧
    fr.ctrl ≤ done * (cellCtrlCharge t + 4) ∧
    fr.opsCap ≤ done * (cellOpsCharge t + 2) ∧
    baseY.length = t.n ∧ allTritList baseY ∧
    accY.length = t.n ∧ allTritList accY

/-- The first cell. `peakS ≤ 7` and `hole ≤ bench` are the initial board's zeros. -/
theorem live_at_initial (t : Spec.Tier) (b : Ecbs.Board) (baseX baseY accX accY : List Nat)
    (fr : RunFrame b t baseX accX)
    (hs : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict =
      (builtBoard t).sudo_5Board_4cost.sudo_5Costs_11peak_strict)
    (hh : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      (builtBoard t).sudo_5Board_4cost.sudo_5Costs_14max_bench_hole)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hY : fr.y4 = baseY) (hA : fr.y1 = accY)
    (hf4 : fr.flag4 = true) (hf1 : fr.flag1 = true)
    (hm0 : fr.moves = 0) (hs0 : fr.slides = 0) (hc0 : fr.ctrl = 0) (ho0 : fr.opsCap = 0)
    (hyB : baseY.length = t.n) (htriY : allTritList baseY)
    (hyA : accY.length = t.n) (htriA : allTritList accY) :
    LiveAt t b baseX baseY accX accY 0 := by
  obtain ⟨hp, ho⟩ := frame_from_initial t b baseX accX fr hs hh
  refine ⟨fr, hmk, hY, hA, hf4, hf1, ?_, ?_, ?_, ?_, ?_, ?_, hyB, htriY, hyA, htriA⟩
  · rw [hp]; decide
  · rw [ho]; exact Nat.zero_le _
  · simp [hm0]
  · simp [hs0]
  · simp [hc0]
  · simp [ho0]

private theorem index_fit (t : Spec.Tier) (tw : TierWalk t) (i : Nat) (hi : i ≤ t.cells) :
    FitsLen (i + 1) := by
  apply FitsLen.of_le tw.roomO
  have hpos : 0 < cellOpsCharge t := by
    have h := tw.opsOver
    omega
  have hlen : i + 1 ≤ t.cells + 1 := by omega
  exact Nat.le_trans hlen (Nat.le_mul_of_pos_right (t.cells + 1) hpos)

private theorem cube_trits (t : Spec.Tier) (sat : TierSat t) (hsh : TierShape t)
    (xs : List Nat) (hxs : allTritList xs) :
    allTritList (fieldCube t.n t.k t.benchlen xs) := by
  apply fieldCube_trits t.n t.k t.benchlen xs hxs
  · have h := sat.cube_span
    omega
  · exact hsh.k_le

private theorem mark_room (t : Spec.Tier) (tw : TierWalk t) :
    (1 + 3 < t.script) ∧ FitsLen (1 + 4) := by
  refine ⟨tw.scriptRoom, ?_⟩
  unfold FitsLen i64MaxNat
  decide

private theorem colour_beq (c : Nat) (hc : c = 1 ∨ c = 2) :
    SudoRt.SEq.beq (Int.ofNat c) (2 : Int) = decide (c = 2) := by
  rcases hc with rfl | rfl <;> decide

private theorem chord_y_trits (n k bench : Nat) (slope dx y : List Nat) :
    allTritList (chordY3 n k bench slope dx y) := by
  simpa [chordY3, fieldSub] using
    fieldAdd_span_trits n (fieldMul n k bench slope dx) (mirrorTrits y)

private theorem chord_y_len (n k bench : Nat) (slope dx y : List Nat) :
    (chordY3 n k bench slope dx y).length = n := by
  simpa [chordY3] using fieldSub_length n (fieldMul n k bench slope dx) y

/-- One live cell. The output bounds are the cell's, not a fresh hypothesis. -/
theorem live_cell (t : Spec.Tier) (tw : TierWalk t) (b : Ecbs.Board)
    (baseX baseY accX accY : List Nat) (done : Nat) (cells : List Nat) (i toN : Nat)
    (hOk : BoardOk t) (sat : TierSat t) (hR : 0 < tierR t) (hsh : TierShape t)
    (hAt : LiveAt t b baseX baseY accX accY done)
    (hdone : done = i) (hto : toN + 1 = t.cells)
    (hsum : done + (t.cells - done) = t.cells)
    (hleft : 0 < t.cells - done)
    (hi : i ≤ toN) (hlen : cells.length = toN + 1)
    (hcAt : cells[i]'(by omega) ≤ 2)
    (hfiti : FitsLen (i + 1))
    (hinv : cells[i]'(by omega) ≠ 0 →
      ∃ inv, fieldInv t.n t.k t.benchlen
        (fieldSub t.n baseX (fieldCube t.n t.k t.benchlen accX)) = some inv) :
    ∃ b' accX' accY',
      chordStep (embed cells) (Int.ofNat toN) (Int.ofNat i, (b, true)) =
        (if i = toN then .ok (SudoRt.Flow.brk (Int.ofNat i, (b', true)))
          else .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), (b', true)))) ∧
      walkStep t.n t.k t.benchlen (baseX, baseY) true (accX, accY) (cells[i]'(by omega)) =
        some (true, (accX', accY')) ∧
      (i < toN → LiveAt t b' baseX baseY accX' accY' (done + 1)) ∧
      (i = toN →
        (∀ h : 0 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[0] = embed accX') ∧
        (∀ h : 1 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[1] = embed accY')) := by
  obtain ⟨fr, hmk, hY, hA, hf4, hf1, hst, hhole, hm, hs, hc, ho, hyB, htriY, hyA, htriA⟩ := hAt
  obtain ⟨bL, bF, frF, hml, hfrob, hmkF, hy1F, hy4F, hctrlF, hmarkF, hopsF, hmvF, hslF,
      hstF, hhoF, _hfitS, _hfitH, _hopsN, _hocc, _hholeEq, hf1F, hf4F⟩ :=
    tier_cell_frob t b baseX accX baseY accY fr done (t.cells - done) tw
      hOk sat hsh hmk hY hA hf4 hf1 hyA htriA hsum hleft hm hs hc ho hst hhole
  by_cases hz : cells[i]'(by omega) = 0
  · have hstep := chordStep_cube cells i toN b bL bF hi hlen hz hml hfrob hfiti
    have hwalk := walkStep_cube t.n t.k t.benchlen (baseX, baseY) (accX, accY)
    refine ⟨bF, fieldCube t.n t.k t.benchlen accX, fieldCube t.n t.k t.benchlen accY,
      by simpa [hz] using hstep, by simpa [hz] using hwalk, ?_, ?_⟩
    · intro hlt
      refine ⟨frF, hmkF, hy4F, hy1F, hf4F, hf1F, hstF, hhoF, ?_, ?_, ?_, ?_, hyB, htriY, ?_, ?_⟩
      · have hcube : cubeCharge t.n t.benchlen = 6 * t.benchlen + 2 * t.n :=
          cube_over _ _ tw.nLe
        have hstepM : frF.moves ≤ fr.moves + (6 * t.benchlen + 2 * t.n) := by
          rw [← hcube]; exact hmvF
        exact next_le done _ _ fr.moves frF.moves hm hstepM (Nat.le_add_left _ _)
      · exact next_le done _ _ fr.slides frF.slides hs hslF (Nat.le_add_left _ _)
      · have hctrl : frF.ctrl ≤ fr.ctrl + (cellCtrlCharge t + 4) := by
          rw [hctrlF]
          omega
        exact next_le done _ _ fr.ctrl frF.ctrl hc hctrl (Nat.le_refl _)
      · have hops : frF.opsCap ≤ fr.opsCap + (cellOpsCharge t + 2) := by
          rw [hopsF]
          omega
        exact next_le done _ _ fr.opsCap frF.opsCap ho hops (Nat.le_refl _)
      · exact fieldCube_length t.n t.k t.benchlen accY tw.nLe
      · exact cube_trits t sat hsh accY htriA
    · intro hlast
      refine ⟨?_, ?_⟩
      · intro _h0
        exact frF.home0
      · intro _h1
        simpa [hy1F] using frF.home1
  · have hc2 : cells[i]'(by omega) = 1 ∨ cells[i]'(by omega) = 2 := by
      have hle := hcAt
      omega
    obtain ⟨inv, hacc⟩ := hinv hz
    have hpreX : fieldCube t.n t.k t.benchlen accX =
        fieldCube t.n t.k t.benchlen accX := rfl
    have hpreY : fieldCube t.n t.k t.benchlen accY =
        fieldCube t.n t.k t.benchlen accY := rfl
    have hyCube : (fieldCube t.n t.k t.benchlen accY).length = t.n :=
      fieldCube_length t.n t.k t.benchlen accY tw.nLe
    have htriCube : allTritList (fieldCube t.n t.k t.benchlen accY) :=
      cube_trits t sat hsh accY htriA
    have htriX : allTritList (fieldCube t.n t.k t.benchlen accX) :=
      cube_trits t sat hsh accX fr.triA
    obtain ⟨hmarkLt, hmarkFit⟩ := mark_room t tw
    have hMark : frF.mark + 3 < t.script := by
      rw [hmarkF]
      exact hmarkLt
    have hMarkFit : FitsLen (frF.mark + 4) := by
      rw [hmarkF]
      exact hmarkFit
    by_cases hlast : i = toN
    · have hleft1 : t.cells - done = 1 := by
        rw [hdone, hlast]
        omega
      have hrooms := chord_rooms t tw fr.moves fr.slides fr.ctrl fr.opsCap
        frF.moves frF.slides frF.ctrl frF.opsCap done (t.cells - done)
        hsum hleft hm hs hc ho hmvF hslF (Nat.le_of_eq hctrlF) (Nat.le_of_eq hopsF)
      have hMove : FitsLen (liveMoveRoom t frF.moves baseX (fieldCube t.n t.k t.benchlen accX)) := by
        apply FitsLen.of_le (by simpa [hleft1] using hrooms.1)
        exact live_move_le t frF.moves baseX (fieldCube t.n t.k t.benchlen accX) fr.lenX
          (fieldCube_length t.n t.k t.benchlen accX tw.nLe)
      have hSlide : FitsLen (liveSlideRoom t frF.slides) :=
        live_slide_of_cell t frF.slides (by simpa [hleft1] using hrooms.2.1)
      have hCtrl : FitsLen (liveCtrlRoom t frF.ctrl) :=
        live_ctrl_of_cell t frF.ctrl (by simpa [hleft1] using hrooms.2.2.1)
      have hOps : FitsLen (liveOpsRoom t frF.opsCap) :=
        live_ops_of_cell t frF.opsCap (by simpa [hleft1] using hrooms.2.2.2)
      obtain ⟨b', hdemo, hx0, hy1, hwalk, _hhigh, _hbud, _hpack⟩ :=
        chord_add_live bF t baseX (fieldCube t.n t.k t.benchlen accX) baseY
          (fieldCube t.n t.k t.benchlen accY) accX accY inv (cells[i]'(by omega)) frF
          hOk sat hR hsh hmkF hc2 hy4F hy1F hf4F hf1F hyB hyCube htriY htriCube
          hpreX hpreY hacc hMove hSlide hCtrl hOps hMark hMarkFit hhoF
      have hadd : Ecbs.chord_add_demo bF
          (SudoRt.SEq.beq (Int.ofNat (cells[i]'(by omega))) (2 : Int)) = .ok (true, b') := by
        rw [colour_beq _ hc2]
        exact hdemo
      have hstep := chordStep_open cells i toN (cells[i]'(by omega)) b bL bF b'
        hi hlen rfl hz (by omega) hml hfrob hadd hfiti
      exact ⟨b', _, _, by simpa [hlast] using hstep, by simpa [hlast] using hwalk,
        fun hlt => absurd hlast (by omega), fun _ => ⟨hx0, hy1⟩⟩
    · have hlt : i < toN := by omega
      have hge : 2 ≤ t.cells - done := by
        rw [hdone]
        omega
      let fuel := t.cells - done - 1
      have hfuel : 1 ≤ fuel := by
        have h := hge
        omega
      have hleftEq : fuel + 1 = t.cells - done := by
        have h := hge
        omega
      obtain ⟨b', x3, y3, fr', hdemo, hwalk, _hops, hmv', hctrl', hsl', hst', hho',
          hy1', hy4', hf1', hf4', hmk', hopsB⟩ :=
        tier_cell_chord t bF baseX (fieldCube t.n t.k t.benchlen accX) baseY
          (fieldCube t.n t.k t.benchlen accY) accX accY inv (cells[i]'(by omega)) fuel frF
          fr.moves fr.slides fr.ctrl fr.opsCap done (t.cells - done) tw
          hOk sat hR hsh hmkF hc2 hy4F hy1F hf4F hf1F hyB hyCube htriY htriCube
          hpreX hpreY hacc hfuel hleftEq hsum hleft hm hs hc ho hmvF hslF
          (Nat.le_of_eq hctrlF) (Nat.le_of_eq hopsF) hstF hhoF hMark hMarkFit
      have hadd : Ecbs.chord_add_demo bF
          (SudoRt.SEq.beq (Int.ofNat (cells[i]'(by omega))) (2 : Int)) = .ok (true, b') := by
        rw [colour_beq _ hc2]
        exact hdemo
      have hstep := chordStep_open cells i toN (cells[i]'(by omega)) b bL bF b'
        hi hlen rfl hz (by omega) hml hfrob hadd hfiti
      have hform := walkStep_live_chord t.n t.k t.benchlen baseX baseY accX accY
        (cells[i]'(by omega)) inv hc2 (by rw [specInv_eq]; exact hacc)
      have hy3 : y3 = chordY3 t.n t.k t.benchlen
          (fieldMul t.n t.k t.benchlen
            (fieldSub t.n (if cells[i]'(by omega) = 2 then mirrorTrits baseY else baseY)
              (fieldCube t.n t.k t.benchlen accY)) inv)
          (fieldSub t.n (fieldCube t.n t.k t.benchlen accX)
            (chordX3 t.n t.k t.benchlen
              (fieldMul t.n t.k t.benchlen
                (fieldSub t.n (if cells[i]'(by omega) = 2 then mirrorTrits baseY else baseY)
                  (fieldCube t.n t.k t.benchlen accY)) inv)
              (fieldCube t.n t.k t.benchlen accX)
              (fieldSub t.n baseX (fieldCube t.n t.k t.benchlen accX))))
          (fieldCube t.n t.k t.benchlen accY) := by
        have hsome := Option.some.inj (hwalk.symm.trans hform)
        exact congrArg Prod.snd (congrArg Prod.snd hsome)
      have htriY3 : allTritList y3 := by
        rw [hy3]
        exact chord_y_trits _ _ _ _ _ _
      have hlenY3 : y3.length = t.n := by
        rw [hy3]
        exact chord_y_len _ _ _ _ _ _
      refine ⟨b', x3, y3, by simpa [hlast] using hstep, hwalk, ?_, fun h => absurd h (by omega)⟩
      intro _
      refine ⟨fr', hmk', hy4', hy1', hf4', hf1', hst', hho', ?_, ?_, ?_, hopsB,
        hyB, htriY, hlenY3, htriY3⟩
      · have hcube : cubeCharge t.n t.benchlen = 6 * t.benchlen + 2 * t.n :=
          cube_over _ _ tw.nLe
        have hstepM : fr'.moves ≤ fr.moves + (walkCharge t + (6 * t.benchlen + 2 * t.n)) := by
          calc
            fr'.moves ≤ frF.moves + walkCharge t := hmv'
            _ ≤ fr.moves + cubeCharge t.n t.benchlen + walkCharge t :=
              Nat.add_le_add_right hmvF _
            _ = fr.moves + (walkCharge t + (6 * t.benchlen + 2 * t.n)) := by
              rw [hcube]; omega
        exact next_le done _ _ fr.moves fr'.moves hm hstepM (Nat.le_refl _)
      · have hstepS : fr'.slides ≤ fr.slides + (cellSlideCharge t + slideCharge t.n) := by
          calc
            fr'.slides ≤ frF.slides + cellSlideCharge t := hsl'
            _ ≤ fr.slides + slideCharge t.n + cellSlideCharge t :=
              Nat.add_le_add_right hslF _
            _ = fr.slides + (cellSlideCharge t + slideCharge t.n) := by omega
        exact next_le done _ _ fr.slides fr'.slides hs hstepS (Nat.le_refl _)
      · have hstepC : fr'.ctrl ≤ fr.ctrl + (cellCtrlCharge t + 4) := by
          rw [hctrlF] at hctrl'
          omega
        exact next_le done _ _ fr.ctrl fr'.ctrl hc hstepC (Nat.le_refl _)

/-- What stays true at index `i` of a live walk. At `toN + 1` the homes are the
    point `walkRun` reached; before that, the board is a `LiveAt` frame.
    `live0` and `acc0` are the spec walk this loop continues. -/
def WalkInv (t : Spec.Tier) (baseX baseY : List Nat) (live0 : Bool)
    (acc0 : List Nat × List Nat) (cells : List Nat)
    (toN : Nat) (i : Nat) (st : Ecbs.Board × Bool) : Prop :=
  st.2 = true ∧
  ∃ ax ay,
    walkRun t.n t.k t.benchlen (baseX, baseY) live0 acc0 (cells.take i) =
      some (true, (ax, ay)) ∧
    (i ≤ toN → LiveAt t st.1 baseX baseY ax ay i) ∧
    (toN < i →
      (∀ h : 0 < st.1.sudo_5Board_4home.size, st.1.sudo_5Board_4home[0] = embed ax) ∧
      (∀ h : 1 < st.1.sudo_5Board_4home.size, st.1.sudo_5Board_4home[1] = embed ay))

/-- The live loop from index `start`. `LiveAt` at `start` already has `peakS ≤ 7`
    and `hole ≤ bench`; later cells keep both. A nonzero cell needs the inverse
    of the run it actually reaches. -/
theorem walk_chord_from (t : Spec.Tier) (tw : TierWalk t) (b : Ecbs.Board)
    (baseX baseY accX accY : List Nat) (live0 : Bool) (acc0 : List Nat × List Nat)
    (start : Nat) (cells : List Nat)
    (hOk : BoardOk t) (sat : TierSat t) (hR : 0 < tierR t) (hsh : TierShape t)
    (hAt : LiveAt t b baseX baseY accX accY start)
    (hlen : cells.length = t.cells) (hpos : 0 < t.cells)
    (hstart : start ≤ t.cells - 1)
    (hspec : walkRun t.n t.k t.benchlen (baseX, baseY) live0 acc0 (cells.take start) =
      some (true, (accX, accY)))
    (hc2 : ∀ i (hi : i < cells.length), cells[i] ≤ 2)
    (hready : ∀ i (hi : i < cells.length), start ≤ i → cells[i] ≠ 0 →
      ∀ ax ay, walkRun t.n t.k t.benchlen (baseX, baseY) live0 acc0 (cells.take i) =
        some (true, (ax, ay)) →
        ∃ inv, fieldInv t.n t.k t.benchlen
          (fieldSub t.n baseX (fieldCube t.n t.k t.benchlen ax)) = some inv) :
    ∃ st : Ecbs.Board × Bool,
      WalkInv t baseX baseY live0 acc0 cells (t.cells - 1) t.cells st ∧
      SudoRt.runLoopOn (Int.ofNat start, (b, true))
        (fuelRange (Int.ofNat start) (Int.ofNat (t.cells - 1)))
        (chordStep (embed cells) (Int.ofNat (t.cells - 1))) chordAfter (fun r => pure r) =
        chordAfter (Int.ofNat (t.cells - 1), st) := by
  let toN := t.cells - 1
  have hto : toN + 1 = t.cells := by
    have h := hpos
    omega
  have h0 : WalkInv t baseX baseY live0 acc0 cells toN start (b, true) := by
    refine ⟨rfl, accX, accY, hspec, fun _ => hAt, fun h => absurd h (by omega)⟩
  have hstep : ∀ i s, start ≤ i → i ≤ toN →
      WalkInv t baseX baseY live0 acc0 cells toN i s →
      ∃ s', WalkInv t baseX baseY live0 acc0 cells toN (i + 1) s' ∧
        chordStep (embed cells) (Int.ofNat toN) (Int.ofNat i, s) =
          if i = toN then .ok (SudoRt.Flow.brk (Int.ofNat i, s'))
          else .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), s')) := by
    intro i st hi hito hI
    cases st with
    | mk sb slive =>
    obtain ⟨hlive, ax, ay, hrun, hliveAt, _hhome⟩ := hI
    have hslive : slive = true := hlive
    subst hslive
    have hAt := hliveAt hito
    have hiLen : i < cells.length := by omega
    have hfiti := index_fit t tw i (by omega)
    have hsum : i + (t.cells - i) = t.cells := by omega
    have hleft : 0 < t.cells - i := by omega
    obtain ⟨b', ax', ay', hstep, hwalk, hnext, hlast⟩ :=
      live_cell t tw sb baseX baseY ax ay i cells i toN hOk sat hR hsh hAt
        rfl hto hsum hleft hito (by rw [hlen]; exact hto.symm) (hc2 i hiLen) hfiti
        (fun hnz => hready i hiLen (by omega) hnz ax ay hrun)
    have htake := take_succ_cell cells i hiLen
    have hrun' := walkRun_snoc t.n t.k t.benchlen (baseX, baseY) acc0
      (ax, ay) (ax', ay') (cells.take i) (cells[i]'hiLen) live0 hrun hwalk
    refine ⟨(b', true), ?_, ?_⟩
    · refine ⟨rfl, ax', ay', ?_, ?_, ?_⟩
      · simpa [htake] using hrun'
      · intro hle'
        have hlt : i < toN := by omega
        exact hnext hlt
      · intro hgt
        have hlastI : i = toN := by omega
        exact hlast hlastI
    exact hstep
  obtain ⟨st, hI, heq⟩ := asc_inv (chordStep (embed cells) (Int.ofNat toN)) chordAfter
    (fun r => pure r) (WalkInv t baseX baseY live0 acc0 cells toN) start toN
    hstart hstep (b, true) h0
  refine ⟨st, ?_, ?_⟩
  · simpa [hto] using hI
  · exact heq

/-- The live suffix from a seated first frame. `peakS ≤ 7` and `hole ≤ bench`
    are the initial board's zeros; the walk does not take either bound. -/
theorem walk_chord_live (t : Spec.Tier) (tw : TierWalk t) (b : Ecbs.Board)
    (baseX baseY accX accY : List Nat) (fr : RunFrame b t baseX accX) (cells : List Nat)
    (hOk : BoardOk t) (sat : TierSat t) (hR : 0 < tierR t) (hsh : TierShape t)
    (hs : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict =
      (builtBoard t).sudo_5Board_4cost.sudo_5Costs_11peak_strict)
    (hh : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      (builtBoard t).sudo_5Board_4cost.sudo_5Costs_14max_bench_hole)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hY : fr.y4 = baseY) (hA : fr.y1 = accY)
    (hf4 : fr.flag4 = true) (hf1 : fr.flag1 = true)
    (hm0 : fr.moves = 0) (hs0 : fr.slides = 0) (hc0 : fr.ctrl = 0) (ho0 : fr.opsCap = 0)
    (hyB : baseY.length = t.n) (htriY : allTritList baseY)
    (hyA : accY.length = t.n) (htriA : allTritList accY)
    (hlen : cells.length = t.cells) (hpos : 0 < t.cells)
    (hc2 : ∀ i (hi : i < cells.length), cells[i] ≤ 2)
    (hready : ∀ i (hi : i < cells.length), cells[i] ≠ 0 →
      ∀ ax ay, walkRun t.n t.k t.benchlen (baseX, baseY) true (accX, accY) (cells.take i) =
        some (true, (ax, ay)) →
        ∃ inv, fieldInv t.n t.k t.benchlen
          (fieldSub t.n baseX (fieldCube t.n t.k t.benchlen ax)) = some inv) :
    ∃ st : Ecbs.Board × Bool,
      WalkInv t baseX baseY true (accX, accY) cells (t.cells - 1) t.cells st ∧
      SudoRt.runLoopOn (Int.ofNat 0, (b, true))
        (fuelRange (Int.ofNat 0) (Int.ofNat (t.cells - 1)))
        (chordStep (embed cells) (Int.ofNat (t.cells - 1))) chordAfter (fun r => pure r) =
        chordAfter (Int.ofNat (t.cells - 1), st) := by
  have hAt := live_at_initial t b baseX baseY accX accY fr hs hh hmk hY hA hf4 hf1
    hm0 hs0 hc0 ho0 hyB htriY hyA htriA
  exact walk_chord_from t tw b baseX baseY accX accY true (accX, accY) 0 cells
    hOk sat hR hsh hAt hlen hpos (Nat.zero_le _) (by simp [walkRun]) hc2
    (fun i hi _ hnz ax ay hrun => hready i hi hnz ax ay hrun)

end EcbsLink2.Link2
