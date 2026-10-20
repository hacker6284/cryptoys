/-
  The cofactor tail `[2, 1, 2]`. The board `white_down_spanAt` leaves is still
  marker `-1`, so the first of those cells is `seat_out` and then the chord.
  `suffix_walk` runs the last two cells of `cofactorCells`. A successful
  `cofactorWalk` is that loop. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.CopySeat
import EcbsLink2.Link2.ChordFrame
import EcbsLink2.Link2.WalkLive
import EcbsLink2.Link2.SuffixInd
import EcbsLink2.Link2.WalkRunInv
import EcbsLink2.Link2.WalkSeat
import EcbsLink2.Link2.WalkBound
import EcbsLink2.Link2.CofactorRoom
import EcbsLink2.Link2.Loop

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open Ecbs
open EcbsLink2.Spec

private theorem two_n_le_walk (t : Spec.Tier) : 2 * t.n ≤ walkCharge t := by
  unfold walkCharge
  omega

private theorem over_le_walk (t : Spec.Tier)
    (hov : (6 * t.benchlen + 2 * t.n) * cofactorSpan ≤ walkCharge t) :
    6 * t.benchlen + 2 * t.n ≤ walkCharge t := by
  have hsp : cofactorSpan = 4 := rfl
  rw [hsp, Nat.mul_comm] at hov
  exact Nat.le_trans (Nat.le_mul_of_pos_left _ (by decide : 0 < 4)) hov

/-- The first cofactor cell copies the root and turns the walk live. -/
theorem cofactor_open_run (n k bench : Nat) (x y : List Nat) :
    walkRun n k bench (x, y) false (whiteHole0 n, whiteHole0 n) (cofactorCells.take 1) =
      some (true, (x, y)) := by
  simp [cofactorCells, walkRun, walkStep]

private theorem cofactor_len : cofactorCells.length = 4 := by
  simp [cofactorCells]

private theorem cofactor_le2 (i : Nat) (hi : i < cofactorCells.length) :
    cofactorCells[i] ≤ 2 := by
  have hi4 : i < 4 := by simpa [cofactor_len] using hi
  match i with
  | 0 => simp [cofactorCells]
  | 1 => simp [cofactorCells]
  | 2 => simp [cofactorCells]
  | 3 => simp [cofactorCells]
  | n + 4 => omega

private theorem cofactor_colour (i : Nat) (hi : i < cofactorCells.length)
    (hnz : cofactorCells[i] ≠ 0) : cofactorCells[i] = 1 ∨ cofactorCells[i] = 2 := by
  have hle := cofactor_le2 i hi
  omega

private theorem cell_one : cofactorCells[1]'(by simp [cofactorCells]) = 2 := by
  simp [cofactorCells]

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

private theorem ctrl_seat (c : Nat) (h : 0 < c) : c - 1 + 4 = c + 3 := by
  omega

private theorem fit_two : FitsLen (1 + 1) := by
  unfold FitsLen i64MaxNat
  decide

private theorem fit_five : FitsLen (1 + 4) := by
  unfold FitsLen i64MaxNat
  decide

private theorem red_beq :
    SudoRt.SEq.beq (Int.ofNat 2) (2 : Int) = true := by
  decide

/-- Three chord charges on the copied counters, read off the five-charge room. -/
private theorem seat_move_room (t : Spec.Tier) (mv0 mv : Nat)
    (hmv : mv ≤ mv0 + 2 * t.n)
    (hroom : FitsLen (mv0 + (cofactorSpan + 1) * walkCharge t)) :
    FitsLen (mv + walkCharge t * 3) := by
  have hsp : cofactorSpan = 4 := rfl
  have h2 := two_n_le_walk t
  apply FitsLen.of_le hroom
  rw [hsp]
  have h3 : walkCharge t * 3 + walkCharge t = walkCharge t * 4 := by omega
  have h5 : walkCharge t * 4 ≤ 5 * walkCharge t := by
    have h4 : walkCharge t * 4 ≤ walkCharge t * 5 := Nat.mul_le_mul_left _ (by decide)
    simpa [Nat.mul_comm] using h4
  omega

private theorem seat_slide_room (t : Spec.Tier) (sl0 sl : Nat)
    (hsl : sl ≤ sl0)
    (hroom : FitsLen (sl0 + (cofactorSpan + 1) * cellSlideCharge t)) :
    FitsLen (sl + cellSlideCharge t * 3) := by
  have hsp : cofactorSpan = 4 := rfl
  apply FitsLen.of_le hroom
  rw [hsp]
  have h3 : cellSlideCharge t * 3 ≤ 5 * cellSlideCharge t := by
    have h : cellSlideCharge t * 3 ≤ cellSlideCharge t * 5 :=
      Nat.mul_le_mul_left _ (by decide)
    simpa [Nat.mul_comm] using h
  omega

private theorem seat_ctrl_room (t : Spec.Tier) (ct0 c : Nat)
    (hc : c ≤ ct0)
    (hroom : FitsLen (ct0 + (cofactorSpan + 1) * cellCtrlCharge t)) :
    FitsLen (c + cellCtrlCharge t * 3) := by
  have hsp : cofactorSpan = 4 := rfl
  apply FitsLen.of_le hroom
  rw [hsp]
  have h3 : cellCtrlCharge t * 3 ≤ 5 * cellCtrlCharge t := by
    have h : cellCtrlCharge t * 3 ≤ cellCtrlCharge t * 5 :=
      Nat.mul_le_mul_left _ (by decide)
    simpa [Nat.mul_comm] using h
  omega

private theorem seat_ops_room (t : Spec.Tier) (op0 o : Nat)
    (ho : o ≤ op0)
    (hroom : FitsLen (op0 + (cofactorSpan + 1) * cellOpsCharge t)) :
    FitsLen (o + cellOpsCharge t * 3) := by
  have hsp : cofactorSpan = 4 := rfl
  apply FitsLen.of_le hroom
  rw [hsp]
  have h3 : cellOpsCharge t * 3 ≤ 5 * cellOpsCharge t := by
    have h : cellOpsCharge t * 3 ≤ cellOpsCharge t * 5 :=
      Nat.mul_le_mul_left _ (by decide)
    simpa [Nat.mul_comm] using h
  omega

/-- The chord of this cell, plus the two cells still after it. -/
private theorem chord_move_room (t : Spec.Tier) (mv0 mv moves : Nat)
    (hmv : mv ≤ mv0 + 2 * t.n)
    (hmoves : moves ≤ mv + cubeCharge t.n t.benchlen)
    (hn : t.n ≤ t.benchlen)
    (hov : (6 * t.benchlen + 2 * t.n) * cofactorSpan ≤ walkCharge t)
    (hroom : FitsLen (mv0 + (cofactorSpan + 1) * walkCharge t)) :
    FitsLen (moves + (2 + 1) * cellMoveCharge t) := by
  have hsp : cofactorSpan = 4 := rfl
  have hcube : cubeCharge t.n t.benchlen = 6 * t.benchlen + 2 * t.n := cube_over _ _ hn
  have hcm : cellMoveCharge t ≤ walkCharge t := cellMove_le_walk t
  have h2 := two_n_le_walk t
  have hover := over_le_walk t hov
  have h3 : 3 * cellMoveCharge t ≤ 3 * walkCharge t := Nat.mul_le_mul_left 3 hcm
  apply FitsLen.of_le hroom
  rw [hsp]
  have hfive : 5 * walkCharge t = (4 + 1) * walkCharge t := by omega
  omega

private theorem chord_slide_room (t : Spec.Tier) (sl0 sl slides : Nat)
    (hsl0 : sl ≤ sl0)
    (hsl : slides ≤ sl + slideCharge t.n)
    (hov : 4 * t.n * cofactorSpan ≤ cellSlideCharge t)
    (hroom : FitsLen (sl0 + (cofactorSpan + 1) * cellSlideCharge t)) :
    FitsLen (slides + (2 + 1) * cellSlideCharge t) := by
  have hsp : cofactorSpan = 4 := rfl
  have hslide : slideCharge t.n = 4 * t.n := slide_over_eq t.n
  rw [hsp, Nat.mul_comm] at hov
  have h4 : 4 * t.n ≤ cellSlideCharge t :=
    Nat.le_trans (Nat.le_mul_of_pos_left _ (by decide : 0 < 4)) hov
  apply FitsLen.of_le hroom
  rw [hsp]
  omega

private theorem chord_ctrl_room (t : Spec.Tier) (ct0 c ctrl : Nat)
    (hc0 : c ≤ ct0) (hpos : 0 < c)
    (hctrl : ctrl = c - 1 + 4)
    (hov : 4 * cofactorSpan ≤ cellCtrlCharge t)
    (hroom : FitsLen (ct0 + (cofactorSpan + 1) * cellCtrlCharge t)) :
    FitsLen (ctrl + (2 + 1) * cellCtrlCharge t) := by
  have hsp : cofactorSpan = 4 := rfl
  have heq : ctrl = c + 3 := by rw [hctrl, ctrl_seat c hpos]
  have h16 : 16 ≤ cellCtrlCharge t := by simpa [hsp] using hov
  apply FitsLen.of_le hroom
  rw [heq, hsp]
  omega

private theorem chord_ops_room (t : Spec.Tier) (op0 o ops : Nat)
    (ho0 : o ≤ op0) (hops : ops = o + 3)
    (hov : 2 * cofactorSpan + 2 ≤ cellOpsCharge t)
    (hroom : FitsLen (op0 + (cofactorSpan + 1) * cellOpsCharge t)) :
    FitsLen (ops + (2 + 1) * cellOpsCharge t) := by
  have hsp : cofactorSpan = 4 := rfl
  have h10 : 10 ≤ cellOpsCharge t := by simpa [hsp] using hov
  apply FitsLen.of_le hroom
  rw [hops, hsp]
  omega

private theorem span_moves (t : Spec.Tier) (mv0 mv moves moves' : Nat)
    (hmv : mv ≤ mv0 + 2 * t.n)
    (hmoves : moves ≤ mv + cubeCharge t.n t.benchlen)
    (hnext : moves' ≤ moves + walkCharge t)
    (hn : t.n ≤ t.benchlen)
    (hov : (6 * t.benchlen + 2 * t.n) * cofactorSpan ≤ walkCharge t) :
    moves' ≤ mv0 + 2 * (walkCharge t + (6 * t.benchlen + 2 * t.n)) := by
  have hcube : cubeCharge t.n t.benchlen = 6 * t.benchlen + 2 * t.n := cube_over _ _ hn
  have h2 := two_n_le_walk t
  have hover := over_le_walk t hov
  omega

private theorem span_slides (t : Spec.Tier) (sl0 sl slides slides' : Nat)
    (hsl0 : sl ≤ sl0)
    (hsl : slides ≤ sl + slideCharge t.n)
    (hnext : slides' ≤ slides + cellSlideCharge t) :
    slides' ≤ sl0 + 2 * (cellSlideCharge t + 4 * t.n) := by
  have hslide : slideCharge t.n = 4 * t.n := slide_over_eq t.n
  omega

private theorem cube_trits (t : Spec.Tier) (sat : TierSat t) (hsh : TierShape t)
    (xs : List Nat) (hxs : allTritList xs) :
    allTritList (fieldCube t.n t.k t.benchlen xs) := by
  apply fieldCube_trits t.n t.k t.benchlen xs hxs
  · have h := sat.cube_span
    omega
  · exact hsh.k_le

private theorem chord_y_trits (n k bench : Nat) (slope dx y : List Nat) :
    allTritList (chordY3 n k bench slope dx y) := by
  simpa [chordY3, fieldSub] using
    fieldAdd_span_trits n (fieldMul n k bench slope dx) (mirrorTrits y)

private theorem chord_y_len (n k bench : Nat) (slope dx y : List Nat) :
    (chordY3 n k bench slope dx y).length = n := by
  simpa [chordY3] using fieldSub_length n (fieldMul n k bench slope dx) y

private theorem cofactor_red_step (b0 b bF bA : Board)
    (hml : marker_lift b0 = .ok b)
    (hfrob : frobenius_affine b = .ok bF)
    (hadd : chord_add_demo bF (SudoRt.SEq.beq (Int.ofNat 2) (2 : Int)) = .ok (true, bA)) :
    chordStep (embed cofactorCells) (Int.ofNat 3) (Int.ofNat 1, (b0, true)) =
      .ok (SudoRt.Flow.cont (Int.ofNat 2, (bA, true))) := by
  have hlen : cofactorCells.length = 3 + 1 := cofactor_len
  have hc : cofactorCells[1]'(by omega) = 2 := cell_one
  have hstep := chordStep_open cofactorCells 1 3 2 b0 b bF bA
    (by decide) hlen hc (by decide) (by decide) hml hfrob hadd fit_two
  simpa using hstep

private theorem cont_from (k toN : Nat) (b b' : Board) (cells : List Nat)
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

private theorem point_eq (ax ay px py : List Nat)
    (h : (true, (ax, ay)) = (true, (px, py))) : ax = px ∧ ay = py := by
  cases h
  exact ⟨rfl, rfl⟩

/-- Seat the copied root, run the red cell, then `suffix_walk` on `[1, 2]`.
    The list stays `cofactorCells`, so the emitted step reads index 1. -/
theorem cofactor_tail (t : Spec.Tier) (b2 : Board) (x y px py : List Nat)
    (mv pk mv0 sl0 ct0 op0 : Nat)
    (out : OutLay t b2 x y y mv pk)
    (hOk : BoardOk t) (sat : TierSat t) (hR : 0 < tierR t) (hsh : TierShape t)
    (hx : x.length = t.n) (hy : y.length = t.n)
    (htriX : allTritList x) (htriY : allTritList y)
    (hn : t.n ≤ t.benchlen) (hscript : 4 < t.script)
    (hmv : mv ≤ mv0 + 2 * t.n)
    (hsl0 : out.sl0 ≤ sl0) (hct0 : out.ctrl0 ≤ ct0) (hop0 : out.ops0 ≤ op0)
    (hstrict : out.strict0 ≤ 7) (hhole : out.hole0 ≤ t.benchlen)
    (hctrlPos : 0 < out.ctrl0)
    (hRoomM : FitsLen (mv0 + (cofactorSpan + 1) * walkCharge t))
    (hRoomS : FitsLen (sl0 + (cofactorSpan + 1) * cellSlideCharge t))
    (hRoomC : FitsLen (ct0 + (cofactorSpan + 1) * cellCtrlCharge t))
    (hRoomO : FitsLen (op0 + (cofactorSpan + 1) * cellOpsCharge t))
    (hmoveOver : (6 * t.benchlen + 2 * t.n) * cofactorSpan ≤ walkCharge t)
    (hslideOver : 4 * t.n * cofactorSpan ≤ cellSlideCharge t)
    (hctrlOver : 4 * cofactorSpan ≤ cellCtrlCharge t)
    (hopsOver : 2 * cofactorSpan + 2 ≤ cellOpsCharge t)
    (hgo : walkRun t.n t.k t.benchlen (x, y) false (whiteHole0 t.n, whiteHole0 t.n)
      cofactorCells = some (true, (px, py))) :
    ∃ b',
      SudoRt.runLoopOn (Int.ofNat 1, (b2, true))
          (fuelRange (Int.ofNat 1) (Int.ofNat 3))
          (chordStep (embed cofactorCells) (Int.ofNat 3)) chordAfter (fun r => pure r) =
        .ok ((true, true), b') ∧
      (∀ h : 0 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[0] = embed px) ∧
      (∀ h : 1 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[1] = embed py) := by
  have hpre := cofactor_open_run t.n t.k t.benchlen x y
  have hi1 : 1 < cofactorCells.length := by simp [cofactorCells]
  have hc1 : cofactorCells[1]'hi1 = 1 ∨ cofactorCells[1]'hi1 = 2 :=
    Or.inr cell_one
  obtain ⟨inv, hinv⟩ :=
    walkRun_live_inv t.n t.k t.benchlen (x, y) (whiteHole0 t.n, whiteHole0 t.n) (x, y)
      cofactorCells 1 (true, (px, py)) hi1 hc1 hpre hgo
  have hM := seat_move_room t mv0 mv hmv hRoomM
  have hS := seat_slide_room t sl0 out.sl0 hsl0 hRoomS
  have hC := seat_ctrl_room t ct0 out.ctrl0 hct0 hRoomC
  have hO := seat_ops_room t op0 out.ops0 hop0 hRoomO
  obtain ⟨bF, fr, hml, hfrob, hmk, hy1, hy4, hmark, hctrl, hst, hho, hmvF, hslF, hopsF,
      hf1, hf4⟩ :=
    seat_out t b2 x y y mv pk out 3 hOk sat hsh hx hy htriX htriY
      (by decide) hctrlPos hstrict hhole hM hS hO hC
  have hMove := chord_move_room t mv0 mv fr.moves hmv hmvF hn hmoveOver hRoomM
  have hSlide := chord_slide_room t sl0 out.sl0 fr.slides hsl0 hslF hslideOver hRoomS
  have hCtrl := chord_ctrl_room t ct0 out.ctrl0 fr.ctrl hct0 hctrlPos hctrl hctrlOver hRoomC
  have hOps := chord_ops_room t op0 out.ops0 fr.opsCap hop0 hopsF hopsOver hRoomO
  have htriCube : allTritList (fieldCube t.n t.k t.benchlen y) :=
    cube_trits t sat hsh y htriY
  have hlenCube : (fieldCube t.n t.k t.benchlen y).length = t.n :=
    fieldCube_length t.n t.k t.benchlen y hn
  have hMark : fr.mark + 3 < t.script := by
    rw [hmark]
    omega
  have hMarkF : FitsLen (fr.mark + 4) := by
    rw [hmark]
    exact fit_five
  obtain ⟨b', x3, y3, hdemo, hx3, hy3, hwalk, fr', hops', hmv', hctrl', hsl',
      hst', hho', hy1', hy4', hf1', hf4', hmk'⟩ :=
    chord_add_live_frame bF t x (fieldCube t.n t.k t.benchlen x) y
      (fieldCube t.n t.k t.benchlen y) x y inv 2 2 fr
      hOk sat hR hsh hmk (Or.inr rfl) hy4 hy1 hf4 hf1 hy hlenCube htriY htriCube
      rfl rfl hinv (by decide) hMove hSlide hCtrl hOps hst hho hMark hMarkF
  have hadd : chord_add_demo bF (SudoRt.SEq.beq (Int.ofNat 2) (2 : Int)) =
      .ok (true, b') := by
    rw [red_beq]
    simpa using hdemo
  have hstep := cofactor_red_step b2 b2 bF b' hml hfrob hadd
  have htriY3 : allTritList y3 := by
    rw [hy3]
    exact chord_y_trits _ _ _ _ _ _
  have hlenY3 : y3.length = t.n := by
    rw [hy3]
    exact chord_y_len _ _ _ _ _ _
  have hAt : SpanFrame t b' x y x3 y3 2 mv0 sl0 ct0 op0 :=
    ⟨fr', hmk', hy4', hy1', hf4', hf1', hst', hho',
      span_moves t mv0 mv fr.moves fr'.moves hmv hmvF hmv' hn hmoveOver,
      span_slides t sl0 out.sl0 fr.slides fr'.slides hsl0 hslF hsl',
      by
        have heq : fr.ctrl = out.ctrl0 + 3 := by rw [hctrl, ctrl_seat _ hctrlPos]
        omega,
      by
        rw [hops', hopsF]
        omega,
      hy, htriY, hlenY3, htriY3⟩
  have hi1b : 1 < cofactorCells.length := by simp [cofactorCells]
  have htake := take_succ_cell cofactorCells 1 hi1b
  have hrun2 := walkRun_snoc t.n t.k t.benchlen (x, y) (whiteHole0 t.n, whiteHole0 t.n)
    (x, y) (x3, y3) (cofactorCells.take 1) 2 false hpre
    (by simpa [cell_one] using hwalk)
  have hspec : walkRun t.n t.k t.benchlen (x, y) false (whiteHole0 t.n, whiteHole0 t.n)
      (cofactorCells.take 2) = some (true, (x3, y3)) := by
    simpa [htake, cell_one] using hrun2
  have hjoin := cont_from 1 3 b2 b' cofactorCells (by decide) hstep
  clear hM hS hC hO hMove hSlide hCtrl hOps hinv hdemo hx3 hy3 hwalk
  obtain ⟨st, hI, heq⟩ :=
    suffix_walk t b' x y x3 y3 false (whiteHole0 t.n, whiteHole0 t.n) cofactorCells
      cofactorSpan 2 mv0 sl0 ct0 op0 hOk sat hR hsh hAt hn hmoveOver hslideOver
      hctrlOver hopsOver hRoomM hRoomS hRoomC hRoomO hscript cofactor_len
      (by decide) (by decide) hspec cofactor_le2
      (fun i hi _ hnz ax ay hrun =>
        walkRun_live_inv t.n t.k t.benchlen (x, y) (whiteHole0 t.n, whiteHole0 t.n)
          (ax, ay) cofactorCells i (true, (px, py)) hi (cofactor_colour i hi hnz) hrun hgo)
  obtain ⟨hlive, ax, ay, hrun, _hspan, hhome⟩ := hI
  have hto : cofactorSpan - 1 = 3 := by simp [cofactorSpan]
  obtain ⟨hxF, hyF, ⟨m, c, hm, hc, hfit⟩⟩ := hhome (by simp [cofactorSpan])
  have htakeF : cofactorCells.take cofactorSpan = cofactorCells := by
    simp [cofactorSpan, cofactorCells]
  have hrunP : walkRun t.n t.k t.benchlen (x, y) false (whiteHole0 t.n, whiteHole0 t.n)
      cofactorCells = some (true, (ax, ay)) := by
    simpa [htakeF] using hrun
  have hp := point_eq ax ay px py (Option.some.inj (hrunP.symm.trans hgo))
  have hslive : st.2 = true := hlive
  cases st with
  | mk sb slive =>
    cases hslive
    have hch := chord_after_nat sb (Int.ofNat 3) true m c hm hc hfit
    have hmid :
        SudoRt.runLoopOn (Int.ofNat 2, (b', true))
            (fuelRange (Int.ofNat 2) (Int.ofNat 3))
            (chordStep (embed cofactorCells) (Int.ofNat 3)) chordAfter (fun r => pure r) =
          chordAfter (Int.ofNat 3, (sb, true)) := by
      simpa [hto] using heq
    refine ⟨_, (hjoin.trans hmid).trans hch, ?_, ?_⟩
    · intro h
      simpa [hp.1] using hxF (by simpa using h)
    · intro h
      simpa [hp.2] using hyF (by simpa using h)

end EcbsLink2.Link2
