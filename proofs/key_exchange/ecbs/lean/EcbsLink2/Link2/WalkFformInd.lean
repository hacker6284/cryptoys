/-
  The live suffix of `walk_fform`, in the shape of `walk_chord_from`.
  The spec point is `walkStep`: a zero cell cubes, and a white or red cell
  is `chordAdd` once the run inverts. The board frame is `FformAt`.
  `ProjOn` is SPEC.md §3 R7: `X = px·Z` and `Y = py·Z`, with `Z` not the
  zero home. `finish` is what clears the denominator.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.WalkFform
import EcbsLink2.Link2.WalkCharge
import EcbsLink2.Link2.WalkSeat
import EcbsLink2.Link2.WalkRunStep

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- Where the projective triple sits. `walk_fform` leaves `Y` on the bench
    after an addition, and `Z` on the bench after a cube. SPEC.md §3 R7. -/
inductive ProjLay
  | homes
  | yBench
  | zBench

/-- The projective triple SPEC.md §3 R7 writes, before `finish` inverts `Z`.
    `X = px·Z` and `Y = py·Z`, and `Z` is not the zero home. Home 0 holds `X`.
    `homes` keeps `Y` and `Z` in homes 1 and 2. `yBench` holds `Y` on the bench,
    aimed at home 1, with `Z` still in home 2. `zBench` holds `Z` on the bench,
    aimed at home 2, with `Y` still in home 1. -/
def ProjOn (t : Spec.Tier) (b : Ecbs.Board) (px py : List Nat) : Prop :=
  ∃ xP yP zP, ∃ lay : ProjLay,
    xP.length = t.n ∧ yP.length = t.n ∧ zP.length = t.n ∧
    allTritList xP ∧ allTritList yP ∧ allTritList zP ∧
    xP = fieldMul t.n t.k t.benchlen px zP ∧
    yP = fieldMul t.n t.k t.benchlen py zP ∧
    zP ≠ List.replicate t.n 0 ∧
    (∀ h : 0 < b.sudo_5Board_4home.size, b.sudo_5Board_4home[0] = embed xP) ∧
    (match lay with
      | .homes =>
          b.sudo_5Board_8bench_on = false ∧
          (∀ h : 1 < b.sudo_5Board_4home.size, b.sudo_5Board_4home[1] = embed yP) ∧
          (∀ h : 2 < b.sudo_5Board_4home.size, b.sudo_5Board_4home[2] = embed zP) ∧
          (∀ h : 1 < b.sudo_5Board_4held.size, b.sudo_5Board_4held[1] = true) ∧
          (∀ h : 2 < b.sudo_5Board_4held.size, b.sudo_5Board_4held[2] = true)
      | .yBench =>
          b.sudo_5Board_8bench_on = true ∧
          b.sudo_5Board_8bench_to = (1 : Int) ∧
          (∃ lane, b.sudo_5Board_5bench = embed lane ∧ t.n ≤ lane.length ∧
            lane.take t.n = yP ∧
            ∀ i, t.n ≤ i → ∀ hi : i < lane.length, lane[i] = 0) ∧
          (∀ h : 1 < b.sudo_5Board_4held.size, b.sudo_5Board_4held[1] = false) ∧
          (∀ h : 2 < b.sudo_5Board_4home.size, b.sudo_5Board_4home[2] = embed zP) ∧
          (∀ h : 2 < b.sudo_5Board_4held.size, b.sudo_5Board_4held[2] = true)
      | .zBench =>
          b.sudo_5Board_8bench_on = true ∧
          b.sudo_5Board_8bench_to = (2 : Int) ∧
          (∃ lane, b.sudo_5Board_5bench = embed lane ∧ t.n ≤ lane.length ∧
            lane.take t.n = zP ∧
            ∀ i, t.n ≤ i → ∀ hi : i < lane.length, lane[i] = 0) ∧
          (∀ h : 1 < b.sudo_5Board_4home.size, b.sudo_5Board_4home[1] = embed yP) ∧
          (∀ h : 1 < b.sudo_5Board_4held.size, b.sudo_5Board_4held[1] = true) ∧
          (∀ h : 2 < b.sudo_5Board_4held.size, b.sudo_5Board_4held[2] = false)) ∧
    ∃ wInv, wInv.length = t.n ∧ allTritList wInv ∧
      fieldMul t.n t.k t.benchlen zP wInv = onePeg t.n

/-- One live cell still to run leaves `FitsLen (c0 + 13)`, which is what
    `comb_u2z` and the tail read off the incoming counter. -/
theorem mul_slack_cell (c0 cells done : Nat)
    (h : FitsLen (c0 + 13 * (cells - done))) (hpos : done < cells) :
    FitsLen (c0 + 13) := by
  refine FitsLen.of_le h ?_
  have hone : 1 ≤ cells - done := by omega
  have hmul : 13 * 1 ≤ 13 * (cells - done) := Nat.mul_le_mul_left 13 hone
  omega

/-- After a cell spends at most 13 multiplies, the same room covers the
    cells that remain. -/
theorem mul_slack_next (c0 k cells done : Nat)
    (h : FitsLen (c0 + 13 * (cells - done))) (hk : k ≤ 13) (hpos : done < cells) :
    FitsLen (c0 + k + 13 * (cells - (done + 1))) := by
  refine FitsLen.of_le h ?_
  have hsplit : cells - done = (cells - (done + 1)) + 1 := by omega
  omega

/-- One cell still to run leaves `FitsLen (c1 + 3)`, the three cubes. -/
theorem cube_slack_cell (c1 cells done : Nat)
    (h : FitsLen (c1 + 3 * (cells - done))) (hpos : done < cells) :
    FitsLen (c1 + 3) := by
  refine FitsLen.of_le h ?_
  have hone : 1 ≤ cells - done := by omega
  have hmul : 3 * 1 ≤ 3 * (cells - done) := Nat.mul_le_mul_left 3 hone
  omega

/-- A cell spends three cubes. The room that remains covers the cells after it. -/
theorem cube_slack_next (c1 cells done : Nat)
    (h : FitsLen (c1 + 3 * (cells - done))) (hpos : done < cells) :
    FitsLen (c1 + 3 + 3 * (cells - (done + 1))) := by
  refine FitsLen.of_le h ?_
  have hsplit : cells - done = (cells - (done + 1)) + 1 := by omega
  omega

/-- One cell spends `spend`. The room that remains is still inside an i64. -/
theorem room_after_spend (moves spend moves' rest : Nat)
    (h : FitsLen (moves + spend + rest)) (hle : moves' ≤ moves + spend) :
    FitsLen (moves' + rest) :=
  FitsLen.of_le h (by omega)

/-- The four shipped tiers leave room for the bottom cube's marker. -/
theorem demo_script_cube : 2 < Spec.demo.script := by decide
theorem toy_script_cube : 2 < Spec.toy.script := by decide
theorem hobby_script_cube : 2 < Spec.hobby.script := by decide
theorem serious_script_cube : 2 < Spec.serious.script := by decide

/-- A live F-form board, `done` cells already run. The charges are `LiveAt`'s.
    `px` and `py` are the affine point `walkRun` has reached. `ProjOn` is the
    projective triple of that point. `c1` is ops slot 1, the cube counter.
    One cell cubes three times, and the field keeps that slack for every cell
    still to run, `3 * (t.cells - done)`. `c0` is ops slot 0, the multiply counter.
    One cell asks for 13 of multiply slack: `comb_u2z` asks for 8, and the
    tail asks for 6 more after the seven multiplies already counted at the
    sum. The field keeps that slack for every cell still to run,
    `13 * (t.cells - done)`. -/
def FformAt (t : Spec.Tier) (b : Ecbs.Board)
    (baseX baseY px py : List Nat) (done : Nat) : Prop :=
  b.sudo_5Board_9marker_on = true ∧
  b.sudo_5Board_1t = embTier t ∧
  px.length = t.n ∧ py.length = t.n ∧
  allTritList px ∧ allTritList py ∧
  baseX.length = t.n ∧ baseY.length = t.n ∧
  allTritList baseX ∧ allTritList baseY ∧
  7 ≤ b.sudo_5Board_4home.size ∧
  7 ≤ b.sudo_5Board_4held.size ∧
  (∀ h : 3 < b.sudo_5Board_4home.size, b.sudo_5Board_4home[3] = embed baseX) ∧
  (∀ h : 4 < b.sudo_5Board_4home.size, b.sudo_5Board_4home[4] = embed baseY) ∧
  (∀ h : 3 < b.sudo_5Board_4held.size, b.sudo_5Board_4held[3] = true) ∧
  (∀ h : 4 < b.sudo_5Board_4held.size, b.sudo_5Board_4held[4] = true) ∧
  (∀ h : 0 < b.sudo_5Board_4held.size, b.sudo_5Board_4held[0] = true) ∧
  2 < t.script ∧
  b.sudo_5Board_4home.size = 8 ∧
  b.sudo_5Board_4held.size = 8 ∧
  ProjOn t b px py ∧
  ∃ (moves slides ctrl mark mx pk peakS hole c1 c0 : Nat),
    b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves ∧
    b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides ∧
    b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl ∧
    b.sudo_5Board_6marker = Int.ofNat mark ∧
    b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx ∧
    b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk ∧
    b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat peakS ∧
    b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole ∧
    1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size ∧
    b.sudo_5Board_4cost.sudo_5Costs_3ops[1]? = some (c1 : Int) ∧
    b.sudo_5Board_4cost.sudo_5Costs_3ops[0]? = some (Int.ofNat c0) ∧
    FitsLen (ctrl + 6) ∧
    FitsLen (c1 + 3 * (t.cells - done)) ∧
    FitsLen (c0 + 13 * (t.cells - done)) ∧
    FitsLen (moves + 2 * t.n + cubeCharge t.n t.benchlen + 2 * t.n +
      3 * (t.benchlen - t.n)) ∧
    FitsLen (slides + 2 * t.n + slideCharge t.n) ∧
    moves ≤ done * (walkCharge t + (6 * t.benchlen + 2 * t.n)) ∧
    slides ≤ done * (cellSlideCharge t + slideCharge t.n) ∧
    ctrl ≤ done * (cellCtrlCharge t + 4) ∧
    b.sudo_5Board_4held[5]? = some false ∧
    b.sudo_5Board_4held[6]? = some false ∧
    b.sudo_5Board_4cost.sudo_5Costs_3ops.size = 5

/-- Gap and spare are empty, and the ops array is the length `new_board` emits. -/
theorem fform_open (t : Spec.Tier) (b : Ecbs.Board)
    (baseX baseY px py : List Nat) (done : Nat)
    (hAt : FformAt t b baseX baseY px py done) :
    b.sudo_5Board_4held[5]? = some false ∧
      b.sudo_5Board_4held[6]? = some false ∧
      b.sudo_5Board_4cost.sudo_5Costs_3ops.size = 5 := by
  rcases hAt with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hrest⟩
  rcases hrest with ⟨_, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, h5, h6, hopsN⟩
  exact ⟨h5, h6, hopsN⟩

/-- What stays true at index `i`. At `toN + 1` the frame is the point the
    whole suffix reached. -/
def FformInv (t : Spec.Tier) (baseX baseY : List Nat) (live0 : Bool)
    (acc0 : List Nat × List Nat) (cells : List Nat)
    (i : Nat) (st : Ecbs.Board × Bool) : Prop :=
  st.2 = true ∧
  ∃ px py,
    walkRun t.n t.k t.benchlen (baseX, baseY) live0 acc0 (cells.take i) =
      some (true, (px, py)) ∧
    FformAt t st.1 baseX baseY px py i

/-- A live white or red cell whose run inverts is `chordAdd` of the cubed
    accumulator and the base point. SPEC.md §3 R7 lines 156–157 and R8. -/
theorem walkStep_chord (n k bench : Nat) (base acc : List Nat × List Nat)
    (c : Nat) (inv : List Nat) (hc : c = 1 ∨ c = 2)
    (hinv : fieldInv n k bench (fieldSub n base.1 (fieldCube n k bench acc.1)) =
      some inv) :
    ∃ p,
      walkStep n k bench base true acc c = some (true, p) ∧
      chordAdd n k bench (pointCube n k bench acc)
        (base.1, if c = 2 then mirrorTrits base.2 else base.2) = some p := by
  have h0 : c ≠ 0 := by rcases hc with rfl | rfl <;> decide
  have hbad : ¬ (c ≠ 1 ∧ c ≠ 2) := by rcases hc with rfl | rfl <;> decide
  unfold walkStep
  simp only [ite_true]
  rw [if_neg h0, if_neg hbad]
  dsimp only [pointCube, chordAdd]
  simp only [specInv_eq, hinv, Prod.fst, Prod.snd]
  exact ⟨_, rfl, rfl⟩

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

/-- The live loop from index `start`, on a spec walk that returns a point.
    `hfull` is that success. `hframe` is the one cell: `fformStep` lands on a
    board whose `FformAt` is the point `walkStep` just produced. -/
theorem walk_fform_from (t : Spec.Tier) (b : Ecbs.Board)
    (baseX baseY px py pxF pyF : List Nat) (live0 : Bool) (acc0 : List Nat × List Nat)
    (start : Nat) (cells : List Nat)
    (hAt : FformAt t b baseX baseY px py start)
    (hlen : cells.length = t.cells) (hpos : 0 < t.cells)
    (hstart : start ≤ t.cells - 1)
    (hspec : walkRun t.n t.k t.benchlen (baseX, baseY) live0 acc0 (cells.take start) =
      some (true, (px, py)))
    (hfull : walkRun t.n t.k t.benchlen (baseX, baseY) live0 acc0 cells =
      some (true, (pxF, pyF)))
    (hframe : ∀ i (sb : Ecbs.Board) (ax ay ax' ay' : List Nat)
      (hi0 : start ≤ i) (hi1 : i ≤ t.cells - 1),
      FformAt t sb baseX baseY ax ay i →
      walkStep t.n t.k t.benchlen (baseX, baseY) true (ax, ay)
        (cells[i]'(by rw [hlen]; omega)) =
        some (true, (ax', ay')) →
      ∃ sb',
        fformStep (embed cells) (Int.ofNat (t.cells - 1)) (Int.ofNat i, (sb, true)) =
          (if i = t.cells - 1 then .ok (SudoRt.Flow.brk (Int.ofNat i, (sb', true)))
            else .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), (sb', true)))) ∧
        FformAt t sb' baseX baseY ax' ay' (i + 1)) :
    ∃ st : Ecbs.Board × Bool,
      FformInv t baseX baseY live0 acc0 cells t.cells st ∧
      FformAt t st.1 baseX baseY pxF pyF t.cells ∧
      walkRun t.n t.k t.benchlen (baseX, baseY) live0 acc0 cells =
        some (true, (pxF, pyF)) ∧
      SudoRt.runLoopOn (Int.ofNat start, (b, true))
        (fuelRange (Int.ofNat start) (Int.ofNat (t.cells - 1)))
        (fformStep (embed cells) (Int.ofNat (t.cells - 1))) chordAfter (fun r => pure r) =
        chordAfter (Int.ofNat (t.cells - 1), st) := by
  let toN := t.cells - 1
  have hto : toN + 1 = t.cells := by omega
  have h0 : FformInv t baseX baseY live0 acc0 cells start (b, true) :=
    ⟨rfl, px, py, hspec, hAt⟩
  have hstep : ∀ i s, start ≤ i → i ≤ toN →
      FformInv t baseX baseY live0 acc0 cells i s →
      ∃ s', FformInv t baseX baseY live0 acc0 cells (i + 1) s' ∧
        fformStep (embed cells) (Int.ofNat toN) (Int.ofNat i, s) =
          if i = toN then .ok (SudoRt.Flow.brk (Int.ofNat i, s'))
          else .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), s')) := by
    intro i st hi hito hI
    cases st with
    | mk sb slive =>
    obtain ⟨hlive, ax, ay, hrun, hAtI⟩ := hI
    have hslive : slive = true := hlive
    subst hslive
    have hiLen : i < cells.length := by omega
    obtain ⟨ax', ay', hwalk⟩ :=
      walkRun_step_of_full t.n t.k t.benchlen (baseX, baseY) live0 acc0
        (pxF, pyF) cells i ax ay hiLen hfull hrun
    have hiTo : i ≤ t.cells - 1 := hito
    obtain ⟨sb', hst, hAt'⟩ := hframe i sb ax ay ax' ay' hi hiTo hAtI hwalk
    have htake := take_succ_cell cells i hiLen
    have hrun' := walkRun_snoc t.n t.k t.benchlen (baseX, baseY) acc0
      (ax, ay) (ax', ay') (cells.take i) (cells[i]'hiLen) live0 hrun hwalk
    refine ⟨(sb', true), ?_, ?_⟩
    · refine ⟨rfl, ax', ay', ?_, ?_⟩
      · simpa [htake, hto] using hrun'
      · simpa [hto] using hAt'
    · simpa [hto] using hst
  rcases asc_inv (fformStep (embed cells) (Int.ofNat toN)) chordAfter
      (fun r => pure r) (FformInv t baseX baseY live0 acc0 cells) start toN
      hstart hstep (b, true) h0 with ⟨st, hInv, heq⟩
  have hInvC : FformInv t baseX baseY live0 acc0 cells t.cells st := by
    rw [hto] at hInv
    exact hInv
  have hcopy := hInvC
  rcases hcopy with ⟨_hlive, pxOut, pyOut, hrun0, hAtF⟩
  have htakeAll : cells.take t.cells = cells := by
    rw [← hlen]
    exact List.take_length cells
  have hrunOut : walkRun t.n t.k t.benchlen (baseX, baseY) live0 acc0 cells =
      some (true, (pxOut, pyOut)) := by
    simpa [htakeAll] using hrun0
  have heqP := Option.some.inj (hrunOut.symm.trans hfull)
  have hpt : (pxOut, pyOut) = (pxF, pyF) := congrArg Prod.snd heqP
  have hpx : pxOut = pxF := congrArg Prod.fst hpt
  have hpy : pyOut = pyF := congrArg Prod.snd hpt
  have hAtF' : FformAt t st.1 baseX baseY pxF pyF t.cells := by
    rw [← hpx, ← hpy]
    exact hAtF
  exact ⟨st, hInvC, hAtF', hfull, heq⟩

/-- Closing the live loop. The frame's marker is a natural and one more
    control step fits, so the suffix is `.ok ((true, true), …)`. The closing
    lift turns the marker off and leaves the homes. Those homes are `ProjOn`:
    the projective triple `walk_fform` returns before `finish`. -/
theorem walk_fform_close (t : Spec.Tier) (b : Ecbs.Board)
    (baseX baseY px py pxF pyF : List Nat) (live0 : Bool) (acc0 : List Nat × List Nat)
    (start : Nat) (cells : List Nat)
    (hAt : FformAt t b baseX baseY px py start)
    (hlen : cells.length = t.cells) (hpos : 0 < t.cells)
    (hstart : start ≤ t.cells - 1)
    (hspec : walkRun t.n t.k t.benchlen (baseX, baseY) live0 acc0 (cells.take start) =
      some (true, (px, py)))
    (hfull : walkRun t.n t.k t.benchlen (baseX, baseY) live0 acc0 cells =
      some (true, (pxF, pyF)))
    (hframe : ∀ i (sb : Ecbs.Board) (ax ay ax' ay' : List Nat)
      (hi0 : start ≤ i) (hi1 : i ≤ t.cells - 1),
      FformAt t sb baseX baseY ax ay i →
      walkStep t.n t.k t.benchlen (baseX, baseY) true (ax, ay)
        (cells[i]'(by rw [hlen]; omega)) =
        some (true, (ax', ay')) →
      ∃ sb',
        fformStep (embed cells) (Int.ofNat (t.cells - 1)) (Int.ofNat i, (sb, true)) =
          (if i = t.cells - 1 then .ok (SudoRt.Flow.brk (Int.ofNat i, (sb', true)))
            else .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), (sb', true)))) ∧
        FformAt t sb' baseX baseY ax' ay' (i + 1)) :
    ∃ bF pxF pyF xP yP zP, ∃ lay : ProjLay, ∃ ctrl,
      FformAt t bF baseX baseY pxF pyF t.cells ∧
      bF.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl ∧
      walkRun t.n t.k t.benchlen (baseX, baseY) live0 acc0 cells =
        some (true, (pxF, pyF)) ∧
      xP.length = t.n ∧ yP.length = t.n ∧ zP.length = t.n ∧
      allTritList xP ∧ allTritList yP ∧ allTritList zP ∧
      xP = fieldMul t.n t.k t.benchlen pxF zP ∧
      yP = fieldMul t.n t.k t.benchlen pyF zP ∧
      zP ≠ List.replicate t.n 0 ∧
      SudoRt.runLoopOn (Int.ofNat start, (b, true))
        (fuelRange (Int.ofNat start) (Int.ofNat (t.cells - 1)))
        (fformStep (embed cells) (Int.ofNat (t.cells - 1))) chordAfter (fun r => pure r) =
        .ok ((true, true),
          { bF with
            sudo_5Board_6marker := -1
            sudo_5Board_4cost := { bF.sudo_5Board_4cost with
              sudo_5Costs_4ctrl := Int.ofNat (ctrl + 1) }
            sudo_5Board_9marker_on := false }) ∧
      (∀ h : 0 < bF.sudo_5Board_4home.size, bF.sudo_5Board_4home[0] = embed xP) ∧
      (match lay with
        | .homes =>
            bF.sudo_5Board_8bench_on = false ∧
            (∀ h : 1 < bF.sudo_5Board_4home.size, bF.sudo_5Board_4home[1] = embed yP) ∧
            (∀ h : 2 < bF.sudo_5Board_4home.size, bF.sudo_5Board_4home[2] = embed zP) ∧
            (∀ h : 1 < bF.sudo_5Board_4held.size, bF.sudo_5Board_4held[1] = true) ∧
            (∀ h : 2 < bF.sudo_5Board_4held.size, bF.sudo_5Board_4held[2] = true)
        | .yBench =>
            bF.sudo_5Board_8bench_on = true ∧
            bF.sudo_5Board_8bench_to = (1 : Int) ∧
            (∃ lane, bF.sudo_5Board_5bench = embed lane ∧ t.n ≤ lane.length ∧
              lane.take t.n = yP ∧
              ∀ i, t.n ≤ i → ∀ hi : i < lane.length, lane[i] = 0) ∧
            (∀ h : 1 < bF.sudo_5Board_4held.size, bF.sudo_5Board_4held[1] = false) ∧
            (∀ h : 2 < bF.sudo_5Board_4home.size, bF.sudo_5Board_4home[2] = embed zP) ∧
            (∀ h : 2 < bF.sudo_5Board_4held.size, bF.sudo_5Board_4held[2] = true)
        | .zBench =>
            bF.sudo_5Board_8bench_on = true ∧
            bF.sudo_5Board_8bench_to = (2 : Int) ∧
            (∃ lane, bF.sudo_5Board_5bench = embed lane ∧ t.n ≤ lane.length ∧
              lane.take t.n = zP ∧
              ∀ i, t.n ≤ i → ∀ hi : i < lane.length, lane[i] = 0) ∧
            (∀ h : 1 < bF.sudo_5Board_4home.size, bF.sudo_5Board_4home[1] = embed yP) ∧
            (∀ h : 1 < bF.sudo_5Board_4held.size, bF.sudo_5Board_4held[1] = true) ∧
            (∀ h : 2 < bF.sudo_5Board_4held.size, bF.sudo_5Board_4held[2] = false)) := by
  obtain ⟨st, hI, hAtF, hrun, hloop⟩ :=
    walk_fform_from t b baseX baseY px py pxF pyF live0 acc0 start cells
      hAt hlen hpos hstart hspec hfull hframe
  have hlive : st.2 = true := hI.1
  cases st with
  | mk bF slive =>
  have hslive : slive = true := hlive
  subst hslive
  have hpack := hAtF
  rcases hpack with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    hproj, ⟨_moves, _slides, ctrl, mark, _mx, _pk, _ps, _hole, _cOps, _c0,
      _, _, hctrl, hmark, _, _, _, _, _, _, _, hfit6, _, _, _, _, _, _, _⟩⟩
  rcases hproj with ⟨xP, yP, zP, lay, hxL, hyL, hzL, hxt, hyt, hzt, hx, hy, hz, h0, hlay, _hw⟩
  have hfit : FitsLen (ctrl + 1) := FitsLen.of_le hfit6 (by omega)
  have hclose := chord_after_nat bF (Int.ofNat (t.cells - 1)) true
    mark ctrl hmark hctrl hfit
  refine ⟨bF, pxF, pyF, xP, yP, zP, lay, ctrl, hAtF, hctrl, hrun,
    hxL, hyL, hzL, hxt, hyt, hzt, hx, hy, hz, ?_, h0, hlay⟩
  rw [hloop, hclose]

end EcbsLink2.Link2
