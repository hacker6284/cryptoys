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

end EcbsLink2.Link2
