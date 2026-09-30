/-
  LINK 2. The emitted `cross`, `mul_vec`, `paint_cubie` and `apply_matrix` against the
  model's `V3.cross`, `Mat.app` and `moveCubie`, for a matrix in `rots` (the only
  matrices Rule B and the seat build on the walk; `Reach.lean`). Proof-only.
-/
import ScrambleV2.Link2.Rots
import ScrambleV2.Link2.TurnRaw
import ScrambleV2.Link2.Turn

namespace ScrambleV2.Link2
open MegaDreifach.Link2

/-! ## Small integer arithmetic -/

theorem narrowI_small (n : Int) (h1 : -1000 ≤ n) (h2 : n ≤ 1000) :
    SudoRt.narrowI n = .ok n := by
  unfold SudoRt.narrowI
  have : ¬ ((n < SudoRt.i64Min || n > SudoRt.i64Max) = true) := by
    simp [SudoRt.i64Min, SudoRt.i64Max]; omega
  rw [if_neg this]

theorem mulI_small (a b : Int) (h1 : -1000 ≤ a * b) (h2 : a * b ≤ 1000) :
    SudoRt.mulI a b = .ok (a * b) := narrowI_small _ h1 h2

theorem addI_small (a b : Int) (h1 : -1000 ≤ a + b) (h2 : a + b ≤ 1000) :
    SudoRt.addI a b = .ok (a + b) := narrowI_small _ h1 h2

theorem subI_small (a b : Int) (h1 : -1000 ≤ a - b) (h2 : a - b ≤ 1000) :
    SudoRt.subI a b = .ok (a - b) := narrowI_small _ h1 h2

theorem mul_unit (a b : Int) (ha1 : -1 ≤ a) (ha2 : a ≤ 1) (hb1 : -1 ≤ b) (hb2 : b ≤ 1) :
    -1 ≤ a * b ∧ a * b ≤ 1 := by
  have : a = -1 ∨ a = 0 ∨ a = 1 := by omega
  rcases this with rfl | rfl | rfl <;> omega

/-! ## Matrices on the bridge -/

/-- Model matrix → the emitted `List<List<int>>`, by rows. -/
def embedMat (m : Mat) : Array (Array Int) :=
  #[#[m.r0.x, m.r0.y, m.r0.z], #[m.r1.x, m.r1.y, m.r1.z], #[m.r2.x, m.r2.y, m.r2.z]]

theorem atL3_0 (a b c : α) : SudoRt.atL #[a, b, c] (0 : Int) = .ok a := rfl
theorem atL3_1 (a b c : α) : SudoRt.atL #[a, b, c] (1 : Int) = .ok b := rfl
theorem atL3_2 (a b c : α) : SudoRt.atL #[a, b, c] (2 : Int) = .ok c := rfl

theorem mul_vec_refines (m : Mat) (hm : SmallMat m) (x y z : Int) (hv : Unit3 ⟨x, y, z⟩) :
    Scramble.mul_vec (embedMat m) x y z =
      .ok ((m.app ⟨x, y, z⟩).x, (m.app ⟨x, y, z⟩).y, (m.app ⟨x, y, z⟩).z) := by
  obtain ⟨⟨a1, a2, a3⟩, ⟨a4, a5, a6⟩, ⟨a7, a8, a9⟩⟩ := m
  obtain ⟨⟨b1, b2, b3, b4, b5, b6⟩, ⟨c1, c2, c3, c4, c5, c6⟩, ⟨d1, d2, d3, d4, d5, d6⟩⟩ := hm
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hv
  simp only at *
  have p1 := mul_unit a1 x b1 b2 h1 h2
  have p2 := mul_unit a2 y b3 b4 h3 h4
  have p3 := mul_unit a3 z b5 b6 h5 h6
  have p4 := mul_unit a4 x c1 c2 h1 h2
  have p5 := mul_unit a5 y c3 c4 h3 h4
  have p6 := mul_unit a6 z c5 c6 h5 h6
  have p7 := mul_unit a7 x d1 d2 h1 h2
  have p8 := mul_unit a8 y d3 d4 h3 h4
  have p9 := mul_unit a9 z d5 d6 h5 h6
  unfold Scramble.mul_vec embedMat
  simp only [atL3_0, atL3_1, atL3_2, ok_bind]
  rw [mulI_small _ _ (by omega) (by omega), ok_bind, mulI_small _ _ (by omega) (by omega), ok_bind,
    addI_small _ _ (by omega) (by omega), ok_bind, mulI_small _ _ (by omega) (by omega), ok_bind,
    addI_small _ _ (by omega) (by omega), ok_bind]
  rw [mulI_small _ _ (by omega) (by omega), ok_bind, mulI_small _ _ (by omega) (by omega), ok_bind,
    addI_small _ _ (by omega) (by omega), ok_bind, mulI_small _ _ (by omega) (by omega), ok_bind,
    addI_small _ _ (by omega) (by omega), ok_bind]
  rw [mulI_small _ _ (by omega) (by omega), ok_bind, mulI_small _ _ (by omega) (by omega), ok_bind,
    addI_small _ _ (by omega) (by omega), ok_bind, mulI_small _ _ (by omega) (by omega), ok_bind,
    addI_small _ _ (by omega) (by omega), ok_bind]
  rfl

theorem cross_refines (a b : V3) (ha : Unit3 a) (hb : Unit3 b) :
    Scramble.cross a.x a.y a.z b.x b.y b.z =
      .ok ((V3.cross a b).x, (V3.cross a b).y, (V3.cross a b).z) := by
  obtain ⟨x, y, z⟩ := a
  obtain ⟨u, v, w⟩ := b
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ha
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := hb
  simp only at *
  have q1 := mul_unit y w h3 h4 k5 k6
  have q2 := mul_unit z v h5 h6 k3 k4
  have q3 := mul_unit z u h5 h6 k1 k2
  have q4 := mul_unit x w h1 h2 k5 k6
  have q5 := mul_unit x v h1 h2 k3 k4
  have q6 := mul_unit y u h3 h4 k1 k2
  unfold Scramble.cross
  rw [mulI_small _ _ (by omega) (by omega), ok_bind, mulI_small _ _ (by omega) (by omega), ok_bind,
    subI_small _ _ (by omega) (by omega), ok_bind, mulI_small _ _ (by omega) (by omega), ok_bind,
    mulI_small _ _ (by omega) (by omega), ok_bind, subI_small _ _ (by omega) (by omega), ok_bind,
    mulI_small _ _ (by omega) (by omega), ok_bind, mulI_small _ _ (by omega) (by omega), ok_bind,
    subI_small _ _ (by omega) (by omega), ok_bind]
  rfl

/-! ## `apply_matrix` -/

theorem embedC_move (M : Mat) (hM : M ∈ rots) (c : Cubie) :
    embedC (moveCubie M.app c) =
      ⟨(M.app c.pos).x, (M.app c.pos).y, (M.app c.pos).z,
       slot c (M.transpose.app ax_xp), slot c (M.transpose.app ax_xn),
       slot c (M.transpose.app ax_yp), slot c (M.transpose.app ax_yn),
       slot c (M.transpose.app ax_zp), slot c (M.transpose.app ax_zn)⟩ := by
  have sm := fun b => slot_move M.app (rots_inj M hM) c (M.transpose.app b) b
    (rots_app_transpose M hM b)
  simp only [embedC, moveCubie_pos, sm]

theorem sel0 (v a b c d e : Int) :
    (if SudoRt.SEq.beq v 0 = true then (Except.ok (0, a, b, c, d, e) : Except SudoRt.Trap _)
      else Except.ok (v, a, b, c, d, e)) = .ok (v, a, b, c, d, e) := by
  by_cases h : v = 0 <;> simp [sEq_int, h]

theorem sel1 (v a b c d e : Int) :
    (if SudoRt.SEq.beq v 0 = true then (Except.ok (a, 0, b, c, d, e) : Except SudoRt.Trap _)
      else Except.ok (a, v, b, c, d, e)) = .ok (a, v, b, c, d, e) := by
  by_cases h : v = 0 <;> simp [sEq_int, h]

theorem sel2 (v a b c d e : Int) :
    (if SudoRt.SEq.beq v 0 = true then (Except.ok (a, b, 0, c, d, e) : Except SudoRt.Trap _)
      else Except.ok (a, b, v, c, d, e)) = .ok (a, b, v, c, d, e) := by
  by_cases h : v = 0 <;> simp [sEq_int, h]

theorem sel3 (v a b c d e : Int) :
    (if SudoRt.SEq.beq v 0 = true then (Except.ok (a, b, c, 0, d, e) : Except SudoRt.Trap _)
      else Except.ok (a, b, c, v, d, e)) = .ok (a, b, c, v, d, e) := by
  by_cases h : v = 0 <;> simp [sEq_int, h]

theorem sel4 (v a b c d e : Int) :
    (if SudoRt.SEq.beq v 0 = true then (Except.ok (a, b, c, d, 0, e) : Except SudoRt.Trap _)
      else Except.ok (a, b, c, d, v, e)) = .ok (a, b, c, d, v, e) := by
  by_cases h : v = 0 <;> simp [sEq_int, h]

theorem sel5 (v a b c d e : Int) :
    (if SudoRt.SEq.beq v 0 = true then (Except.ok (a, b, c, d, e, 0) : Except SudoRt.Trap _)
      else Except.ok (a, b, c, d, e, v)) = .ok (a, b, c, d, e, v) := by
  by_cases h : v = 0 <;> simp [sEq_int, h]


/-- The emitted `apply_matrix` with a rotation from `rots` is the model's
    `map (moveCubie M.app)` on a lattice cube. -/
theorem apply_matrix_refines (M : Mat) (hM : M ∈ rots) (cube : Cube)
    (hu : ∀ c ∈ cube, Unit3 c.pos) (hfit : FitsLen cube.length) :
    Scramble.apply_matrix (embedCube cube) (embedMat M) =
      .ok (embedCube (cube.map (moveCubie M.app))) := by
  unfold Scramble.apply_matrix
  simp only [listLen_embedCube, fuelRange_eq, bind_pure_right]
  rcases Nat.eq_zero_or_pos cube.length with h0 | hpos
  · have hnil : cube = [] := List.eq_nil_of_length_eq_zero h0
    subst hnil
    rfl
  · rw [subI_ofNat_one _ hpos hfit, ok_bind]
    have hz : (0 : Int) = Int.ofNat 0 := rfl
    rw [hz]
    have hinit : (#[] : Array Scramble.Cubie) =
        embedCube ((cube.take 0).map (moveCubie M.app)) := by
      simp [embedCube]
    rw [hinit]
    refine chain_loop _ _ _ (fun i => embedCube ((cube.take i).map (moveCubie M.app))) 0
      (cube.length - 1) (Nat.zero_le _) ?_ _ ?_
    · intro i _ hi
      have hix : i < cube.length := by omega
      simp only
      rw [if_neg (ofNat_not_gt hi), atL_embedCube cube i hix, ok_bind]
      have hc := hu _ (List.getElem_mem hix)
      have htail : (embedCube ((cube.take (i + 1)).map (moveCubie M.app))) =
          (embedCube ((cube.take i).map (moveCubie M.app))).push
            (embedC (moveCubie M.app cube[i])) := by
        rw [take_succ_map _ _ _ hix, ← push_embedCube]
      rw [htail, embedC_move M hM]
      simp only [← hz]
      clear htail hinit hz
      generalize embedCube ((cube.take i).map (moveCubie M.app)) = out
      generalize cube[i] = c at hc ⊢
      have hs := rots_small M hM
      have e0 := mul_vec_refines M hs c.pos.x c.pos.y c.pos.z hc
      have e1 := mul_vec_refines M hs 1 0 0 (by unfold Unit3; decide)
      have e2 := mul_vec_refines M hs (-1) 0 0 (by unfold Unit3; decide)
      have e3 := mul_vec_refines M hs 0 1 0 (by unfold Unit3; decide)
      have e4 := mul_vec_refines M hs 0 (-1) 0 (by unfold Unit3; decide)
      have e5 := mul_vec_refines M hs 0 0 1 (by unfold Unit3; decide)
      have e6 := mul_vec_refines M hs 0 0 (-1) (by unfold Unit3; decide)
      simp only [embedC] at *
      rw [e0, ok_bind]
      simp only [Scramble.paint_cubie, negI_one, ok_bind, appendL_spec, pure_eq_ok,
        asc_tail _ i (FitsLen.succ_le hix hfit)]
      simp only [rots, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hM
      rcases hM with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals
        simp only [Mat.app, V3.dot, Mat.transpose, Int.reduceMul, Int.reduceAdd,
          Int.reduceNeg] at e1 e2 e3 e4 e5 e6 ⊢
        simp only [e1, e2, e3, e4, e5, e6, ok_bind, wxp, wxn, wyp, wyn, wzp, wzn, pure_eq_ok,
          sel0, sel1, sel2, sel3, sel4, sel5, ax_xp, ax_xn, ax_yp, ax_yn, ax_zp, ax_zn,
          Int.reduceMul, Int.reduceAdd, Int.reduceNeg]
    · simp only
      rw [show cube.length - 1 + 1 = cube.length by omega, List.take_length]
      rfl

end ScrambleV2.Link2
