/-
  LINK 2. The emitted lookups `cubie_at`, `is_center`, `has_color`, `center_dir`
  against the model's `cubieAt`, `isCenter`, `centerOf`. Proof-only.
-/
import ScrambleV2.Link2.Find
import ScrambleV2.Link2.Reach

namespace ScrambleV2.Link2
open MegaDreifach.Link2

theorem v3_beq (p q : V3) :
    (decide (p.x = q.x) && decide (p.y = q.y) && decide (p.z = q.z)) = decide (p = q) := by
  obtain ⟨a, b, c⟩ := p
  obtain ⟨x, y, z⟩ := q
  simp only [V3.mk.injEq]
  by_cases h1 : a = x <;> by_cases h2 : b = y <;> by_cases h3 : c = z <;> simp [h1, h2, h3]

theorem ite_ok_bool (b c : Bool) :
    (if b = true then (Except.ok c : Except SudoRt.Trap Bool) else Except.ok false) =
      Except.ok (b && c) := by
  cases b <;> rfl

/-- The emitted `cubie_at` returns the first index whose cubie sits at `q`. -/
theorem cubie_at_refines (cube : Cube) (q : V3) (j : Nat) (hj : j < cube.length)
    (hpj : cube[j].pos = q) (hfirst : ∀ i (hi : i < j), (cube[i]'(by omega)).pos ≠ q)
    (hfit : FitsLen cube.length) :
    Scramble.cubie_at (embedCube cube) q.x q.y q.z = .ok (Int.ofNat j) := by
  unfold Scramble.cubie_at
  simp only [listLen_embedCube, fuelRange_eq, bind_pure_right]
  have hpos : 0 < cube.length := by omega
  rw [subI_ofNat_one _ hpos hfit, ok_bind]
  have hz : (0 : Int) = Int.ofNat 0 := rfl
  rw [hz]
  refine find_idx _ _ _ (cube.length - 1) j (by omega) (Int.ofNat j) ?_ ?_ j 0 (by omega)
  · intro i hi
    have hix : i < cube.length := by omega
    rw [if_neg (ofNat_not_gt (by omega)), atL_embedCube cube i hix, ok_bind]
    simp only [sEq_int, pure_eq_ok, ite_ok_bool, ok_bind, embedC, v3_beq,
      decide_eq_false (hfirst i hi), Bool.false_eq_true, if_false]
    rw [asc_tail_idx _ i (FitsLen.succ_le hix hfit), if_neg (by omega)]
  · rw [if_neg (ofNat_not_gt (by omega)), atL_embedCube cube j hj, ok_bind]
    simp only [sEq_int, pure_eq_ok, ite_ok_bool, ok_bind, embedC, v3_beq,
      decide_eq_true hpj, if_true]

/-! ## `is_center`, `has_color` -/

theorem addI_zero_one : SudoRt.addI 0 1 = .ok 1 := rfl
theorem addI_one_one : SudoRt.addI 1 1 = .ok 2 := rfl
theorem addI_two_one : SudoRt.addI 2 1 = .ok 3 := rfl

theorem is_center_refines (c : Cubie) :
    Scramble.is_center (embedC c) = .ok (isCenter c.pos) := by
  obtain ⟨⟨x, y, z⟩, st⟩ := c
  unfold Scramble.is_center isCenter
  simp only [embedC, sEq_int]
  by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> by_cases hz : z = 0 <;>
    simp [hx, hy, hz, addI_zero_one, addI_one_one, addI_two_one] <;> rfl

/-- The sudo's six sticker slots, in `has_color`'s order. -/
def sixAxes : List V3 := [ax_xp, ax_xn, ax_yp, ax_yn, ax_zp, ax_zn]

/-- Some slot of `c` holds code `k`. -/
def hasCode (c : Cubie) (k : Int) : Bool := sixAxes.any fun a => decide (slot c a = k)

theorem has_color_refines (c : Cubie) (k : Int) :
    Scramble.has_color (embedC c) k = .ok (hasCode c k) := by
  unfold Scramble.has_color hasCode
  simp only [embedC, sEq_int, sixAxes, List.any_cons, List.any_nil, Bool.or_false]
  by_cases h1 : slot c ax_xp = k <;> by_cases h2 : slot c ax_xn = k <;>
    by_cases h3 : slot c ax_yp = k <;> by_cases h4 : slot c ax_yn = k <;>
    by_cases h5 : slot c ax_zp = k <;> simp [h1, h2, h3, h4, h5] <;> rfl

theorem sixAxes_perm_all : ∀ g ∈ rots, (sixAxes.map g.transpose.app).Perm sixAxes := by decide

theorem slot_rot (g : Mat) (hg : g ∈ rots) (c : Cubie) (a : V3) :
    slot (moveCubie g.app c) a = slot c (g.transpose.app a) := by
  unfold slot; rw [colorFacing_rot g hg]

theorem perm_any {α} {l1 l2 : List α} (h : l1.Perm l2) (p : α → Bool) : l1.any p = l2.any p := by
  rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  exact ⟨fun ⟨x, hx, hp⟩ => ⟨x, h.mem_iff.mp hx, hp⟩, fun ⟨x, hx, hp⟩ => ⟨x, h.mem_iff.mpr hx, hp⟩⟩

theorem hasCode_rot (g : Mat) (hg : g ∈ rots) (c : Cubie) (k : Int) :
    hasCode (moveCubie g.app c) k = hasCode c k := by
  unfold hasCode
  simp only [slot_rot g hg]
  have hp := sixAxes_perm_all g hg
  have := perm_any hp (fun a => decide (slot c a = k))
  rw [List.any_map] at this
  exact this

theorem hasCode_solved_all : ∀ p ∈ lattice, ∀ col ∈ allColors,
    hasCode (solvedCubie p) col.code = (solvedCubie p).stickers.any (·.2 = col) := by
  decide

/-- On a rotated solved cubie, the emitted "some slot holds the code" is the model's
    "some sticker has the color". -/
theorem hasCode_posed (g : Mat) (hg : g ∈ rots) (p : V3) (hp : p ∈ lattice) (col : Color) :
    hasCode (moveCubie g.app (solvedCubie p)) col.code =
      (moveCubie g.app (solvedCubie p)).stickers.any (·.2 = col) := by
  rw [hasCode_rot g hg, hasCode_solved_all p hp col (mem_allColors col)]
  simp only [moveCubie, List.any_map, Function.comp_def]

/-! ## `center_dir` -/

theorem find?_index {α} (P : α → Bool) (l : List α) (c : α) (h : l.find? P = some c) :
    ∃ j, ∃ hj : j < l.length, l[j] = c ∧ ∀ i (hi : i < j), P (l[i]'(by omega)) = false := by
  obtain ⟨hpc, as, bs, rfl, hbefore⟩ := List.find?_eq_some.mp h
  refine ⟨as.length, by simp, by rw [List.getElem_append_right (Nat.le_refl _)]; simp, fun i hi => ?_⟩
  have hmem : (as ++ c :: bs)[i]'(by simp; omega) ∈ as := by
    rw [List.getElem_append_left hi]; exact List.getElem_mem hi
  simpa using hbefore _ hmem

theorem reach_posed (F : Mat) (cube : Cube) (h : ReachF F cube) :
    ∀ c ∈ cube, ∃ g ∈ rots, ∃ p ∈ lattice, c = moveCubie g.app (solvedCubie p) := by
  intro c hc
  obtain ⟨p, hp, ⟨g, hg, hcg⟩, _⟩ := All2.mem_left h.2.1 c hc
  exact ⟨g, hg, p, hp, hcg⟩

/-- The emitted `center_dir` returns where the model's `centerOf` finds the center. -/
theorem center_dir_refines (cube : Cube)
    (hposed : ∀ c ∈ cube, ∃ g ∈ rots, ∃ p ∈ lattice, c = moveCubie g.app (solvedCubie p))
    (col : Color) (e : V3) (he : centerOf cube col = some e) (hfit : FitsLen cube.length) :
    Scramble.center_dir (embedCube cube) col.code = .ok (e.x, e.y, e.z) := by
  unfold centerOf at he
  obtain ⟨c, hc, hce⟩ := Option.map_eq_some'.mp he
  obtain ⟨j, hj, hjc, hfirst⟩ := find?_index _ _ _ hc
  have hP : ∀ i (hi : i < cube.length), (isCenter cube[i].pos && hasCode cube[i] col.code) =
      (isCenter cube[i].pos && cube[i].stickers.any (·.2 = col)) := by
    intro i hi
    obtain ⟨g, hg, p, hp, hcg⟩ := hposed _ (List.getElem_mem hi)
    rw [hcg, hasCode_posed g hg p hp]
  have hPj : (isCenter cube[j].pos && cube[j].stickers.any (·.2 = col)) = true := by
    rw [hjc]; have := List.find?_some hc; exact this
  unfold Scramble.center_dir
  simp only [listLen_embedCube, fuelRange_eq, bind_pure_right]
  have hpos : 0 < cube.length := by omega
  rw [subI_ofNat_one _ hpos hfit, ok_bind]
  have hz : (0 : Int) = Int.ofNat 0 := rfl
  rw [hz]
  refine find_idx _ _ _ (cube.length - 1) j (by omega) (e.x, e.y, e.z) ?_ ?_ j 0 (by omega)
  · intro i hi
    have hix : i < cube.length := by omega
    rw [if_neg (ofNat_not_gt (by omega)), atL_embedCube cube i hix, ok_bind,
      is_center_refines, ok_bind]
    simp only [has_color_refines, pure_eq_ok, ok_bind, bind_ok_right', ite_ok_bool, hP i hix,
      hfirst i hi, Bool.false_eq_true, if_false]
    rw [asc_tail_idx _ i (FitsLen.succ_le hix hfit), if_neg (by omega)]
  · rw [if_neg (ofNat_not_gt (by omega)), atL_embedCube cube j hj, ok_bind,
      is_center_refines, ok_bind]
    simp only [has_color_refines, pure_eq_ok, ok_bind, bind_ok_right', ite_ok_bool, hP j hj, hPj,
      if_true]
    rw [hjc, ← hce]
    rfl

end ScrambleV2.Link2
