/-
  LINK 2. The emitted `reorient` is the model's `rotateTo` on a reachable cube, for two
  colors on perpendicular faces (Rule B, and the seat's white/green). The matrix is the
  tuple of rows `e × t`, `e`, `t`. Proof-only.
-/
import ScrambleV2.Link2.Matrix
import ScrambleV2.Link2.Lookup

namespace ScrambleV2.Link2
open MegaDreifach.Link2

theorem lattice_unit_all : ∀ p ∈ lattice, Unit3 p := by
  unfold Unit3
  decide

theorem Reach.pos_unit (cube : Cube) (h : Reach cube) {c : Cubie} (hc : c ∈ cube) : Unit3 c.pos := by
  obtain ⟨_, _, _, hperm⟩ := h
  have hmem : c.pos ∈ cube.map Cubie.pos := List.mem_map.mpr ⟨c, hc, rfl⟩
  exact lattice_unit_all c.pos (hperm.mem_iff.mp hmem)

/-- One seated-test step: `if b then the next bit else false`. -/
theorem band_step (b : Bool) (q : Prop) [Decidable q] :
    (if b = true then (Except.ok (decide q) : Except SudoRt.Trap Bool) else Except.ok false) =
      .ok (b && decide q) := by
  cases b <;> rfl

theorem band_decide (p q : Prop) [Decidable p] [Decidable q] :
    (decide p && decide q) = decide (p ∧ q) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

theorem v3_eq_yp (v : V3) :
    decide (v.x = 0 ∧ v.y = 1 ∧ v.z = 0) = decide (v = ⟨0, 1, 0⟩) := by
  obtain ⟨x, y, z⟩ := v
  by_cases h1 : x = 0 <;> by_cases h2 : y = 1 <;> by_cases h3 : z = 0 <;>
    simp [h1, h2, h3, V3.mk.injEq]

theorem v3_eq_zp (v : V3) :
    decide (v.x = 0 ∧ v.y = 0 ∧ v.z = 1) = decide (v = ⟨0, 0, 1⟩) := by
  obtain ⟨x, y, z⟩ := v
  by_cases h1 : x = 0 <;> by_cases h2 : y = 0 <;> by_cases h3 : z = 1 <;>
    simp [h1, h2, h3, V3.mk.injEq]

theorem seated_decide (e t : V3) :
    decide (((((e.x = 0 ∧ e.y = 1) ∧ e.z = 0) ∧ t.x = 0) ∧ t.y = 0) ∧ t.z = 1) =
      decide (e = ⟨0, 1, 0⟩ ∧ t = ⟨0, 0, 1⟩) := by
  obtain ⟨ex, ey, ez⟩ := e
  obtain ⟨tx, ty, tz⟩ := t
  by_cases h1 : ex = 0 <;> by_cases h2 : ey = 1 <;> by_cases h3 : ez = 0 <;>
    by_cases h4 : tx = 0 <;> by_cases h5 : ty = 0 <;> by_cases h6 : tz = 1 <;>
      simp [h1, h2, h3, h4, h5, h6, V3.mk.injEq]

/-- `reorient` on a reachable cube, with `up` and `front` on perpendicular faces, is
    `rotateTo`. -/
theorem reorient_refines (cube : Cube) (h : Reach cube) (up front : Color)
    (hperp : V3.dot (homeAxis up) (homeAxis front) = 0) :
    ∃ cube', Scramble.reorient (embedCube cube) up.code front.code = .ok (embedCube cube') ∧
      rotateTo cube up front = some cube' ∧ Reach cube' := by
  obtain ⟨F, hF⟩ := h
  have he := centerOf_reach F cube hF up
  have ht := centerOf_reach F cube hF front
  have hlen : cube.length = lattice.length := by
    simpa using hF.2.2.length_eq
  have hlatt : lattice.length = 26 := by decide
  have hfit : FitsLen cube.length := by
    rw [hlen, hlatt]
    unfold FitsLen i64MaxNat
    decide
  have hdu := center_dir_refines cube (reach_posed F cube hF) up _ he hfit
  have hdf := center_dir_refines cube (reach_posed F cube hF) front _ ht hfit
  generalize hev : F.app (homeAxis up) = e at *
  generalize htv : F.app (homeAxis front) = t at *
  have heu : Unit3 e := by
    rw [← hev]; exact axes_unit _ (rots_axes F hF.1 _ (homeAxis_mem up))
  have htu : Unit3 t := by
    rw [← htv]; exact axes_unit _ (rots_axes F hF.1 _ (homeAxis_mem front))
  unfold Scramble.reorient rotateTo
  rw [he, ht]
  simp only [Option.bind_eq_bind, Option.some_bind]
  rw [hdu, ok_bind, hdf, ok_bind]
  dsimp only
  simp only [sEq_int, pure_eq_ok]
  rw [band_step, ok_bind, band_step, ok_bind, band_step, ok_bind, band_step, ok_bind, band_step,
    ok_bind]
  simp only [band_decide]
  rw [seated_decide e t]
  by_cases hs : e = ⟨0, 1, 0⟩ ∧ t = ⟨0, 0, 1⟩
  · have hb : decide (e = ⟨0, 1, 0⟩ ∧ t = ⟨0, 0, 1⟩) = true := by simp [hs]
    simp only [hb, hs, if_true]
    exact ⟨cube, rfl, rfl, F, hF⟩
  · have hb : decide (e = ⟨0, 1, 0⟩ ∧ t = ⟨0, 0, 1⟩) = false := by simp [hs]
    simp only [hb, hs, if_false]
    have hM : (⟨V3.cross e t, e, t⟩ : Mat) ∈ rots := by
      simpa [hev, htv] using
        ruleMat_all F hF.1 _ (homeAxis_mem up) _ (homeAxis_mem front) hperp
    rw [cross_refines e t heu htu, ok_bind]
    dsimp only
    have hmat :
        (((V3.cross e t).x, (V3.cross e t).y, (V3.cross e t).z), (e.x, e.y, e.z), (t.x, t.y, t.z)) =
          embedMat ⟨V3.cross e t, e, t⟩ := rfl
    rw [hmat]
    have hpos : ∀ c ∈ cube, Unit3 c.pos := fun c hc => Reach.pos_unit cube ⟨F, hF⟩ hc
    rw [apply_matrix_refines _ hM cube hpos hfit]
    exact ⟨cube.map (moveCubie (⟨V3.cross e t, e, t⟩ : Mat).app), rfl, rfl,
      _, reach_rotate F _ hM cube hF⟩

end ScrambleV2.Link2
