/-
  LINK 2. A face turn: the emitted `turn_cubie`, `quarter` and `apply_turns` refine the
  model's `moveCubie`, `quarter`. Proof-only. Domain: cubie positions in `{-1, 0, 1}`
  (`Unit3`, so the emitted `0 - x` never overflows). No hypothesis on stickers: a turn
  permutes the six axes, so the emitted "write each nonzero slot to its turned axis"
  equals the model's "turn every sticker direction" read back by `slot`.
-/
import ScrambleV2.Link2.TurnRaw
import ScrambleV2.Link2.Loop

namespace ScrambleV2.Link2
open MegaDreifach.Link2

/-! ## Model side: moving a cubie by an injective map permutes its slots -/

theorem Face.map_inj (f : Face) (v w : V3) (h : f.map v = f.map w) : v = w := by
  obtain ⟨x, y, z⟩ := v
  obtain ⟨x', y', z'⟩ := w
  cases f <;> simp only [Face.map, V3.mk.injEq] at h ⊢ <;> omega

theorem colorFacing_move (g : V3 → V3) (hg : ∀ v w, g v = g w → v = w) (c : Cubie) (a : V3) :
    colorFacing (moveCubie g c) (g a) = colorFacing c a := by
  unfold colorFacing moveCubie
  simp only [List.find?_map, Option.map_map]
  have hp : ((fun s : V3 × Color => decide (s.1 = g a)) ∘ fun s : V3 × Color => (g s.1, s.2)) =
      fun s => decide (s.1 = a) := by
    funext s
    simp only [Function.comp, decide_eq_decide]
    exact ⟨hg _ _, fun h => h ▸ rfl⟩
  rw [hp]
  rfl

theorem slot_move (g : V3 → V3) (hg : ∀ v w, g v = g w → v = w) (c : Cubie) (a b : V3)
    (h : g a = b) : slot (moveCubie g c) b = slot c a := by
  unfold slot
  rw [← h, colorFacing_move g hg]

theorem moveCubie_pos (g : V3 → V3) (c : Cubie) : (moveCubie g c).pos = g c.pos := rfl

/-! ## `turn_cubie` -/

/-- The emitted `turn_cubie` is the model's `moveCubie f.map`. -/
theorem turn_cubie_refines (f : Face) (c : Cubie) (hc : Unit3 c.pos) :
    Scramble.turn_cubie (embedC c) f.code = .ok (embedC (moveCubie f.map c)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hc
  have sm := fun a b h => slot_move f.map (Face.map_inj f) c a b h
  cases f
  · rw [show embedC c = ⟨c.pos.x, c.pos.y, c.pos.z, slot c ax_xp, slot c ax_xn, slot c ax_yp,
      slot c ax_yn, slot c ax_zp, slot c ax_zn⟩ from rfl, Face.code, turn_raw0 _ _ _ _ _ _ _ _ _ h1 h2]
    simp only [embedC, moveCubie_pos, Face.map, sm ax_zp ax_xp rfl, sm ax_zn ax_xn rfl,
      sm ax_yp ax_yp rfl, sm ax_yn ax_yn rfl, sm ax_xn ax_zp rfl, sm ax_xp ax_zn rfl]
  · rw [show embedC c = ⟨c.pos.x, c.pos.y, c.pos.z, slot c ax_xp, slot c ax_xn, slot c ax_yp,
      slot c ax_yn, slot c ax_zp, slot c ax_zn⟩ from rfl, Face.code, turn_raw1 _ _ _ _ _ _ _ _ _ h1 h2]
    simp only [embedC, moveCubie_pos, Face.map, sm ax_zp ax_xp rfl, sm ax_zn ax_xn rfl,
      sm ax_yp ax_yp rfl, sm ax_yn ax_yn rfl, sm ax_xn ax_zp rfl, sm ax_xp ax_zn rfl]
  · rw [show embedC c = ⟨c.pos.x, c.pos.y, c.pos.z, slot c ax_xp, slot c ax_xn, slot c ax_yp,
      slot c ax_yn, slot c ax_zp, slot c ax_zn⟩ from rfl, Face.code, turn_raw2 _ _ _ _ _ _ _ _ _ h3 h4]
    simp only [embedC, moveCubie_pos, Face.map, sm ax_xp ax_xp rfl, sm ax_xn ax_xn rfl,
      sm ax_zp ax_yp rfl, sm ax_zn ax_yn rfl, sm ax_yn ax_zp rfl, sm ax_yp ax_zn rfl]
  · rw [show embedC c = ⟨c.pos.x, c.pos.y, c.pos.z, slot c ax_xp, slot c ax_xn, slot c ax_yp,
      slot c ax_yn, slot c ax_zp, slot c ax_zn⟩ from rfl, Face.code, turn_raw3 _ _ _ _ _ _ _ _ _ h5 h6]
    simp only [embedC, moveCubie_pos, Face.map, sm ax_xp ax_xp rfl, sm ax_xn ax_xn rfl,
      sm ax_zn ax_yp rfl, sm ax_zp ax_yn rfl, sm ax_yp ax_zp rfl, sm ax_yn ax_zn rfl]
  · rw [show embedC c = ⟨c.pos.x, c.pos.y, c.pos.z, slot c ax_xp, slot c ax_xn, slot c ax_yp,
      slot c ax_yn, slot c ax_zp, slot c ax_zn⟩ from rfl, Face.code, turn_raw4 _ _ _ _ _ _ _ _ _ h1 h2]
    simp only [embedC, moveCubie_pos, Face.map, sm ax_yp ax_xp rfl, sm ax_yn ax_xn rfl,
      sm ax_xn ax_yp rfl, sm ax_xp ax_yn rfl, sm ax_zp ax_zp rfl, sm ax_zn ax_zn rfl]
  · rw [show embedC c = ⟨c.pos.x, c.pos.y, c.pos.z, slot c ax_xp, slot c ax_xn, slot c ax_yp,
      slot c ax_yn, slot c ax_zp, slot c ax_zn⟩ from rfl, Face.code, turn_raw5 _ _ _ _ _ _ _ _ _ h3 h4]
    simp only [embedC, moveCubie_pos, Face.map, sm ax_yn ax_xp rfl, sm ax_yp ax_xn rfl,
      sm ax_xp ax_yp rfl, sm ax_xn ax_yn rfl, sm ax_zp ax_zp rfl, sm ax_zn ax_zn rfl]

/-! ## `quarter` -/

/-- The model's per-cubie step of a quarter turn. -/
def quarterStep (f : Face) (c : Cubie) : Cubie :=
  if f.onFace c.pos then moveCubie f.map c else c

theorem quarter_eq_map (f : Face) (cube : Cube) : quarter f cube = cube.map (quarterStep f) :=
  rfl

theorem take_succ_map {α β} (g : α → β) (l : List α) (i : Nat) (h : i < l.length) :
    (l.take (i + 1)).map g = (l.take i).map g ++ [g l[i]] := by
  rw [List.take_succ, List.getElem?_eq_getElem h]
  simp

/-- The emitted `quarter` is the model's `quarter` on a lattice cube. -/
theorem quarter_refines (f : Face) (cube : Cube) (hu : ∀ c ∈ cube, Unit3 c.pos)
    (hfit : FitsLen cube.length) :
    Scramble.quarter (embedCube cube) f.code = .ok (embedCube (quarter f cube)) := by
  unfold Scramble.quarter
  simp only [listLen_embedCube, fuelRange_eq, bind_pure_right]
  rcases Nat.eq_zero_or_pos cube.length with h0 | hpos
  · have hnil : cube = [] := List.eq_nil_of_length_eq_zero h0
    subst hnil
    rfl
  · rw [subI_ofNat_one _ hpos hfit, ok_bind]
    have hz : (0 : Int) = Int.ofNat 0 := rfl
    rw [hz]
    have hinit : (#[] : Array Scramble.Cubie) = embedCube ((cube.take 0).map (quarterStep f)) := by
      simp [embedCube]
    rw [hinit]
    refine chain_loop _ _ _ (fun i => embedCube ((cube.take i).map (quarterStep f))) 0
      (cube.length - 1) (Nat.zero_le _) ?_ _ ?_
    · intro i _ hi
      have hix : i < cube.length := by omega
      simp only
      rw [if_neg (ofNat_not_gt hi), atL_embedCube cube i hix, ok_bind]
      have hc := hu _ (List.getElem_mem hix)
      simp only [embedC] at *
      rw [show cube[i].pos.x = cube[i].pos.x from rfl]
      have hof := on_face_refines f cube[i].pos
      simp only [hof, ok_bind]
      by_cases hon : f.onFace cube[i].pos = true
      · simp only [hon, if_true]
        have ht := turn_cubie_refines f cube[i] hc
        simp only [embedC] at ht
        rw [ht, ok_bind]
        simp only [appendL_spec, pure_eq_ok, ok_bind]
        rw [asc_tail _ i (FitsLen.succ_le hix hfit)]
        have : (embedCube ((cube.take i).map (quarterStep f))).push
            (embedC (moveCubie f.map cube[i])) =
            embedCube ((cube.take (i + 1)).map (quarterStep f)) := by
          rw [take_succ_map _ _ _ hix, ← push_embedCube, quarterStep, if_pos hon]
        simp only [embedC] at this
        rw [this]
      · simp only [hon, Bool.false_eq_true, if_false]
        simp only [appendL_spec, pure_eq_ok, ok_bind]
        rw [asc_tail _ i (FitsLen.succ_le hix hfit)]
        have : (embedCube ((cube.take i).map (quarterStep f))).push (embedC cube[i]) =
            embedCube ((cube.take (i + 1)).map (quarterStep f)) := by
          rw [take_succ_map _ _ _ hix, ← push_embedCube, quarterStep, if_neg hon]
        simp only [embedC] at this
        rw [this]
    · simp only
      rw [show cube.length - 1 + 1 = cube.length by omega, List.take_length]
      rfl

theorem Face.map_unit (f : Face) (v : V3) (h : Unit3 v) : Unit3 (f.map v) := by
  obtain ⟨x, y, z⟩ := v
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  cases f <;> simp only [Face.map, Unit3] at * <;> omega

theorem quarter_unit (f : Face) (cube : Cube) (hu : ∀ c ∈ cube, Unit3 c.pos) :
    ∀ c ∈ quarter f cube, Unit3 c.pos := by
  intro c hc
  simp only [quarter, List.mem_map] at hc
  obtain ⟨c0, h0, rfl⟩ := hc
  split
  · exact Face.map_unit f _ (hu c0 h0)
  · exact hu c0 h0

theorem quarter_length (f : Face) (cube : Cube) : (quarter f cube).length = cube.length := by
  simp [quarter]

/-- `n` quarter turns of one face. -/
def turnsN (f : Face) : Nat → Cube → Cube
  | 0, cube => cube
  | n + 1, cube => quarter f (turnsN f n cube)

theorem iterate_quarter_unit (f : Face) (n : Nat) (cube : Cube) (hu : ∀ c ∈ cube, Unit3 c.pos) :
    ∀ c ∈ turnsN f n cube, Unit3 c.pos := by
  induction n generalizing cube with
  | zero => exact hu
  | succ n ih => exact quarter_unit f _ (ih cube hu)

theorem iterate_quarter_length (f : Face) (n : Nat) (cube : Cube) :
    (turnsN f n cube).length = cube.length := by
  induction n generalizing cube with
  | zero => rfl
  | succ n ih => rw [turnsN, quarter_length, ih]

/-- The emitted `apply_turns face n` is `n` model quarter turns (`n ≥ 1`). -/
theorem apply_turns_refines (f : Face) (n : Nat) (hn : 1 ≤ n) (hnfit : FitsLen (n + 1))
    (cube : Cube) (hu : ∀ c ∈ cube, Unit3 c.pos) (hfit : FitsLen cube.length) :
    Scramble.apply_turns (embedCube cube) f.code (Int.ofNat n) =
      .ok (embedCube (turnsN f n cube)) := by
  unfold Scramble.apply_turns
  simp only [fuelRange_eq, bind_pure_right]
  have h1 : (1 : Int) = Int.ofNat 1 := rfl
  rw [h1]
  have hinit : embedCube cube = embedCube (turnsN f (1 - 1) cube) := rfl
  rw [hinit]
  refine chain_loop _ _ _ (fun i => embedCube (turnsN f (i - 1) cube)) 1 n hn ?_ _ ?_
  · intro i hi1 hi
    simp only
    rw [if_neg (ofNat_not_gt hi),
      quarter_refines f _ (iterate_quarter_unit f _ cube hu)
        (by rw [iterate_quarter_length]; exact hfit), ok_bind]
    simp only [pure_eq_ok, ok_bind]
    rw [← h1, asc_tail _ i (FitsLen.of_le hnfit (by omega))]
    have : quarter f (turnsN f (i - 1) cube) = turnsN f (i + 1 - 1) cube := by
      rw [show i + 1 - 1 = (i - 1) + 1 by omega, turnsN]
    rw [this]
  · simp only [Nat.add_sub_cancel]
    rfl

end ScrambleV2.Link2
