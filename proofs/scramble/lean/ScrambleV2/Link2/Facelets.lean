/-
  LINK 2. The emitted `facelets_of` never traps on a reachable cube: every one of the 54
  facelet slots (tables `fx fy fz fa`) holds a cubie with a sticker on that axis, in every
  one of the 24 poses (`decide`), so `color_char` always sees a color code and the result
  is 54 color letters. Proof-only.
-/
import ScrambleV2.Link2.Index

namespace ScrambleV2.Link2
open MegaDreifach.Link2

/-- The axis with sudo code `k`. -/
def codeAx (k : Int) : V3 := ((axisCode.find? (·.1 = k)).map (·.2)).getD v0

/-- Facelet `i`'s slot and outward axis, read off the emitted tables `fx fy fz fa`. -/
def fsl (i : Nat) : V3 × List V3 :=
  (⟨Scramble.fx.getD i 0, Scramble.fy.getD i 0, Scramble.fz.getD i 0⟩, [codeAx (Scramble.fa.getD i 0)])

theorem facelet_tables_all : ∀ i ∈ List.range 54,
    SudoRt.atL Scramble.fx (Int.ofNat i) = .ok (fsl i).1.x ∧
    SudoRt.atL Scramble.fy (Int.ofNat i) = .ok (fsl i).1.y ∧
    SudoRt.atL Scramble.fz (Int.ofNat i) = .ok (fsl i).1.z ∧
    SudoRt.atL Scramble.fa (Int.ofNat i) = .ok (axc ((fsl i).2.getD 0 v0)) ∧
    (fsl i).2 = [(fsl i).2.getD 0 v0] ∧
    (axc ((fsl i).2.getD 0 v0), (fsl i).2.getD 0 v0) ∈ axisCode ∧
    (fsl i).1 ∈ lattice := by decide

/-- Every facelet's slot, in every one of the 24 poses, carries a sticker on that axis. -/
theorem facelet_colored_all : ∀ g ∈ rots, ∀ i ∈ List.range 54,
    ((fsl i).2.mapM fun a =>
      colorFacing (solvedCubie (g.transpose.app (fsl i).1)) (g.transpose.app a)).isSome := by
  decide


theorem mapM1 {α β} (f : α → Option β) (a : α) (ys : List β) (h : [a].mapM f = some ys) :
    ∃ u, f a = some u := by
  cases ha : f a <;> simp_all [List.mapM_cons]

/-- The sticker on facelet `i` of a reachable cube, as the emitted body reads it. -/
theorem facelet_read (F : Mat) (cube : Cube) (h : ReachF F cube) (hfit : FitsLen cube.length)
    (i : Nat) (hi : i < 54) : ∃ j, ∃ hj : j < cube.length, ∃ col : Color,
      Scramble.cubie_at (embedCube cube) (fsl i).1.x (fsl i).1.y (fsl i).1.z = .ok (Int.ofNat j) ∧
      Scramble.sticker_on (embedC cube[j]) (axc ((fsl i).2.getD 0 v0)) = .ok col.code := by
  obtain ⟨_, _, _, _, hl, m0, hlat⟩ := facelet_tables_all i (List.mem_range.mpr hi)
  obtain ⟨g, hg, hr⟩ := readSlot_rot F cube h (fsl i) hlat
  have hs := facelet_colored_all g hg i (List.mem_range.mpr hi)
  rw [← hr] at hs
  obtain ⟨cols, hcols⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨j, hj, hcub, hm⟩ := slot_read cube hfit _ cols hcols
  rw [hl] at hm
  obtain ⟨col, hc⟩ := mapM1 _ _ _ hm
  exact ⟨j, hj, col, hcub, by rw [sticker_on_refines _ _ m0, slot_of_facing _ _ _ hc]⟩

/-- LINK 2. `facelets_of` never traps on a reachable cube: it returns 54 color letters. -/
theorem Reach.facelets_of (cube : Cube) (h : Reach cube) :
    ∃ cols : List Color, cols.length = 54 ∧
      Scramble.facelets_of (embedCube cube) = .ok (Array.mk (cols.map Color.letter)) := by
  have hfit := Reach.fits cube h
  obtain ⟨F, hF⟩ := h
  unfold Scramble.facelets_of
  simp only [fuelRange_eq, bind_pure_right]
  refine chain_inv _ _ _ (fun i out => ∃ cols : List Color, cols.length = i ∧
      out = Array.mk (cols.map Color.letter)) 0 53 (by omega) ?_
    (fun r => ∃ cols : List Color, cols.length = 54 ∧ r = .ok (Array.mk (cols.map Color.letter)))
    ?_ _ ⟨[], rfl, rfl⟩
  · rintro i out - hi ⟨cols, hlen, rfl⟩
    obtain ⟨hx, hy, hz, ha, _⟩ := facelet_tables_all i (List.mem_range.mpr (by omega))
    obtain ⟨j, hj, col, hcub, hs⟩ := facelet_read F cube hF hfit i (by omega)
    refine ⟨Array.mk ((cols ++ [col]).map Color.letter), ⟨cols ++ [col], by simp [hlen], rfl⟩, ?_⟩
    dsimp only
    rw [if_neg (show ¬ (Int.ofNat i > (53 : Int)) from ofNat_not_gt hi)]
    simp only [hx, hy, hz, ha, ok_bind, hcub, atL_embedCube cube j hj, hs, color_char_refines,
      appendL_spec, pure_eq_ok]
    rw [show (53 : Int) = Int.ofNat 53 from rfl]
    have : (Array.mk (cols.map Color.letter)).push col.letter =
        Array.mk ((cols ++ [col]).map Color.letter) := by simp
    rw [this, asc_tail 53 i (fits_small (by omega))]
  · rintro out ⟨cols, hlen, rfl⟩
    exact ⟨cols, hlen, rfl⟩


/-- The emitted solved cube is the model's (closed term, `decide`). -/
theorem solved_cube_refines : Scramble.solved_cube = .ok (embedCube solvedCube) := by decide

/-- `solved_facelets` never traps: 54 color letters. -/
theorem solved_facelets_ok : ∃ cols : List Color, cols.length = 54 ∧
    Scramble.solved_facelets = .ok (Array.mk (cols.map Color.letter)) := by
  obtain ⟨cols, hlen, h⟩ := Reach.facelets_of solvedCube ⟨_, reach_solved⟩
  refine ⟨cols, hlen, ?_⟩
  unfold Scramble.solved_facelets
  rw [solved_cube_refines, ok_bind, h]
  rfl


/-! ## Trace names (not in the digest; never trap on their inputs) -/

theorem letter_refines (col : Color) : Scramble.letter col.code = .ok #[col.letter] := by
  cases col <;> rfl

/-- SPEC's uppercase hex digit. -/
def hexChar (n : Nat) : Int := if n < 10 then 48 + n else 55 + n

theorem hex_digit_all : ∀ n ∈ List.range 16,
    Scramble.hex_digit (Int.ofNat n) = .ok #[hexChar n] := by decide

theorem hex_digit_refines (n : Nat) (h : n < 16) :
    Scramble.hex_digit (Int.ofNat n) = .ok #[hexChar n] :=
  hex_digit_all n (List.mem_range.mpr h)

/-- Move name: the face letter, then `2` for a half turn or `'` for three quarters. -/
def moveName (f : Face) (t : Int) : Array Int :=
  #[f.letter] ++ (if t = 2 then #[50] else if t = 3 then #[39] else #[])

theorem move_name_refines (f : Face) (t : Int) (ht : t = 1 ∨ t = 2 ∨ t = 3) :
    Scramble.move_name f.code t = .ok (moveName f t) := by
  rcases ht with rfl | rfl | rfl <;> cases f <;> rfl

end ScrambleV2.Link2
