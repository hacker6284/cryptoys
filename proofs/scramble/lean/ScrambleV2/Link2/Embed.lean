/-
  LINK 2 bridge for Scramble v2. Proof-only.

  Interprets the hand-written model (`ScrambleV2.Spec`) into the emitted
  `Scramble.Cubie` / `Array Scramble.Cubie` without editing Generated sources. The
  sudo's integer codes (colors `1 W, 2 Y, 3 R, 4 O, 5 B, 6 G`, faces
  `0 U, 1 D, 2 R, 3 L, 4 F, 5 B`, `0` for an empty sticker slot) live here, on the
  bridge; the model itself uses `Color` and `Face`. Not emitter soundness.
-/
import ScrambleV2.Spec
import Scramble
import MegaDreifach.Link2.Loop

namespace ScrambleV2

/-- The sudo's color codes (`scramble.sudo`, header comment). -/
def Color.code : Color → Int
  | .W => 1 | .Y => 2 | .R => 3 | .O => 4 | .B => 5 | .G => 6

/-- The sudo's face codes. -/
def Face.code : Face → Int
  | .U => 0 | .D => 1 | .R => 2 | .L => 3 | .F => 4 | .B => 5

end ScrambleV2

namespace ScrambleV2.Link2
open MegaDreifach.Link2

deriving instance DecidableEq for Scramble.Cubie
deriving instance DecidableEq for SudoRt.Trap
deriving instance DecidableEq for Except

/-- The six unit axes by name. -/
def ax_xp : V3 := ⟨1, 0, 0⟩
def ax_xn : V3 := ⟨-1, 0, 0⟩
def ax_yp : V3 := ⟨0, 1, 0⟩
def ax_yn : V3 := ⟨0, -1, 0⟩
def ax_zp : V3 := ⟨0, 0, 1⟩
def ax_zn : V3 := ⟨0, 0, -1⟩

/-- The emitted sticker slot for direction `a`: the code of the color facing `a`, or
    `0` if none. -/
def slot (c : Cubie) (a : V3) : Int :=
  match colorFacing c a with
  | some col => col.code
  | none => 0

/-- Model cubie → emitted cubie. -/
def embedC (c : Cubie) : Scramble.Cubie where
  sudo_5Cubie_1x := c.pos.x
  sudo_5Cubie_1y := c.pos.y
  sudo_5Cubie_1z := c.pos.z
  sudo_5Cubie_2xp := slot c ax_xp
  sudo_5Cubie_2xn := slot c ax_xn
  sudo_5Cubie_2yp := slot c ax_yp
  sudo_5Cubie_2yn := slot c ax_yn
  sudo_5Cubie_2zp := slot c ax_zp
  sudo_5Cubie_2zn := slot c ax_zn

/-- Model cube → emitted cube (same order). -/
def embedCube (cube : Cube) : Array Scramble.Cubie := Array.mk (cube.map embedC)

/-- Coordinates in `{-1, 0, 1}` (the SPEC lattice). -/
def Unit3 (v : V3) : Prop := -1 ≤ v.x ∧ v.x ≤ 1 ∧ -1 ≤ v.y ∧ v.y ≤ 1 ∧ -1 ≤ v.z ∧ v.z ≤ 1

theorem size_embedCube (cube : Cube) : (embedCube cube).size = cube.length := by
  simp [embedCube]

theorem getElem_embedCube (cube : Cube) (i : Nat) (h : i < (embedCube cube).size) :
    (embedCube cube)[i] = embedC (cube[i]'(by rw [size_embedCube] at h; exact h)) := by
  simp [embedCube]

theorem listLen_embedCube (cube : Cube) :
    SudoRt.listLen (embedCube cube) = Int.ofNat cube.length := by
  rw [listLen_eq, size_embedCube]

theorem atL_embedCube (cube : Cube) (i : Nat) (h : i < cube.length) :
    SudoRt.atL (embedCube cube) (Int.ofNat i) = .ok (embedC cube[i]) := by
  rw [atL_ofNat _ i (by rw [size_embedCube]; exact h)]
  simp [embedCube]

theorem embedCube_append (a b : Cube) : embedCube (a ++ b) = embedCube a ++ embedCube b := by
  apply Array.ext'; simp [embedCube]

theorem push_embedCube (a : Cube) (c : Cubie) :
    (embedCube a).push (embedC c) = embedCube (a ++ [c]) := by
  apply Array.ext'; simp [embedCube]

theorem embedCube_nil : embedCube [] = #[] := rfl

end ScrambleV2.Link2
