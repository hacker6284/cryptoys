/-
  LINK 2. The emitted `rot_xyz`, `on_face`, `write_axis` and `turn_cubie` on raw
  integer slots (one theorem per face code), split out because the 64-branch
  `turn_cubie` reductions are the slowest step of the package. Proof-only.
-/
import ScrambleV2.Link2.Embed

namespace ScrambleV2.Link2
open MegaDreifach.Link2

theorem subI_zero_unit (x : Int) (h1 : -1 ≤ x) (h2 : x ≤ 1) :
    SudoRt.subI 0 x = .ok (-x) := by
  unfold SudoRt.subI SudoRt.narrowI
  have : ¬ ((0 - x < SudoRt.i64Min || 0 - x > SudoRt.i64Max) = true) := by
    simp [SudoRt.i64Min, SudoRt.i64Max]; omega
  rw [if_neg this]; simp

theorem negI_one : SudoRt.negI 1 = .ok (-1) := rfl

/-! ## The six axes under each turn (emitted `rot_xyz` on literals) -/


/-- `rot_xyz` on a lattice point is `Face.map`. -/
theorem rot_xyz_refines (f : Face) (v : V3) (hv : Unit3 v) :
    Scramble.rot_xyz f.code v.x v.y v.z = .ok ((f.map v).x, (f.map v).y, (f.map v).z) := by
  obtain ⟨x, y, z⟩ := v
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hv
  cases f <;>
  simp [Scramble.rot_xyz, Face.code, Face.map, sEq_int, subI_zero_unit _ h1 h2,
    subI_zero_unit _ h3 h4, subI_zero_unit _ h5 h6] <;> rfl

theorem on_face_refines (f : Face) (v : V3) :
    Scramble.on_face f.code v.x v.y v.z = .ok (f.onFace v) := by
  cases f <;> simp [Scramble.on_face, Face.code, Face.onFace, sEq_int, negI_one] <;> rfl

/-! ## `write_axis` on the six axes -/

theorem wxp (xp xn yp yn zp zn col : Int) :
    Scramble.write_axis xp xn yp yn zp zn 1 0 0 col = .ok (col, xn, yp, yn, zp, zn) := rfl
theorem wxn (xp xn yp yn zp zn col : Int) :
    Scramble.write_axis xp xn yp yn zp zn (-1) 0 0 col = .ok (xp, col, yp, yn, zp, zn) := rfl
theorem wyp (xp xn yp yn zp zn col : Int) :
    Scramble.write_axis xp xn yp yn zp zn 0 1 0 col = .ok (xp, xn, col, yn, zp, zn) := rfl
theorem wyn (xp xn yp yn zp zn col : Int) :
    Scramble.write_axis xp xn yp yn zp zn 0 (-1) 0 col = .ok (xp, xn, yp, col, zp, zn) := rfl
theorem wzp (xp xn yp yn zp zn col : Int) :
    Scramble.write_axis xp xn yp yn zp zn 0 0 1 col = .ok (xp, xn, yp, yn, col, zn) := rfl
theorem wzn (xp xn yp yn zp zn col : Int) :
    Scramble.write_axis xp xn yp yn zp zn 0 0 (-1) col = .ok (xp, xn, yp, yn, zp, col) := rfl

theorem rotU (x y z : Int) (h1 : -1 ≤ x) (h2 : x ≤ 1) :
    Scramble.rot_xyz 0 x y z = .ok (z, y, -x) := by
  simp [Scramble.rot_xyz, sEq_int, subI_zero_unit x h1 h2]
theorem rotD (x y z : Int) (h1 : -1 ≤ x) (h2 : x ≤ 1) :
    Scramble.rot_xyz 1 x y z = .ok (z, y, -x) := by
  simp [Scramble.rot_xyz, sEq_int, subI_zero_unit x h1 h2]
theorem rotR (x y z : Int) (h1 : -1 ≤ y) (h2 : y ≤ 1) :
    Scramble.rot_xyz 2 x y z = .ok (x, z, -y) := by
  simp [Scramble.rot_xyz, sEq_int, subI_zero_unit y h1 h2]
theorem rotL (x y z : Int) (h1 : -1 ≤ z) (h2 : z ≤ 1) :
    Scramble.rot_xyz 3 x y z = .ok (x, -z, y) := by
  simp [Scramble.rot_xyz, sEq_int, subI_zero_unit z h1 h2]
theorem rotF (x y z : Int) (h1 : -1 ≤ x) (h2 : x ≤ 1) :
    Scramble.rot_xyz 4 x y z = .ok (y, -x, z) := by
  simp [Scramble.rot_xyz, sEq_int, subI_zero_unit x h1 h2]
theorem rotB (x y z : Int) (h1 : -1 ≤ y) (h2 : y ≤ 1) :
    Scramble.rot_xyz 5 x y z = .ok (-y, x, z) := by
  simp [Scramble.rot_xyz, sEq_int, subI_zero_unit y h1 h2]

/-! ## `rot_xyz` on the six axes, per face code -/

theorem rot0_xp : Scramble.rot_xyz 0 1 0 0 = .ok (0, 0, (-1)) := rfl
theorem rot0_xn : Scramble.rot_xyz 0 (-1) 0 0 = .ok (0, 0, 1) := rfl
theorem rot0_yp : Scramble.rot_xyz 0 0 1 0 = .ok (0, 1, 0) := rfl
theorem rot0_yn : Scramble.rot_xyz 0 0 (-1) 0 = .ok (0, (-1), 0) := rfl
theorem rot0_zp : Scramble.rot_xyz 0 0 0 1 = .ok (1, 0, 0) := rfl
theorem rot0_zn : Scramble.rot_xyz 0 0 0 (-1) = .ok ((-1), 0, 0) := rfl
theorem rot1_xp : Scramble.rot_xyz 1 1 0 0 = .ok (0, 0, (-1)) := rfl
theorem rot1_xn : Scramble.rot_xyz 1 (-1) 0 0 = .ok (0, 0, 1) := rfl
theorem rot1_yp : Scramble.rot_xyz 1 0 1 0 = .ok (0, 1, 0) := rfl
theorem rot1_yn : Scramble.rot_xyz 1 0 (-1) 0 = .ok (0, (-1), 0) := rfl
theorem rot1_zp : Scramble.rot_xyz 1 0 0 1 = .ok (1, 0, 0) := rfl
theorem rot1_zn : Scramble.rot_xyz 1 0 0 (-1) = .ok ((-1), 0, 0) := rfl
theorem rot2_xp : Scramble.rot_xyz 2 1 0 0 = .ok (1, 0, 0) := rfl
theorem rot2_xn : Scramble.rot_xyz 2 (-1) 0 0 = .ok ((-1), 0, 0) := rfl
theorem rot2_yp : Scramble.rot_xyz 2 0 1 0 = .ok (0, 0, (-1)) := rfl
theorem rot2_yn : Scramble.rot_xyz 2 0 (-1) 0 = .ok (0, 0, 1) := rfl
theorem rot2_zp : Scramble.rot_xyz 2 0 0 1 = .ok (0, 1, 0) := rfl
theorem rot2_zn : Scramble.rot_xyz 2 0 0 (-1) = .ok (0, (-1), 0) := rfl
theorem rot3_xp : Scramble.rot_xyz 3 1 0 0 = .ok (1, 0, 0) := rfl
theorem rot3_xn : Scramble.rot_xyz 3 (-1) 0 0 = .ok ((-1), 0, 0) := rfl
theorem rot3_yp : Scramble.rot_xyz 3 0 1 0 = .ok (0, 0, 1) := rfl
theorem rot3_yn : Scramble.rot_xyz 3 0 (-1) 0 = .ok (0, 0, (-1)) := rfl
theorem rot3_zp : Scramble.rot_xyz 3 0 0 1 = .ok (0, (-1), 0) := rfl
theorem rot3_zn : Scramble.rot_xyz 3 0 0 (-1) = .ok (0, 1, 0) := rfl
theorem rot4_xp : Scramble.rot_xyz 4 1 0 0 = .ok (0, (-1), 0) := rfl
theorem rot4_xn : Scramble.rot_xyz 4 (-1) 0 0 = .ok (0, 1, 0) := rfl
theorem rot4_yp : Scramble.rot_xyz 4 0 1 0 = .ok (1, 0, 0) := rfl
theorem rot4_yn : Scramble.rot_xyz 4 0 (-1) 0 = .ok ((-1), 0, 0) := rfl
theorem rot4_zp : Scramble.rot_xyz 4 0 0 1 = .ok (0, 0, 1) := rfl
theorem rot4_zn : Scramble.rot_xyz 4 0 0 (-1) = .ok (0, 0, (-1)) := rfl
theorem rot5_xp : Scramble.rot_xyz 5 1 0 0 = .ok (0, 1, 0) := rfl
theorem rot5_xn : Scramble.rot_xyz 5 (-1) 0 0 = .ok (0, (-1), 0) := rfl
theorem rot5_yp : Scramble.rot_xyz 5 0 1 0 = .ok ((-1), 0, 0) := rfl
theorem rot5_yn : Scramble.rot_xyz 5 0 (-1) 0 = .ok (1, 0, 0) := rfl
theorem rot5_zp : Scramble.rot_xyz 5 0 0 1 = .ok (0, 0, 1) := rfl
theorem rot5_zn : Scramble.rot_xyz 5 0 0 (-1) = .ok (0, 0, (-1)) := rfl



/-! Raw turns. Slots are `(xp, xn, yp, yn, zp, zn) = (a, b, c, d, e, f)`. -/

theorem turn_raw0 (x y z a b c d e f : Int) (h1 : -1 ≤ x) (h2 : x ≤ 1) :
    Scramble.turn_cubie ⟨x, y, z, a, b, c, d, e, f⟩ 0 = .ok ⟨z, y, -x, e, f, c, d, b, a⟩ := by
  rw [Scramble.turn_cubie, rotU x y z h1 h2, ok_bind]
  simp only [negI_one, ok_bind, wxp, wxn, wyp, wyn, wzp, wzn, ]
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> by_cases hc : c = 0 <;>
    by_cases hd : d = 0 <;> by_cases he : e = 0 <;> by_cases hf : f = 0 <;>
    simp only [ha, hb, hc, hd, he, hf, sEq_int, decide_True, decide_False, Bool.not_true,
      Bool.not_false, if_true, if_false, ok_bind, Bool.false_eq_true, pure_eq_ok,
      negI_one, wxp, wxn, wyp, wyn, wzp, wzn, rot0_xp, rot0_xn, rot0_yp, rot0_yn, rot0_zp, rot0_zn, rot1_xp, rot1_xn, rot1_yp, rot1_yn, rot1_zp, rot1_zn, rot2_xp, rot2_xn, rot2_yp, rot2_yn, rot2_zp, rot2_zn, rot3_xp, rot3_xn, rot3_yp, rot3_yn, rot3_zp, rot3_zn, rot4_xp, rot4_xn, rot4_yp, rot4_yn, rot4_zp, rot4_zn, rot5_xp, rot5_xn, rot5_yp, rot5_yn, rot5_zp, rot5_zn]
theorem turn_raw1 (x y z a b c d e f : Int) (h1 : -1 ≤ x) (h2 : x ≤ 1) :
    Scramble.turn_cubie ⟨x, y, z, a, b, c, d, e, f⟩ 1 = .ok ⟨z, y, -x, e, f, c, d, b, a⟩ := by
  rw [Scramble.turn_cubie, rotD x y z h1 h2, ok_bind]
  simp only [negI_one, ok_bind, wxp, wxn, wyp, wyn, wzp, wzn, ]
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> by_cases hc : c = 0 <;>
    by_cases hd : d = 0 <;> by_cases he : e = 0 <;> by_cases hf : f = 0 <;>
    simp only [ha, hb, hc, hd, he, hf, sEq_int, decide_True, decide_False, Bool.not_true,
      Bool.not_false, if_true, if_false, ok_bind, Bool.false_eq_true, pure_eq_ok,
      negI_one, wxp, wxn, wyp, wyn, wzp, wzn, rot0_xp, rot0_xn, rot0_yp, rot0_yn, rot0_zp, rot0_zn, rot1_xp, rot1_xn, rot1_yp, rot1_yn, rot1_zp, rot1_zn, rot2_xp, rot2_xn, rot2_yp, rot2_yn, rot2_zp, rot2_zn, rot3_xp, rot3_xn, rot3_yp, rot3_yn, rot3_zp, rot3_zn, rot4_xp, rot4_xn, rot4_yp, rot4_yn, rot4_zp, rot4_zn, rot5_xp, rot5_xn, rot5_yp, rot5_yn, rot5_zp, rot5_zn]
theorem turn_raw2 (x y z a b c d e f : Int) (h1 : -1 ≤ y) (h2 : y ≤ 1) :
    Scramble.turn_cubie ⟨x, y, z, a, b, c, d, e, f⟩ 2 = .ok ⟨x, z, -y, a, b, e, f, d, c⟩ := by
  rw [Scramble.turn_cubie, rotR x y z h1 h2, ok_bind]
  simp only [negI_one, ok_bind, wxp, wxn, wyp, wyn, wzp, wzn, ]
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> by_cases hc : c = 0 <;>
    by_cases hd : d = 0 <;> by_cases he : e = 0 <;> by_cases hf : f = 0 <;>
    simp only [ha, hb, hc, hd, he, hf, sEq_int, decide_True, decide_False, Bool.not_true,
      Bool.not_false, if_true, if_false, ok_bind, Bool.false_eq_true, pure_eq_ok,
      negI_one, wxp, wxn, wyp, wyn, wzp, wzn, rot0_xp, rot0_xn, rot0_yp, rot0_yn, rot0_zp, rot0_zn, rot1_xp, rot1_xn, rot1_yp, rot1_yn, rot1_zp, rot1_zn, rot2_xp, rot2_xn, rot2_yp, rot2_yn, rot2_zp, rot2_zn, rot3_xp, rot3_xn, rot3_yp, rot3_yn, rot3_zp, rot3_zn, rot4_xp, rot4_xn, rot4_yp, rot4_yn, rot4_zp, rot4_zn, rot5_xp, rot5_xn, rot5_yp, rot5_yn, rot5_zp, rot5_zn]
theorem turn_raw3 (x y z a b c d e f : Int) (h1 : -1 ≤ z) (h2 : z ≤ 1) :
    Scramble.turn_cubie ⟨x, y, z, a, b, c, d, e, f⟩ 3 = .ok ⟨x, -z, y, a, b, f, e, c, d⟩ := by
  rw [Scramble.turn_cubie, rotL x y z h1 h2, ok_bind]
  simp only [negI_one, ok_bind, wxp, wxn, wyp, wyn, wzp, wzn, ]
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> by_cases hc : c = 0 <;>
    by_cases hd : d = 0 <;> by_cases he : e = 0 <;> by_cases hf : f = 0 <;>
    simp only [ha, hb, hc, hd, he, hf, sEq_int, decide_True, decide_False, Bool.not_true,
      Bool.not_false, if_true, if_false, ok_bind, Bool.false_eq_true, pure_eq_ok,
      negI_one, wxp, wxn, wyp, wyn, wzp, wzn, rot0_xp, rot0_xn, rot0_yp, rot0_yn, rot0_zp, rot0_zn, rot1_xp, rot1_xn, rot1_yp, rot1_yn, rot1_zp, rot1_zn, rot2_xp, rot2_xn, rot2_yp, rot2_yn, rot2_zp, rot2_zn, rot3_xp, rot3_xn, rot3_yp, rot3_yn, rot3_zp, rot3_zn, rot4_xp, rot4_xn, rot4_yp, rot4_yn, rot4_zp, rot4_zn, rot5_xp, rot5_xn, rot5_yp, rot5_yn, rot5_zp, rot5_zn]
theorem turn_raw4 (x y z a b c d e f : Int) (h1 : -1 ≤ x) (h2 : x ≤ 1) :
    Scramble.turn_cubie ⟨x, y, z, a, b, c, d, e, f⟩ 4 = .ok ⟨y, -x, z, c, d, b, a, e, f⟩ := by
  rw [Scramble.turn_cubie, rotF x y z h1 h2, ok_bind]
  simp only [negI_one, ok_bind, wxp, wxn, wyp, wyn, wzp, wzn, ]
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> by_cases hc : c = 0 <;>
    by_cases hd : d = 0 <;> by_cases he : e = 0 <;> by_cases hf : f = 0 <;>
    simp only [ha, hb, hc, hd, he, hf, sEq_int, decide_True, decide_False, Bool.not_true,
      Bool.not_false, if_true, if_false, ok_bind, Bool.false_eq_true, pure_eq_ok,
      negI_one, wxp, wxn, wyp, wyn, wzp, wzn, rot0_xp, rot0_xn, rot0_yp, rot0_yn, rot0_zp, rot0_zn, rot1_xp, rot1_xn, rot1_yp, rot1_yn, rot1_zp, rot1_zn, rot2_xp, rot2_xn, rot2_yp, rot2_yn, rot2_zp, rot2_zn, rot3_xp, rot3_xn, rot3_yp, rot3_yn, rot3_zp, rot3_zn, rot4_xp, rot4_xn, rot4_yp, rot4_yn, rot4_zp, rot4_zn, rot5_xp, rot5_xn, rot5_yp, rot5_yn, rot5_zp, rot5_zn]
theorem turn_raw5 (x y z a b c d e f : Int) (h1 : -1 ≤ y) (h2 : y ≤ 1) :
    Scramble.turn_cubie ⟨x, y, z, a, b, c, d, e, f⟩ 5 = .ok ⟨-y, x, z, d, c, a, b, e, f⟩ := by
  rw [Scramble.turn_cubie, rotB x y z h1 h2, ok_bind]
  simp only [negI_one, ok_bind, wxp, wxn, wyp, wyn, wzp, wzn, ]
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> by_cases hc : c = 0 <;>
    by_cases hd : d = 0 <;> by_cases he : e = 0 <;> by_cases hf : f = 0 <;>
    simp only [ha, hb, hc, hd, he, hf, sEq_int, decide_True, decide_False, Bool.not_true,
      Bool.not_false, if_true, if_false, ok_bind, Bool.false_eq_true, pure_eq_ok,
      negI_one, wxp, wxn, wyp, wyn, wzp, wzn, rot0_xp, rot0_xn, rot0_yp, rot0_yn, rot0_zp, rot0_zn, rot1_xp, rot1_xn, rot1_yp, rot1_yn, rot1_zp, rot1_zn, rot2_xp, rot2_xn, rot2_yp, rot2_yn, rot2_zp, rot2_zn, rot3_xp, rot3_xn, rot3_yp, rot3_yn, rot3_zp, rot3_zn, rot4_xp, rot4_xn, rot4_yp, rot4_yn, rot4_zp, rot4_zn, rot5_xp, rot5_xn, rot5_yp, rot5_yn, rot5_zp, rot5_zn]

end ScrambleV2.Link2
