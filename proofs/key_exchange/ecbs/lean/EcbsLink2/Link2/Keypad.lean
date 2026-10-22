/-
  ECBS Link 2: the d10 keypad (SPEC §4). Proof-only.

  Claimed for faces `1 .. 9` only. Face `0` is the blank the row cup rethrows; `roll_key`
  skips it before these functions run. `keypad_first` / `keypad_second` themselves do not
  assert the range: `0 - 1` is the integer `-1`, and the model's `Nat` subtraction is a
  different operation, so face `0` is outside this theorem rather than a SPEC disagreement.
-/
import EcbsLink2.Link2.Basic

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

private theorem subI_one_cast (n : Nat) (h : 0 < n) (hf : FitsLen n) :
    SudoRt.subI (n : Int) (1 : Int) = .ok (Int.ofNat (n - 1)) := by
  rw [← ofNat_eq_natCast n]
  exact subI_ofNat_one n h hf

private theorem divI_three (a : Nat) :
    SudoRt.divI (Int.ofNat a) (3 : Int) = .ok (Int.ofNat (a / 3)) :=
  divI_ofNat a (by decide)

private theorem modI_three (a : Nat) :
    SudoRt.modI (Int.ofNat a) (3 : Int) = .ok (Int.ofNat (a % 3)) :=
  modI_ofNat a (by decide)

/-- §4. Keypad row of a face `1 .. 9`: `(face - 1) / 3`. -/
theorem keypad_first_refines (face : Nat) (h1 : 1 ≤ face) (h9 : face ≤ 9) :
    Ecbs.keypad_first (face : Int) = .ok (Int.ofNat (keypadFirst face)) := by
  unfold Ecbs.keypad_first keypadFirst
  rw [subI_one_cast face (by omega) (fits_small (by omega)), ok_bind, divI_three (face - 1),
    ok_bind, pure_eq_ok]

/-- §4. Keypad column of a face `1 .. 9`: `(face - 1) % 3`. -/
theorem keypad_second_refines (face : Nat) (h1 : 1 ≤ face) (h9 : face ≤ 9) :
    Ecbs.keypad_second (face : Int) = .ok (Int.ofNat (keypadSecond face)) := by
  unfold Ecbs.keypad_second keypadSecond
  rw [subI_one_cast face (by omega) (fits_small (by omega)), ok_bind, modI_three (face - 1),
    ok_bind, pure_eq_ok]

end EcbsLink2.Link2
