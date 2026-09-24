/-
  ShiftRows / inv ShiftRows on 4×13 grids — correctness, zero sorry.
  Row i rotates left by i (SPEC SHIFT = (0,1,2,3)).
-/
import DoubleDeal.Grid
import DoubleDeal.Rotate

namespace DoubleDeal

/-- Left-rotate row `r` by `r.val` places (mod 13). -/
def shiftRows (g : Grid α) : Grid α :=
  fun r c =>
    g r ⟨(c.val + r.val) % 13, Nat.mod_lt _ (by decide)⟩

/-- Right-rotate row `r` by `r.val` places (mod 13). -/
def invShiftRows (g : Grid α) : Grid α :=
  fun r c =>
    g r ⟨(c.val + (13 - r.val)) % 13, Nat.mod_lt _ (by decide)⟩

theorem invShiftRows_shiftRows (g : Grid α) :
    invShiftRows (shiftRows g) = g := by
  funext r c
  dsimp [invShiftRows, shiftRows]
  congr 1
  apply Fin.ext
  dsimp
  have hr : r.val % 13 = r.val := Nat.mod_eq_of_lt (by have := r.isLt; omega)
  have h := rotate_right_left_cancel c.val r.val 13 c.isLt (by decide)
  simpa [hr] using h

theorem shiftRows_invShiftRows (g : Grid α) :
    shiftRows (invShiftRows g) = g := by
  funext r c
  dsimp [invShiftRows, shiftRows]
  congr 1
  apply Fin.ext
  dsimp
  have hr : r.val % 13 = r.val := Nat.mod_eq_of_lt (by have := r.isLt; omega)
  have h := rotate_left_right_cancel c.val r.val 13 c.isLt (by decide)
  simpa [hr] using h

end DoubleDeal
