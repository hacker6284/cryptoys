/-
  BS Link 2: registers as arrays of trits, their value, and the loop drivers used by
  the refinement proofs. Proof-only.
-/
import Bs
import MegaDreifach.Link2.Loop
import BsLink2.Link2.Loop

namespace BsLink2.Link2

open MegaDreifach.Link2

/-- The value of a trit list, hole 0 first: `x₀ + 3·x₁ + 9·x₂ + …`. -/
def valL : List Int → Int
  | [] => 0
  | x :: xs => x + 3 * valL xs

/-- The value of a register or strip (hole `i` is worth `3^i`). -/
def val (a : Array Int) : Int := valL a.toList

/-- Every entry is a trit `0, 1, 2`. -/
def TritsL (xs : List Int) : Prop := ∀ x ∈ xs, 0 ≤ x ∧ x ≤ 2

def Trits (a : Array Int) : Prop := TritsL a.toList

/-- `3^i` as an integer (by recursion, so the proofs need no `Int` power library). -/
def pw : Nat → Int
  | 0 => 1
  | i + 1 => 3 * pw i

theorem pw_zero : pw 0 = 1 := rfl

theorem pw_succ (i : Nat) : pw (i + 1) = 3 * pw i := rfl

theorem pw_pos (i : Nat) : 0 < pw i := by
  induction i with
  | zero => decide
  | succ i ih => rw [pw_succ]; omega

theorem pw_add (i j : Nat) : pw (i + j) = pw i * pw j := by
  induction j with
  | zero => simp [pw_zero]
  | succ j ih => rw [← Nat.add_assoc, pw_succ, pw_succ, ih, Int.mul_left_comm]

theorem pw_mono {i j : Nat} (h : i ≤ j) : pw i ≤ pw j := by
  induction j with
  | zero => rw [Nat.le_zero.mp h]; exact Int.le_refl _
  | succ j ih =>
    rcases Nat.lt_or_eq_of_le h with h | h
    · have := ih (by omega); have := pw_pos j; rw [pw_succ]; omega
    · rw [h]; exact Int.le_refl _

theorem pw_natCast (i : Nat) : pw i = ((3 ^ i : Nat) : Int) := by
  induction i with
  | zero => rfl
  | succ i ih => rw [pw_succ, ih, Nat.pow_succ, Int.ofNat_mul, Int.mul_comm]; rfl

theorem valL_set (xs : List Int) (i : Nat) (v : Int) (h : i < xs.length) :
    valL (xs.set i v) = valL xs + (v - xs[i]) * pw i := by
  induction xs generalizing i with
  | nil => simp at h
  | cons x xs ih =>
    cases i with
    | zero => simp [valL, pw_zero]; omega
    | succ i =>
      have hi : i < xs.length := by simpa using h
      simp only [List.set_cons_succ, valL, List.getElem_cons_succ]
      rw [ih i hi, pw_succ, Int.mul_left_comm (v - xs[i])]
      omega

theorem val_set (a : Array Int) (i : Nat) (h : i < a.size) (v : Int) :
    val (a.set ⟨i, h⟩ v) = val a + (v - a[i]) * pw i := by
  unfold val
  rw [Array.toList_set]
  have h' : i < a.toList.length := by simpa using h
  rw [valL_set _ _ _ h']
  rfl

theorem tritsL_cons {x : Int} {xs : List Int} :
    TritsL (x :: xs) ↔ (0 ≤ x ∧ x ≤ 2) ∧ TritsL xs := by
  simp [TritsL]

theorem valL_nonneg {xs : List Int} (h : TritsL xs) : 0 ≤ valL xs := by
  induction xs with
  | nil => simp [valL]
  | cons x xs ih =>
    rw [tritsL_cons] at h
    have := ih h.2
    simp only [valL]; omega

theorem valL_lt {xs : List Int} (h : TritsL xs) : valL xs < pw xs.length := by
  induction xs with
  | nil => simp [valL, pw_zero]
  | cons x xs ih =>
    rw [tritsL_cons] at h
    have := ih h.2
    simp only [valL, List.length_cons, pw_succ]; omega

theorem val_nonneg {a : Array Int} (h : Trits a) : 0 ≤ val a := valL_nonneg h

theorem val_lt {a : Array Int} (h : Trits a) : val a < pw a.size := by
  have := valL_lt h
  simpa [val] using this

theorem tritsL_set {xs : List Int} (h : TritsL xs) (i : Nat) {v : Int}
    (hv : 0 ≤ v ∧ v ≤ 2) : TritsL (xs.set i v) := by
  intro x hx
  rcases List.mem_or_eq_of_mem_set hx with hx | hx
  · exact h x hx
  · subst hx; exact hv

theorem trits_set {a : Array Int} (h : Trits a) (i : Nat) (hi : i < a.size) {v : Int}
    (hv : 0 ≤ v ∧ v ≤ 2) : Trits (a.set ⟨i, hi⟩ v) := by
  unfold Trits
  rw [Array.toList_set]
  exact tritsL_set h i hv

theorem trits_get {a : Array Int} (h : Trits a) (i : Nat) (hi : i < a.size) :
    0 ≤ a[i] ∧ a[i] ≤ 2 := by
  apply h
  exact Array.getElem_mem_toList a hi

theorem valL_append (xs ys : List Int) :
    valL (xs ++ ys) = valL xs + pw xs.length * valL ys := by
  induction xs with
  | nil => simp [valL, pw_zero]
  | cons x xs ih =>
    rw [List.cons_append, valL, valL, ih, List.length_cons, pw_succ, Int.mul_add,
      Int.mul_assoc]
    omega

theorem valL_replicate_zero (n : Nat) : valL (List.replicate n 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, valL, ih]

theorem tritsL_append {xs ys : List Int} : TritsL (xs ++ ys) ↔ TritsL xs ∧ TritsL ys := by
  simp only [TritsL, List.mem_append]
  constructor
  · intro h; exact ⟨fun x hx => h x (Or.inl hx), fun x hx => h x (Or.inr hx)⟩
  · intro h x hx; rcases hx with hx | hx
    · exact h.1 x hx
    · exact h.2 x hx

theorem tritsL_replicate_zero (n : Nat) : TritsL (List.replicate n 0) := by
  intro x hx
  rw [List.eq_of_mem_replicate hx]; decide

/-- Splitting a value at hole `k`. -/
theorem valL_split (xs : List Int) (k : Nat) :
    valL xs = valL (xs.take k) + pw (xs.take k).length * valL (xs.drop k) := by
  conv => lhs; rw [← List.take_append_drop k xs]
  exact valL_append _ _

/-- A trit list whose value is below `3^k` has nothing at or above hole `k`. -/
theorem valL_high_zero {xs : List Int} (h : TritsL xs) (k : Nat) (hv : valL xs < pw k) :
    ∀ i (hi : i < xs.length), k ≤ i → xs[i] = 0 := by
  induction xs generalizing k with
  | nil => intro i hi; simp at hi
  | cons x xs ih =>
    rw [tritsL_cons] at h
    intro i hi hk
    have hn := valL_nonneg h.2
    cases k with
    | zero =>
      simp only [valL, pw_zero] at hv
      -- x + 3 * rest < 1 with both nonneg forces x = 0 and rest = 0
      have hx0 : x = 0 := by omega
      have hr0 : valL xs < 3 ^ 0 := by simp; omega
      cases i with
      | zero => simpa using hx0
      | succ i =>
        simp only [List.getElem_cons_succ]
        exact ih h.2 0 hr0 i (by simpa using hi) (Nat.zero_le _)
    | succ k =>
      cases i with
      | zero => omega
      | succ i =>
        simp only [List.getElem_cons_succ]
        have hr : valL xs < pw k := by
          simp only [valL, pw_succ] at hv; omega
        exact ih h.2 k hr i (by simpa using hi) (by omega)

end BsLink2.Link2

namespace BsLink2.Link2

open MegaDreifach.Link2

/-! ## SudoRt on `Nat`-cast indices (the form `simp` normalises `Int.ofNat i` to) -/

theorem atL_cast {α} (a : Array α) (i : Nat) (h : i < a.size) :
    SudoRt.atL a (i : Int) = .ok a[i] := atL_ofNat a i h

theorem putL_cast {α} (a : Array α) (i : Nat) (v : α) (h : i < a.size) :
    SudoRt.putL a (i : Int) v = .ok (a.set ⟨i, h⟩ v) := putL_ofNat a i v h

theorem set_set (a : Array Int) (i : Nat) (h : i < a.size) (u v : Int)
    (h' : i < (a.set ⟨i, h⟩ u).size) : (a.set ⟨i, h⟩ u).set ⟨i, h'⟩ v = a.set ⟨i, h⟩ v := by
  apply Array.ext
  · simp
  · intro j h1 h2
    simp only [Array.getElem_set]
    split <;> rfl

theorem click_0 : Bs.click 0 = .ok 1 := rfl
theorem click_1 : Bs.click 1 = .ok 2 := rfl
theorem click_2 : Bs.click 2 = .ok 0 := rfl

theorem addI_1_1 : SudoRt.addI 1 1 = .ok 2 := rfl

end BsLink2.Link2

namespace BsLink2.Link2

theorem valL_take_succ (xs : List Int) (j : Nat) (h : j < xs.length) :
    valL (xs.take (j + 1)) = valL (xs.take j) + xs[j] * pw j := by
  rw [List.take_succ, List.getElem?_eq_getElem h, Option.toList_some, valL_append,
    List.length_take, Nat.min_eq_left (Nat.le_of_lt h)]
  simp only [valL, Int.mul_zero, Int.add_zero]
  rw [Int.mul_comm (pw j)]

theorem tritsL_take {xs : List Int} (h : TritsL xs) (k : Nat) : TritsL (xs.take k) :=
  fun x hx => h x (List.mem_of_mem_take hx)

theorem tritsL_drop {xs : List Int} (h : TritsL xs) (k : Nat) : TritsL (xs.drop k) :=
  fun x hx => h x (List.mem_of_mem_drop hx)

theorem valL_take_le {xs : List Int} (h : TritsL xs) (k : Nat) :
    valL (xs.take k) ≤ valL xs := by
  have hs := valL_split xs k
  have h1 := valL_nonneg (tritsL_drop h k)
  have h2 := pw_pos (xs.take k).length
  have := Int.mul_nonneg (Int.le_of_lt h2) h1
  omega

theorem valL_take_length (xs : List Int) : xs.take xs.length = xs := List.take_length _

end BsLink2.Link2

namespace BsLink2.Link2

theorem valL_drop_cons (xs : List Int) (h : Nat) (hh : h < xs.length) :
    valL (xs.drop h) = xs[h] + 3 * valL (xs.drop (h + 1)) := by
  rw [List.drop_eq_getElem_cons hh]; rfl

theorem length_take_of_lt {xs : List Int} {h : Nat} (hh : h < xs.length) :
    (xs.take h).length = h := by simp; omega

/-- A trit strip is worth at least its digit at hole `h` times `3^h`. -/
theorem val_ge_digit {a : Array Int} (ht : Trits a) (h : Nat) (hh : h < a.size) :
    a[h] * pw h ≤ val a := by
  have hl : h < a.toList.length := by simpa using hh
  have hs := valL_split a.toList h
  rw [length_take_of_lt hl] at hs
  have hd := valL_drop_cons a.toList h hl
  have h1 := valL_nonneg (tritsL_drop ht (h + 1))
  have h2 := valL_nonneg (tritsL_take ht h)
  have hget : a.toList[h] = a[h] := by simp
  rw [hget] at hd
  have hp := pw_pos h
  have hm : a[h] * pw h ≤ valL (a.toList.drop h) * pw h :=
    Int.mul_le_mul_of_nonneg_right (by omega) (Int.le_of_lt hp)
  unfold val
  rw [Int.mul_comm (pw h)] at hs
  omega

/-- A trit strip below `3^(h+1)` with an empty hole `h` is below `3^h`. -/
theorem val_lt_of_digit_zero {a : Array Int} (ht : Trits a) (h : Nat) (hh : h < a.size)
    (hv : val a < pw (h + 1)) (hz : a[h] = 0) : val a < pw h := by
  have hl : h < a.toList.length := by simpa using hh
  have hs := valL_split a.toList h
  rw [length_take_of_lt hl] at hs
  have hd := valL_drop_cons a.toList h hl
  have hget : a.toList[h] = a[h] := by simp
  rw [hget, hz] at hd
  have h1 := valL_nonneg (tritsL_drop ht (h + 1))
  have h2 := valL_lt (tritsL_take ht h)
  rw [length_take_of_lt hl] at h2
  have h3 := valL_nonneg (tritsL_take ht h)
  have hp := pw_pos h
  unfold val at hv ⊢
  rw [pw_succ] at hv
  rcases (by omega : valL (a.toList.drop (h + 1)) = 0 ∨ 1 ≤ valL (a.toList.drop (h + 1)))
    with h0 | h0
  · rw [hd, h0] at hs; simp at hs; omega
  · have hm : pw h * 1 ≤ pw h * valL (a.toList.drop (h + 1)) :=
      Int.mul_le_mul_of_nonneg_left h0 (Int.le_of_lt hp)
    rw [hd] at hs
    rw [Int.mul_add, Int.mul_left_comm] at hs
    omega

theorem trits_mkArray_zero (n : Nat) : Trits (Array.mkArray n 0) := by
  unfold Trits; rw [Array.toList_mkArray]; exact tritsL_replicate_zero n

theorem val_mkArray_zero (n : Nat) : val (Array.mkArray n 0) = 0 := by
  unfold val; rw [Array.toList_mkArray]; exact valL_replicate_zero n

end BsLink2.Link2
