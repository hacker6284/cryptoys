/-
  The Demo climb, as one row per length-7 trit list. `checked` is the
  kernel fact each band decides. A zero home is skipped: `FieldOk` does
  not claim it. Proof-only. Not a security claim.
-/
import EcbsLink2.SpecBase

namespace EcbsLink2.Link2

open EcbsLink2.Spec

/-- One Demo climb: the input, the two rung gaps, the cubed gap, the
    answer `specInv` returns, and whether the hole-0 product was white. -/
structure DemoRow where
  x : List Nat
  g1 : List Nat
  g2 : List Nat
  gap : List Nat
  ans : List Nat
  white : Bool

-- <generated rowOk>
/-- The four kernel steps behind `specInv_white_7` / `specInv_mirror_7`. -/
def rowOk (r : DemoRow) : Bool :=
  (invRung 7 5 20 r.x r.x 1 2 false == (r.g1, 3)) &&
    (invRung 7 5 20 r.x r.g1 3 1 true == (r.g2, 3)) &&
      (fieldCube 7 5 20 r.g2 == r.gap) &&
        (if r.white then
          (fieldMul 7 5 20 r.gap r.x == whiteHole0 7) && (r.gap == r.ans)
        else
          (fieldMul 7 5 20 r.gap r.x == (2 :: List.replicate 6 0)) &&
            (mirrorTrits r.gap == r.ans))

/-- Zero is not a `FieldOk` input. Every other row must pass `rowOk`. -/
def checked (r : DemoRow) : Bool :=
  (r.x == [0, 0, 0, 0, 0, 0, 0]) || rowOk r
-- </generated rowOk>

def demoChecked (rs : List DemoRow) : Bool :=
  rs.all checked

/-- Base-3 digits of `n`, hole 0 in the last place. `3^7 = 2187`. -/
def expected (n : Nat) : List Nat :=
  [n / 729 % 3, n / 243 % 3, n / 81 % 3, n / 27 % 3, n / 9 % 3, n / 3 % 3, n % 3]

def tri (a b c d e f g : Nat) : Nat :=
  a * 729 + b * 243 + c * 81 + d * 27 + e * 9 + f * 3 + g

private theorem mul_le_two (a k : Nat) (ha : a ≤ 2) : a * k ≤ 2 * k :=
  Nat.mul_le_mul_right k ha

private theorem le2 (a : Nat) (ha : a < 3) : a ≤ 2 :=
  Nat.le_of_lt_succ ha

theorem tri_lt (a b c d e f g : Nat)
    (ha : a < 3) (hb : b < 3) (hc : c < 3) (hd : d < 3)
    (he : e < 3) (hf : f < 3) (hg : g < 3) :
    tri a b c d e f g < 2187 := by
  have hsum : a * 729 + b * 243 + c * 81 + d * 27 + e * 9 + f * 3 + g ≤
      2 * 729 + 2 * 243 + 2 * 81 + 2 * 27 + 2 * 9 + 2 * 3 + 2 :=
    Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
      (Nat.add_le_add (Nat.add_le_add
        (mul_le_two a 729 (le2 a ha)) (mul_le_two b 243 (le2 b hb)))
        (mul_le_two c 81 (le2 c hc))) (mul_le_two d 27 (le2 d hd)))
      (mul_le_two e 9 (le2 e he))) (mul_le_two f 3 (le2 f hf))) (le2 g hg)
  have hcap : 2 * 729 + 2 * 243 + 2 * 81 + 2 * 27 + 2 * 9 + 2 * 3 + 2 = 2186 := by
    decide
  rw [hcap] at hsum
  unfold tri
  exact Nat.lt_succ_of_le hsum

theorem expected_tri (a b c d e f g : Nat)
    (ha : a < 3) (hb : b < 3) (hc : c < 3) (hd : d < 3)
    (he : e < 3) (hf : f < 3) (hg : g < 3) :
    expected (tri a b c d e f g) = [a, b, c, d, e, f, g] := by
  have ha' : a = 0 ∨ a = 1 ∨ a = 2 := by omega
  have hb' : b = 0 ∨ b = 1 ∨ b = 2 := by omega
  have hc' : c = 0 ∨ c = 1 ∨ c = 2 := by omega
  have hd' : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  have he' : e = 0 ∨ e = 1 ∨ e = 2 := by omega
  have hf' : f = 0 ∨ f = 1 ∨ f = 2 := by omega
  have hg' : g = 0 ∨ g = 1 ∨ g = 2 := by omega
  rcases ha' with rfl | rfl | rfl <;>
    rcases hb' with rfl | rfl | rfl <;>
    rcases hc' with rfl | rfl | rfl <;>
    rcases hd' with rfl | rfl | rfl <;>
    rcases he' with rfl | rfl | rfl <;>
    rcases hf' with rfl | rfl | rfl <;>
    rcases hg' with rfl | rfl | rfl <;>
    decide

end EcbsLink2.Link2
