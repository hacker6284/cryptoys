/-
  The Toy root at hole 2, assembled from the per-step exponent.
  SPEC.md §5.1 lines 195 and 197.
-/
import EcbsLink2Eval.ToyPow

namespace EcbsLink2.Spec

theorem toy_rootY :
    rootY 23 15 72 (basisPeg 23 2) = [2, 0, 0, 1, 1, 2, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 2, 0, 2, 0] := by
  simp only [rootY, fieldPowDigits, toy_digits]
  rw [toy_side]
  have h0 : whiteHole0 23 = [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide
  rw [h0]
  unfold List.foldl
  rw [toy_pow_0]
  unfold List.foldl
  rw [toy_pow_1]
  unfold List.foldl
  rw [toy_pow_2]
  unfold List.foldl
  rw [toy_pow_3]
  unfold List.foldl
  rw [toy_pow_4]
  unfold List.foldl
  rw [toy_pow_5]
  unfold List.foldl
  rw [toy_pow_6]
  unfold List.foldl
  rw [toy_pow_7]
  unfold List.foldl
  rw [toy_pow_8]
  unfold List.foldl
  rw [toy_pow_9]
  unfold List.foldl
  rw [toy_pow_10]
  unfold List.foldl
  rw [toy_pow_11]
  unfold List.foldl
  rw [toy_pow_12]
  unfold List.foldl
  rw [toy_pow_13]
  unfold List.foldl
  rw [toy_pow_14]
  unfold List.foldl
  rw [toy_pow_15]
  unfold List.foldl
  rw [toy_pow_16]
  unfold List.foldl
  rw [toy_pow_17]
  unfold List.foldl
  rw [toy_pow_18]
  unfold List.foldl
  rw [toy_pow_19]
  unfold List.foldl
  rw [toy_pow_20]
  unfold List.foldl
  rw [toy_pow_21]
  unfold List.foldl
  rfl

end EcbsLink2.Spec
