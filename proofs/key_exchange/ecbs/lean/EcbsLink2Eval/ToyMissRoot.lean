/-
  Hole 1 on Toy is not a root. The exponent is the hole-2 proof's digit list.
-/
import EcbsLink2Eval.ToyMiss
import EcbsLink2Eval.ToyPow

namespace EcbsLink2.Spec

theorem toy_rootY_1 :
    rootY 23 15 72 (basisPeg 23 1) = [2, 1, 0, 1, 0, 1, 1, 1, 1, 1, 2, 2, 0, 1, 2, 0, 1, 1, 1, 2, 2, 0, 0] := by
  simp only [rootY, fieldPowDigits, toy_digits]
  rw [toy_side_1]
  have h0 : whiteHole0 23 = [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide
  rw [h0]
  unfold List.foldl
  rw [toy_miss_0]
  unfold List.foldl
  rw [toy_miss_1]
  unfold List.foldl
  rw [toy_miss_2]
  unfold List.foldl
  rw [toy_miss_3]
  unfold List.foldl
  rw [toy_miss_4]
  unfold List.foldl
  rw [toy_miss_5]
  unfold List.foldl
  rw [toy_miss_6]
  unfold List.foldl
  rw [toy_miss_7]
  unfold List.foldl
  rw [toy_miss_8]
  unfold List.foldl
  rw [toy_miss_9]
  unfold List.foldl
  rw [toy_miss_10]
  unfold List.foldl
  rw [toy_miss_11]
  unfold List.foldl
  rw [toy_miss_12]
  unfold List.foldl
  rw [toy_miss_13]
  unfold List.foldl
  rw [toy_miss_14]
  unfold List.foldl
  rw [toy_miss_15]
  unfold List.foldl
  rw [toy_miss_16]
  unfold List.foldl
  rw [toy_miss_17]
  unfold List.foldl
  rw [toy_miss_18]
  unfold List.foldl
  rw [toy_miss_19]
  unfold List.foldl
  rw [toy_miss_20]
  unfold List.foldl
  rw [toy_miss_21]
  unfold List.foldl
  rfl

end EcbsLink2.Spec
