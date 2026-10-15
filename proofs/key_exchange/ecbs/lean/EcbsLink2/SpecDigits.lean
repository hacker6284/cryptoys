import EcbsLink2.SpecBase

namespace EcbsLink2.Spec

private def step (acc d : Nat) : Nat := acc * 3 + d

private theorem fold_shift (ys : List Nat) (b : Nat) :
    ys.foldl step b = ys.foldl step 0 + b * 3 ^ ys.length := by
  induction ys generalizing b with
  | nil => simp [step]
  | cons d ys ih =>
    rw [List.foldl_cons, List.foldl_cons]
    have h0 : step 0 d = d := by simp [step]
    rw [h0, ih (step b d), ih d, List.length_cons, Nat.pow_succ]
    simp only [step, Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm 3 (3 ^ ys.length), Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem digitsValue_append (xs ys : List Nat) :
    digitsValue (xs ++ ys) = digitsValue ys + digitsValue xs * 3 ^ ys.length := by
  unfold digitsValue
  rw [List.foldl_append]
  simpa [step] using fold_shift ys (xs.foldl step 0)

private theorem range_add {α : Type} (a b : Nat) (f : Nat → α) :
    (List.range (a + b)).map f = (List.range a).map f ++ (List.range b).map (fun i => f (a + i)) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Nat.add_succ, List.range_succ, List.map_append, ih, List.range_succ, List.map_append]
    simp [Nat.add_assoc]

private theorem dig_0 : (List.range 15).map (rootDigit 179) = [2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2] := by decide

private theorem val_0 : digitsValue [2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2] = 10761680 := by decide

private theorem dig_1 : (List.range 15).map (fun i => rootDigit 179 (15 + i)) = [0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0] := by decide

private theorem val_1 : digitsValue [0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0] = 3587226 := by decide

private theorem dig_2 : (List.range 15).map (fun i => rootDigit 179 (30 + i)) = [2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2] := by decide

private theorem val_2 : digitsValue [2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2] = 10761680 := by decide

private theorem dig_3 : (List.range 15).map (fun i => rootDigit 179 (45 + i)) = [0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0] := by decide

private theorem val_3 : digitsValue [0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0] = 3587226 := by decide

private theorem dig_4 : (List.range 15).map (fun i => rootDigit 179 (60 + i)) = [2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2] := by decide

private theorem val_4 : digitsValue [2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2] = 10761680 := by decide

private theorem dig_5 : (List.range 15).map (fun i => rootDigit 179 (75 + i)) = [0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0] := by decide

private theorem val_5 : digitsValue [0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0] = 3587226 := by decide

private theorem dig_6 : (List.range 15).map (fun i => rootDigit 179 (90 + i)) = [2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2] := by decide

private theorem val_6 : digitsValue [2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2] = 10761680 := by decide

private theorem dig_7 : (List.range 15).map (fun i => rootDigit 179 (105 + i)) = [0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0] := by decide

private theorem val_7 : digitsValue [0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0] = 3587226 := by decide

private theorem dig_8 : (List.range 15).map (fun i => rootDigit 179 (120 + i)) = [2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2] := by decide

private theorem val_8 : digitsValue [2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2] = 10761680 := by decide

private theorem dig_9 : (List.range 15).map (fun i => rootDigit 179 (135 + i)) = [0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0] := by decide

private theorem val_9 : digitsValue [0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0] = 3587226 := by decide

private theorem dig_10 : (List.range 15).map (fun i => rootDigit 179 (150 + i)) = [2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2] := by decide

private theorem val_10 : digitsValue [2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2] = 10761680 := by decide

private theorem dig_11 : (List.range 13).map (fun i => rootDigit 179 (165 + i)) = [0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 1] := by decide

private theorem val_11 : digitsValue [0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 1] = 398581 := by decide

private theorem pref_0 : digitsValue ((List.range 15).map (rootDigit 179)) = 10761680 := by
  rw [dig_0, val_0]

private theorem pref_1 : digitsValue ((List.range 30).map (rootDigit 179)) = 154418349070986 := by
  rw [show (30 : Nat) = 15 + 15 by decide, range_add, digitsValue_append, pref_0, dig_1, val_1]
  decide

private theorem pref_2 : digitsValue ((List.range 45).map (rootDigit 179)) = 2215734529913125273982 := by
  rw [show (45 : Nat) = 30 + 15 by decide, range_add, digitsValue_append, pref_1, dig_2, val_2]
  decide

private theorem pref_3 : digitsValue ((List.range 60).map (rootDigit 179)) = 31793368706412152635720824900 := by
  rw [show (60 : Nat) = 45 + 15 by decide, range_add, digitsValue_append, pref_2, dig_3, val_3]
  decide

private theorem pref_4 : digitsValue ((List.range 75).map (rootDigit 179)) = 456200090785018281839762994464145980 := by
  rw [show (75 : Nat) = 60 + 15 by decide, range_add, digitsValue_append, pref_3, dig_4, val_4]
  decide

private theorem pref_5 : digitsValue ((List.range 90).map (rootDigit 179)) = 6545972676065784319418548109607545505031086 := by
  rw [show (90 : Nat) = 75 + 15 by decide, range_add, digitsValue_append, pref_4, dig_5, val_5]
  decide

private theorem pref_6 : digitsValue ((List.range 105).map (rootDigit 179)) = 93927553153409065081395040899784476949959095884682 := by
  rw [show (105 : Nat) = 90 + 15 by decide, range_add, digitsValue_append, pref_5, dig_6, val_6]
  decide

private theorem pref_7 : digitsValue ((List.range 120).map (rootDigit 179)) = 1347757724935823407809884872132203779798606720653388329800 := by
  rw [show (120 : Nat) = 105 + 15 by decide, range_add, digitsValue_append, pref_6, dig_7, val_7]
  decide

private theorem pref_8 : digitsValue ((List.range 135).map (rootDigit 179)) = 19338850253635711047087111710931883741378686564230448379196290280 := by
  rw [show (135 : Nat) = 120 + 15 by decide, range_add, digitsValue_append, pref_7, dig_8, val_8]
  decide

private theorem pref_9 : digitsValue ((List.range 150).map (rootDigit 179)) = 277491363776345229693525586838772483139854825292292230361388303976311186 := by
  rw [show (150 : Nat) = 135 + 15 by decide, range_add, digitsValue_append, pref_8, dig_9, val_9]
  decide

private theorem pref_10 : digitsValue ((List.range 165).map (rootDigit 179)) = 3981697772129946500766037147669970354732844881620349030278137164643819421735382 := by
  rw [show (165 : Nat) = 150 + 15 by decide, range_add, digitsValue_append, pref_9, dig_10, val_10]
  decide

private theorem pref_11 : digitsValue ((List.range 178).map (rootDigit 179)) = 6348112337155532694940810643384630145868733450199599727000130478746428111919419834967 := by
  rw [show (178 : Nat) = 165 + 13 by decide, range_add, digitsValue_append, pref_10, dig_11, val_11]
  decide

theorem serious_rootDigits : digitsValue (rootDigits 179) = rootExpNat 179 := by
  unfold rootDigits
  rw [show (179 - 1) = 178 by decide, pref_11]
  unfold rootExpNat
  decide

end EcbsLink2.Spec
