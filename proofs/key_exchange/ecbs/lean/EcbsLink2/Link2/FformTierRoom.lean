/-
  The five numeric rooms a live F-form cell reads off the tier.
  `h8` and `h12` and `h46` are the zero cell. `hwide` and `h32` are the
  live tail. Each comparison is `Nat.ble` after both sides are numerals.
  Demo does not fit `32 * stepBudget`, so `demo_room` is the rooms a
  Demo chord reads. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FformSpend
import EcbsLink2.Link2.FformRunRoom
import EcbsLink2.Link2.FformSumRoom

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

private theorem ble_le (a b : Nat) (h : Nat.ble a b = true) : a ≤ b :=
  Nat.le_of_ble_eq_true h

/-- `h8` is eight step-budgets inside one cell's moves. `h12` is twelve
    length-`n` slides. `hwide` is thirty-two step-budgets. `h32` is
    thirty-two length-`n` slides. `h46` is the comb's control. -/
structure TierRoom (t : Spec.Tier) : Prop where
  h8 : 8 * stepBudget t.n t.benchlen ≤
    walkCharge t + (6 * t.benchlen + 2 * t.n)
  h12 : 12 * t.n ≤ cellSlideCharge t + slideCharge t.n
  hwide : 32 * stepBudget t.n t.benchlen ≤
    walkCharge t + (6 * t.benchlen + 2 * t.n)
  h32 : 32 * t.n ≤ cellSlideCharge t + slideCharge t.n
  h46 : 46 ≤ cellCtrlCharge t + 4

theorem toy_wide :
    32 * stepBudget toy.n toy.benchlen ≤
      walkCharge toy + (6 * toy.benchlen + 2 * toy.n) := by
  have hL : 32 * stepBudget toy.n toy.benchlen = 23840 := by
    rw [toy_step]
  have hAdd : 6 * toy.benchlen + 2 * toy.n = 478 := by simp [toy]
  rw [hL, hAdd, toy_walk]
  exact ble_le _ _ rfl

theorem hobby_wide :
    32 * stepBudget hobby.n hobby.benchlen ≤
      walkCharge hobby + (6 * hobby.benchlen + 2 * hobby.n) := by
  have hL : 32 * stepBudget hobby.n hobby.benchlen = 128672 := by
    rw [hobby_step]
  have hAdd : 6 * hobby.benchlen + 2 * hobby.n = 1198 := by simp [hobby]
  rw [hL, hAdd, hobby_walk]
  exact ble_le _ _ rfl

theorem serious_wide :
    32 * stepBudget serious.n serious.benchlen ≤
      walkCharge serious + (6 * serious.benchlen + 2 * serious.n) := by
  have hL : 32 * stepBudget serious.n serious.benchlen = 1077152 := by
    rw [serious_step]
  have hAdd : 6 * serious.benchlen + 2 * serious.n = 3598 := by simp [serious]
  rw [hL, hAdd, serious_walk]
  exact ble_le _ _ rfl

theorem toy_room : TierRoom toy where
  h8 := toy_tail_moves
  h12 := toy_slide12
  hwide := toy_wide
  h32 := toy_sum_slide
  h46 := toy_sum_ctrl

theorem hobby_room : TierRoom hobby where
  h8 := hobby_tail_moves
  h12 := hobby_slide12
  hwide := hobby_wide
  h32 := hobby_sum_slide
  h46 := hobby_sum_ctrl

theorem serious_room : TierRoom serious where
  h8 := serious_tail_moves
  h12 := serious_slide12
  hwide := serious_wide
  h32 := serious_sum_slide
  h46 := serious_sum_ctrl

/-- Demo's chord rooms. Eight step-budgets fit, twelve and thirty-two
    length-`n` slides fit, and the comb's control fits. Thirty-two
    step-budgets do not fit Demo's move charge, and `walk_fform` is not
    stated for Demo. -/
theorem demo_room :
    8 * stepBudget demo.n demo.benchlen ≤
      walkCharge demo + (6 * demo.benchlen + 2 * demo.n) ∧
    12 * demo.n ≤ cellSlideCharge demo + slideCharge demo.n ∧
    32 * demo.n ≤ cellSlideCharge demo + slideCharge demo.n ∧
    46 ≤ cellCtrlCharge demo + 4 :=
  ⟨demo_tail_moves, demo_slide12, demo_sum_slide, demo_sum_ctrl⟩

theorem tier_room (t : Spec.Tier) (h : t = toy ∨ t = hobby ∨ t = serious) :
    TierRoom t := by
  rcases h with rfl | rfl | rfl
  · exact toy_room
  · exact hobby_room
  · exact serious_room

theorem demo_bench_fit : FitsLen demo.benchlen := by
  have h : demo.benchlen = 20 := by simp [demo]
  rw [h]
  unfold FitsLen i64MaxNat
  exact ble_le _ _ rfl

theorem toy_bench_fit : FitsLen toy.benchlen := by
  have h : toy.benchlen = 72 := by simp [toy]
  rw [h]
  unfold FitsLen i64MaxNat
  exact ble_le _ _ rfl

theorem hobby_bench_fit : FitsLen hobby.benchlen := by
  have h : hobby.benchlen = 180 := by simp [hobby]
  rw [h]
  unfold FitsLen i64MaxNat
  exact ble_le _ _ rfl

theorem serious_bench_fit : FitsLen serious.benchlen := by
  have h : serious.benchlen = 540 := by simp [serious]
  rw [h]
  unfold FitsLen i64MaxNat
  exact ble_le _ _ rfl

/-- A bench no longer than the tier's bench fits in an i64. -/
theorem bench_fit (t : Spec.Tier)
    (h : t = demo ∨ t = toy ∨ t = hobby ∨ t = serious) (n : Nat)
    (hn : n ≤ t.benchlen) : FitsLen n := by
  rcases h with rfl | rfl | rfl | rfl
  · exact FitsLen.of_le demo_bench_fit hn
  · exact FitsLen.of_le toy_bench_fit hn
  · exact FitsLen.of_le hobby_bench_fit hn
  · exact FitsLen.of_le serious_bench_fit hn

/-- The lane of a shipped tier's bench fits in an i64. -/
theorem lane_fit (t : Spec.Tier)
    (h : t = demo ∨ t = toy ∨ t = hobby ∨ t = serious)
    {ys : List Nat} (hlen : ys.length ≤ t.benchlen) : FitsLen ys.length :=
  bench_fit t h ys.length hlen

end EcbsLink2.Link2
