/-
  The one-peg list is a unit for `fieldMul` and `fieldCube`, so the climb
  leaves it fixed and `fieldInv` accepts it. Instantiated on each shipped tier.
-/
import EcbsLink2.Link2.CheckTail

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

theorem coeff_one_zero (n : Nat) (h : 0 < n) : coeff (onePeg n) 0 = 1 := by
  unfold coeff onePeg
  simp [List.getD_cons_zero]

theorem coeff_one_pos (n i : Nat) (_h : 0 < n) (hi : 0 < i) : coeff (onePeg n) i = 0 := by
  unfold coeff onePeg
  cases i with
  | zero => cases hi
  | succ j =>
    simp [List.getD_cons_succ, List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split <;> simp

private theorem foldl_row_one (n bench m : Nat) (hm : m ≤ n) (hpos : 0 < n) (hb : 0 < bench) :
    (List.range m).foldl (fun s j => schoolStep (onePeg n) 0 false s j) (List.replicate bench 0) =
      if m = 0 then List.replicate bench 0 else (List.replicate bench 0).set 0 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    by_cases hm0 : m = 0
    · subst hm0
      unfold schoolStep layCell tritAdd
      rw [coeff_one_zero n hpos]
      have hcz : coeff (List.replicate bench 0) 0 = 0 := by
        unfold coeff
        cases bench with
        | zero => cases hb
        | succ b => simp [List.replicate_succ, List.getD_cons_zero]
      simp [hcz]
    · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
      have hlt : m < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self m) hm
      rw [ih (Nat.le_of_lt hlt)]
      unfold schoolStep
      rw [coeff_one_pos n m hpos hmpos]
      simp [hm0]

private theorem schoolRow_one (n bench : Nat) (hpos : 0 < n) (hb : 0 < bench) :
    schoolRow n (onePeg n) 0 false (List.replicate bench 0) =
      (List.replicate bench 0).set 0 1 := by
  unfold schoolRow
  have h := foldl_row_one n bench n (Nat.le_refl n) hpos hb
  simpa [Nat.ne_of_gt hpos] using h

private theorem foldr_school_one (n bench m : Nat) (hm : m ≤ n) (hpos : 0 < n) (hb : 0 < bench) :
    (List.range m).foldr (fun i st =>
        let c := coeff (onePeg n) i
        if c = 0 then st else schoolRow n (onePeg n) i (decide (c = 2) != false) st)
        (List.replicate bench 0) =
      if m = 0 then List.replicate bench 0
      else schoolRow n (onePeg n) 0 false (List.replicate bench 0) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil]
    by_cases hm0 : m = 0
    · subst hm0
      rw [coeff_one_zero n hpos]
      have hmir : (decide ((1 : Nat) = 2) != false) = false := by decide
      simp [hmir, schoolRow_one n bench hpos hb]
    · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
      rw [coeff_one_pos n m hpos hmpos]
      conv =>
        lhs
        enter [2]
        simp
      have h := ih (Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self m) hm))
      simp only [hm0, if_false] at h
      simp only [Nat.succ_ne_zero m, if_false]
      exact h

private theorem school_one (n bench : Nat) (hpos : 0 < n) (hb : 0 < bench) :
    school n (onePeg n) (onePeg n) (List.replicate bench 0) false =
      (List.replicate bench 0).set 0 1 := by
  unfold school
  rw [foldr_school_one n bench n (Nat.le_refl _) hpos hb]
  simpa [Nat.ne_of_gt hpos] using schoolRow_one n bench hpos hb

private theorem coeff_set0_pos (bench e : Nat) (he : 0 < e) (hb : 0 < bench) :
    coeff ((List.replicate bench 0).set 0 1) e = 0 := by
  unfold coeff
  cases bench with
  | zero => cases hb
  | succ b =>
    simp [List.replicate_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_eq_getElem?_getD,
      List.getElem?_replicate]
    cases e with
    | zero => cases he
    | succ e =>
      simp [List.getD_cons_succ]
      -- getD of replicate b 0 at e
      simp [List.getD_eq_getElem?_getD, List.getElem?_replicate]
      split <;> simp

private theorem reduce_zeros (n gap : Nat) (strip : List Nat)
    (h : ∀ e, n ≤ e → e < strip.length → coeff strip e = 0) :
    reduceStrip n gap strip = strip := by
  unfold reduceStrip
  suffices ∀ m, m ≤ strip.length - n →
      (List.range m).foldr (fun d st => foldHigh n gap (n + d) st) strip = strip by
    exact this (strip.length - n) (Nat.le_refl _)
  intro m hm
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil]
    have hlt : n + m < strip.length := by omega
    have hz : coeff strip (n + m) = 0 := h (n + m) (Nat.le_add_right _ _) hlt
    have hstep : foldHigh n gap (n + m) strip = strip := by
      unfold foldHigh
      simp [hz]
    rw [hstep, ih (Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self m) hm))]

private theorem set0_high_zero (n bench e : Nat) (he : n ≤ e) (hel : e < bench) (hn : 0 < n) :
    coeff ((List.replicate bench 0).set 0 1) e = 0 :=
    coeff_set0_pos bench e (Nat.lt_of_lt_of_le hn he)
      (Nat.lt_of_le_of_lt (Nat.zero_le e) hel)

private theorem one_prefix (n bench : Nat) (hpos : 0 < n) (hn : n ≤ bench) :
    (((List.replicate bench 0).set 0 1).take n) = onePeg n := by
  cases bench with
  | zero => omega
  | succ b =>
    have hn' : n - 1 ≤ b := by omega
    simp only [List.replicate_succ, List.set_cons_zero, onePeg]
    rw [show n = (n - 1) + 1 from (Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)).symm,
      List.take_succ_cons, List.take_replicate, Nat.min_eq_left hn']
    rw [show n - 1 + 1 - 1 = n - 1 from by omega]

/-- `1` times `1` is `1` in this basis: the schoolbook lays a single white peg
    in hole 0, and the lane fold never sees a high peg. -/
theorem fieldMul_one (n k bench : Nat) (hpos : 0 < n) (hn : n ≤ bench) :
    fieldMul n k bench (onePeg n) (onePeg n) = onePeg n := by
  unfold fieldMul
  rw [school_one n bench hpos (Nat.lt_of_lt_of_le hpos hn)]
  have hred : reduceStrip n (n - k) ((List.replicate bench 0).set 0 1) =
      (List.replicate bench 0).set 0 1 := by
    refine reduce_zeros n (n - k) _ ?_
    intro e he hel
    have hlen : ((List.replicate bench 0).set 0 1).length = bench := by
      cases bench with
      | zero => omega
      | succ b => simp [List.replicate_succ, List.set_cons_zero, List.length_replicate]
    rw [hlen] at hel
    exact set0_high_zero n bench e he hel hpos
  rw [hred, one_prefix n bench hpos hn]

private theorem foldl_comb_one (n bench m : Nat) (hm : m ≤ n) (hpos : 0 < n) (hb : 0 < bench) :
    (List.range m).foldl (fun s i =>
        let c := coeff (onePeg n) i
        if c = 0 then s else s.set (3 * i) c) (List.replicate bench 0) =
      if m = 0 then List.replicate bench 0 else (List.replicate bench 0).set 0 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    by_cases hm0 : m = 0
    · subst hm0
      simp [coeff_one_zero n hpos, hb, if_false]
    · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
      rw [ih (Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self m) hm))]
      simp [hm0, coeff_one_pos n m hpos hmpos]

private theorem comb_one (n bench : Nat) (hpos : 0 < n) (hb : 0 < bench) :
    combStrip n bench (onePeg n) = (List.replicate bench 0).set 0 1 := by
  unfold combStrip
  have h := foldl_comb_one n bench n (Nat.le_refl _) hpos hb
  simpa [Nat.ne_of_gt hpos] using h

theorem fieldCube_one (n k bench : Nat) (hpos : 0 < n) (hn : n ≤ bench) :
    fieldCube n k bench (onePeg n) = onePeg n := by
  unfold fieldCube
  rw [comb_one n bench hpos (Nat.lt_of_lt_of_le hpos hn)]
  have hred : reduceStrip n (n - k) ((List.replicate bench 0).set 0 1) =
      (List.replicate bench 0).set 0 1 := by
    refine reduce_zeros n (n - k) _ ?_
    intro e he hel
    have hlen : ((List.replicate bench 0).set 0 1).length = bench := by
      cases bench with
      | zero => omega
      | succ b => simp [List.replicate_succ, List.set_cons_zero, List.length_replicate]
    rw [hlen] at hel
    exact set0_high_zero n bench e he hel hpos
  rw [hred, one_prefix n bench hpos hn]

theorem cubeTimes_one (n k bench t : Nat) (hpos : 0 < n) (hn : n ≤ bench) :
    cubeTimes n k bench (onePeg n) t = onePeg n := by
  induction t with
  | zero => simp [cubeTimes]
  | succ t ih =>
    rw [cubeTimes, ih, fieldCube_one n k bench hpos hn]

theorem invRung_one (n k bench tally rung : Nat) (last : Bool) (hpos : 0 < n) (hn : n ≤ bench) :
    (invRung n k bench (onePeg n) (onePeg n) tally rung last).1 = onePeg n := by
  unfold invRung
  simp only [cubeTimes_one n k bench tally hpos hn, fieldMul_one n k bench hpos hn]
  by_cases hr : rung = 2
  · simp [hr, fieldCube_one n k bench hpos hn, fieldMul_one n k bench hpos hn]
  · simp [hr]

theorem invClimb_one (n k bench tally : Nat) (rs : List Nat) (hpos : 0 < n) (hn : n ≤ bench) :
    (invClimb n k bench (onePeg n) (onePeg n, tally) rs).1 = onePeg n := by
  induction rs generalizing tally with
  | nil => simp [invClimb]
  | cons r rs ih =>
    rw [invClimb]
    have hpair : invRung n k bench (onePeg n) (onePeg n) tally r rs.isEmpty =
        (onePeg n, (invRung n k bench (onePeg n) (onePeg n) tally r rs.isEmpty).2) :=
      Prod.ext (invRung_one n k bench tally r rs.isEmpty hpos hn) rfl
    rw [hpair]
    exact ih _

theorem invGap_one (n k bench : Nat) (hpos : 0 < n) (hn : n ≤ bench) :
    invGap n k bench (onePeg n) = onePeg n := by
  unfold invGap
  rw [invClimb_one n k bench 1 ((rungList (n - 1)).reverse) hpos hn,
    fieldCube_one n k bench hpos hn]

/-- The one-peg input is a unit, so the climb accepts it as its own inverse. -/
theorem fieldInv_one (n k bench : Nat) (hpos : 0 < n) (hn : n ≤ bench) :
    fieldInv n k bench (onePeg n) = some (onePeg n) := by
  unfold fieldInv
  rw [invGap_one n k bench hpos hn]
  conv => zeta
  rw [fieldMul_one n k bench hpos hn, onePeg]
  simp

private theorem tier_n_le (t : Spec.Tier) (hpos : 0 < t.n) (hspan : 2 * (t.n - 1) < t.benchlen) :
    t.n ≤ t.benchlen :=
  mul_span_n t.n t.benchlen hpos hspan

theorem demo_fieldInv_one :
    fieldInv Spec.demo.n Spec.demo.k Spec.demo.benchlen (onePeg Spec.demo.n) =
      some (onePeg Spec.demo.n) :=
  fieldInv_one _ _ _ demo_board.n_pos
    (tier_n_le _ demo_board.n_pos demo_tier_sat.mul_span)

theorem toy_fieldInv_one :
    fieldInv Spec.toy.n Spec.toy.k Spec.toy.benchlen (onePeg Spec.toy.n) =
      some (onePeg Spec.toy.n) :=
  fieldInv_one _ _ _ toy_board.n_pos
    (tier_n_le _ toy_board.n_pos toy_tier_sat.mul_span)

theorem hobby_fieldInv_one :
    fieldInv Spec.hobby.n Spec.hobby.k Spec.hobby.benchlen (onePeg Spec.hobby.n) =
      some (onePeg Spec.hobby.n) :=
  fieldInv_one _ _ _ hobby_board.n_pos
    (tier_n_le _ hobby_board.n_pos hobby_tier_sat.mul_span)

theorem serious_fieldInv_one :
    fieldInv Spec.serious.n Spec.serious.k Spec.serious.benchlen (onePeg Spec.serious.n) =
      some (onePeg Spec.serious.n) :=
  fieldInv_one _ _ _ serious_board.n_pos
    (tier_n_le _ serious_board.n_pos serious_tier_sat.mul_span)

private theorem rung_pos_demo : 0 < tierR Spec.demo := by
  rw [tierR, demo_rungs]; decide

private theorem rung_pos_toy : 0 < tierR Spec.toy := by
  rw [tierR, toy_rungs]; decide

private theorem rung_pos_hobby : 0 < tierR Spec.hobby := by
  rw [tierR, hobby_rungs]; decide

private theorem rung_pos_serious : 0 < tierR Spec.serious := by
  rw [tierR, serious_rungs]; decide

theorem demo_invert_one :
    Ecbs.invert_number (embTier Spec.demo) (embed (onePeg Spec.demo.n)) =
      .ok (embed (onePeg Spec.demo.n)) :=
  invert_number_refines Spec.demo demo_board (onePeg Spec.demo.n)
    (onePeg_length _ demo_board.n_pos) (onePeg_trits _) demo_tier_sat rung_pos_demo
    demo_shape _ demo_fieldInv_one

theorem toy_invert_one :
    Ecbs.invert_number (embTier Spec.toy) (embed (onePeg Spec.toy.n)) =
      .ok (embed (onePeg Spec.toy.n)) :=
  invert_number_refines Spec.toy toy_board (onePeg Spec.toy.n)
    (onePeg_length _ toy_board.n_pos) (onePeg_trits _) toy_tier_sat rung_pos_toy
    toy_shape _ toy_fieldInv_one

theorem hobby_invert_one :
    Ecbs.invert_number (embTier Spec.hobby) (embed (onePeg Spec.hobby.n)) =
      .ok (embed (onePeg Spec.hobby.n)) :=
  invert_number_refines Spec.hobby hobby_board (onePeg Spec.hobby.n)
    (onePeg_length _ hobby_board.n_pos) (onePeg_trits _) hobby_tier_sat rung_pos_hobby
    hobby_shape _ hobby_fieldInv_one

theorem serious_invert_one :
    Ecbs.invert_number (embTier Spec.serious) (embed (onePeg Spec.serious.n)) =
      .ok (embed (onePeg Spec.serious.n)) :=
  invert_number_refines Spec.serious serious_board (onePeg Spec.serious.n)
    (onePeg_length _ serious_board.n_pos) (onePeg_trits _) serious_tier_sat rung_pos_serious
    serious_shape _ serious_fieldInv_one

end EcbsLink2.Link2
