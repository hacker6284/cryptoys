/-
  The one-peg list is a unit for `fieldMul` and `fieldCube`, so the climb
  leaves it fixed and `fieldInv` accepts it. Instantiated on each shipped tier.
-/
import EcbsLink2.Link2.CheckTail
import EcbsLink2.SpecCurve

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

def zeroPeg (n : Nat) : List Nat := List.replicate n 0

theorem coeff_zeroPeg (n i : Nat) : coeff (zeroPeg n) i = 0 := by
  unfold coeff zeroPeg
  rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> simp

private theorem range_foldr_id {α : Type} (m : Nat) (f : Nat → α → α) (a : α)
    (h : ∀ i, i < m → ∀ x, f i x = x) :
    (List.range m).foldr f a = a := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil,
      h m (Nat.lt_succ_self m)]
    exact ih fun i hi x => h i (Nat.lt_succ_of_lt hi) x

private theorem range_foldl_id {α : Type} (m : Nat) (f : Nat → α → α) (a : α)
    (h : ∀ i, i < m → ∀ x, f i x = x) :
    (List.range m).foldl (fun s i => f i s) a = a := by
  induction m generalizing a with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [ih a fun i hi x => h i (Nat.lt_succ_of_lt hi) x]
    exact h m (Nat.lt_succ_self m) _

theorem school_zero (n : Nat) (first strip : List Nat) (mirror : Bool) :
    school n first (zeroPeg n) strip mirror = strip := by
  unfold school
  refine range_foldr_id n _ strip ?_
  intro i hi st
  simp [coeff_zeroPeg]

theorem reduce_zero (n gap bench : Nat) :
    reduceStrip n gap (List.replicate bench 0) = List.replicate bench 0 := by
  refine reduce_zeros n gap _ ?_
  intro e _he hel
  have : e < (List.replicate bench 0).length := by simpa [List.length_replicate] using hel
  exact coeff_zeroPeg bench e

theorem take_zero (n bench : Nat) (hn : n ≤ bench) :
    (List.replicate bench 0).take n = zeroPeg n := by
  simp [zeroPeg, List.take_replicate, Nat.min_eq_left hn]

/-- A zero factor kills the product. The schoolbook never lays a peg. -/
theorem fieldMul_zero (n k bench : Nat) (x : List Nat) (hn : n ≤ bench) :
    fieldMul n k bench x (zeroPeg n) = zeroPeg n := by
  unfold fieldMul
  rw [school_zero, reduce_zero, take_zero n bench hn]

theorem comb_zero (n bench : Nat) :
    combStrip n bench (zeroPeg n) = List.replicate bench 0 := by
  unfold combStrip
  refine range_foldl_id n _ _ ?_
  intro i hi st
  simp [coeff_zeroPeg]

theorem fieldCube_zero (n k bench : Nat) (hn : n ≤ bench) :
    fieldCube n k bench (zeroPeg n) = zeroPeg n := by
  unfold fieldCube
  rw [comb_zero, reduce_zero, take_zero n bench hn]

theorem mirrorTrits_zero (n : Nat) : mirrorTrits (zeroPeg n) = zeroPeg n := by
  unfold mirrorTrits zeroPeg
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih, flipTrit]

theorem fieldAdd_zero (n : Nat) :
    fieldAdd n (zeroPeg n) (zeroPeg n) = zeroPeg n := by
  unfold fieldAdd
  apply List.ext_getElem
  · simp [zeroPeg, List.length_map, List.length_range, List.length_replicate]
  · intro i hi hi2
    have hz : (zeroPeg n)[i] = 0 := by
      simpa [zeroPeg, List.getElem_replicate] using hi2
    rw [List.getElem_map, List.getElem_range, coeff_zeroPeg n i, hz]
    decide

theorem fieldAdd_zero_one (n : Nat) (hpos : 0 < n) :
    fieldAdd n (zeroPeg n) (onePeg n) = onePeg n := by
  unfold fieldAdd
  apply List.ext_getElem
  · simp [onePeg, List.length_map, List.length_range, List.length_replicate]
    omega
  · intro i hi hi1
    rw [List.getElem_map, List.getElem_range, coeff_zeroPeg]
    by_cases hz : i = 0
    · subst hz
      rw [coeff_one_zero n hpos]
      simp [tritAdd, onePeg, List.getElem_cons_zero]
    · rw [coeff_one_pos n i hpos (Nat.pos_of_ne_zero hz)]
      simp [tritAdd]
      have hi0 : 0 < i := Nat.pos_of_ne_zero hz
      have hgd : (onePeg n).getD i 0 = 0 := by
        rw [onePeg, show i = (i - 1) + 1 from (Nat.sub_add_cancel hi0).symm,
          List.getD_cons_succ, List.getD_eq_getElem?_getD, List.getElem?_replicate]
        split <;> simp
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi1, Option.getD_some] at hgd
      exact hgd.symm

/-- `(x, y) = (0, 1)` lies on `y² = x³ − x² + 1` in every `GF(3ⁿ)`. -/
theorem onCurve_zero_one (n k bench : Nat) (hpos : 0 < n) (hn : n ≤ bench) :
    onCurve n k bench (zeroPeg n) (onePeg n) = true := by
  unfold onCurve
  rw [fieldMul_one n k bench hpos hn, fieldMul_zero n k bench (zeroPeg n) hn,
    fieldCube_zero n k bench hn]
  dsimp
  rw [show (1 :: List.replicate (n - 1) 0) = onePeg n from rfl,
    mirrorTrits_zero, fieldAdd_zero, fieldAdd_zero_one n hpos]
  simp

theorem demo_onCurve_zero_one :
    onCurve Spec.demo.n Spec.demo.k Spec.demo.benchlen
      (zeroPeg Spec.demo.n) (onePeg Spec.demo.n) = true :=
  onCurve_zero_one _ _ _ demo_board.n_pos
    (tier_n_le _ demo_board.n_pos demo_tier_sat.mul_span)

theorem toy_onCurve_zero_one :
    onCurve Spec.toy.n Spec.toy.k Spec.toy.benchlen
      (zeroPeg Spec.toy.n) (onePeg Spec.toy.n) = true :=
  onCurve_zero_one _ _ _ toy_board.n_pos
    (tier_n_le _ toy_board.n_pos toy_tier_sat.mul_span)

theorem hobby_onCurve_zero_one :
    onCurve Spec.hobby.n Spec.hobby.k Spec.hobby.benchlen
      (zeroPeg Spec.hobby.n) (onePeg Spec.hobby.n) = true :=
  onCurve_zero_one _ _ _ hobby_board.n_pos
    (tier_n_le _ hobby_board.n_pos hobby_tier_sat.mul_span)

theorem serious_onCurve_zero_one :
    onCurve Spec.serious.n Spec.serious.k Spec.serious.benchlen
      (zeroPeg Spec.serious.n) (onePeg Spec.serious.n) = true :=
  onCurve_zero_one _ _ _ serious_board.n_pos
    (tier_n_le _ serious_board.n_pos serious_tier_sat.mul_span)

theorem serious_invert_one :
    Ecbs.invert_number (embTier Spec.serious) (embed (onePeg Spec.serious.n)) =
      .ok (embed (onePeg Spec.serious.n)) :=
  invert_number_refines Spec.serious serious_board (onePeg Spec.serious.n)
    (onePeg_length _ serious_board.n_pos) (onePeg_trits _) serious_tier_sat rung_pos_serious
    serious_shape _ serious_fieldInv_one

end EcbsLink2.Link2
