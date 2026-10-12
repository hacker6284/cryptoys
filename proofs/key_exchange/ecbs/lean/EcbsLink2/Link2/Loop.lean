/-
  ECBS Link 2: invariant-style drivers for the emitted inclusive `for` loops.
  The MegaDreifach drivers (`chain_loop`, `asc_tail`, `fuelRange`) need the state at
  every index as a function; these only need an invariant. Same shape as the BS
  drivers (`BsLink2.Link2.Loop`), which are not in the shared MegaDreifach library,
  so they are proved again here rather than imported from the BS package.
-/
import Ecbs
import MegaDreifach.Link2.Loop

namespace EcbsLink2.Link2

open MegaDreifach.Link2

theorem asc_inv {α ρ β}
    (step : Int × α → Except SudoRt.Trap (SudoRt.Flow (Int × α) ρ))
    (after : Int × α → Except SudoRt.Trap β)
    (onRet : ρ → Except SudoRt.Trap β)
    (Inv : Nat → α → Prop) (fromN toN : Nat) (hle : fromN ≤ toN)
    (hstep : ∀ i s, fromN ≤ i → i ≤ toN → Inv i s → ∃ s', Inv (i + 1) s' ∧
      step (Int.ofNat i, s) =
        if i = toN then .ok (SudoRt.Flow.brk (Int.ofNat i, s'))
        else .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), s')))
    (s0 : α) (h0 : Inv fromN s0) :
    ∃ s, Inv (toN + 1) s ∧
      SudoRt.runLoopOn (Int.ofNat fromN, s0) (fuelRange (Int.ofNat fromN) (Int.ofNat toN))
        step after onRet = after (Int.ofNat toN, s) := by
  rw [fuelRange_le hle]
  obtain ⟨d, hd⟩ : ∃ d, toN - fromN = d := ⟨_, rfl⟩
  rw [hd]
  induction d generalizing fromN s0 with
  | zero =>
    have heq : fromN = toN := by omega
    subst heq
    obtain ⟨s', hs', hst⟩ := hstep fromN s0 (Nat.le_refl _) (Nat.le_refl _) h0
    rw [runLoopOn_succ, hst, if_pos rfl]
    exact ⟨s', hs', rfl⟩
  | succ d ih =>
    have hne : fromN ≠ toN := by omega
    obtain ⟨s', hs', hst⟩ := hstep fromN s0 (Nat.le_refl _) hle h0
    rw [runLoopOn_succ, hst, if_neg hne]
    exact ih (fromN + 1) (by omega)
      (fun i s h1 h2 hI => hstep i s (by omega) h2 hI) s' hs' (by omega)

theorem asc_goal {α ρ β}
    {step : Int × α → Except SudoRt.Trap (SudoRt.Flow (Int × α) ρ)}
    {after : Int × α → Except SudoRt.Trap β}
    {onRet : ρ → Except SudoRt.Trap β}
    (Inv : Nat → α → Prop) {fromN toN : Nat} {s0 : α} {goal : Except SudoRt.Trap β}
    (hle : fromN ≤ toN)
    (h0 : Inv fromN s0)
    (hstep : ∀ i s, fromN ≤ i → i ≤ toN → Inv i s → ∃ s', Inv (i + 1) s' ∧
      step (Int.ofNat i, s) =
        if i = toN then .ok (SudoRt.Flow.brk (Int.ofNat i, s'))
        else .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), s')))
    (hpost : ∀ s, Inv (toN + 1) s → after (Int.ofNat toN, s) = goal) :
    SudoRt.runLoopOn (Int.ofNat fromN, s0) (fuelRange (Int.ofNat fromN) (Int.ofNat toN))
      step after onRet = goal := by
  obtain ⟨s, hs, heq⟩ := asc_inv step after onRet Inv fromN toN hle hstep s0 h0
  rw [heq, hpost s hs]

theorem desc_inv {α ρ β}
    (step : Int × α → Except SudoRt.Trap (SudoRt.Flow (Int × α) ρ))
    (after : Int × α → Except SudoRt.Trap β)
    (onRet : ρ → Except SudoRt.Trap β)
    (Inv : Nat → α → Prop) (fromN toN : Nat) (hle : toN ≤ fromN)
    (hstep : ∀ i s, toN ≤ i → i ≤ fromN → Inv (i + 1) s → ∃ s', Inv i s' ∧
      step (Int.ofNat i, s) =
        if i = toN then .ok (SudoRt.Flow.brk (Int.ofNat i, s'))
        else .ok (SudoRt.Flow.cont (Int.ofNat (i - 1), s')))
    (s0 : α) (h0 : Inv (fromN + 1) s0) :
    ∃ s, Inv toN s ∧
      SudoRt.runLoopOn (Int.ofNat fromN, s0) (fuelDown (Int.ofNat fromN) (Int.ofNat toN))
        step after onRet = after (Int.ofNat toN, s) := by
  rw [fuelDown_le hle]
  obtain ⟨d, hd⟩ : ∃ d, fromN - toN = d := ⟨_, rfl⟩
  rw [hd]
  induction d generalizing fromN s0 with
  | zero =>
    have heq : fromN = toN := by omega
    subst heq
    obtain ⟨s', hs', hst⟩ := hstep fromN s0 (Nat.le_refl _) (Nat.le_refl _) h0
    rw [runLoopOn_succ, hst, if_pos rfl]
    exact ⟨s', hs', rfl⟩
  | succ d ih =>
    have hne : fromN ≠ toN := by omega
    obtain ⟨s', hs', hst⟩ := hstep fromN s0 hle (Nat.le_refl _) h0
    rw [runLoopOn_succ, hst, if_neg hne]
    have hf : fromN - 1 + 1 = fromN := by omega
    exact ih (fromN - 1) (by omega)
      (fun i s h1 h2 hI => hstep i s h1 (by omega) hI) s' (by rw [hf]; exact hs') (by omega)

theorem desc_goal {α ρ β}
    {step : Int × α → Except SudoRt.Trap (SudoRt.Flow (Int × α) ρ)}
    {after : Int × α → Except SudoRt.Trap β}
    {onRet : ρ → Except SudoRt.Trap β}
    (Inv : Nat → α → Prop) {fromN toN : Nat} {s0 : α} {goal : Except SudoRt.Trap β}
    (hle : toN ≤ fromN)
    (h0 : Inv (fromN + 1) s0)
    (hstep : ∀ i s, toN ≤ i → i ≤ fromN → Inv (i + 1) s → ∃ s', Inv i s' ∧
      step (Int.ofNat i, s) =
        if i = toN then .ok (SudoRt.Flow.brk (Int.ofNat i, s'))
        else .ok (SudoRt.Flow.cont (Int.ofNat (i - 1), s')))
    (hpost : ∀ s, Inv toN s → after (Int.ofNat toN, s) = goal) :
    SudoRt.runLoopOn (Int.ofNat fromN, s0) (fuelDown (Int.ofNat fromN) (Int.ofNat toN))
      step after onRet = goal := by
  obtain ⟨s, hs, heq⟩ := desc_inv step after onRet Inv fromN toN hle hstep s0 h0
  rw [heq, hpost s hs]

/-- Ascending loop that may `break` early. Each step either advances the invariant or
    breaks with `Done i`. The join index `j` satisfies `fromN ≤ j ≤ toN`. -/
theorem asc_brk_inv {α ρ β}
    (step : Int × α → Except SudoRt.Trap (SudoRt.Flow (Int × α) ρ))
    (after : Int × α → Except SudoRt.Trap β)
    (onRet : ρ → Except SudoRt.Trap β)
    (Inv : Nat → α → Prop) (Done : Nat → α → Prop) (fromN toN : Nat) (hle : fromN ≤ toN)
    (hstep : ∀ i s, fromN ≤ i → i ≤ toN → Inv i s →
      (∃ s', Inv (i + 1) s' ∧
        step (Int.ofNat i, s) =
          if i = toN then .ok (SudoRt.Flow.brk (Int.ofNat i, s'))
          else .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), s'))) ∨
      (∃ s', Done i s' ∧ step (Int.ofNat i, s) = .ok (SudoRt.Flow.brk (Int.ofNat i, s'))))
    (s0 : α) (h0 : Inv fromN s0) :
    ∃ j s, fromN ≤ j ∧ j ≤ toN ∧ (Inv (toN + 1) s ∨ Done j s) ∧
      SudoRt.runLoopOn (Int.ofNat fromN, s0) (fuelRange (Int.ofNat fromN) (Int.ofNat toN))
        step after onRet = after (Int.ofNat j, s) := by
  rw [fuelRange_le hle]
  obtain ⟨d, hd⟩ : ∃ d, toN - fromN = d := ⟨_, rfl⟩
  rw [hd]
  induction d generalizing fromN s0 with
  | zero =>
    have heq : fromN = toN := by omega
    subst heq
    rcases hstep fromN s0 (Nat.le_refl _) (Nat.le_refl _) h0 with
      ⟨s', hs', hst⟩ | ⟨s', hs', hst⟩
    · rw [runLoopOn_succ, hst, if_pos rfl]
      exact ⟨fromN, s', Nat.le_refl _, Nat.le_refl _, Or.inl hs', rfl⟩
    · rw [runLoopOn_succ, hst]
      exact ⟨fromN, s', Nat.le_refl _, Nat.le_refl _, Or.inr hs', rfl⟩
  | succ d ih =>
    have hne : fromN ≠ toN := by omega
    rcases hstep fromN s0 (Nat.le_refl _) hle h0 with ⟨s', hs', hst⟩ | ⟨s', hs', hst⟩
    · rw [runLoopOn_succ, hst, if_neg hne]
      obtain ⟨j, s, hj1, hj2, hs, heq⟩ := ih (fromN + 1) (by omega)
        (fun i s h1 h2 hI => hstep i s (by omega) h2 hI) s' hs' (by omega)
      exact ⟨j, s, by omega, hj2, hs, heq⟩
    · rw [runLoopOn_succ, hst]
      exact ⟨fromN, s', Nat.le_refl _, hle, Or.inr hs', rfl⟩

theorem asc_brk_goal {α ρ β}
    {step : Int × α → Except SudoRt.Trap (SudoRt.Flow (Int × α) ρ)}
    {after : Int × α → Except SudoRt.Trap β}
    {onRet : ρ → Except SudoRt.Trap β}
    (Inv : Nat → α → Prop) (Done : Nat → α → Prop) {fromN toN : Nat} {s0 : α}
    {goal : Except SudoRt.Trap β}
    (hle : fromN ≤ toN)
    (h0 : Inv fromN s0)
    (hstep : ∀ i s, fromN ≤ i → i ≤ toN → Inv i s →
      (∃ s', Inv (i + 1) s' ∧
        step (Int.ofNat i, s) =
          if i = toN then .ok (SudoRt.Flow.brk (Int.ofNat i, s'))
          else .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), s'))) ∨
      (∃ s', Done i s' ∧ step (Int.ofNat i, s) = .ok (SudoRt.Flow.brk (Int.ofNat i, s'))))
    (hpost : ∀ j s, fromN ≤ j → j ≤ toN → (Inv (toN + 1) s ∨ Done j s) →
      after (Int.ofNat j, s) = goal) :
    SudoRt.runLoopOn (Int.ofNat fromN, s0) (fuelRange (Int.ofNat fromN) (Int.ofNat toN))
      step after onRet = goal := by
  obtain ⟨j, s, hj1, hj2, hs, heq⟩ :=
    asc_brk_inv step after onRet Inv Done fromN toN hle hstep s0 h0
  rw [heq]; exact hpost j s hj1 hj2 hs

theorem subI_len_one (n : Nat) (h : FitsLen n) :
    SudoRt.subI (Int.ofNat n) 1 = .ok (Int.ofNat n - 1) := by
  cases n with
  | zero => exact subI_zero_one
  | succ m =>
    rw [subI_ofNat_one _ (Nat.succ_pos _) h]
    congr 1
    show ((m + 1 - 1 : Nat) : Int) = ((m + 1 : Nat) : Int) - 1
    omega

theorem asc_goal_upto {α ρ β}
    {step : Int × α → Except SudoRt.Trap (SudoRt.Flow (Int × α) ρ)}
    {after : Int × α → Except SudoRt.Trap β}
    {onRet : ρ → Except SudoRt.Trap β}
    (Inv : Nat → α → Prop) {n : Nat} {s0 : α} {goal : Except SudoRt.Trap β}
    (h0 : Inv 0 s0)
    (hempty : n = 0 → step (0, s0) = .ok (SudoRt.Flow.brk (0, s0)))
    (hstep : ∀ i s, i < n → Inv i s → ∃ s', Inv (i + 1) s' ∧
      step (Int.ofNat i, s) =
        if i = n - 1 then .ok (SudoRt.Flow.brk (Int.ofNat i, s'))
        else .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), s')))
    (hpost : ∀ j s, Inv n s → after (j, s) = goal) :
    SudoRt.runLoopOn ((0 : Int), s0) (fuelRange 0 (Int.ofNat n - 1)) step after onRet = goal := by
  cases n with
  | zero =>
    rw [show fuelRange 0 (Int.ofNat 0 - 1) = 0 + 1 from rfl, runLoopOn_succ, hempty rfl]
    exact hpost 0 s0 h0
  | succ m =>
    rw [show Int.ofNat (m + 1) - 1 = Int.ofNat m by
      rw [ofNat_eq_natCast, ofNat_eq_natCast]; omega]
    exact asc_goal (fromN := 0) (toN := m) Inv (Nat.zero_le _) h0
      (fun i s _ hi hI => hstep i s (by omega) hI) (fun s hs => hpost _ s hs)

theorem asc_tail_len {S ρ : Type} (n i : Nat) (hi : i < n) (hfit : FitsLen (i + 1)) (s : S) :
    (if (Int.ofNat i == Int.ofNat n - 1) = true then
        (Except.ok (SudoRt.Flow.brk (Int.ofNat i, s)) : Except SudoRt.Trap (SudoRt.Flow (Int × S) ρ))
      else SudoRt.addI (Int.ofNat i) 1 >>= fun i' => Except.ok (SudoRt.Flow.cont (i', s))) =
      if i = n - 1 then .ok (.brk (Int.ofNat i, s)) else .ok (.cont (Int.ofNat (i + 1), s)) := by
  rw [show Int.ofNat n - 1 = Int.ofNat (n - 1) by
    rw [ofNat_eq_natCast, ofNat_eq_natCast]; omega]
  exact asc_tail (n - 1) i hfit s

theorem not_gt_len {i n : Nat} (hi : i < n) : ¬ (Int.ofNat i > Int.ofNat n - 1) := by
  rw [ofNat_eq_natCast, ofNat_eq_natCast]; omega

theorem asc_scan_ret {ρ β} (rv : ρ)
    (step : Int → Except SudoRt.Trap (SudoRt.Flow Int ρ))
    (after : Int → Except SudoRt.Trap β) (onRet : ρ → Except SudoRt.Trap β)
    (bad : Nat → Bool) (fromN toN : Nat) (hle : fromN ≤ toN)
    (hstep : ∀ i, fromN ≤ i → i ≤ toN → step (Int.ofNat i) =
      if bad i then .ok (.ret rv)
      else if i = toN then .ok (.brk (Int.ofNat i)) else .ok (.cont (Int.ofNat (i + 1)))) :
    ((∀ i, fromN ≤ i → i ≤ toN → bad i = false) →
      SudoRt.runLoopOn (Int.ofNat fromN) (fuelRange (Int.ofNat fromN) (Int.ofNat toN))
        step after onRet = after (Int.ofNat toN)) ∧
    ((∃ i, fromN ≤ i ∧ i ≤ toN ∧ bad i = true) →
      SudoRt.runLoopOn (Int.ofNat fromN) (fuelRange (Int.ofNat fromN) (Int.ofNat toN))
        step after onRet = onRet rv) := by
  rw [fuelRange_le hle]
  obtain ⟨d, hd⟩ : ∃ d, toN - fromN = d := ⟨_, rfl⟩
  rw [hd]
  induction d generalizing fromN with
  | zero =>
    have heq : fromN = toN := by omega
    subst heq
    constructor
    · intro hall
      have hb := hall fromN (Nat.le_refl _) (Nat.le_refl _)
      rw [runLoopOn_succ, hstep fromN (Nat.le_refl _) (Nat.le_refl _),
        if_neg (by simp [hb]), if_pos rfl]
    · intro ⟨i, h1, h2, hb⟩
      have heq : i = fromN := by omega
      subst heq
      rw [runLoopOn_succ, hstep i (Nat.le_refl _) (Nat.le_refl _), if_pos hb]
  | succ d ih =>
    have hne : fromN ≠ toN := by omega
    have ih' := ih (fromN + 1) (by omega) (fun i h1 h2 => hstep i (by omega) h2) (by omega)
    constructor
    · intro hall
      have hb := hall fromN (Nat.le_refl _) hle
      rw [runLoopOn_succ, hstep fromN (Nat.le_refl _) hle,
        if_neg (by simp [hb]), if_neg hne]
      exact ih'.1 (fun i h1 h2 => hall i (by omega) h2)
    · intro ⟨i, h1, h2, hb⟩
      cases hf : bad fromN
      · rw [runLoopOn_succ, hstep fromN (Nat.le_refl _) hle, hf]
        simp only [Bool.false_eq_true, if_false, if_neg hne]
        have : i ≠ fromN := fun e => by subst e; rw [hf] at hb; exact absurd hb (by decide)
        exact ih'.2 ⟨i, by omega, h2, hb⟩
      · rw [runLoopOn_succ, hstep fromN (Nat.le_refl _) hle, hf]
        rfl

theorem asc_scan_ret_goal {ρ β} (rv : ρ)
    (step : Int → Except SudoRt.Trap (SudoRt.Flow Int ρ))
    (after : Int → Except SudoRt.Trap β) (onRet : ρ → Except SudoRt.Trap β)
    (bad : Nat → Bool) (fromN toN : Nat) (hle : fromN ≤ toN) (R : Except SudoRt.Trap β)
    (hstep : ∀ i, fromN ≤ i → i ≤ toN → step (Int.ofNat i) =
      if bad i then .ok (.ret rv)
      else if i = toN then .ok (.brk (Int.ofNat i)) else .ok (.cont (Int.ofNat (i + 1))))
    (hA : (∀ i, fromN ≤ i → i ≤ toN → bad i = false) → after (Int.ofNat toN) = R)
    (hB : ∀ i, fromN ≤ i → i ≤ toN → bad i = true → onRet rv = R) :
    SudoRt.runLoopOn (Int.ofNat fromN) (fuelRange (Int.ofNat fromN) (Int.ofNat toN))
      step after onRet = R := by
  have hsc := asc_scan_ret rv step after onRet bad fromN toN hle hstep
  by_cases hall : ∀ i, fromN ≤ i → i ≤ toN → bad i = false
  · rw [hsc.1 hall]; exact hA hall
  · have hex : ∃ i, fromN ≤ i ∧ i ≤ toN ∧ bad i = true := by
      apply Classical.byContradiction
      intro hne; apply hall
      intro i h1 h2
      cases h : bad i
      · rfl
      · exact absurd ⟨i, h1, h2, h⟩ hne
    obtain ⟨i, h1, h2, hb⟩ := hex
    rw [hsc.2 ⟨i, h1, h2, hb⟩]; exact hB i h1 h2 hb

theorem asc_scan_goal {β}
    (step : Int → Except SudoRt.Trap (SudoRt.Flow Int Bool))
    (after : Int → Except SudoRt.Trap β) (onRet : Bool → Except SudoRt.Trap β)
    (bad : Nat → Bool) (fromN toN : Nat) (hle : fromN ≤ toN) (R : Except SudoRt.Trap β)
    (hstep : ∀ i, fromN ≤ i → i ≤ toN → step (Int.ofNat i) =
      if bad i then .ok (.ret false)
      else if i = toN then .ok (.brk (Int.ofNat i)) else .ok (.cont (Int.ofNat (i + 1))))
    (hA : (∀ i, fromN ≤ i → i ≤ toN → bad i = false) → after (Int.ofNat toN) = R)
    (hB : ∀ i, fromN ≤ i → i ≤ toN → bad i = true → onRet false = R) :
    SudoRt.runLoopOn (Int.ofNat fromN) (fuelRange (Int.ofNat fromN) (Int.ofNat toN))
      step after onRet = R :=
  asc_scan_ret_goal false step after onRet bad fromN toN hle R hstep hA hB

/-- `asc_tail` after `simp` has turned `Int.ofNat` into a cast. -/
theorem asc_tail_cast {S ρ : Type} (toN i : Nat) (hfit : FitsLen (i + 1)) (s : S) :
    (if (i : Int) = (toN : Int) then
        (Except.ok (SudoRt.Flow.brk ((i : Int), s)) : Except SudoRt.Trap (SudoRt.Flow (Int × S) ρ))
      else SudoRt.addI (i : Int) 1 >>= fun i' => Except.ok (SudoRt.Flow.cont (i', s))) =
      if i = toN then .ok (.brk ((i : Int), s)) else .ok (.cont ((i : Int) + 1, s)) := by
  by_cases h : i = toN
  · subst h; simp
  · have hne : ¬ ((i : Int) = (toN : Int)) := by omega
    simp only [hne, if_false, h]
    rw [show (i : Int) = Int.ofNat i from rfl, addI_ofNat_one i hfit]
    rfl

theorem narrowI_small (x : Int) (h1 : -1000000 ≤ x) (h2 : x ≤ 1000000) :
    SudoRt.narrowI x = .ok x := by
  unfold SudoRt.narrowI
  have : ¬ ((x < SudoRt.i64Min || x > SudoRt.i64Max) = true) := by
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or]
    constructor
    · show ¬ x < -9223372036854775808; omega
    · show ¬ x > 9223372036854775807; omega
  rw [if_neg this]

theorem negI_one : SudoRt.negI (1 : Int) = .ok (-1) := by
  unfold SudoRt.negI
  exact narrowI_small _ (by decide) (by decide)

theorem fits_small {n : Nat} (h : n ≤ 1000000) : FitsLen n := by
  unfold FitsLen i64MaxNat
  omega

/-- The index scan `invert_checked` runs from `1` through `listLen v - 1`.
    The body reads `v[i]` and asserts it is `0` (sudo line 730). It does not
    return, and it breaks only on the last index or immediately when the range
    is empty (`length = 1`, so `1 > 0`). The `match ←` is the join the emitter
    writes: an inner `do` of type `Flow Unit`, then `.ret` / `.brk` / `.cont`. -/
def zeroScanStep (v : Array Int) (toV : Int) (i : Int) :
    Except SudoRt.Trap (SudoRt.Flow Int Ecbs.Board) :=
  do
    if i > toV then
      pure (SudoRt.Flow.brk i)
    else
      match ← ((do
        let _t1225 ← SudoRt.atL v i
        let _as1226 ← SudoRt.sudoAssertEq _t1225 (0 : Int) 730
        pure (SudoRt.Flow.cont ())) :
          Except SudoRt.Trap (SudoRt.Flow _ Ecbs.Board)) with
      | .ret r => pure (SudoRt.Flow.ret r)
      | .brk _fs => pure (SudoRt.Flow.brk i)
      | .cont _fs => do
          if i == toV then
            pure (SudoRt.Flow.brk i)
          else do
            let i' ← SudoRt.addI i (1 : Int)
            pure (SudoRt.Flow.cont i')

/-- In range, a passing read-and-assert is the last-index break or `i + 1`. -/
theorem zeroScanStep_cont (v : Array Int) (toV i c : Int)
    (hc : SudoRt.atL v i = .ok c)
    (hu : SudoRt.sudoAssertEq c (0 : Int) 730 = .ok ())
    (hng : ¬ i > toV) :
    zeroScanStep v toV i =
      (if i == toV then .ok (SudoRt.Flow.brk i)
       else SudoRt.addI i (1 : Int) >>= fun i' => pure (SudoRt.Flow.cont i')) := by
  simp only [zeroScanStep, hng, if_false, hc, hu, bind, Except.bind, pure, Except.pure]

/-- In range, a failing assert is that error. The join is not reached. -/
theorem zeroScanStep_fail (v : Array Int) (toV i c : Int) (e : SudoRt.Trap)
    (hc : SudoRt.atL v i = .ok c)
    (hu : SudoRt.sudoAssertEq c (0 : Int) 730 = .error e)
    (hng : ¬ i > toV) :
    zeroScanStep v toV i = .error e := by
  simp only [zeroScanStep, hng, if_false, hc, hu, bind, Except.bind, pure, Except.pure]

/-- `sudoAssertEq` against `0` fails at the given line, with that line in the detail. -/
theorem sudoAssertEq_ne_zero (c : Nat) (h : c ≠ 0) (line : Nat) :
    SudoRt.sudoAssertEq (Int.ofNat c) (0 : Int) line =
      .error { kind := "AssertFailed"
               detail := s!"line {line}: {SudoRt.Canon.canon (Int.ofNat c)} != {SudoRt.Canon.canon (0 : Int)}" } := by
  unfold SudoRt.sudoAssertEq SudoRt.fail
  rw [sEq_ofNat_zero, decide_eq_false h]
  rfl

/-- Hole 0 of the check product: accepted iff the coefficient is not zero.
    Rejection is sudo line 728. -/
theorem hole0_assert (c : Nat) :
    SudoRt.sudoAssert (!(SudoRt.SEq.beq (Int.ofNat c) (0 : Int))) 728 =
      if c = 0 then
        .error { kind := "AssertFailed", detail := s!"line 728" }
      else
        .ok () := by
  rw [sEq_ofNat_zero]
  by_cases h : c = 0
  · subst h
    have hdec : decide ((0 : Nat) = 0) = true := rfl
    rw [hdec, Bool.not_true]
    unfold SudoRt.sudoAssert SudoRt.fail
    rfl
  · rw [decide_eq_false h, Bool.not_false]
    unfold SudoRt.sudoAssert
    simp [h]

private theorem zeroScan_step_zero (L : List Nat) (i : Nat)
    (hi : i < L.length) (hz : L[i] = 0) (hto : i ≤ L.length - 1)
    (hf : FitsLen (i + 1)) :
    zeroScanStep (embed L) (Int.ofNat (L.length - 1)) (Int.ofNat i) =
      if i = L.length - 1 then .ok (SudoRt.Flow.brk (Int.ofNat i))
      else .ok (SudoRt.Flow.cont (Int.ofNat (i + 1))) := by
  have hng : ¬ Int.ofNat i > Int.ofNat (L.length - 1) := ofNat_not_gt hto
  have hassert : SudoRt.sudoAssertEq (Int.ofNat 0) (0 : Int) 730 = .ok () := by
    unfold SudoRt.sudoAssertEq
    rw [sEq_ofNat_zero]
    rfl
  have hc : SudoRt.atL (embed L) (Int.ofNat i) = .ok (Int.ofNat 0) := by
    rw [atL_embed L i hi, hz]
  rw [zeroScanStep_cont (embed L) (Int.ofNat (L.length - 1)) (Int.ofNat i)
    (Int.ofNat 0) hc hassert hng]
  by_cases hlast : i = L.length - 1
  · have heq : (i : Int) = ((L.length - 1 : Nat) : Int) := by rw [hlast]
    simp [heq, hlast, pure_eq_ok]
  · have hne : (i : Int) ≠ ((L.length - 1 : Nat) : Int) := by
      intro h
      exact hlast (Int.ofNat.inj (by
        rw [← ofNat_eq_natCast i, ← ofNat_eq_natCast (L.length - 1)] at h
        exact h))
    simp [hne, hlast]
    rw [show (i : Int) = Int.ofNat i from rfl]
    rw [addI_ofNat_one i hf]
    simp [pure_eq_ok]

private theorem zeroScan_step_nz (L : List Nat) (i : Nat)
    (hi : i < L.length) (hnz : L[i] ≠ 0) (hto : i ≤ L.length - 1) :
    zeroScanStep (embed L) (Int.ofNat (L.length - 1)) (Int.ofNat i) =
      .error { kind := "AssertFailed"
               detail := s!"line {730}: {SudoRt.Canon.canon (Int.ofNat L[i])} != {SudoRt.Canon.canon (0 : Int)}" } := by
  have hng : ¬ Int.ofNat i > Int.ofNat (L.length - 1) := ofNat_not_gt hto
  exact zeroScanStep_fail (embed L) (Int.ofNat (L.length - 1)) (Int.ofNat i)
    (Int.ofNat L[i]) _ (atL_embed L i hi) (sudoAssertEq_ne_zero L[i] hnz 730) hng

/-- Tail zeros from `i` through `L.length - 1`. The scan breaks into `after`
    at `L.length - 1`, or at `i` itself when `i` is already past that end
    (`L.length = 1` and `i = 1`). -/
theorem zeroScan_ok {α : Type} (L : List Nat) (i : Nat)
    (hpos : 0 < L.length) (hi : 1 ≤ i) (hiL : i ≤ L.length) (hf : FitsLen L.length)
    (htail : ∀ j, i ≤ j → ∀ hj : j < L.length, L[j] = 0)
    (after : Int → Except SudoRt.Trap α) (onRet : Ecbs.Board → Except SudoRt.Trap α) :
    SudoRt.runLoopOn (Int.ofNat i)
        (fuelRange (Int.ofNat i) (Int.ofNat (L.length - 1)))
        (fun k => zeroScanStep (embed L) (Int.ofNat (L.length - 1)) k)
        after onRet =
      after (Int.ofNat (if L.length ≤ i then i else L.length - 1)) := by
  generalize hd : L.length - i = d
  induction d generalizing i with
  | zero =>
    have hiEq : i = L.length := by omega
    have hgt : (L.length - 1 : Nat) < i := by omega
    rw [fuelRange_gt (Iff.mpr (ofNat_lt_iff (L.length - 1) i) hgt),
      show (1 : Nat) = 0 + 1 from rfl, runLoopOn_succ]
    have hstep : zeroScanStep (embed L) (Int.ofNat (L.length - 1)) (Int.ofNat i) =
        .ok (SudoRt.Flow.brk (Int.ofNat i)) := by
      unfold zeroScanStep
      rw [if_pos (Iff.mpr (ofNat_lt_iff (L.length - 1) i) (by omega : L.length - 1 < i)),
        pure_eq_ok]
    rw [hstep]
    simp [hiEq]
  | succ d ih =>
    have hiLt : i < L.length := by omega
    have hto : i ≤ L.length - 1 := by omega
    have hz : L[i]'(hiLt) = 0 := htail i (Nat.le_refl _) hiLt
    have hfi : FitsLen (i + 1) := FitsLen.of_le hf (by omega)
    rw [fuelRange_le hto, show (L.length - 1) - i + 1 = d + 1 from by omega, runLoopOn_succ]
    rw [zeroScan_step_zero L i hiLt hz hto hfi]
    by_cases hlast : i = L.length - 1
    · simp [hlast]
    · simp only [hlast, ite_false]
      have hnext : L.length - (i + 1) = d := by omega
      have htail' : ∀ j, i + 1 ≤ j → ∀ hj : j < L.length, L[j] = 0 := by
        intro j hj1 hj
        exact htail j (by omega) hj
      have hfuel : d = fuelRange (Int.ofNat (i + 1)) (Int.ofNat (L.length - 1)) := by
        rw [fuelRange_le (by omega : i + 1 ≤ L.length - 1)]
        omega
      rw [hfuel]
      have hnot : ¬ L.length ≤ i + 1 := by omega
      have hgot := ih (i + 1) (by omega) (by omega) htail' hnext
      simp only [hnot, show ¬ L.length ≤ i from by omega] at hgot ⊢
      exact hgot

/-- The first nonzero tail entry rejects the scan at sudo line 730.
    Earlier tail entries are zero, so the loop reaches that index. -/
theorem zeroScan_err {α : Type} (L : List Nat) (j : Nat)
    (hpos : 0 < L.length) (hj : 1 ≤ j) (hjL : j < L.length) (hf : FitsLen L.length)
    (hbad : L[j] ≠ 0)
    (hpre : ∀ k, 1 ≤ k → ∀ hk : k < j, L[k]'(Nat.lt_trans hk hjL) = 0)
    (after : Int → Except SudoRt.Trap α) (onRet : Ecbs.Board → Except SudoRt.Trap α) :
    SudoRt.runLoopOn (1 : Int)
        (fuelRange (1 : Int) (Int.ofNat (L.length - 1)))
        (fun k => zeroScanStep (embed L) (Int.ofNat (L.length - 1)) k)
        after onRet =
      .error { kind := "AssertFailed"
               detail := s!"line {730}: {SudoRt.Canon.canon (Int.ofNat L[j])} != {SudoRt.Canon.canon (0 : Int)}" } := by
  suffices ∀ i, 1 ≤ i → i ≤ j →
      (∀ k, i ≤ k → ∀ hk : k < j, L[k]'(Nat.lt_trans hk hjL) = 0) →
      SudoRt.runLoopOn (Int.ofNat i)
          (fuelRange (Int.ofNat i) (Int.ofNat (L.length - 1)))
          (fun k => zeroScanStep (embed L) (Int.ofNat (L.length - 1)) k)
          after onRet =
        .error { kind := "AssertFailed"
                 detail := s!"line {730}: {SudoRt.Canon.canon (Int.ofNat L[j])} != {SudoRt.Canon.canon (0 : Int)}" } by
    exact this 1 (Nat.le_refl _) hj hpre
  intro i hi hij hprei
  generalize hd : j - i = d
  induction d generalizing i with
  | zero =>
    have hEq : i = j := by omega
    have hiL : i < L.length := by omega
    have hto : i ≤ L.length - 1 := by omega
    rw [fuelRange_le hto, show (L.length - 1) - i + 1 = ((L.length - 1) - i) + 1 from rfl,
      runLoopOn_succ, hEq, zeroScan_step_nz L j (by omega) hbad (by omega)]
  | succ d ih =>
    have hlt : i < j := by omega
    have hiL : i < L.length := Nat.lt_trans hlt hjL
    have hto : i ≤ L.length - 1 := by omega
    have hz : L[i] = 0 := hprei i (Nat.le_refl _) hlt
    have hfi : FitsLen (i + 1) := FitsLen.of_le hf (by omega)
    have hnot : i ≠ L.length - 1 := by omega
    rw [fuelRange_le hto, show (L.length - 1) - i + 1 = ((L.length - 1) - i) + 1 from rfl,
      runLoopOn_succ, zeroScan_step_zero L i hiL hz hto hfi, if_neg hnot]
    have hfuel : (L.length - 1) - i =
        fuelRange (Int.ofNat (i + 1)) (Int.ofNat (L.length - 1)) := by
      rw [fuelRange_le (by omega : i + 1 ≤ L.length - 1)]
      omega
    rw [hfuel]
    exact ih (i + 1) (by omega) (by omega) (by
      intro k hk1 hk2
      exact hprei k (by omega) hk2) (by omega)

end EcbsLink2.Link2
