/-
  BS Link 2: invariant-style drivers for the emitted inclusive `for` loops
  (`runLoopOn` + break on the last index), ascending and descending. The MegaDreifach
  drivers (`chain_loop`, `chain_down`) need the state at every index as a function; these
  only need an invariant that each iteration preserves. Also an early-`break` driver and an
  index-only scan driver for loops that return early. Proof-only.
-/
import MegaDreifach.Link2.Loop

namespace BsLink2.Link2

open MegaDreifach.Link2

/-- Ascending `for i = fromN to toN` with an invariant: `Inv i s` holds on entry to
    iteration `i`; the loop joins `after` with a state satisfying `Inv (toN + 1)`. -/
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

/-- Descending `for i = fromN downto toN` with an invariant: `Inv (i + 1) s` holds on
    entry to iteration `i` (everything above `i` is done); the loop joins `after` with a
    state satisfying `Inv toN`. -/
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

/-- `asc_inv` in goal form: `apply` it to an emitted loop and the step, after and
    onRet functions are read off the goal. -/
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

/-- `asc_goal` for a loop followed by more code (`let x ← loop; k x`). -/
theorem asc_goal_bind {α ρ β γ}
    {step : Int × α → Except SudoRt.Trap (SudoRt.Flow (Int × α) ρ)}
    {after : Int × α → Except SudoRt.Trap β}
    {onRet : ρ → Except SudoRt.Trap β}
    {k : β → Except SudoRt.Trap γ}
    (Inv : Nat → α → Prop) {fromN toN : Nat} {s0 : α} {goal : Except SudoRt.Trap γ}
    (hle : fromN ≤ toN)
    (h0 : Inv fromN s0)
    (hstep : ∀ i s, fromN ≤ i → i ≤ toN → Inv i s → ∃ s', Inv (i + 1) s' ∧
      step (Int.ofNat i, s) =
        if i = toN then .ok (SudoRt.Flow.brk (Int.ofNat i, s'))
        else .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), s')))
    (hpost : ∀ s, Inv (toN + 1) s → (after (Int.ofNat toN, s) >>= k) = goal) :
    (SudoRt.runLoopOn (Int.ofNat fromN, s0) (fuelRange (Int.ofNat fromN) (Int.ofNat toN))
      step after onRet >>= k) = goal := by
  obtain ⟨s, hs, heq⟩ := asc_inv step after onRet Inv fromN toN hle hstep s0 h0
  rw [heq, hpost s hs]

/-- `desc_inv` in goal form. -/
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

/-- `asc_inv` for an existential goal `∃ r, loop = .ok r ∧ P r`. -/
theorem asc_exists {α ρ β}
    {step : Int × α → Except SudoRt.Trap (SudoRt.Flow (Int × α) ρ)}
    {after : Int × α → Except SudoRt.Trap β}
    {onRet : ρ → Except SudoRt.Trap β}
    (Inv : Nat → α → Prop) {fromN toN : Nat} {s0 : α} {P : β → Prop}
    (hle : fromN ≤ toN)
    (h0 : Inv fromN s0)
    (hstep : ∀ i s, fromN ≤ i → i ≤ toN → Inv i s → ∃ s', Inv (i + 1) s' ∧
      step (Int.ofNat i, s) =
        if i = toN then .ok (SudoRt.Flow.brk (Int.ofNat i, s'))
        else .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), s')))
    (hpost : ∀ s, Inv (toN + 1) s → ∃ r, after (Int.ofNat toN, s) = .ok r ∧ P r) :
    ∃ r, SudoRt.runLoopOn (Int.ofNat fromN, s0) (fuelRange (Int.ofNat fromN) (Int.ofNat toN))
      step after onRet = .ok r ∧ P r := by
  obtain ⟨s, hs, heq⟩ := asc_inv step after onRet Inv fromN toN hle hstep s0 h0
  rw [heq]; exact hpost s hs

/-- `asc_exists` for a loop followed by more code. -/
theorem asc_exists_bind {α ρ β γ}
    {step : Int × α → Except SudoRt.Trap (SudoRt.Flow (Int × α) ρ)}
    {after : Int × α → Except SudoRt.Trap β}
    {onRet : ρ → Except SudoRt.Trap β}
    {k : β → Except SudoRt.Trap γ}
    (Inv : Nat → α → Prop) {fromN toN : Nat} {s0 : α} {P : γ → Prop}
    (hle : fromN ≤ toN)
    (h0 : Inv fromN s0)
    (hstep : ∀ i s, fromN ≤ i → i ≤ toN → Inv i s → ∃ s', Inv (i + 1) s' ∧
      step (Int.ofNat i, s) =
        if i = toN then .ok (SudoRt.Flow.brk (Int.ofNat i, s'))
        else .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), s')))
    (hpost : ∀ s, Inv (toN + 1) s → ∃ r, (after (Int.ofNat toN, s) >>= k) = .ok r ∧ P r) :
    ∃ r, (SudoRt.runLoopOn (Int.ofNat fromN, s0) (fuelRange (Int.ofNat fromN) (Int.ofNat toN))
      step after onRet >>= k) = .ok r ∧ P r := by
  obtain ⟨s, hs, heq⟩ := asc_inv step after onRet Inv fromN toN hle hstep s0 h0
  rw [heq]; exact hpost s hs

/-- `desc_inv` for an existential goal. -/
theorem desc_exists {α ρ β}
    {step : Int × α → Except SudoRt.Trap (SudoRt.Flow (Int × α) ρ)}
    {after : Int × α → Except SudoRt.Trap β}
    {onRet : ρ → Except SudoRt.Trap β}
    (Inv : Nat → α → Prop) {fromN toN : Nat} {s0 : α} {P : β → Prop}
    (hle : toN ≤ fromN)
    (h0 : Inv (fromN + 1) s0)
    (hstep : ∀ i s, toN ≤ i → i ≤ fromN → Inv (i + 1) s → ∃ s', Inv i s' ∧
      step (Int.ofNat i, s) =
        if i = toN then .ok (SudoRt.Flow.brk (Int.ofNat i, s'))
        else .ok (SudoRt.Flow.cont (Int.ofNat (i - 1), s')))
    (hpost : ∀ s, Inv toN s → ∃ r, after (Int.ofNat toN, s) = .ok r ∧ P r) :
    ∃ r, SudoRt.runLoopOn (Int.ofNat fromN, s0) (fuelDown (Int.ofNat fromN) (Int.ofNat toN))
      step after onRet = .ok r ∧ P r := by
  obtain ⟨s, hs, heq⟩ := desc_inv step after onRet Inv fromN toN hle hstep s0 h0
  rw [heq]; exact hpost s hs

/-- Ascending `for i = fromN to toN` that may `break` early: each iteration either
    keeps the invariant (and continues, or ends the loop at `toN`) or breaks with a state
    satisfying `Done i` at the iteration `i` it breaks in. The loop joins `after` at some
    index `j` with a state satisfying `Inv (toN + 1)` or `Done j`. -/
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
    ∃ j s, (Inv (toN + 1) s ∨ Done j s) ∧
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
      exact ⟨fromN, s', Or.inl hs', rfl⟩
    · rw [runLoopOn_succ, hst]
      exact ⟨fromN, s', Or.inr hs', rfl⟩
  | succ d ih =>
    have hne : fromN ≠ toN := by omega
    rcases hstep fromN s0 (Nat.le_refl _) hle h0 with ⟨s', hs', hst⟩ | ⟨s', hs', hst⟩
    · rw [runLoopOn_succ, hst, if_neg hne]
      exact ih (fromN + 1) (by omega)
        (fun i s h1 h2 hI => hstep i s (by omega) h2 hI) s' hs' (by omega)
    · rw [runLoopOn_succ, hst]
      exact ⟨fromN, s', Or.inr hs', rfl⟩

/-- `asc_brk_inv` for an existential goal `∃ r, loop = .ok r ∧ P r`. -/
theorem asc_brk_exists {α ρ β}
    {step : Int × α → Except SudoRt.Trap (SudoRt.Flow (Int × α) ρ)}
    {after : Int × α → Except SudoRt.Trap β}
    {onRet : ρ → Except SudoRt.Trap β}
    (Inv : Nat → α → Prop) (Done : Nat → α → Prop) {fromN toN : Nat} {s0 : α} {P : β → Prop}
    (hle : fromN ≤ toN)
    (h0 : Inv fromN s0)
    (hstep : ∀ i s, fromN ≤ i → i ≤ toN → Inv i s →
      (∃ s', Inv (i + 1) s' ∧
        step (Int.ofNat i, s) =
          if i = toN then .ok (SudoRt.Flow.brk (Int.ofNat i, s'))
          else .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), s'))) ∨
      (∃ s', Done i s' ∧ step (Int.ofNat i, s) = .ok (SudoRt.Flow.brk (Int.ofNat i, s'))))
    (hpost : ∀ j s, (Inv (toN + 1) s ∨ Done j s) → ∃ r, after (Int.ofNat j, s) = .ok r ∧ P r) :
    ∃ r, SudoRt.runLoopOn (Int.ofNat fromN, s0) (fuelRange (Int.ofNat fromN) (Int.ofNat toN))
      step after onRet = .ok r ∧ P r := by
  obtain ⟨j, s, hs, heq⟩ := asc_brk_inv step after onRet Inv Done fromN toN hle hstep s0 h0
  rw [heq]; exact hpost j s hs

/-- `len - 1` for a list length that may be 0 (the bound of `for i = 0 to xs.length - 1`). -/
theorem subI_len_one (n : Nat) (h : FitsLen n) :
    SudoRt.subI (Int.ofNat n) 1 = .ok (Int.ofNat n - 1) := by
  cases n with
  | zero => exact subI_zero_one
  | succ m =>
    rw [subI_ofNat_one _ (Nat.succ_pos _) h]
    congr 1
    show ((m + 1 - 1 : Nat) : Int) = ((m + 1 : Nat) : Int) - 1
    omega

/-- `for i = 0 to n - 1` over a list of length `n`, possibly empty: with `n = 0` the
    emitted loop breaks at once (`0 > -1`) and joins `after` with the start state. -/
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

/-- The tail of an emitted `for i = 0 to n - 1` (bound `Int.ofNat n - 1`). -/
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

/-- Ascending index-only `for` loop that returns `false` at the first bad index. -/
theorem asc_scan {β}
    (step : Int → Except SudoRt.Trap (SudoRt.Flow Int Bool))
    (after : Int → Except SudoRt.Trap β) (onRet : Bool → Except SudoRt.Trap β)
    (bad : Nat → Bool) (fromN toN : Nat) (hle : fromN ≤ toN)
    (hstep : ∀ i, fromN ≤ i → i ≤ toN → step (Int.ofNat i) =
      if bad i then .ok (.ret false)
      else if i = toN then .ok (.brk (Int.ofNat i)) else .ok (.cont (Int.ofNat (i + 1)))) :
    ((∀ i, fromN ≤ i → i ≤ toN → bad i = false) →
      SudoRt.runLoopOn (Int.ofNat fromN) (fuelRange (Int.ofNat fromN) (Int.ofNat toN))
        step after onRet = after (Int.ofNat toN)) ∧
    ((∃ i, fromN ≤ i ∧ i ≤ toN ∧ bad i = true) →
      SudoRt.runLoopOn (Int.ofNat fromN) (fuelRange (Int.ofNat fromN) (Int.ofNat toN))
        step after onRet = onRet false) := by
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
      rw [runLoopOn_succ, hstep i (Nat.le_refl _) (Nat.le_refl _),
        if_pos hb]
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

/-- `asc_scan` in goal form. -/
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
      step after onRet = R := by
  have hsc := asc_scan step after onRet bad fromN toN hle hstep
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

/-- `asc_tail` in the shape `simp` leaves it (casts, `decide` gone). -/
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

/-- `do let x ← m; .ok x` is `m` (the `pure _out` tail once `pure` is `Except.ok`). -/
theorem bind_ok_right {ε α} (m : Except ε α) : (m >>= fun x => Except.ok x) = m := by
  cases m <;> rfl

/-- Pick the result of the first action of a `do` block before choosing the witness. -/
theorem exists_bind {ε α β γ} {m : Except ε α} {k : α → Except ε β} {Q : γ → Prop}
    {rhs : γ → Except ε β} (P : α → Prop) (hm : ∃ r, m = .ok r ∧ P r)
    (hk : ∀ r, P r → ∃ s', Q s' ∧ k r = rhs s') :
    ∃ s', Q s' ∧ (m >>= k) = rhs s' := by
  obtain ⟨r, hr, hp⟩ := hm
  rw [hr]
  exact hk r hp

/-- `desc_tail_to` in the shape `simp` leaves it. -/
theorem desc_tail_cast {S ρ : Type} (i toN : Nat) (hle : toN ≤ i) (hfit : FitsLen i) (s : S) :
    (if (i : Int) = (toN : Int) then
        (Except.ok (SudoRt.Flow.brk ((i : Int), s)) : Except SudoRt.Trap (SudoRt.Flow (Int × S) ρ))
      else SudoRt.subI (i : Int) 1 >>= fun i' => Except.ok (SudoRt.Flow.cont (i', s))) =
      if i = toN then .ok (.brk ((i : Int), s)) else .ok (.cont (((i - 1 : Nat) : Int), s)) := by
  by_cases h : i = toN
  · subst h; simp
  · have hne : ¬ ((i : Int) = (toN : Int)) := by omega
    simp only [hne, if_false, h]
    rw [show (i : Int) = Int.ofNat i from rfl, subI_ofNat_one i (by omega) hfit]
    rfl

/-- The tail of an emitted descending loop `for i = from downto toN`. -/
theorem desc_tail_to {S ρ : Type} (i toN : Nat) (hle : toN ≤ i) (hfit : FitsLen i) (s : S) :
    (if (Int.ofNat i == Int.ofNat toN) = true then
        (Except.ok (SudoRt.Flow.brk (Int.ofNat i, s)) : Except SudoRt.Trap (SudoRt.Flow (Int × S) ρ))
      else SudoRt.subI (Int.ofNat i) 1 >>= fun i' => Except.ok (SudoRt.Flow.cont (i', s))) =
      if i = toN then .ok (.brk (Int.ofNat i, s)) else .ok (.cont (Int.ofNat (i - 1), s)) := by
  by_cases h : i = toN
  · subst h; simp [beq_int_iff]
  · have hne : ¬ (Int.ofNat i = Int.ofNat toN) := fun e => h (Int.ofNat.inj e)
    simp only [beq_int_iff, hne, if_false, h]
    rw [subI_ofNat_one i (by omega) hfit]
    rfl

end BsLink2.Link2
