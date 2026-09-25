/-
  LINK 2. Lemmas about the emitted runtime (`SudoRt`) on the well-formed
  domain. Proof-only. Not emitter soundness.
-/
import SudoRt
import MegaDreifach.Link2.Embed

namespace MegaDreifach.Link2

/-! ## Except -/

@[simp] theorem ok_bind {ε α β} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := rfl

@[simp] theorem error_bind {ε α β} (e : ε) (f : α → Except ε β) :
    (Except.error e >>= f) = Except.error e := rfl

/-- `do let x ← m; pure x` is `m`. Generated `pure _out` after `runLoopOn`. -/
theorem except_bind_pure {ε α} (m : Except ε α) :
    (do let x ← m; pure x) = m := by
  cases m <;> rfl

@[simp] theorem map_ok {ε α β} (f : α → β) (a : α) :
    (f <$> (Except.ok a : Except ε α)) = Except.ok (f a) := rfl

theorem bind_match_flow {σ ρ α}
    (m : Except SudoRt.Trap (SudoRt.Flow σ ρ))
    (onRet : ρ → Except SudoRt.Trap α)
    (after : σ → Except SudoRt.Trap α) :
    (do
      match ← m with
      | .ret r => onRet r
      | .brk s => after s
      | .cont s => after s) =
      match m with
      | .error e => .error e
      | .ok (.ret r) => onRet r
      | .ok (.brk s) => after s
      | .ok (.cont s) => after s := by
  cases m with
  | error e => simp
  | ok fl => cases fl <;> simp

/-! ## Int / i64 helpers -/

theorem i64Min_lt_zero : SudoRt.i64Min < 0 := by decide

theorem ofNat_eq_natCast (n : Nat) : Int.ofNat n = (↑n : Int) := rfl

theorem ofNat_succ (n : Nat) : (Int.ofNat n) + 1 = Int.ofNat (n + 1) := by
  simp [Int.ofNat_add]

theorem natCast_succ (n : Nat) : (n : Int) + 1 = Int.ofNat (n + 1) :=
  ofNat_succ n

theorem narrowI_ofNat (n : Nat) (h : FitsLen n) :
    SudoRt.narrowI (Int.ofNat n) = .ok (Int.ofNat n) := by
  unfold SudoRt.narrowI
  split
  · next ht =>
    simp at ht
    have hle : (n : Int) ≤ SudoRt.i64Max := by
      have : SudoRt.i64Max = (i64MaxNat : Int) := i64MaxNat_spec.symm
      rw [this]
      exact Int.ofNat_le.mpr h
    have hge : SudoRt.i64Min ≤ (n : Int) := by
      have : SudoRt.i64Min < 0 := i64Min_lt_zero
      have : (0 : Int) ≤ (n : Int) := Int.ofNat_zero_le n
      omega
    omega
  · rfl

theorem addI_ofNat (a b : Nat) (h : FitsLen (a + b)) :
    SudoRt.addI (Int.ofNat a) (Int.ofNat b) = .ok (Int.ofNat (a + b)) := by
  unfold SudoRt.addI
  have : Int.ofNat a + Int.ofNat b = Int.ofNat (a + b) := rfl
  rw [this]
  exact narrowI_ofNat (a + b) h

theorem addI_ofNat_one (n : Nat) (h : FitsLen (n + 1)) :
    SudoRt.addI (Int.ofNat n) 1 = .ok (Int.ofNat (n + 1)) := by
  have : (1 : Int) = Int.ofNat 1 := rfl
  rw [this]
  exact addI_ofNat n 1 h

theorem subI_ofNat (a b : Nat) (hfits : FitsLen a) (hle : b ≤ a) :
    SudoRt.subI (Int.ofNat a) (Int.ofNat b) = .ok (Int.ofNat (a - b)) := by
  unfold SudoRt.subI
  have : Int.ofNat a - Int.ofNat b = Int.ofNat (a - b) := by
    rw [ofNat_eq_natCast a, ofNat_eq_natCast b, ← Int.ofNat_sub hle,
        ofNat_eq_natCast]
  rw [this]
  exact narrowI_ofNat (a - b) (FitsLen.of_le hfits (Nat.sub_le _ _))

theorem subI_ofNat_one (n : Nat) (hpos : 0 < n) (h : FitsLen n) :
    SudoRt.subI (Int.ofNat n) 1 = .ok (Int.ofNat (n - 1)) := by
  have : (1 : Int) = Int.ofNat 1 := rfl
  rw [this]
  exact subI_ofNat n 1 h (Nat.succ_le_of_lt hpos)

theorem subI_zero_one : SudoRt.subI (0 : Int) 1 = .ok (-1) := by
  unfold SudoRt.subI SudoRt.narrowI
  split
  · next ht =>
    simp at ht
    have : ¬ (-1 : Int) < SudoRt.i64Min := by decide
    have : ¬ (-1 : Int) > SudoRt.i64Max := by decide
    omega
  · rfl

theorem mulI_ofNat (a b : Nat) (h : FitsLen (a * b)) :
    SudoRt.mulI (Int.ofNat a) (Int.ofNat b) = .ok (Int.ofNat (a * b)) := by
  unfold SudoRt.mulI
  have : Int.ofNat a * Int.ofNat b = Int.ofNat (a * b) := rfl
  rw [this]
  exact narrowI_ofNat (a * b) h

theorem ofNat_ne_zero {b : Nat} (hb : b ≠ 0) : (b : Int) ≠ 0 := by
  intro h
  exact hb (Int.ofNat.inj h)

theorem fdiv_ofNat (a b : Nat) :
    Int.fdiv (Int.ofNat a) (Int.ofNat b) = Int.ofNat (a / b) := by
  cases a <;> cases b <;> simp [Int.fdiv]

theorem fmod_ofNat (a b : Nat) :
    Int.fmod (Int.ofNat a) (Int.ofNat b) = Int.ofNat (a % b) := by
  cases a <;> cases b <;> simp [Int.fmod]

theorem beq_int_iff (x y : Int) : (x == y) = true ↔ x = y := by
  simp [BEq.beq, decide_eq_true_eq]

theorem ite_int_beq {α} (x y : Int) (t e : α) :
    (if x == y then t else e) = (if x = y then t else e) := by
  by_cases h : x = y
  · simp [h, beq_int_iff]
  · simp [h, beq_int_iff]

theorem divI_ofNat (a : Nat) {b : Nat} (hb : b ≠ 0) :
    SudoRt.divI (Int.ofNat a) (Int.ofNat b) = .ok (Int.ofNat (a / b)) := by
  unfold SudoRt.divI
  split
  · next h0 =>
    have : Int.ofNat b = 0 := (beq_int_iff _ _).mp h0
    exact absurd (Int.ofNat.inj this) hb
  · split
    · next hmin =>
      have : (0 : Int) ≤ Int.ofNat a := Int.ofNat_zero_le a
      have : SudoRt.i64Min < 0 := i64Min_lt_zero
      simp [Bool.and_eq_true, beq_int_iff] at hmin
    · exact congrArg Except.ok (fdiv_ofNat a b)

theorem divI_cast (a : Nat) {b : Nat} (hb : b ≠ 0) :
    SudoRt.divI (a : Int) (b : Int) = .ok (Int.ofNat (a / b)) := by
  rw [← ofNat_eq_natCast a, ← ofNat_eq_natCast b]
  exact divI_ofNat a hb

theorem modI_ofNat (a : Nat) {b : Nat} (hb : b ≠ 0) :
    SudoRt.modI (Int.ofNat a) (Int.ofNat b) = .ok (Int.ofNat (a % b)) := by
  unfold SudoRt.modI
  split
  · next h0 =>
    have : Int.ofNat b = 0 := (beq_int_iff _ _).mp h0
    exact absurd (Int.ofNat.inj this) hb
  · exact congrArg Except.ok (fmod_ofNat a b)

theorem mulI_cast (a b : Nat) (h : FitsLen (a * b)) :
    SudoRt.mulI (a : Int) (b : Int) = .ok (Int.ofNat (a * b)) := by
  rw [← ofNat_eq_natCast a, ← ofNat_eq_natCast b]
  exact mulI_ofNat a b h

theorem addI_cast (a b : Nat) (h : FitsLen (a + b)) :
    SudoRt.addI (a : Int) (b : Int) = .ok (Int.ofNat (a + b)) := by
  rw [← ofNat_eq_natCast a, ← ofNat_eq_natCast b]
  exact addI_ofNat a b h

theorem modI_cast (a : Nat) {b : Nat} (hb : b ≠ 0) :
    SudoRt.modI (a : Int) (b : Int) = .ok (Int.ofNat (a % b)) := by
  rw [← ofNat_eq_natCast a, ← ofNat_eq_natCast b]
  exact modI_ofNat a hb

/-! ## Arrays / lists -/

theorem listLen_eq (a : Array α) : SudoRt.listLen a = Int.ofNat a.size := rfl

theorem listLen_embed (xs : List Nat) : SudoRt.listLen (embed xs) = Int.ofNat xs.length := by
  rw [listLen_eq, size_embed]

theorem sEq_int (x y : Int) : SudoRt.SEq.beq x y = decide (x = y) := rfl

theorem ofNat_eq_zero_iff (n : Nat) : Int.ofNat n = (0 : Int) ↔ n = 0 :=
  ⟨fun h => Int.ofNat.inj (h.trans (rfl : (0 : Int) = Int.ofNat 0)),
   fun h => h ▸ rfl⟩

theorem ofNat_pos_iff (n : Nat) : Int.ofNat n > (0 : Int) ↔ 0 < n := by
  change Int.ofNat 0 < Int.ofNat n ↔ 0 < n
  exact Int.ofNat_lt

theorem ofNat_lt_iff (a b : Nat) : Int.ofNat a < Int.ofNat b ↔ a < b :=
  Int.ofNat_lt

theorem ofNat_le_iff (a b : Nat) : Int.ofNat a ≤ Int.ofNat b ↔ a ≤ b :=
  Int.ofNat_le

theorem ofNat_not_gt {a b : Nat} (h : a ≤ b) : ¬ Int.ofNat a > Int.ofNat b :=
  Int.not_lt.mpr (Int.ofNat_le.mpr h)

theorem sEq_ofNat_zero (n : Nat) :
    SudoRt.SEq.beq (Int.ofNat n) (0 : Int) = decide (n = 0) := by
  rw [sEq_int, decide_eq_decide, ofNat_eq_zero_iff]

theorem decide_ofNat_pos (n : Nat) :
    decide (Int.ofNat n > (0 : Int)) = decide (0 < n) := by
  rw [decide_eq_decide, ofNat_pos_iff]

theorem decide_ofNat_le (a b : Nat) :
    decide (Int.ofNat a ≤ Int.ofNat b) = decide (a ≤ b) := by
  rw [decide_eq_decide, ofNat_le_iff]

theorem sudoAssert_true (line : Nat) : SudoRt.sudoAssert true line = .ok () := rfl

theorem appendL_spec (a : Array α) (v : α) : SudoRt.appendL a v = (a.push v, ()) := rfl

theorem idxCheck_ofNat (len i : Nat) (h : i < len) :
    SudoRt.idxCheck len (Int.ofNat i) = .ok i := by
  unfold SudoRt.idxCheck
  split
  · next ht =>
    simp at ht
    have : ¬ (i : Int) < 0 := Int.not_lt.mpr (Int.ofNat_zero_le i)
    have : ¬ len ≤ i := Nat.not_le_of_lt h
    omega
  · rfl

theorem atL_ofNat (a : Array α) (i : Nat) (h : i < a.size) :
    SudoRt.atL a (Int.ofNat i) = .ok a[i] := by
  unfold SudoRt.atL
  rw [idxCheck_ofNat a.size i h]
  simp only [ok_bind]
  exact dif_pos h

theorem atL_embed (xs : List Nat) (i : Nat) (h : i < xs.length) :
    SudoRt.atL (embed xs) (Int.ofNat i) = .ok (Int.ofNat (xs[i])) := by
  have hsz : i < (embed xs).size := by rw [size_embed]; exact h
  rw [atL_ofNat (embed xs) i hsz, get_embed]

theorem putL_ofNat (a : Array α) (i : Nat) (v : α) (h : i < a.size) :
    SudoRt.putL a (Int.ofNat i) v = .ok (a.set ⟨i, h⟩ v) := by
  unfold SudoRt.putL
  rw [idxCheck_ofNat a.size i h]
  simp only [ok_bind]
  exact dif_pos h

theorem filledL_ofNat (n : Nat) (v : α) :
    SudoRt.filledL (Int.ofNat n) v = .ok (Array.mkArray n v) := by
  unfold SudoRt.filledL
  have hnn : ¬ (Int.ofNat n) < 0 := Int.not_lt.mpr (Int.ofNat_zero_le n)
  rw [if_neg hnn]
  rfl

/-! ## `natIter` / `runLoopOn` unfolding -/

theorem natIter_succ_do {σ ρ}
    (step : σ → Except SudoRt.Trap (SudoRt.Flow σ ρ)) (fuel : Nat) (s : σ) :
    SudoRt.natIter (ρ := ρ) (fuel + 1) step s =
      (do
        match ← step s with
        | .ret r => pure (.ret r)
        | .brk s => pure (.brk s)
        | .cont s => SudoRt.natIter (ρ := ρ) fuel step s) :=
  rfl

theorem runLoopOn_def {σ ρ α} (s0 : σ) (fuel : Nat)
    (step : σ → Except SudoRt.Trap (SudoRt.Flow σ ρ))
    (after : σ → Except SudoRt.Trap α)
    (onRet : ρ → Except SudoRt.Trap α) :
    SudoRt.runLoopOn (ρ := ρ) s0 fuel step after onRet =
      match SudoRt.natIter (ρ := ρ) fuel step s0 with
      | .error e => .error e
      | .ok (.ret r) => onRet r
      | .ok (.brk s) => after s
      | .ok (.cont s) => after s := by
  simp only [SudoRt.runLoopOn, SudoRt.natIterOn]
  exact bind_match_flow (SudoRt.natIter (ρ := ρ) fuel step s0) onRet after

theorem runLoopOn_step_pointwise {σ ρ α} (s0 : σ) (fuel : Nat)
    (step step' : σ → Except SudoRt.Trap (SudoRt.Flow σ ρ))
    (h : ∀ s, step s = step' s)
    (after : σ → Except SudoRt.Trap α)
    (onRet : ρ → Except SudoRt.Trap α) :
    SudoRt.runLoopOn (ρ := ρ) s0 fuel step after onRet =
      SudoRt.runLoopOn (ρ := ρ) s0 fuel step' after onRet := by
  rw [show step = step' from funext h]

theorem runLoopOn_succ {σ ρ α} (s0 : σ) (fuel : Nat)
    (step : σ → Except SudoRt.Trap (SudoRt.Flow σ ρ))
    (after : σ → Except SudoRt.Trap α)
    (onRet : ρ → Except SudoRt.Trap α) :
    SudoRt.runLoopOn (ρ := ρ) s0 (fuel + 1) step after onRet =
      match step s0 with
      | .error e => .error e
      | .ok (.ret r) => onRet r
      | .ok (.brk s) => after s
      | .ok (.cont s) => SudoRt.runLoopOn (ρ := ρ) s fuel step after onRet := by
  rw [runLoopOn_def, natIter_succ_do]
  cases step s0 with
  | error e => simp
  | ok fl =>
    cases fl with
    | ret r => rfl
    | brk s => rfl
    | cont s =>
      simp
      exact (runLoopOn_def s fuel step after onRet).symm

theorem toList_push (a : Array Int) (x : Int) : (a.push x).toList = a.toList ++ [x] := by
  simp [Array.push, List.concat_eq_append]

theorem mk_toList (a : Array Int) : Array.mk a.toList = a := by
  cases a
  rfl

def fuelRange (fromV toV : Int) : Nat :=
  if fromV > toV then 1 else (toV - fromV).natAbs + 1

theorem fuelRange_gt {fromV toV : Int} (h : fromV > toV) : fuelRange fromV toV = 1 := by
  simp [fuelRange, h]

theorem fuelRange_le {fromN toN : Nat} (h : fromN ≤ toN) :
    fuelRange (Int.ofNat fromN) (Int.ofNat toN) = toN - fromN + 1 := by
  have hngt : ¬ (fromN : Int) > (toN : Int) :=
    Int.not_lt.mpr (Int.ofNat_le.mpr h)
  have hsub : ((toN : Int) - (fromN : Int)).natAbs = toN - fromN := by
    have : (toN : Int) - (fromN : Int) = ((toN - fromN : Nat) : Int) := by
      simp [Int.ofNat_sub h]
    rw [this, Int.natAbs_ofNat]
  simp [fuelRange, hngt, hsub]

theorem fuelRange_eq (fromV toV : Int) :
    (if fromV > toV then 1 else (toV - fromV).natAbs + 1) = fuelRange fromV toV :=
  rfl

/-- Descending fuel: `for i = from downto to`. -/
def fuelDown (fromV toV : Int) : Nat :=
  if fromV < toV then 1 else (fromV - toV).natAbs + 1

theorem fuelDown_lt {fromV toV : Int} (h : fromV < toV) : fuelDown fromV toV = 1 := by
  simp [fuelDown, h]

theorem fuelDown_le {fromN toN : Nat} (h : toN ≤ fromN) :
    fuelDown (Int.ofNat fromN) (Int.ofNat toN) = fromN - toN + 1 := by
  have hnlt : ¬ (fromN : Int) < (toN : Int) :=
    Int.not_lt.mpr (Int.ofNat_le.mpr h)
  have hsub : ((fromN : Int) - (toN : Int)).natAbs = fromN - toN := by
    have : (fromN : Int) - (toN : Int) = ((fromN - toN : Nat) : Int) := by
      simp [Int.ofNat_sub h]
    rw [this, Int.natAbs_ofNat]
  simp [fuelDown, hnlt, hsub]

theorem fuelDown_eq (fromV toV : Int) :
    (if fromV < toV then 1 else (fromV - toV).natAbs + 1) = fuelDown fromV toV :=
  rfl

theorem fuelDown_toZero (n : Nat) : fuelDown (Int.ofNat n) 0 = n + 1 := by
  have hz : (0 : Int) = Int.ofNat 0 := rfl
  rw [hz, fuelDown_le (Nat.zero_le n), Nat.sub_zero]

end MegaDreifach.Link2
