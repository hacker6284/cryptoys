/-
  LINK 2. Inclusive `for` loops as emitted by the Lean backend
  (`runLoopOn` + break on the last index). Proof-only.
-/
import MegaDreifach.Link2.Embed
import MegaDreifach.Link2.Sudo

namespace MegaDreifach.Link2

/-- Emitter inclusive-loop stepper, once the body has been reduced to
    `Flow.cont` of the next state (no early `ret` / `brk`). -/
def inclAfter {α ρ} (toV i : Int) (st' : α) :
    Except SudoRt.Trap (SudoRt.Flow (Int × α) ρ) :=
  if i == toV then
    .ok (SudoRt.Flow.brk (i, st'))
  else
    SudoRt.addI i (1 : Int) >>= fun i' => .ok (SudoRt.Flow.cont (i', st'))

/-- Inclusive countdown driver. `f i` is the state on entry to index `i`.
    The body stores `g i`. At `0` the loop breaks; otherwise it continues
    at `i - 1`, and `g i` must be `f (i - 1)`. -/
theorem chain_down {α ρ β}
    (step : Int × α → Except SudoRt.Trap (SudoRt.Flow (Int × α) ρ))
    (after : Int × α → Except SudoRt.Trap β)
    (onRet : ρ → Except SudoRt.Trap β)
    (f g : Nat → α) (fromN : Nat)
    (hstep : ∀ i, i ≤ fromN →
      step (Int.ofNat i, f i) =
        if i = 0 then
          .ok (SudoRt.Flow.brk (Int.ofNat i, g i))
        else
          .ok (SudoRt.Flow.cont (Int.ofNat (i - 1), g i)))
    (hlink : ∀ i, 0 < i → i ≤ fromN → g i = f (i - 1))
    (goal : Except SudoRt.Trap β)
    (hafter : after (Int.ofNat 0, g 0) = goal) :
    SudoRt.runLoopOn (Int.ofNat fromN, f fromN)
      (fuelDown (Int.ofNat fromN) 0)
      step after onRet = goal := by
  induction fromN with
  | zero =>
    rw [fuelDown_toZero, show 0 + 1 = 0 + 1 from rfl, runLoopOn_succ]
    have hs := hstep 0 (Nat.le_refl _)
    simp only [hs, ↓reduceIte]
    exact hafter
  | succ n ih =>
    have hfuel :
        fuelDown (Int.ofNat (n + 1)) 0 = fuelDown (Int.ofNat n) 0 + 1 := by
      rw [fuelDown_toZero, fuelDown_toZero]
    rw [hfuel, runLoopOn_succ]
    have hs := hstep (n + 1) (Nat.le_refl _)
    have hne : n + 1 ≠ 0 := Nat.succ_ne_zero _
    simp only [hs, hne, ↓reduceIte]
    have hnext : (n + 1) - 1 = n := by omega
    simp only [hnext, hlink (n + 1) (Nat.succ_pos _) (Nat.le_refl _)]
    exact ih (fun i hi => hstep i (Nat.le_succ_of_le hi))
      (fun i hp hi => hlink i hp (Nat.le_succ_of_le hi))

private theorem chain_idx_fromEnd {ρ β}
    (step : Int → Except SudoRt.Trap (SudoRt.Flow Int ρ))
    (after : Int → Except SudoRt.Trap β)
    (onRet : ρ → Except SudoRt.Trap β)
    (toN delta : Nat)
    (hstep : ∀ i, toN - delta ≤ i → i ≤ toN →
      step (Int.ofNat i) =
        if i = toN then
          .ok (SudoRt.Flow.brk (Int.ofNat i))
        else
          .ok (SudoRt.Flow.cont (Int.ofNat (i + 1))))
    (goal : Except SudoRt.Trap β)
    (hafter : after (Int.ofNat toN) = goal)
    (hdelta : delta ≤ toN) :
    SudoRt.runLoopOn (Int.ofNat (toN - delta))
      (fuelRange (Int.ofNat (toN - delta)) (Int.ofNat toN))
      step after onRet = goal := by
  induction delta with
  | zero =>
    rw [Nat.sub_zero, fuelRange_le (Nat.le_refl _),
      show toN - toN + 1 = 0 + 1 from by omega, runLoopOn_succ]
    have hs := hstep toN (by omega) (Nat.le_refl _)
    simp only [hs, ↓reduceIte]
    exact hafter
  | succ delta ih =>
    have hfrom_le : toN - (delta + 1) ≤ toN := Nat.sub_le _ _
    have hne : toN - (delta + 1) ≠ toN := by omega
    have hfuel :
        fuelRange (Int.ofNat (toN - (delta + 1))) (Int.ofNat toN) =
          fuelRange (Int.ofNat (toN - delta)) (Int.ofNat toN) + 1 := by
      rw [fuelRange_le hfrom_le, fuelRange_le (Nat.sub_le _ _)]
      omega
    rw [hfuel, runLoopOn_succ]
    have hs := hstep (toN - (delta + 1)) (Nat.le_refl _) hfrom_le
    simp only [hs, hne, ↓reduceIte]
    have hnext : (toN - (delta + 1)) + 1 = toN - delta := by omega
    simp only [hnext]
    exact ih (fun i hi1 hi2 => hstep i (by omega) hi2)
      (Nat.le_trans (Nat.le_succ delta) hdelta)

/-- Drive an inclusive index from `fromN` to `toN`. The index is the whole state. -/
theorem chain_idx {ρ β}
    (step : Int → Except SudoRt.Trap (SudoRt.Flow Int ρ))
    (after : Int → Except SudoRt.Trap β)
    (onRet : ρ → Except SudoRt.Trap β)
    (fromN toN : Nat)
    (hle : fromN ≤ toN)
    (hstep : ∀ i, fromN ≤ i → i ≤ toN →
      step (Int.ofNat i) =
        if i = toN then
          .ok (SudoRt.Flow.brk (Int.ofNat i))
        else
          .ok (SudoRt.Flow.cont (Int.ofNat (i + 1))))
    (goal : Except SudoRt.Trap β)
    (hafter : after (Int.ofNat toN) = goal) :
    SudoRt.runLoopOn (Int.ofNat fromN)
      (fuelRange (Int.ofNat fromN) (Int.ofNat toN))
      step after onRet = goal := by
  have hfrom : fromN = toN - (toN - fromN) := by omega
  rw [hfrom]
  exact chain_idx_fromEnd step after onRet toN (toN - fromN)
    (fun i hi1 hi2 => hstep i (by omega) hi2) goal hafter (Nat.sub_le _ _)

private theorem chain_loop_fromEnd {α ρ β}
    (step : Int × α → Except SudoRt.Trap (SudoRt.Flow (Int × α) ρ))
    (after : Int × α → Except SudoRt.Trap β)
    (onRet : ρ → Except SudoRt.Trap β)
    (f : Nat → α) (toN delta : Nat)
    (hstep : ∀ i, toN - delta ≤ i → i ≤ toN →
      step (Int.ofNat i, f i) =
        if i = toN then
          .ok (SudoRt.Flow.brk (Int.ofNat i, f (i + 1)))
        else
          .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), f (i + 1))))
    (goal : Except SudoRt.Trap β)
    (hafter : after (Int.ofNat toN, f (toN + 1)) = goal)
    (hdelta : delta ≤ toN) :
    SudoRt.runLoopOn (Int.ofNat (toN - delta), f (toN - delta))
      (fuelRange (Int.ofNat (toN - delta)) (Int.ofNat toN))
      step after onRet = goal := by
  induction delta with
  | zero =>
    rw [Nat.sub_zero, fuelRange_le (Nat.le_refl _),
      show toN - toN + 1 = 0 + 1 from by omega, runLoopOn_succ]
    have hs := hstep toN (by omega) (Nat.le_refl _)
    simp only [hs, ↓reduceIte]
    exact hafter
  | succ delta ih =>
    have hfrom_le : toN - (delta + 1) ≤ toN := Nat.sub_le _ _
    have hne : toN - (delta + 1) ≠ toN := by omega
    have hfuel :
        fuelRange (Int.ofNat (toN - (delta + 1))) (Int.ofNat toN) =
          fuelRange (Int.ofNat (toN - delta)) (Int.ofNat toN) + 1 := by
      rw [fuelRange_le hfrom_le, fuelRange_le (Nat.sub_le _ _)]
      omega
    rw [hfuel, runLoopOn_succ]
    have hs := hstep (toN - (delta + 1)) (Nat.le_refl _) hfrom_le
    simp only [hs, hne, ↓reduceIte]
    have hnext : (toN - (delta + 1)) + 1 = toN - delta := by omega
    simp only [hnext]
    exact ih (fun i hi1 hi2 => hstep i (by omega) hi2)
      (Nat.le_trans (Nat.le_succ delta) hdelta)

/-- Drive an inclusive index from `fromN` to `toN`. `f i` is the state at
    the start of iteration `i`; the body stores `f (i+1)`. The loop joins
    with `after` on the break state `(toN, f (toN+1))`. -/
theorem chain_loop {α ρ β}
    (step : Int × α → Except SudoRt.Trap (SudoRt.Flow (Int × α) ρ))
    (after : Int × α → Except SudoRt.Trap β)
    (onRet : ρ → Except SudoRt.Trap β)
    (f : Nat → α) (fromN toN : Nat)
    (hle : fromN ≤ toN)
    (hstep : ∀ i, fromN ≤ i → i ≤ toN →
      step (Int.ofNat i, f i) =
        if i = toN then
          .ok (SudoRt.Flow.brk (Int.ofNat i, f (i + 1)))
        else
          .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), f (i + 1))))
    (goal : Except SudoRt.Trap β)
    (hafter : after (Int.ofNat toN, f (toN + 1)) = goal) :
    SudoRt.runLoopOn (Int.ofNat fromN, f fromN)
      (fuelRange (Int.ofNat fromN) (Int.ofNat toN))
      step after onRet = goal := by
  have hfrom : fromN = toN - (toN - fromN) := by omega
  rw [hfrom]
  exact chain_loop_fromEnd step after onRet f toN (toN - fromN)
    (fun i hi1 hi2 => hstep i (by omega) hi2) goal hafter (Nat.sub_le _ _)

/-- Ascending loop that breaks immediately because `fromV > toV`. -/
theorem asc_break {α ρ β} (fromV toV : Int) (s : α)
    (step : Int × α → Except SudoRt.Trap (SudoRt.Flow (Int × α) ρ))
    (after : Int × α → Except SudoRt.Trap β)
    (onRet : ρ → Except SudoRt.Trap β)
    (hgt : fromV > toV)
    (hstep : step (fromV, s) = .ok (SudoRt.Flow.brk (fromV, s))) :
    SudoRt.runLoopOn (fromV, s) (fuelRange fromV toV) step after onRet =
      after (fromV, s) := by
  rw [fuelRange_gt hgt, show 1 = 0 + 1 from rfl, runLoopOn_succ, hstep]

theorem idx_break {ρ β} (fromV toV : Int)
    (step : Int → Except SudoRt.Trap (SudoRt.Flow Int ρ))
    (after : Int → Except SudoRt.Trap β)
    (onRet : ρ → Except SudoRt.Trap β)
    (hgt : fromV > toV)
    (hstep : step fromV = .ok (SudoRt.Flow.brk fromV)) :
    SudoRt.runLoopOn fromV (fuelRange fromV toV) step after onRet = after fromV := by
  rw [fuelRange_gt hgt, show 1 = 0 + 1 from rfl, runLoopOn_succ, hstep]

/-- Range-copy stepper in the shape Lean leaves after unfolding emit. -/
def copyStep (ρ : Type) (xs : Array Int) (toV : Int) (σ : Int × Array Int) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Array Int) ρ) :=
  if σ.1 > toV then
    pure (SudoRt.Flow.brk (ρ := ρ) (σ.1, σ.2))
  else do
    let lift ←
      ((do
        let t ← SudoRt.atL xs σ.1
        pure (SudoRt.Flow.cont (ρ := ρ) (SudoRt.appendL σ.2 t).1)) :
        Except SudoRt.Trap (SudoRt.Flow (Array Int) ρ))
    match lift with
    | .ret r => pure (SudoRt.Flow.ret (ρ := ρ) r)
    | .brk fs => pure (SudoRt.Flow.brk (ρ := ρ) (σ.1, fs))
    | .cont fs =>
      if (σ.1 == toV) = true then
        pure (SudoRt.Flow.brk (ρ := ρ) (σ.1, fs))
      else do
        let i' ← SudoRt.addI σ.1 (1 : Int)
        pure (SudoRt.Flow.cont (ρ := ρ) (i', fs))

theorem copyStep_gt (ρ : Type) (xs : Array Int) (toV i : Int) (acc : Array Int)
    (h : i > toV) :
    copyStep ρ xs toV (i, acc) = .ok (.brk (i, acc)) := by
  unfold copyStep
  rw [if_pos h]
  rfl

theorem copyStep_hit (ρ : Type) (xs : Array Int) (toN fromN : Nat) (acc : Array Int)
    (hfrom : fromN ≤ toN) (hidx : fromN < xs.size) (hfits : FitsLen xs.size) :
    copyStep ρ xs (Int.ofNat toN) (Int.ofNat fromN, acc) =
      if fromN = toN then
        .ok (.brk (Int.ofNat fromN, acc.push (xs.get ⟨fromN, hidx⟩)))
      else
        .ok (.cont ((fromN : Int) + 1, acc.push (xs.get ⟨fromN, hidx⟩))) := by
  unfold copyStep
  dsimp
  have hngt : ¬ (fromN : Int) > (toN : Int) :=
    Int.not_lt.mpr (Int.ofNat_le.mpr hfrom)
  rw [if_neg hngt]
  have hat : SudoRt.atL xs (fromN : Int) = .ok (xs.get ⟨fromN, hidx⟩) :=
    ofNat_eq_natCast fromN ▸ atL_ofNat xs fromN hidx
  simp [hat, SudoRt.appendL]
  by_cases heq : fromN = toN
  · subst heq
    have hbeq : ((fromN : Int) == (fromN : Int)) = true := by simp
    simp [hbeq]
    rfl
  · have hneInt : ¬ (fromN : Int) = (toN : Int) := fun h => heq (Int.ofNat.inj h)
    rw [if_neg hneInt]
    have hadd : SudoRt.addI (fromN : Int) 1 = .ok ((fromN : Int) + 1) := by
      have h := addI_ofNat_one fromN (FitsLen.of_le hfits (Nat.succ_le_of_lt hidx))
      rw [ofNat_eq_natCast fromN] at h
      rwa [← natCast_succ fromN] at h
    rw [hadd, map_ok, if_neg heq]

/-- Append a constant. `for i = from to toV: out.append(v)`. -/
def pushStep (ρ : Type) (v toV : Int) (σ : Int × Array Int) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Array Int) ρ) :=
  if σ.1 > toV then
    pure (SudoRt.Flow.brk (ρ := ρ) (σ.1, σ.2))
  else do
    let lift ←
      ((do
        pure (SudoRt.Flow.cont (ρ := ρ) (SudoRt.appendL σ.2 v).1)) :
        Except SudoRt.Trap (SudoRt.Flow (Array Int) ρ))
    match lift with
    | .ret r => pure (SudoRt.Flow.ret (ρ := ρ) r)
    | .brk fs => pure (SudoRt.Flow.brk (ρ := ρ) (σ.1, fs))
    | .cont fs =>
      if (σ.1 == toV) = true then
        pure (SudoRt.Flow.brk (ρ := ρ) (σ.1, fs))
      else do
        let i' ← SudoRt.addI σ.1 (1 : Int)
        pure (SudoRt.Flow.cont (ρ := ρ) (i', fs))

theorem pushStep_gt (ρ : Type) (v toV i : Int) (acc : Array Int) (h : i > toV) :
    pushStep ρ v toV (i, acc) = .ok (.brk (i, acc)) := by
  unfold pushStep
  rw [if_pos h]
  rfl

theorem pushStep_hit (ρ : Type) (v : Int) (toN fromN : Nat) (acc : Array Int)
    (hfrom : fromN ≤ toN) (hfits : FitsLen (fromN + 1)) :
    pushStep ρ v (Int.ofNat toN) (Int.ofNat fromN, acc) =
      if fromN = toN then
        .ok (.brk (Int.ofNat fromN, acc.push v))
      else
        .ok (.cont (Int.ofNat (fromN + 1), acc.push v)) := by
  unfold pushStep
  dsimp
  have hngt : ¬ (fromN : Int) > (toN : Int) := ofNat_not_gt hfrom
  rw [if_neg hngt]
  simp [SudoRt.appendL]
  by_cases heq : fromN = toN
  · subst heq
    simp [beq_int_iff]
    rfl
  · have hneI : ¬ (fromN : Int) = (toN : Int) := fun h => heq (Int.ofNat.inj h)
    have hadd := addI_ofNat_one fromN hfits
    rw [ofNat_eq_natCast fromN] at hadd
    rw [if_neg hneI, hadd, map_ok, if_neg heq, natCast_succ]

/-- Byte-range scan: `for i = 0 to len-1: assert 0 ≤ xs[i] ≤ 255`. State is the index. -/
def byteCheckStep (xs : Array Int) (toV : Int) (i : Int) :
    Except SudoRt.Trap (SudoRt.Flow Int (Array Int)) := do
  if i > toV then
    pure (SudoRt.Flow.brk (ρ := Array Int) i)
  else
    match ←
      ((do
        let b ← SudoRt.atL xs i
        let ok ← (if (decide (b ≥ (0 : Int))) then (do
          let b2 ← SudoRt.atL xs i
          pure (decide (b2 ≤ (255 : Int)))) else pure false)
        let u ← SudoRt.sudoAssert ok 483
        pure (SudoRt.Flow.cont (ρ := Array Int) ())) :
        Except SudoRt.Trap (SudoRt.Flow Unit (Array Int))) with
    | .ret r => pure (SudoRt.Flow.ret (ρ := Array Int) r)
    | .brk _fs => pure (SudoRt.Flow.brk (ρ := Array Int) i)
    | .cont _fs => do
        if i == toV then
          pure (SudoRt.Flow.brk (ρ := Array Int) i)
        else do
          let i' ← SudoRt.addI i (1 : Int)
          pure (SudoRt.Flow.cont (ρ := Array Int) i')

theorem byteCheckStep_gt (xs : Array Int) (toV i : Int) (h : i > toV) :
    byteCheckStep xs toV i = .ok (.brk i) := by
  unfold byteCheckStep
  rw [if_pos h]
  rfl

theorem byteCheckStep_hit (xs : List Nat) (toN i : Nat)
    (hle : i ≤ toN) (hi : i < xs.length) (hb : Byte xs[i]) (hfits : FitsLen xs.length) :
    byteCheckStep (embed xs) (Int.ofNat toN) (Int.ofNat i) =
      if i = toN then .ok (.brk (Int.ofNat i))
      else .ok (.cont (Int.ofNat (i + 1))) := by
  unfold byteCheckStep
  dsimp
  have hngt : ¬ (i : Int) > (toN : Int) := ofNat_not_gt hle
  rw [if_neg hngt]
  have hat := atL_embed xs i hi
  rw [show (i : Int) = Int.ofNat i from rfl, hat]
  simp only [ok_bind]
  have hnn : decide (Int.ofNat (xs[i]) ≥ (0 : Int)) = true := by
    rw [decide_eq_true_eq]
    exact Int.ofNat_zero_le _
  have hleB : decide (Int.ofNat (xs[i]) ≤ (255 : Int)) = true := by
    rw [decide_eq_true_eq]
    exact Int.ofNat_le.mpr hb
  rw [hnn, hleB]
  have hif :
      (if true = true then (pure true : Except SudoRt.Trap Bool) else pure false) = pure true := by
    simp
  rw [hif]
  rw [show (pure true : Except SudoRt.Trap Bool) = .ok true from rfl, ok_bind, sudoAssert_true]
  rw [show (pure (SudoRt.Flow.cont () : SudoRt.Flow Unit (Array Int)) :
        Except SudoRt.Trap _) = .ok (.cont ()) from rfl, ok_bind]
  by_cases heq : i = toN
  · subst heq
    simp [beq_int_iff]
    rfl
  · have hneI : ¬ (i : Int) = (toN : Int) := fun h => heq (Int.ofNat.inj h)
    have hfit : FitsLen (i + 1) := FitsLen.succ_le hi hfits
    have hadd := addI_ofNat_one i hfit
    rw [ofNat_eq_natCast i] at hadd
    rw [ok_bind, ite_int_beq]
    dsimp
    rw [if_neg hneI, hadd, ok_bind, if_neg heq]
    rfl

end MegaDreifach.Link2
