/-
  The white scan and the cube-peg loop never return `Flow.ret`. Their checked
  blocks end in `Flow.cont`; a failing check is an `Except` trap. `Flow.brk` is
  only the inclusive-loop stop (`j > toV` or `j == toV`).

  A loop whose body never returns can therefore bind its `after` as a
  continuation. The generated nest (the cube loop, mul, and clear are the white
  scan's `after`, and a `ret` would skip them) is that bind. `climbClear`
  sequences the same scan and then discards the index. The two `onRet`
  handlers need not agree: the `ret` arm is empty.

  `tally_len_fuel` is the generated `subI` / `natAbs` fuel. `last_beq_isEmpty`
  is `beq idx (nr - 1)` against `(L.drop (i + 1)).isEmpty`.
-/
import EcbsLink2.Link2.IdxFold

namespace EcbsLink2.Link2

open MegaDreifach.Link2

/-- The checked block inside `whiteStep` succeeds only as `Flow.cont`. -/
theorem whiteScan_cont (b : Ecbs.Board) (j : Int)
    (fl : SudoRt.Flow Unit Ecbs.Board)
    (h : (do
        let ix ← SudoRt.addI b.sudo_5Board_6tally0 j
        let c ← SudoRt.atL b.sudo_5Board_3row ix
        let _ ← SudoRt.sudoAssertEq c (1 : Int) 703
        pure (SudoRt.Flow.cont (ρ := Ecbs.Board) ())) = .ok fl) :
    fl = .cont () := by
  cases hix : SudoRt.addI b.sudo_5Board_6tally0 j with
  | error _ =>
    rw [hix] at h
    simp only [error_bind] at h
    cases h
  | ok ix =>
    rw [hix] at h
    simp only [ok_bind] at h
    cases hc : SudoRt.atL b.sudo_5Board_3row ix with
    | error _ =>
      rw [hc] at h
      simp only [error_bind] at h
      cases h
    | ok c =>
      rw [hc] at h
      simp only [ok_bind] at h
      cases ha : SudoRt.sudoAssertEq c (1 : Int) 703 with
      | error _ =>
        rw [ha] at h
        simp only [error_bind] at h
        cases h
      | ok _ =>
        simp only [ha, ok_bind, pure_eq_ok] at h
        cases h
        rfl

/-- `whiteStep` is `.brk`, `.cont`, or a trap. The `.ret` arm matches a block
    that only returns `.cont`. -/
theorem whiteStep_no_ret (b : Ecbs.Board) (toV j : Int) (r : Ecbs.Board) :
    whiteStep b toV j ≠ .ok (SudoRt.Flow.ret r) := by
  intro h
  unfold whiteStep at h
  by_cases hgt : j > toV
  · rw [if_pos hgt, pure_eq_ok] at h
    cases h
  · rw [if_neg hgt] at h
    generalize hix :
      SudoRt.addI b.sudo_5Board_6tally0 j = eix at h
    cases eix with
    | error _ =>
      simp only [error_bind] at h
      cases h
    | ok ix =>
      simp only [ok_bind] at h
      generalize hc : SudoRt.atL b.sudo_5Board_3row ix = ec at h
      cases ec with
      | error _ =>
        simp only [error_bind] at h
        cases h
      | ok c =>
        simp only [ok_bind] at h
        generalize ha : SudoRt.sudoAssertEq c (1 : Int) 703 = ea at h
        cases ea with
        | error _ =>
          simp only [error_bind] at h
          cases h
        | ok _ =>
          simp only [ok_bind, pure_eq_ok, map_ok] at h
          by_cases hbeq : (j == toV) = true
          · rw [if_pos hbeq] at h
            cases h
          · rw [if_neg hbeq] at h
            cases hj : SudoRt.addI j (1 : Int) with
            | error _ =>
              rw [hj, error_bind] at h
              cases h
            | ok _ =>
              rw [hj, ok_bind] at h
              cases h

/-- `cubePegBody` wrapped as `Flow.cont` succeeds only as `Flow.cont`. -/
theorem cubePegBody_cont (src : Nat) (b : Ecbs.Board) (j : Int)
    (fl : SudoRt.Flow Ecbs.Board Ecbs.Board)
    (h : (cubePegBody src b j >>= fun b' =>
        pure (SudoRt.Flow.cont (ρ := Ecbs.Board) b')) = .ok fl) :
    ∃ (b' : Ecbs.Board), fl = .cont b' := by
  cases hb : cubePegBody src b j with
  | error _ =>
    rw [hb, error_bind] at h
    cases h
  | ok b' =>
    rw [hb, ok_bind, pure_eq_ok] at h
    cases h
    exact ⟨b', rfl⟩

/-- `cubePegStep` is `.brk`, `.cont`, or a trap. The `.ret` arm matches a
    block that only returns `.cont`. -/
theorem cubePegStep_no_ret (src : Nat) (toV : Int) (σ : Int × Ecbs.Board)
    (r : Ecbs.Board) :
    cubePegStep src toV σ ≠ .ok (SudoRt.Flow.ret r) := by
  intro h
  unfold cubePegStep at h
  dsimp only at h
  by_cases hgt : σ.1 > toV
  · rw [if_pos hgt, pure_eq_ok] at h
    cases h
  · rw [if_neg hgt] at h
    cases hb : cubePegBody src σ.2 σ.1 with
    | error _ =>
      rw [hb] at h
      simp only [error_bind] at h
      cases h
    | ok b' =>
      simp only [hb, ok_bind, pure_eq_ok, map_ok] at h
      by_cases hbeq : (σ.1 == toV) = true
      · rw [if_pos hbeq] at h
        cases h
      · rw [if_neg hbeq] at h
        cases hj : SudoRt.addI σ.1 (1 : Int) with
        | error _ =>
          rw [hj, error_bind] at h
          cases h
        | ok _ =>
          rw [hj, ok_bind] at h
          cases h

theorem natIter_zero {σ ρ : Type}
    (step : σ → Except SudoRt.Trap (SudoRt.Flow σ ρ)) (s : σ) :
    SudoRt.natIter (ρ := ρ) 0 step s =
      SudoRt.fail "StackOverflow" "loop fuel exhausted" := rfl

theorem runLoopOn_zero {σ ρ α : Type} (s0 : σ)
    (step : σ → Except SudoRt.Trap (SudoRt.Flow σ ρ))
    (after : σ → Except SudoRt.Trap α)
    (onRet : ρ → Except SudoRt.Trap α) :
    SudoRt.runLoopOn (ρ := ρ) s0 0 step after onRet =
      SudoRt.fail "StackOverflow" "loop fuel exhausted" := by
  rw [runLoopOn_def, natIter_zero]
  rfl

/-- A body that never returns `Flow.ret` makes `onRet` dead. The loop with a
    real `after` is the loop that returns its state, bound into `after`.
    The two `onRet` handlers are not used. -/
theorem runLoopOn_after_split {σ ρ α : Type}
    (s0 : σ) (fuel : Nat)
    (step : σ → Except SudoRt.Trap (SudoRt.Flow σ ρ))
    (after : σ → Except SudoRt.Trap α)
    (onRet : ρ → Except SudoRt.Trap α)
    (onRetId : ρ → Except SudoRt.Trap σ)
    (hno : ∀ s r, step s ≠ Except.ok (SudoRt.Flow.ret r)) :
    SudoRt.runLoopOn (ρ := ρ) s0 fuel step after onRet =
      (SudoRt.runLoopOn (ρ := ρ) s0 fuel step (fun s => pure s) onRetId) >>= after := by
  induction fuel generalizing s0 with
  | zero =>
    rw [runLoopOn_zero, runLoopOn_zero]
    unfold SudoRt.fail
    rw [error_bind]
  | succ fuel ih =>
    rw [runLoopOn_succ, runLoopOn_succ]
    cases hst : step s0 with
    | error _ =>
      rw [error_bind]
    | ok fl =>
      cases fl with
      | ret r =>
        exact absurd hst (hno s0 r)
      | brk s =>
        change after s = ((pure s : Except SudoRt.Trap σ) >>= after)
        rw [pure_eq_ok, ok_bind]
      | cont s =>
        exact ih s

/-- The packed `after` is discarded, so it agrees with binding straight into
    a continuation that ignores the state. -/
theorem runLoopOn_discard {σ ρ β α : Type}
    (s0 : σ) (fuel : Nat)
    (step : σ → Except SudoRt.Trap (SudoRt.Flow σ ρ))
    (pack : σ → β)
    (k : Except SudoRt.Trap α)
    (onRetPack : ρ → Except SudoRt.Trap β)
    (onRetId : ρ → Except SudoRt.Trap σ)
    (hno : ∀ s r, step s ≠ Except.ok (SudoRt.Flow.ret r)) :
    ((SudoRt.runLoopOn (ρ := ρ) s0 fuel step (fun s => pure (pack s)) onRetPack) >>=
        fun _ => k) =
      (SudoRt.runLoopOn (ρ := ρ) s0 fuel step (fun s => pure s) onRetId) >>=
        fun _ => k := by
  rw [runLoopOn_after_split s0 fuel step (fun s => pure (pack s)) onRetPack onRetId hno]
  rw [bind_assoc
      (SudoRt.runLoopOn (ρ := ρ) s0 fuel step (fun s => pure s) onRetId)
      (fun s => pure (pack s))
      (fun _ => k)]
  have hd :
      (fun s => (pure (pack s) : Except SudoRt.Trap β) >>= fun _ => k) =
        fun _ => k := by
    funext s
    rw [pure_eq_ok, ok_bind]
  rw [hd]

/-- Generated white nest (`after` is the rest of the rung) against `climbClear`'s
    scan, which returns `(b, j)` and then ignores it. -/
theorem whiteStep_nest {α : Type}
    (b : Ecbs.Board) (toV j0 : Int) (fuel : Nat)
    (cube : Except SudoRt.Trap α)
    (onRetW : Ecbs.Board → Except SudoRt.Trap (Ecbs.Board × Int))
    (onRetN : Ecbs.Board → Except SudoRt.Trap α)
    (onRetId : Ecbs.Board → Except SudoRt.Trap Int) :
    ((SudoRt.runLoopOn j0 fuel (whiteStep b toV)
        (fun j => Except.ok (b, j)) onRetW) >>= fun _ => cube) =
      SudoRt.runLoopOn j0 fuel (whiteStep b toV) (fun _ => cube) onRetN := by
  have hpure :
      (fun j => (Except.ok (b, j) : Except SudoRt.Trap (Ecbs.Board × Int))) =
        fun j => pure (b, j) := by
    funext j
    exact (pure_eq_ok (b, j)).symm
  rw [hpure]
  rw [runLoopOn_discard j0 fuel (whiteStep b toV) (fun j => (b, j)) cube
      onRetW onRetId (fun s r => whiteStep_no_ret b toV s r)]
  rw [runLoopOn_after_split j0 fuel (whiteStep b toV) (fun _ => cube)
      onRetN onRetId (fun s r => whiteStep_no_ret b toV s r)]

/-- Generated cube-peg nest against `climbClear`, which returns the pair and
    then continues from its board. -/
theorem cubePegStep_nest {α : Type}
    (src : Nat) (toV : Int) (s0 : Int × Ecbs.Board) (fuel : Nat)
    (rest : Int × Ecbs.Board → Except SudoRt.Trap α)
    (onRetG : Ecbs.Board → Except SudoRt.Trap α)
    (onRetC : Ecbs.Board → Except SudoRt.Trap (Int × Ecbs.Board))
    (onRetId : Ecbs.Board → Except SudoRt.Trap (Int × Ecbs.Board)) :
    SudoRt.runLoopOn s0 fuel (cubePegStep src toV) rest onRetG =
      (SudoRt.runLoopOn s0 fuel (cubePegStep src toV) (fun σ => Except.ok σ) onRetC) >>=
        rest := by
  have hpure :
      (fun σ => (Except.ok σ : Except SudoRt.Trap (Int × Ecbs.Board))) =
        fun σ => pure σ := by
    funext σ
    exact (pure_eq_ok σ).symm
  rw [hpure]
  rw [runLoopOn_after_split s0 fuel (cubePegStep src toV) rest onRetG onRetId
      (fun s r => cubePegStep_no_ret src toV s r)]
  rw [runLoopOn_after_split s0 fuel (cubePegStep src toV) (fun σ => pure σ) onRetC onRetId
      (fun s r => cubePegStep_no_ret src toV s r)]
  rw [except_bind_pure
      (SudoRt.runLoopOn s0 fuel (cubePegStep src toV) (fun σ => pure σ) onRetId)]

/-- `b.tally_len = Int.ofNat m` with `0 < m` makes the generated fuel the
    inclusive range `fuelRange` uses. -/
theorem tally_len_fuel (m : Nat) (hm : 0 < m) (hfit : FitsLen m) :
    SudoRt.subI (Int.ofNat m) 1 = .ok (Int.ofNat (m - 1)) ∧
    (if (0 : Int) > Int.ofNat (m - 1) then (1 : Nat)
      else (Int.ofNat (m - 1) - (0 : Int)).natAbs + 1) =
      fuelRange (Int.ofNat 0) (Int.ofNat (m - 1)) := by
  refine ⟨subI_ofNat_one m hm hfit, ?_⟩
  have hng : ¬ ((0 : Int) > Int.ofNat (m - 1)) :=
    Int.not_lt.mpr (Int.ofNat_zero_le (m - 1))
  rw [if_neg hng, fuelRange_le (Nat.zero_le (m - 1)), Int.sub_zero,
    ofNat_eq_natCast (m - 1), Int.natAbs_ofNat, Nat.sub_zero]

/-- `beq idx (length - 1)` is `(L.drop (i + 1)).isEmpty` on a real index. -/
theorem last_flag (L : List Nat) (i : Nat) (hi : i < L.length) :
    SudoRt.SEq.beq (Int.ofNat i) (Int.ofNat (L.length - 1)) =
      (L.drop (i + 1)).isEmpty := by
  rw [drop_isEmpty_eq L (i + 1) (Nat.succ_le_of_lt hi), sEq_int]
  exact decide_eq_decide.mpr <|
    ⟨fun h => by
      have hi0 : i = L.length - 1 := Int.ofNat.inj h
      omega,
    fun h => by
      have hi0 : i = L.length - 1 := by omega
      rw [hi0]⟩

/-- The generated `subI nr 1` then `beq` is that same flag. -/
theorem last_beq_isEmpty (L : List Nat) (i : Nat) (hi : i < L.length)
    (hfit : FitsLen L.length) :
    (do
      let t ← SudoRt.subI (Int.ofNat L.length) (1 : Int)
      pure (SudoRt.SEq.beq (Int.ofNat i) t)) =
      .ok ((L.drop (i + 1)).isEmpty) := by
  have hpos : 0 < L.length := by omega
  rw [subI_ofNat_one L.length hpos hfit, ok_bind, pure_eq_ok, last_flag L i hi]

end EcbsLink2.Link2
