/-
  The emitted search index is `searchStep` on every state the loop can reach.
  The strip loop is `emittedStrip` and the power loop is `powRun`, by
  congruence of the loop bodies. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.BasePointEq
import EcbsLink2.Link2.SearchGo
import EcbsLink2.Link2.LoopCongr
import EcbsLink2.Link2.ScanSplit

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open Ecbs
open EcbsLink2.Spec

/-- Paint one strip hole: an even index is red, an odd index stays. -/
def stripPaint (i : Int) (strip : Array Int) : Except SudoRt.Trap (Array Int) :=
  do
    let t ← SudoRt.modI i (2 : Int)
    if SudoRt.SEq.beq t (0 : Int) then
      SudoRt.putL strip i (2 : Int)
    else
      pure strip

private theorem root_paint_flow {ρ : Type} (i : Int) (strip : Array Int) :
    ((do
        let t ← SudoRt.modI i (2 : Int)
        if SudoRt.SEq.beq t (0 : Int) then
          do
            let strip ← SudoRt.putL strip i (2 : Int)
            pure (SudoRt.Flow.cont (ρ := ρ) strip)
        else
          pure (SudoRt.Flow.cont (ρ := ρ) strip)) :
        Except SudoRt.Trap (SudoRt.Flow (Array Int) ρ)) =
      (stripPaint i strip >>= fun s => pure (SudoRt.Flow.cont (ρ := ρ) s)) := by
  unfold stripPaint
  cases hm : SudoRt.modI i (2 : Int) with
  | error _ =>
    simp only [hm, error_bind]
  | ok t =>
    simp only [hm, ok_bind]
    by_cases hb : SudoRt.SEq.beq t (0 : Int) = true
    · rw [hb]
      rfl
    · rw [if_neg hb, if_neg hb]
      rfl

private theorem strip_paint_flow {ρ : Type} (i : Int) (strip : Array Int) :
    ((do
        let t ← SudoRt.modI i (2 : Int)
        if SudoRt.SEq.beq t (0 : Int) then
          do
            let ix := i
            let strip ← SudoRt.putL strip ix (2 : Int)
            let strip := strip
            pure (SudoRt.Flow.cont (ρ := ρ) strip)
        else
          do
            pure (SudoRt.Flow.cont (ρ := ρ) strip)) :
        Except SudoRt.Trap (SudoRt.Flow (Array Int) ρ)) =
      (stripPaint i strip >>= fun s => pure (SudoRt.Flow.cont (ρ := ρ) s)) := by
  unfold stripPaint
  cases hm : SudoRt.modI i (2 : Int) with
  | error _ =>
    simp only [hm, error_bind]
  | ok t =>
    simp only [hm, ok_bind]
    by_cases hb : SudoRt.SEq.beq t (0 : Int) = true
    · rw [hb]
      rfl
    · simp only [if_neg hb, pure_eq_ok, ok_bind]

/-- The emitted strip step never returns. Both arms of the paint are `cont`. -/
theorem emittedStripStep_noret (toV : Int) (σ : Int × Array Int) (r : Int × Board) :
    emittedStripStep toV σ ≠ .ok (SudoRt.Flow.ret r) := by
  intro h
  unfold emittedStripStep at h
  dsimp only at h
  by_cases hgt : σ.1 > toV
  · rw [if_pos hgt, pure_eq_ok] at h
    cases h
  · rw [if_neg hgt] at h
    have hflow := strip_paint_flow (ρ := Int × Board) σ.1 σ.2
    rw [hflow] at h
    cases hp : stripPaint σ.1 σ.2 with
    | error _ =>
      rw [hp, error_bind] at h
      cases h
    | ok s =>
      simp only [hp, ok_bind, pure_eq_ok, map_ok] at h
      by_cases hbeq : (σ.1 == toV) = true
      · rw [if_pos hbeq] at h
        cases h
      · rw [if_neg hbeq] at h
        cases ha : SudoRt.addI σ.1 (1 : Int) with
        | error _ =>
          rw [ha, error_bind] at h
          cases h
        | ok _ =>
          rw [ha, ok_bind] at h
          cases h

/-- `rootStripStep` never returns. The paint is the same `cont`. -/
theorem rootStripStep_noret (toV : Int) (σ : Int × Array Int) (r : Array Int) :
    rootStripStep toV σ ≠ .ok (SudoRt.Flow.ret r) := by
  intro h
  unfold rootStripStep at h
  dsimp only at h
  by_cases hgt : σ.1 > toV
  · rw [if_pos hgt, pure_eq_ok] at h
    cases h
  · rw [if_neg hgt] at h
    have hflow := root_paint_flow (ρ := Array Int) σ.1 σ.2
    rw [hflow] at h
    cases hp : stripPaint σ.1 σ.2 with
    | error _ =>
      rw [hp, error_bind] at h
      cases h
    | ok s =>
      simp only [hp, ok_bind, pure_eq_ok, map_ok] at h
      by_cases hbeq : (σ.1 == toV) = true
      · rw [if_pos hbeq] at h
        cases h
      · rw [if_neg hbeq] at h
        cases ha : SudoRt.addI σ.1 (1 : Int) with
        | error _ =>
          rw [ha, error_bind] at h
          cases h
        | ok _ =>
          rw [ha, ok_bind] at h
          cases h

/-- The emitted strip body and `rootStripStep` take the same branch.
    The `ret` payload is the only difference, and neither step returns. -/
theorem strip_step_act (toV : Int) (σ : Int × Array Int) :
    loopAct (emittedStripStep toV σ) = loopAct (rootStripStep toV σ) := by
  unfold emittedStripStep rootStripStep
  dsimp only
  by_cases hgt : σ.1 > toV
  · rw [if_pos hgt, if_pos hgt, pure_eq_ok, pure_eq_ok]
    rfl
  · rw [if_neg hgt, if_neg hgt]
    have hem := strip_paint_flow (ρ := Int × Board) σ.1 σ.2
    have hrt := root_paint_flow (ρ := Array Int) σ.1 σ.2
    rw [hem, hrt]
    cases hp : stripPaint σ.1 σ.2 with
    | error e =>
      simp only [hp, error_bind, map_ok, loopAct]
    | ok s =>
      simp only [hp, ok_bind, pure_eq_ok, map_ok]
      by_cases hbeq : (σ.1 == toV) = true
      · rw [if_pos hbeq, if_pos hbeq]
        rfl
      · rw [if_neg hbeq, if_neg hbeq]
        cases ha : SudoRt.addI σ.1 (1 : Int) with
        | error _ =>
          simp only [ha, error_bind, loopAct]
        | ok i' =>
          simp only [ha, ok_bind, pure_eq_ok, loopAct]

/-- The emitted strip loop, including the final white peg, is `emittedStrip`. -/
theorem emitted_strip_loop (n : Nat) :
    SudoRt.runLoopOn (Int.ofNat 0, Array.mkArray n (0 : Int))
        (fuelRange (Int.ofNat 0) (Int.ofNat (n - 2)))
        (emittedStripStep (Int.ofNat (n - 2)))
        (fun σ =>
          SudoRt.subI (Int.ofNat n) (2 : Int) >>= fun ix =>
            SudoRt.putL σ.2 ix (1 : Int))
        (fun _ : Int × Board => pure (Array.mkArray n (0 : Int))) =
      emittedStrip n := by
  rw [emittedStrip]
  exact runLoopOn_act
    (Int.ofNat 0, Array.mkArray n (0 : Int))
    (fuelRange (Int.ofNat 0) (Int.ofNat (n - 2)))
    (emittedStripStep (Int.ofNat (n - 2)))
    (rootStripStep (Int.ofNat (n - 2)))
    (fun s => strip_step_act _ s)
    (fun s r => emittedStripStep_noret _ s r)
    (fun s r => rootStripStep_noret _ s r)
    (fun σ =>
      SudoRt.subI (Int.ofNat n) (2 : Int) >>= fun ix =>
        SudoRt.putL σ.2 ix (1 : Int))
    (fun _ => pure (Array.mkArray n (0 : Int)))
    (fun r => pure r)

/-- The card's digit branch is `powDigitRun`. Digit 2 copies the gap;
    any other positive digit copies the bottom; zero only settles. -/
theorem pow_from_digit (b : Board) (d : Nat) :
    (do
        let b ← marker_lift b
        let b ← cube b up up
        if !(SudoRt.SEq.beq (Int.ofNat d) (0 : Int)) then
          do
            if SudoRt.SEq.beq (Int.ofNat d) (2 : Int) then
              do
                let b ← copy_band b spare gap false
                let b ← mul b up up spare false false false
                let b ← clear b up
                settle b
            else
              do
                let b ← copy_band b spare bottom false
                let b ← mul b up up spare false false false
                let b ← clear b up
                settle b
        else
          settle b) =
      powDigitRun b d (if d = 2 then powGap else powBottom) := by
  rw [sEq_ofNat_zero d]
  have htwo : SudoRt.SEq.beq (Int.ofNat d) (2 : Int) = decide (d = 2) := by
    rw [show (2 : Int) = Int.ofNat 2 from rfl, sEq_ofNat]
  by_cases h0 : d = 0
  · rw [h0, decide_eq_true rfl, Bool.not_true]
    unfold powDigitRun
    simp only [if_pos rfl, powUp]
    rfl
  · rw [decide_eq_false h0, Bool.not_false]
    unfold powDigitRun
    simp only [if_neg h0, powUp, powSpare]
    rw [htwo]
    by_cases h2 : d = 2
    · rw [h2, decide_eq_true rfl]
      simp only [if_pos rfl, powGap]
      rfl
    · rw [decide_eq_false h2]
      simp only [if_neg h2, powBottom]
      rfl

theorem rootStrip_len (n : Nat) (hn : 2 ≤ n) : (rootStrip n).length = n := by
  rw [rootStrip_eq n hn]
  simp [rootDigits, List.length_append, List.length_map, List.length_range]
  omega

theorem rootStrip_digit (n i : Nat) (hn : 2 ≤ n) (hi : i ≤ n - 2) :
    (rootStrip n)[i]'(by rw [rootStrip_len n hn]; omega) = rootDigit n i := by
  have hlen : (rootDigits n).length = n - 1 := by simp [rootDigits]
  have hiD : i < (rootDigits n).length := by rw [hlen]; omega
  have h? : (rootStrip n)[i]? = some (rootDigit n i) := by
    rw [rootStrip_eq n hn, List.getElem?_append_left hiD, List.getElem?_eq_getElem hiD]
    simp [rootDigits, List.getElem_map, List.getElem_range]
  rw [List.getElem?_eq_getElem (by rw [rootStrip_len n hn]; omega)] at h?
  exact Option.some.inj h?

private theorem pull3 (m : Except SudoRt.Trap Board)
    (f g : Board → Except SudoRt.Trap Board) :
    (do
        let b ← m
        let b ← f b
        let b ← g b
        Except.ok (SudoRt.Flow.cont (ρ := Int × Board) b)) =
      (do
        let b ← (do
          let b ← m
          let b ← f b
          g b)
        Except.ok (SudoRt.Flow.cont (ρ := Int × Board) b)) := by
  cases m with
  | error _ => simp [Except.map]
  | ok a =>
    simp only [ok_bind]
    cases f a with
    | error _ => simp [Except.map]
    | ok _ =>
      simp only [ok_bind]

private theorem pull6 (m : Except SudoRt.Trap Board)
    (f1 f2 f3 f4 f5 : Board → Except SudoRt.Trap Board) :
    (do
        let b ← m
        let b ← f1 b
        let b ← f2 b
        let b ← f3 b
        let b ← f4 b
        let b ← f5 b
        Except.ok (SudoRt.Flow.cont (ρ := Int × Board) b)) =
      (do
        let b ← (do
          let b ← m
          let b ← f1 b
          let b ← f2 b
          let b ← f3 b
          let b ← f4 b
          f5 b)
        Except.ok (SudoRt.Flow.cont (ρ := Int × Board) b)) := by
  cases m with
  | error _ => simp [Except.map]
  | ok a =>
    simp only [ok_bind]
    cases f1 a with
    | error _ => simp [Except.map]
    | ok a =>
      simp only [ok_bind]
      cases f2 a with
      | error _ => simp [Except.map]
      | ok a =>
        simp only [ok_bind]
        cases f3 a with
        | error _ => simp [Except.map]
        | ok a =>
          simp only [ok_bind]
          cases f4 a with
          | error _ => simp [Except.map]
          | ok _ =>
            simp only [ok_bind]

/-- One emitted power index, once the strip is the root strip. The body is
    `powDigitRun` of that digit, then the usual break-or-step. -/
theorem emitted_pow_at (n i : Nat) (strip : Array Int) (b : Board)
    (hn : 2 ≤ n) (hi : i ≤ n - 2) (hfit : FitsLen (i + 1))
    (hstrip : strip = embed (rootStrip n)) :
    emittedPowStep strip (Int.ofNat (n - 2)) (Int.ofNat i, b) =
      (powDigitRun b (rootDigit n i) (if rootDigit n i = 2 then powGap else powBottom) >>=
        fun b' =>
          if i = n - 2 then .ok (SudoRt.Flow.brk (Int.ofNat i, b'))
          else .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), b'))) := by
  unfold emittedPowStep
  dsimp only
  have hng : ¬ Int.ofNat i > Int.ofNat (n - 2) := ofNat_not_gt hi
  rw [if_neg hng]
  have hlt : i < (rootStrip n).length := by rw [rootStrip_len n hn]; omega
  rw [hstrip, atL_embed (rootStrip n) i hlt, rootStrip_digit n i hn hi, ok_bind]
  have hflow :
      (do
          let b ← marker_lift b
          let b ← cube b up up
          if !(SudoRt.SEq.beq (Int.ofNat (rootDigit n i)) (0 : Int)) then
            do
              if SudoRt.SEq.beq (Int.ofNat (rootDigit n i)) (2 : Int) then
                do
                  let b ← copy_band b spare gap false
                  let b ← mul b up up spare false false false
                  let b ← clear b up
                  let b ← settle b
                  pure (SudoRt.Flow.cont (ρ := Int × Board) b)
              else
                do
                  let b ← copy_band b spare bottom false
                  let b ← mul b up up spare false false false
                  let b ← clear b up
                  let b ← settle b
                  pure (SudoRt.Flow.cont (ρ := Int × Board) b)
          else
            do
              let b ← settle b
              pure (SudoRt.Flow.cont (ρ := Int × Board) b)) =
        (powDigitRun b (rootDigit n i) (if rootDigit n i = 2 then powGap else powBottom) >>=
          fun b' => pure (SudoRt.Flow.cont (ρ := Int × Board) b')) := by
    have hboard := pow_from_digit b (rootDigit n i)
    rw [← hboard]
    rw [sEq_ofNat_zero (rootDigit n i)]
    have htwo : SudoRt.SEq.beq (Int.ofNat (rootDigit n i)) (2 : Int) =
        decide (rootDigit n i = 2) := by
      rw [show (2 : Int) = Int.ofNat 2 from rfl, sEq_ofNat]
    by_cases h0 : rootDigit n i = 0
    · rw [h0, decide_eq_true rfl, Bool.not_true]
      simp only [Bool.false_eq_true, if_false, pure_eq_ok, ok_bind]
      exact pull3 (marker_lift b) (fun b => cube b up up) settle
    · rw [decide_eq_false h0, Bool.not_false, htwo]
      by_cases h2 : rootDigit n i = 2
      · rw [h2, decide_eq_true rfl]
        simp only [if_true, pure_eq_ok, ok_bind]
        exact pull6 (marker_lift b) (fun b => cube b up up)
          (fun b => copy_band b spare gap false)
          (fun b => mul b up up spare false false false)
          (fun b => clear b up) settle
      · rw [decide_eq_false h2]
        simp only [if_true, Bool.false_eq_true, if_false, pure_eq_ok, ok_bind]
        exact pull6 (marker_lift b) (fun b => cube b up up)
          (fun b => copy_band b spare bottom false)
          (fun b => mul b up up spare false false false)
          (fun b => clear b up) settle
  rw [hflow]
  cases hr : powDigitRun b (rootDigit n i)
      (if rootDigit n i = 2 then powGap else powBottom) with
  | error e =>
    simp only [hr, error_bind]
  | ok b' =>
    simp only [hr, ok_bind, pure_eq_ok, map_ok]
    exact asc_tail (n - 2) i hfit b'

private theorem digits_drop (n i : Nat) (hi : i ≤ n - 2) (hn : 2 ≤ n) :
    (rootDigits n).drop i = rootDigit n i :: (rootDigits n).drop (i + 1) := by
  have hlen : (rootDigits n).length = n - 1 := by simp [rootDigits]
  have hiL : i < (rootDigits n).length := by rw [hlen]; omega
  rw [List.drop_eq_getElem_cons hiL]
  simp [rootDigits, List.getElem_map, List.getElem_range]

private theorem pow_loop_from {α : Type} (n i : Nat) (strip : Array Int) (b : Board)
    (k : Board → Except SudoRt.Trap α)
    (onRet : Int × Board → Except SudoRt.Trap α)
    (hn : 2 ≤ n) (hi : i ≤ n - 2) (hfit : FitsLen n)
    (hstrip : strip = embed (rootStrip n)) :
    SudoRt.runLoopOn (Int.ofNat i, b)
        (fuelRange (Int.ofNat i) (Int.ofNat (n - 2)))
        (emittedPowStep strip (Int.ofNat (n - 2)))
        (fun σ => k σ.2) onRet =
      (powRun b ((rootDigits n).drop i) >>= k) := by
  obtain ⟨d, hd⟩ : ∃ d, n - 2 - i = d := ⟨_, rfl⟩
  induction d generalizing i b with
  | zero =>
    have heq : i = n - 2 := by omega
    subst heq
    rw [fuelRange_le (Nat.le_refl _), runLoopOn_succ]
    have hfi : FitsLen ((n - 2) + 1) := FitsLen.of_le hfit (by omega)
    rw [emitted_pow_at n (n - 2) strip b hn (Nat.le_refl _) hfi hstrip,
      digits_drop n (n - 2) (Nat.le_refl _) hn]
    cases hr : powDigitRun b (rootDigit n (n - 2))
        (if rootDigit n (n - 2) = 2 then powGap else powBottom) with
    | error e =>
      simp only [hr, error_bind, powRun]
    | ok b' =>
      have hempty : (rootDigits n).drop ((n - 2) + 1) = [] := by
        rw [List.drop_eq_nil_iff]
        simp [rootDigits]
        omega
      simp only [hr, ok_bind, if_true, pure_eq_ok, powRun, hempty, ok_bind]
  | succ d ih =>
    have hlt : i < n - 2 := by omega
    have hi1 : i + 1 ≤ n - 2 := by omega
    have hnext : n - 2 - (i + 1) = d := by omega
    rw [fuelRange_le (Nat.le_of_lt hlt), hd, runLoopOn_succ]
    have hfi : FitsLen (i + 1) := FitsLen.of_le hfit (by omega)
    rw [emitted_pow_at n i strip b hn (Nat.le_of_lt hlt) hfi hstrip,
      digits_drop n i (Nat.le_of_lt hlt) hn]
    have hne : i ≠ n - 2 := by omega
    cases hr : powDigitRun b (rootDigit n i)
        (if rootDigit n i = 2 then powGap else powBottom) with
    | error e =>
      simp only [hr, error_bind, powRun, if_neg hne]
    | ok b' =>
      simp only [hr, ok_bind, if_neg hne, pure_eq_ok, powRun]
      have hfr : fuelRange (Int.ofNat (i + 1)) (Int.ofNat (n - 2)) = d + 1 := by
        rw [fuelRange_le hi1, hnext]
      rw [← hfr]
      exact ih (i + 1) b' hi1 hnext

private theorem bind_assoc {α β γ : Type} (m : Except SudoRt.Trap α)
    (f : α → Except SudoRt.Trap β) (g : β → Except SudoRt.Trap γ) :
    ((m >>= f) >>= g) = (m >>= fun a => f a >>= g) := by
  cases m <;> rfl

private theorem bind_pure {α : Type} (m : Except SudoRt.Trap α) :
    (m >>= fun x => pure x) = m := by
  cases m <;> rfl

private theorem pow_eta {α : Type} (m : Except SudoRt.Trap Board) (ds : List Nat)
    (f : Board → Board) (k : Board → Except SudoRt.Trap α) :
    ((m >>= fun b => powRun (f b) ds) >>= k) =
      (((m >>= fun b => pure (f b)) >>= fun b => powRun b ds) >>= k) := by
  cases m with
  | error _ => simp [error_bind]
  | ok _ =>
    simp only [ok_bind, pure_eq_ok]

private theorem bind_assoc' {α β γ : Type} (m : Except SudoRt.Trap α)
    (f : α → Except SudoRt.Trap β) (g : β → Except SudoRt.Trap γ) :
    (m >>= fun a => f a >>= g) = ((m >>= f) >>= g) := by
  cases m <;> rfl

/-- A loop whose `after` binds a continuation is the loop that returns the
    state, then that continuation. `onRet` is dead. -/
private theorem run_bind {σ ρ α β : Type} (s0 : σ) (fuel : Nat)
    (step : σ → Except SudoRt.Trap (SudoRt.Flow σ ρ))
    (thin : σ → Except SudoRt.Trap α) (k : α → Except SudoRt.Trap β)
    (onRet : ρ → Except SudoRt.Trap β) (onRetA : ρ → Except SudoRt.Trap α)
    (onRetId : ρ → Except SudoRt.Trap σ)
    (hno : ∀ s r, step s ≠ .ok (SudoRt.Flow.ret r)) :
    SudoRt.runLoopOn s0 fuel step (fun s => thin s >>= k) onRet =
      ((SudoRt.runLoopOn s0 fuel step thin onRetA) >>= k) := by
  rw [runLoopOn_after_split s0 fuel step (fun s => thin s >>= k) onRet onRetId hno]
  rw [bind_assoc' (SudoRt.runLoopOn s0 fuel step (fun s => pure s) onRetId) thin k]
  rw [← runLoopOn_after_split s0 fuel step thin onRetA onRetId hno]

theorem emittedStrip_val (n : Nat) (hn : 2 ≤ n) (hfit : FitsLen n) :
    emittedStrip n = .ok (embed (rootStrip n)) := by
  rw [emittedStrip, root_strip_loop n hn hfit, ← rootStrip_eq n hn]

/-- The strip loop inside one search index, continuation included, is
    `emittedStrip` bound into that continuation. -/
theorem strip_block {α : Type} (n : Nat) (strip0 : Array Int)
    (k : Array Int → Except SudoRt.Trap α)
    (onRet : Int × Board → Except SudoRt.Trap α)
    (hn : 2 ≤ n) (hfit : FitsLen n) (h0 : strip0 = Array.mkArray n (0 : Int)) :
    (do
        let toV ← SudoRt.subI (Int.ofNat n) (2 : Int)
        SudoRt.runLoopOn ((0 : Int), strip0) (fuelRange (0 : Int) toV) (emittedStripStep toV)
          (fun σ => do
            let ix ← SudoRt.subI (Int.ofNat n) (2 : Int)
            let strip ← SudoRt.putL σ.2 ix (1 : Int)
            k strip)
          onRet) =
      (emittedStrip n >>= k) := by
  have hk : ∀ σ : Int × Array Int,
      (do
          let ix ← SudoRt.subI (Int.ofNat n) (2 : Int)
          let strip ← SudoRt.putL σ.2 ix (1 : Int)
          k strip) =
        ((SudoRt.subI (Int.ofNat n) (2 : Int) >>= fun ix =>
            SudoRt.putL σ.2 ix (1 : Int)) >>= k) := by
    intro σ
    simp only [bind_assoc']
  have hsub : SudoRt.subI (Int.ofNat n) (2 : Int) = .ok (Int.ofNat (n - 2)) := by
    rw [show (2 : Int) = Int.ofNat 2 from rfl]
    exact subI_ofNat n 2 hfit (by omega)
  simp only [hk]
  conv =>
    lhs
    pattern SudoRt.subI _ _
    rw [hsub]
  simp only [ok_bind]
  rw [show (0 : Int) = Int.ofNat 0 from rfl, h0]
  rw [run_bind (Int.ofNat 0, Array.mkArray n (0 : Int))
      (fuelRange (Int.ofNat 0) (Int.ofNat (n - 2)))
      (emittedStripStep (Int.ofNat (n - 2)))
      (fun σ => SudoRt.subI (Int.ofNat n) (2 : Int) >>= fun ix => SudoRt.putL σ.2 ix (1 : Int))
      k onRet (fun _ => pure (Array.mkArray n (0 : Int)))
      (fun _ => pure (Int.ofNat 0, Array.mkArray n (0 : Int)))
      (fun s r => emittedStripStep_noret _ s r)]
  rw [emitted_strip_loop n]

/-- The emitted power loop is `powRun` of the root digits. -/
theorem emitted_pow_loop {α : Type} (n : Nat) (strip : Array Int) (b : Board)
    (k : Board → Except SudoRt.Trap α)
    (onRet : Int × Board → Except SudoRt.Trap α)
    (hn : 2 ≤ n) (hfit : FitsLen n)
    (hstrip : strip = embed (rootStrip n)) :
    SudoRt.runLoopOn (Int.ofNat 0, b)
        (fuelRange (Int.ofNat 0) (Int.ofNat (n - 2)))
        (emittedPowStep strip (Int.ofNat (n - 2)))
        (fun σ => k σ.2) onRet =
      (powRun b (rootDigits n) >>= k) := by
  have hdrop0 : (rootDigits n).drop 0 = rootDigits n := by simp
  rw [← hdrop0]
  exact pow_loop_from n 0 strip b k onRet hn (by omega) hfit hstrip

/-- The emitted power loop, continuation included, is `powRun` of the root digits. -/
theorem pow_block {α : Type} (n : Nat) (strip : Array Int) (b0 : Board)
    (aft : Int × Board → Except SudoRt.Trap α)
    (k : Board → Except SudoRt.Trap α)
    (onRet : Int × Board → Except SudoRt.Trap α)
    (hn : 2 ≤ n) (hfit : FitsLen n) (hstrip : strip = embed (rootStrip n))
    (haft : ∀ i bb, aft (i, bb) = k bb) :
    (do
        let toV ← SudoRt.subI (Int.ofNat n) (2 : Int)
        SudoRt.runLoopOn ((0 : Int), b0) (fuelRange (0 : Int) toV) (emittedPowStep strip toV)
          aft onRet) =
      (powRun b0 (rootDigits n) >>= k) := by
  have haft' : aft = fun σ => k σ.2 := by
    funext σ
    cases σ with
    | mk i bb =>
      simpa using haft i bb
  rw [haft']
  have hsub := subI_ofNat n 2 hfit (by omega)
  rw [show (2 : Int) = Int.ofNat 2 from rfl, hsub, ok_bind]
  rw [show (0 : Int) = Int.ofNat 0 from rfl]
  exact emitted_pow_loop n strip b0 k onRet hn hfit hstrip

/-- The hit test and the five clears are `searchCheck`, then break or miss. -/
theorem check_block (b : Board) (j found : Int) (jN : Nat) (hj : j = Int.ofNat jN) :
    (do
        let b ← marker_lift b
        let b := { b with sudo_5Board_9marker_on := false }
        let b ← clear b gap
        let b ← mul b gap up up true false false
        let b ← settle b
        let y2 ← value b gap
        let side ← value b bottom
        if SudoRt.SEq.beq y2 side then
          pure (SudoRt.Flow.brk (ρ := Int × Board) (b, j))
        else
          do
            let b ← clear b gap
            let b ← clear b bottom
            let b ← clear b up
            let b ← clear b across
            let b ← clear b base_across
            pure (SudoRt.Flow.cont (ρ := Int × Board) (b, found))) =
      (searchCheck b >>= fun r =>
        if r.1 = true then
          pure (SudoRt.Flow.brk (ρ := Int × Board) (r.2, Int.ofNat jN))
        else
          searchMiss r.2 >>= fun b =>
            pure (SudoRt.Flow.cont (ρ := Int × Board) (b, found))) := by
  rw [hj]
  unfold searchCheck searchMiss
  simp only [searchGap_int, searchUp_int, searchBottom_int, searchAcross_int, searchBase_int]
  cases hm : marker_lift b with
  | error _ => simp [hm, error_bind]
  | ok b1 =>
    simp only [hm, ok_bind]
    cases hc : clear { b1 with sudo_5Board_9marker_on := false } gap with
    | error _ => simp [hc, error_bind]
    | ok b2 =>
      simp only [hc, ok_bind]
      cases hmul : mul b2 gap up up true false false with
      | error _ => simp [hmul, error_bind]
      | ok b3 =>
        simp only [hmul, ok_bind]
        cases hs : settle b3 with
        | error _ => simp [hs, error_bind]
        | ok b4 =>
          simp only [hs, ok_bind]
          cases hy : value b4 gap with
          | error _ => simp [hy, error_bind]
          | ok y2 =>
            simp only [hy, ok_bind]
            cases hside : value b4 bottom with
            | error _ => simp [hside, error_bind]
            | ok sidev =>
              simp only [hside, ok_bind, pure_eq_ok]
              by_cases hb : SudoRt.SEq.beq y2 sidev = true
              · simp only [hb, if_true, pure_eq_ok]
              · simp only [if_neg hb, bind_assoc', ok_bind]

/-- One emitted search index is `searchStep`. The board's `n` is `t.n`, and the
    index is `Int.ofNat σ.1.toNat`. The power `after` is `searchTail` of that
    outer index, so it does not read the power loop's own index. -/
theorem emitted_hole_eq (t : Spec.Tier) (σ : Int × (Board × Int))
    (x y side gapXs ax bx : List Nat) (left : Nat)
    (hAt : SearchAt σ.2.1 t x y side gapXs ax bx left)
    (h1 : (1 : Int) ≤ σ.1) (hn : σ.1 ≤ Int.ofNat (t.n - 1)) :
    emittedHole σ.2.1.sudo_5Board_1t.sudo_4Tier_1n (Int.ofNat (t.n - 1)) σ =
      searchStep (ρ := Int × Board) t (t.n - 1) σ := by
  have hN : σ.2.1.sudo_5Board_1t.sudo_4Tier_1n = Int.ofNat t.n := by
    rw [hAt.tier]
    rfl
  have hj : Int.ofNat σ.1.toNat = σ.1 := Int.toNat_of_nonneg (by omega)
  have hfit : FitsLen t.n := fits_small hAt.shape.n_small
  have hle : (1 : Int) ≤ Int.ofNat (t.n - 1) := by
    calc (1 : Int) ≤ σ.1 := h1
      _ ≤ Int.ofNat (t.n - 1) := hn
  have hn2 : 2 ≤ t.n := by
    have h1n : (1 : Nat) ≤ t.n - 1 := Int.ofNat_le.mp hle
    omega
  have hpair : σ = (Int.ofNat σ.1.toNat, σ.2) := by
    cases σ with
    | mk i rest =>
      exact Prod.ext hj.symm rfl
  rw [hN, hpair]
  unfold emittedHole searchStep searchBody
  dsimp only
  have hng : ¬ Int.ofNat σ.1.toNat > Int.ofNat (t.n - 1) := by
    rw [hj]
    exact Int.not_lt.mpr hn
  rw [if_neg hng, if_neg hng]
  simp only [filledL_ofNat, ok_bind, bind_pure]
  conv =>
    lhs
    pattern (SudoRt.subI (Int.ofNat t.n) (2 : Int) >>= fun toV =>
      SudoRt.runLoopOn ((0 : Int), Array.mkArray t.n (0 : Int))
        (fuelRange (0 : Int) toV) (emittedStripStep toV) _ _)
    rw [strip_block t.n (Array.mkArray t.n (0 : Int)) _ _ hn2 hfit rfl]
  rw [emittedStrip_val t.n hn2 hfit]
  simp only [ok_bind]
  conv =>
    lhs
    pattern (SudoRt.subI (Int.ofNat t.n) (2 : Int) >>= fun toV =>
      SudoRt.runLoopOn ((0 : Int), _) (fuelRange (0 : Int) toV)
        (emittedPowStep (embed (rootStrip t.n)) toV) _ _)
    rw [pow_block (n := t.n) (strip := embed (rootStrip t.n))
        (k := searchTail (Int.ofNat σ.1.toNat) σ.2.2)
        (hn := hn2) (hfit := hfit) (hstrip := rfl) (haft := fun _ _ => rfl)]
  unfold searchReadyDo
  have hto : ∀ n : Nat, (Int.ofNat n).toNat = n := fun _ => rfl
  simp only [hto, filledL_ofNat, emittedStrip_val t.n hn2 hfit, ok_bind, pure_eq_ok, bind_pure,
    bind_assoc']
  congr 1
  · rw [pow_eta]
    rfl
  · funext fl
    cases fl <;> rfl

end EcbsLink2.Link2
