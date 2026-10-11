/-
  The ladder array is written only when a rung is laid on a fresh board. Park,
  the spare copy, the white scan, cube, mul, clear, doubling, and the extra peg
  leave `sudo_5Board_6ladder` where they found it. Each primitive is one
  projection. `keeps_bind` stacks them.
-/
import EcbsLink2.Link2.ScanSplit

namespace EcbsLink2.Link2

open MegaDreifach.Link2

/-- `f` returns a board with the same ladder, or a trap. -/
def Keeps (f : Ecbs.Board → Except SudoRt.Trap Ecbs.Board) : Prop :=
  ∀ b b', f b = .ok b' → b'.sudo_5Board_6ladder = b.sudo_5Board_6ladder

theorem keeps_pure : Keeps (fun b => pure b) := by
  intro b b' h
  dsimp only at h
  rw [pure_eq_ok] at h
  cases h
  rfl

theorem keeps_bind
    (f g : Ecbs.Board → Except SudoRt.Trap Ecbs.Board)
    (hf : Keeps f) (hg : Keeps g) :
    Keeps (fun b => f b >>= g) := by
  intro b b' h
  dsimp only at h
  cases hf0 : f b with
  | error _ =>
    rw [hf0, error_bind] at h
    cases h
  | ok b1 =>
    rw [hf0, ok_bind] at h
    exact (hg b1 b' h).trans (hf b b1 hf0)

theorem note_peak_ladder (b b' : Ecbs.Board) (h : Ecbs.note_peak b = .ok b') :
    b'.sudo_5Board_6ladder = b.sudo_5Board_6ladder := by
  unfold Ecbs.note_peak at h
  dsimp only at h
  cases hv : Ecbs.occupied b with
  | error _ =>
    rw [hv] at h
    simp only [error_bind] at h; cases h
  | ok v =>
    rw [hv] at h
    simp only [ok_bind] at h
    by_cases hc : decide (v > b.sudo_5Board_4cost.sudo_5Costs_4peak) = true
    · rw [if_pos hc, pure_eq_ok] at h
      cases h
      rfl
    · rw [if_neg hc, pure_eq_ok] at h
      cases h
      rfl

theorem note_strict_ladder (b b' : Ecbs.Board) (h : Ecbs.note_strict b = .ok b') :
    b'.sudo_5Board_6ladder = b.sudo_5Board_6ladder := by
  unfold Ecbs.note_strict at h
  dsimp only at h
  cases hv : Ecbs.occupied b with
  | error _ =>
    rw [hv] at h
    simp only [error_bind] at h; cases h
  | ok v =>
    rw [hv] at h
    simp only [ok_bind] at h
    by_cases hc : decide (v > b.sudo_5Board_4cost.sudo_5Costs_11peak_strict) = true
    · rw [if_pos hc, pure_eq_ok] at h
      cases h
      rfl
    · rw [if_neg hc, pure_eq_ok] at h
      cases h
      rfl

theorem tally_note_ladder (b b' : Ecbs.Board) (h : Ecbs.tally_note b = .ok b') :
    b'.sudo_5Board_6ladder = b.sudo_5Board_6ladder := by
  unfold Ecbs.tally_note at h
  dsimp only at h
  by_cases hc :
      decide (b.sudo_5Board_9tally_len > b.sudo_5Board_4cost.sudo_5Costs_9tally_max) = true
  · rw [if_pos hc, pure_eq_ok] at h
    cases h
    rfl
  · rw [if_neg hc, pure_eq_ok] at h
    cases h
    rfl

theorem set_control_ladder (b b' : Ecbs.Board) (i c : Int)
    (h : Ecbs.set_control b i c = .ok b') :
    b'.sudo_5Board_6ladder = b.sudo_5Board_6ladder := by
  unfold Ecbs.set_control at h
  dsimp only at h
  by_cases hge : decide (i ≥ (0 : Int)) = true
  · rw [if_pos hge, pure_eq_ok, ok_bind] at h
    cases ha : SudoRt.sudoAssert (decide (i < b.sudo_5Board_1t.sudo_4Tier_7control)) 263 with
    | error _ =>
      rw [ha] at h
      simp only [error_bind] at h; cases h
    | ok _ =>
      rw [ha] at h
      simp only [ok_bind] at h
      cases hp : SudoRt.putL b.sudo_5Board_3row i c with
      | error _ =>
        rw [hp] at h
        simp only [error_bind] at h; cases h
      | ok row =>
        rw [hp] at h
        simp only [ok_bind] at h
        by_cases hhi :
            decide (i > b.sudo_5Board_4cost.sudo_5Costs_15control_highest) = true
        · rw [if_pos hhi, pure_eq_ok] at h
          cases h
          rfl
        · rw [if_neg hhi, pure_eq_ok] at h
          cases h
          rfl
  · rw [if_neg hge, pure_eq_ok, ok_bind] at h
    cases ha : SudoRt.sudoAssert false 263 with
    | error _ =>
      rw [ha] at h
      simp only [error_bind] at h; cases h
    | ok _ =>
      rw [ha] at h
      simp only [ok_bind] at h
      cases hp : SudoRt.putL b.sudo_5Board_3row i c with
      | error _ =>
        rw [hp] at h
        simp only [error_bind] at h; cases h
      | ok row =>
        rw [hp] at h
        simp only [ok_bind] at h
        by_cases hhi :
            decide (i > b.sudo_5Board_4cost.sudo_5Costs_15control_highest) = true
        · rw [if_pos hhi, pure_eq_ok] at h
          cases h
          rfl
        · rw [if_neg hhi, pure_eq_ok] at h
          cases h
          rfl

theorem tally_put_ladder (b b' : Ecbs.Board) (j c : Int)
    (h : Ecbs.tally_put b j c = .ok b') :
    b'.sudo_5Board_6ladder = b.sudo_5Board_6ladder := by
  unfold Ecbs.tally_put at h
  dsimp only at h
  cases hix : SudoRt.addI b.sudo_5Board_6tally0 j with
  | error _ =>
    rw [hix] at h
    simp only [error_bind] at h; cases h
  | ok ix =>
    rw [hix] at h
    simp only [ok_bind] at h
    cases hs : Ecbs.set_control b ix c with
    | error _ =>
      rw [hs] at h
      simp only [error_bind] at h; cases h
    | ok b1 =>
      rw [hs] at h
      simp only [ok_bind, pure_eq_ok] at h
      cases h
      exact set_control_ladder b b' ix c hs

theorem marker_step_ladder (b b' : Ecbs.Board) (h : Ecbs.marker_step b = .ok b') :
    b'.sudo_5Board_6ladder = b.sudo_5Board_6ladder := by
  unfold Ecbs.marker_step at h
  dsimp only at h
  by_cases hlt : decide (b.sudo_5Board_6marker < (0 : Int)) = true
  · rw [if_pos hlt] at h
    cases hc : SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_4ctrl (1 : Int) with
    | error _ =>
      rw [hc] at h
      simp only [error_bind] at h; cases h
    | ok v =>
      rw [hc] at h
      simp only [ok_bind] at h
      cases ha :
          SudoRt.sudoAssert (decide ((0 : Int) < b.sudo_5Board_1t.sudo_4Tier_6script)) 321 with
      | error _ =>
        rw [ha] at h
        simp only [error_bind] at h; cases h
      | ok _ =>
        rw [ha] at h
        simp only [ok_bind] at h
        cases hm : SudoRt.addI (0 : Int) (1 : Int) with
        | error _ =>
          rw [hm] at h
          simp only [error_bind] at h; cases h
        | ok m =>
          rw [hm] at h
          simp only [ok_bind] at h
          by_cases hmx :
              decide (m > b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max) = true
          · rw [if_pos hmx, pure_eq_ok] at h
            cases h
            rfl
          · rw [if_neg hmx, pure_eq_ok] at h
            cases h
            rfl
  · rw [if_neg hlt] at h
    cases hm : SudoRt.addI b.sudo_5Board_6marker (1 : Int) with
    | error _ =>
      rw [hm] at h
      simp only [error_bind] at h; cases h
    | ok m =>
      rw [hm] at h
      simp only [ok_bind] at h
      cases hc : SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_4ctrl (2 : Int) with
      | error _ =>
        rw [hc] at h
        simp only [error_bind] at h; cases h
      | ok v =>
        rw [hc] at h
        simp only [ok_bind] at h
        cases ha :
            SudoRt.sudoAssert (decide (m < b.sudo_5Board_1t.sudo_4Tier_6script)) 321 with
        | error _ =>
          rw [ha] at h
          simp only [error_bind] at h; cases h
        | ok _ =>
          rw [ha] at h
          simp only [ok_bind] at h
          cases hm2 : SudoRt.addI m (1 : Int) with
          | error _ =>
            rw [hm2] at h
            simp only [error_bind] at h; cases h
          | ok m2 =>
            rw [hm2] at h
            simp only [ok_bind] at h
            by_cases hmx :
                decide (m2 > b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max) = true
            · rw [if_pos hmx, pure_eq_ok] at h
              cases h
              rfl
            · rw [if_neg hmx, pure_eq_ok] at h
              cases h
              rfl

theorem log_op_ladder (b b' : Ecbs.Board) (h : Ecbs.log_op b = .ok b') :
    b'.sudo_5Board_6ladder = b.sudo_5Board_6ladder := by
  unfold Ecbs.log_op at h
  dsimp only at h
  by_cases hon : b.sudo_5Board_9marker_on = true
  · rw [if_pos hon] at h
    cases hs : Ecbs.marker_step b with
    | error _ =>
      rw [hs] at h
      simp only [error_bind] at h; cases h
    | ok b1 =>
      rw [hs] at h
      simp only [ok_bind, pure_eq_ok] at h
      cases h
      exact marker_step_ladder b b' hs
  · rw [if_neg hon, pure_eq_ok] at h
    cases h
    rfl

/-- The named cube board does not write the ladder. -/
theorem cubeOff_ladder (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (n k moves hole bench peak peakS cOps : Nat)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hF : src < b.sudo_5Board_4held.size)
    (hHome : src < b.sudo_5Board_4home.size) :
    (cubeOffBoard b dst src xs n k moves hole bench peak peakS cOps hops hF hHome).sudo_5Board_6ladder =
      b.sudo_5Board_6ladder := rfl

/-- The named nocopy mul board does not write the ladder. -/
theorem mulOff_ladder (b : Ecbs.Board) (dst second : Nat) (xs ys : List Nat)
    (n k moves hole bench peak peakS cOps : Nat)
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hS : second < b.sudo_5Board_4held.size)
    (hHomeS : second < b.sudo_5Board_4home.size) :
    (mulNoOffBoard b dst second xs ys n k moves hole bench peak peakS cOps hops hS hHomeS).sudo_5Board_6ladder =
      b.sudo_5Board_6ladder := rfl

theorem settleBoard_ladder (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (n moves slides peak : Nat) :
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_6ladder =
      b.sudo_5Board_6ladder := by
  unfold settleBoard
  split <;> rfl

/-- A successful loop preserves `Q` when the step preserves `P` and neither
    `after` nor a `ret` leaves `Q`. Fuel 0 is a trap. -/
theorem runLoopOn_ok_inv {σ ρ α : Type}
    (P : σ → Prop) (Q : α → Prop)
    (s0 : σ) (fuel : Nat)
    (step : σ → Except SudoRt.Trap (SudoRt.Flow σ ρ))
    (after : σ → Except SudoRt.Trap α)
    (onRet : ρ → Except SudoRt.Trap α)
    (h0 : P s0)
    (hcont : ∀ s s', P s → step s = .ok (.cont s') → P s')
    (hbrk : ∀ s s', P s → step s = .ok (.brk s') → P s')
    (hret : ∀ s r a, P s → step s = .ok (.ret r) → onRet r = .ok a → Q a)
    (hafter : ∀ s a, P s → after s = .ok a → Q a)
    (a : α)
    (h : SudoRt.runLoopOn s0 fuel step after onRet = .ok a) :
    Q a := by
  induction fuel generalizing s0 with
  | zero =>
    rw [runLoopOn_zero] at h
    unfold SudoRt.fail at h
    cases h
  | succ fuel ih =>
    rw [runLoopOn_succ] at h
    cases hst : step s0 with
    | error _ =>
      rw [hst] at h
      cases h
    | ok fl =>
      rw [hst] at h
      cases fl with
      | ret r =>
        exact hret s0 r a h0 hst h
      | brk s =>
        change after s = .ok a at h
        exact hafter s a (hbrk s0 s h0 hst) h
      | cont s =>
        exact ih s (hcont s0 s h0 hst) h

/-- An `.ok` result is `after` on a state the stepper stopped in, or `onRet`
    on a value some step returned. Fuel 0 is a trap, so it is not `.ok`. -/
theorem runLoopOn_ok_after {σ ρ α : Type}
    (s0 : σ) (fuel : Nat)
    (step : σ → Except SudoRt.Trap (SudoRt.Flow σ ρ))
    (after : σ → Except SudoRt.Trap α)
    (onRet : ρ → Except SudoRt.Trap α)
    (a : α)
    (h : SudoRt.runLoopOn s0 fuel step after onRet = .ok a) :
    (∃ s, after s = .ok a) ∨
      (∃ r, onRet r = .ok a ∧ ∃ s, step s = .ok (.ret r)) := by
  induction fuel generalizing s0 with
  | zero =>
    rw [runLoopOn_zero] at h
    unfold SudoRt.fail at h
    cases h
  | succ fuel ih =>
    rw [runLoopOn_succ] at h
    cases hst : step s0 with
    | error _ =>
      rw [hst] at h
      cases h
    | ok fl =>
      rw [hst] at h
      cases fl with
      | ret r =>
        exact Or.inr ⟨r, ⟨h, ⟨s0, hst⟩⟩⟩
      | brk s =>
        change after s = .ok a at h
        exact Or.inl ⟨s, h⟩
      | cont s =>
        exact ih s h

/-- The white scan returns the board it was given. `onRet` is `(b, 0)`. -/
theorem white_loop_ladder (b : Ecbs.Board) (toV j0 : Int) (fuel : Nat)
    (p : Ecbs.Board × Int)
    (h : SudoRt.runLoopOn j0 fuel (whiteStep b toV)
        (fun j => .ok (b, j)) (fun _ => .ok (b, (0 : Int))) = .ok p) :
    p.1 = b := by
  exact runLoopOn_ok_inv (fun _ => True) (fun q => q.1 = b) j0 fuel
    (whiteStep b toV) (fun j => .ok (b, j)) (fun _ => .ok (b, (0 : Int)))
    trivial
    (fun _ _ _ _ => trivial)
    (fun _ _ _ _ => trivial)
    (fun _ _ q _ _ hq => by
      cases hq
      rfl)
    (fun j q _ hq => by
      cases hq
      rfl)
    p h

end EcbsLink2.Link2
