/-
  One cell of a spec walk that returns a point. `none` ends the run.
  A live step never returns `(false, _)`. A not-live white or red cell
  seats the base and becomes live, so `(false, _)` does not absorb.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.WalkCopy
import EcbsLink2.Link2.WalkFail

namespace EcbsLink2.Link2

open EcbsLink2.Spec

/-- The walk is a fold. The cells after a prefix continue from that prefix. -/
theorem walkRun_append (n k bench : Nat) (base : List Nat × List Nat)
    (live : Bool) (acc : List Nat × List Nat) (xs ys : List Nat) :
    walkRun n k bench base live acc (xs ++ ys) =
      (walkRun n k bench base live acc xs).bind
        (fun q => walkRun n k bench base q.1 q.2 ys) := by
  induction xs generalizing live acc with
  | nil =>
    simp [walkRun, Option.bind]
  | cons c cs ih =>
    simp only [List.cons_append, walkRun]
    cases hstep : walkStep n k bench base live acc c with
    | none =>
      simp [hstep, Option.bind]
    | some q =>
      simp only [hstep, Option.bind]
      exact ih q.1 q.2

/-- A refused step makes the rest of the run `none`. -/
theorem walkRun_none_absorb (n k bench : Nat) (base : List Nat × List Nat)
    (live : Bool) (acc : List Nat × List Nat) (c : Nat) (cs : List Nat)
    (h : walkStep n k bench base live acc c = none) :
    walkRun n k bench base live acc (c :: cs) = none := by
  simp [walkRun, h]

/-- A not-live white cell seats the base point and turns the live bit on.
    `(false, _)` is not absorbing: the cells after a dead zero can still
    return `some (true, _)`. -/
theorem walkStep_false_seats (n k bench : Nat) (base acc : List Nat × List Nat) :
    walkStep n k bench base false acc 1 = some (true, base) :=
  walkStep_fresh_white n k bench base acc

private theorem drop_get (cells : List Nat) (i : Nat) (hi : i < cells.length) :
    cells.drop i = cells[i] :: cells.drop (i + 1) := by
  induction cells generalizing i with
  | nil => simp at hi
  | cons c cs ih =>
    cases i with
    | zero => simp
    | succ i =>
      simpa [List.drop] using ih (by simp at hi; omega)

/-- The cell at `i`, once the prefix is live and the whole walk returns a
    point. The step is live, so `walkStep_true_bit` rules out `(false, _)`,
    and `walkRun_none_absorb` rules out `none`. -/
theorem walkRun_step_of_full (n k bench : Nat) (base : List Nat × List Nat)
    (live0 : Bool) (acc0 pF : List Nat × List Nat)
    (cells : List Nat) (i : Nat) (ax ay : List Nat)
    (hi : i < cells.length)
    (hfull : walkRun n k bench base live0 acc0 cells = some (true, pF))
    (hpre : walkRun n k bench base live0 acc0 (cells.take i) =
      some (true, (ax, ay))) :
    ∃ ax' ay',
      walkStep n k bench base true (ax, ay) (cells[i]'hi) =
        some (true, (ax', ay')) := by
  rw [← List.take_append_drop i cells] at hfull
  rw [walkRun_append] at hfull
  rw [hpre] at hfull
  simp only [Option.bind] at hfull
  rw [drop_get cells i hi] at hfull
  simp only [walkRun] at hfull
  cases hstep : walkStep n k bench base true (ax, ay) (cells[i]'hi) with
  | none =>
    simp [hstep] at hfull
  | some q =>
    simp only [hstep] at hfull
    have hbit := walkStep_true_bit n k bench base (ax, ay) (cells[i]'hi) q hstep
    cases q with
    | mk bit acc' =>
      cases bit with
      | false => cases hbit
      | true =>
        cases acc' with
        | mk ax' ay' =>
          exact ⟨ax', ay', rfl⟩

end EcbsLink2.Link2
