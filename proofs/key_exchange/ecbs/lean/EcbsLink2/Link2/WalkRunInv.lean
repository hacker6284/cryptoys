/-
  A successful `walkRun` makes every live white or red cell invertible.
  `walk_chord` reads that inverse off the run. It is not an extra hypothesis.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.CopySeat

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

theorem walkRun_cons_some (n k bench : Nat) (base : List Nat × List Nat)
    (live : Bool) (acc : List Nat × List Nat) (c : Nat) (cs : List Nat)
    (q : Bool × (List Nat × List Nat))
    (h : walkRun n k bench base live acc (c :: cs) = some q) :
    ∃ step, walkStep n k bench base live acc c = some step ∧
      walkRun n k bench base step.1 step.2 cs = some q := by
  simp only [walkRun] at h
  cases hstep : walkStep n k bench base live acc c with
  | none => simp [hstep] at h
  | some step =>
    simp only [hstep] at h
    exact ⟨step, rfl, h⟩

theorem walkRun_at (n k bench : Nat) (base : List Nat × List Nat)
    (live : Bool) (acc : List Nat × List Nat) (cells : List Nat) (i : Nat)
    (q : Bool × (List Nat × List Nat))
    (hi : i < cells.length)
    (h : walkRun n k bench base live acc cells = some q) :
    ∃ liveI accI step,
      walkRun n k bench base live acc (cells.take i) = some (liveI, accI) ∧
      walkStep n k bench base liveI accI (cells[i]'hi) = some step ∧
      walkRun n k bench base step.1 step.2 (cells.drop (i + 1)) = some q := by
  induction i generalizing cells live acc with
  | zero =>
    cases cells with
    | nil => simp at hi
    | cons c cs =>
      obtain ⟨step, hstep, htail⟩ := walkRun_cons_some n k bench base live acc c cs q h
      refine ⟨live, acc, step, ?_, ?_, ?_⟩
      · simp [walkRun]
      · simpa using hstep
      · simpa using htail
  | succ i ih =>
    cases cells with
    | nil => simp at hi
    | cons c cs =>
      obtain ⟨step, hstep, htail⟩ := walkRun_cons_some n k bench base live acc c cs q h
      have hi' : i < cs.length := by simp at hi; omega
      obtain ⟨liveI, accI, stepI, hpre, hcell, hdrop⟩ :=
        ih (cells := cs) (live := step.1) (acc := step.2) hi' htail
      refine ⟨liveI, accI, stepI, ?_, ?_, ?_⟩
      · simpa [walkRun, hstep, List.take_succ_cons] using hpre
      · simpa [List.getElem_cons_succ] using hcell
      · simpa [List.drop_succ_cons] using hdrop

/-- The inverse at a live white or red cell of a successful run. -/
theorem walkRun_live_inv (n k bench : Nat) (base acc accI : List Nat × List Nat)
    (cells : List Nat) (i : Nat) (q : Bool × (List Nat × List Nat))
    (hi : i < cells.length)
    (hc : cells[i]'hi = 1 ∨ cells[i]'hi = 2)
    (hpre : walkRun n k bench base false acc (cells.take i) = some (true, accI))
    (h : walkRun n k bench base false acc cells = some q) :
    ∃ inv, fieldInv n k bench
      (fieldSub n base.1 (fieldCube n k bench accI.1)) = some inv := by
  obtain ⟨liveI, accI', step, hpre', hcell, _⟩ :=
    walkRun_at n k bench base false acc cells i q hi h
  have hs : (liveI, accI') = (true, accI) :=
    Option.some.inj (hpre'.symm.trans hpre)
  have hliveI : liveI = true := congrArg Prod.fst hs
  have hacc : accI' = accI := congrArg Prod.snd hs
  rw [hliveI, hacc] at hcell
  exact live_chord_inv n k bench base accI (cells[i]'hi) step hc hcell

end EcbsLink2.Link2
