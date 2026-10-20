/-
  On Demo, a positive basis peg is not fixed by the field cube. The kernel
  checks the six holes. A low power, `3 · j < n`, is the shifted peg on every
  tier.
  Proof-only. Not a security claim.
-/
import EcbsLink2.SpecBase

namespace EcbsLink2.Link2

open EcbsLink2.Spec

def pegFixed (n k bench j : Nat) : Bool :=
  decide (fieldCube n k bench (basisPeg n j) = basisPeg n j)

def noneFixed (n k bench fuel j : Nat) : Bool :=
  match fuel with
  | 0 => true
  | fuel + 1 => !(pegFixed n k bench j) && noneFixed n k bench fuel (j + 1)

private theorem step_and (fuel n k bench j : Nat)
    (h : noneFixed n k bench (fuel + 1) j = true) :
    pegFixed n k bench j = false ∧ noneFixed n k bench fuel (j + 1) = true := by
  unfold noneFixed at h
  cases hpeg : pegFixed n k bench j <;> cases hrest : noneFixed n k bench fuel (j + 1)
  · simp [hpeg, hrest] at h
  · exact ⟨rfl, rfl⟩
  · simp [hpeg, hrest] at h
  · simp [hpeg, hrest] at h

theorem noneFixed_at (n k bench fuel j0 d : Nat)
    (h : noneFixed n k bench fuel j0 = true) (hd : d < fuel) :
    fieldCube n k bench (basisPeg n (j0 + d)) ≠ basisPeg n (j0 + d) := by
  induction fuel generalizing j0 d with
  | zero =>
    exact absurd hd (Nat.not_lt_zero _)
  | succ fuel ih =>
    have hstep := step_and fuel n k bench j0 h
    cases d with
    | zero =>
      have hdec : decide (fieldCube n k bench (basisPeg n j0) = basisPeg n j0) = false := by
        simpa [pegFixed] using hstep.1
      exact of_decide_eq_false hdec
    | succ d =>
      have hlt : d < fuel := by omega
      simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        ih (j0 + 1) d hstep.2 hlt

theorem demo_noneFixed : noneFixed 7 5 20 6 1 = true := by
  decide

theorem demo_basis_cube_ne (j : Nat) (hj : 0 < j) (hjn : j < 7) :
    fieldCube 7 5 20 (basisPeg 7 j) ≠ basisPeg 7 j := by
  have h := noneFixed_at 7 5 20 6 1 (j - 1) demo_noneFixed (by omega)
  have heq : 1 + (j - 1) = j := by omega
  simpa [heq] using h

def runZero (j : Nat) : Bool :=
  decide (fieldSub 7 (basisPeg 7 j) (fieldCube 7 5 20 (basisPeg 7 j)) =
    List.replicate 7 0)

def noneRun (fuel j : Nat) : Bool :=
  match fuel with
  | 0 => true
  | fuel + 1 => !(runZero j) && noneRun fuel (j + 1)

private theorem run_step (fuel j : Nat) (h : noneRun (fuel + 1) j = true) :
    runZero j = false ∧ noneRun fuel (j + 1) = true := by
  unfold noneRun at h
  cases hz : runZero j <;> cases hr : noneRun fuel (j + 1)
  · simp [hz, hr] at h
  · exact ⟨rfl, rfl⟩
  · simp [hz, hr] at h
  · simp [hz, hr] at h

theorem noneRun_at (fuel j0 d : Nat) (h : noneRun fuel j0 = true) (hd : d < fuel) :
    fieldSub 7 (basisPeg 7 (j0 + d)) (fieldCube 7 5 20 (basisPeg 7 (j0 + d))) ≠
      List.replicate 7 0 := by
  induction fuel generalizing j0 d with
  | zero =>
    exact absurd hd (Nat.not_lt_zero _)
  | succ fuel ih =>
    have hstep := run_step fuel j0 h
    cases d with
    | zero =>
      have hdec : decide (fieldSub 7 (basisPeg 7 j0) (fieldCube 7 5 20 (basisPeg 7 j0)) =
          List.replicate 7 0) = false := by
        simpa [runZero] using hstep.1
      exact of_decide_eq_false hdec
    | succ d =>
      have hlt : d < fuel := by omega
      simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        ih (j0 + 1) d hstep.2 hlt

theorem demo_noneRun : noneRun 6 1 = true := by
  decide

/-- Demo: the cofactor run `e_j − e_j³` is not the zero home. -/
theorem demo_run_ne (j : Nat) (hj : 0 < j) (hjn : j < 7) :
    fieldSub 7 (basisPeg 7 j) (fieldCube 7 5 20 (basisPeg 7 j)) ≠ List.replicate 7 0 := by
  have h := noneRun_at 6 1 (j - 1) demo_noneRun (by omega)
  have heq : 1 + (j - 1) = j := by omega
  simpa [heq] using h

end EcbsLink2.Link2
