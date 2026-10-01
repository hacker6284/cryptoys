/-
  HEAVY (not in the default build target): the unconditional forms of the affine
  results of DoubleDealSecurity/CovariantAffine.lean.
  * `affPairsCheck_ok`: check A of `AffChecks` (four stem evaluations).
  * Check B, one `decide!` per nontrivial linear part `(k, g)`, is the generated file
    `CovariantAffineChecks.lean` (`check_lin_0_1` … `check_lin_11_5`, `lin_checks_all`).
  Timing and memory: see `../README.md` (module table) for the measured figures and
  their scope. Built and audited by the `doubledeal-security-heavy` CI job.
  Python reproduction: `analysis/v12-primenonswap/aff_witness.py`.
-/
import DoubleDealSecurity.CovariantAffine
import DoubleDealSecurityHeavy.CovariantAffineChecks

namespace DoubleDeal.Security.CovariantAffine

open DoubleDeal Relabel

/-- (PROVED, kernel `decide!`) Finite check A of `AffChecks`. -/
theorem affPairsCheck_ok : affPairsCheck = true := by decide!

/-- (PROVED) Both finite checks. -/
theorem affChecks_ok : AffChecks := ⟨affPairsCheck_ok, lin_checks_all⟩

/-- (PROVED, unconditional) A nontrivial linear part `linSym k g` fails the seat-26
    condition `Cell0Cov` for every τ. -/
theorem not_cell0Cov_lin (k : Fin 12) (g : Fin 6) (hkg : (k, g) ≠ (0, 0)) (τ : Relabel) :
    ¬ CovariantNarrow.Cell0Cov (linSym k g) τ :=
  not_cell0Cov_lin_of_check affChecks_ok k g hkg τ

/-- (PROVED, unconditional) No affine relabelling `v10Sym a x * linSym k g` with a
    nontrivial linear part `(k, g) ≠ (0, 0)` (i.e. no element of the normalizer of
    `v10Sym` outside `v10Sym`) is covariant for the unkeyed round body, for ANY output
    relabelling τ. This is the statement of `roundBody_covariant_iff_id` restricted to
    these 3692 σ; the general conjecture stays open and keeps its `sorry`. -/
theorem roundBody_not_covariant_affine (a : Fin 13) (x : Fin 4) (k : Fin 12) (g : Fin 6)
    (hkg : (k, g) ≠ (0, 0)) : ¬ Covariant (v10Sym a x * linSym k g) unkeyedWithMix :=
  not_covariant_affine_of_check affChecks_ok a x k g hkg

/-- (PROVED, unconditional) The same with the translation on the other side. -/
theorem roundBody_not_covariant_affine_right (a : Fin 13) (x : Fin 4) (k : Fin 12)
    (g : Fin 6) (hkg : (k, g) ≠ (0, 0)) :
    ¬ Covariant (linSym k g * v10Sym a x) unkeyedWithMix :=
  not_covariant_affine_right_of_check affChecks_ok a x k g hkg

/-- (PROVED, unconditional) `roundBody_covariant_iff_id` restricted to the 3744
    affine relabellings: covariant iff the identity. -/
theorem roundBody_covariant_affine_iff (a : Fin 13) (x : Fin 4) (k : Fin 12) (g : Fin 6) :
    Covariant (v10Sym a x * linSym k g) unkeyedWithMix ↔ v10Sym a x * linSym k g = 1 :=
  covariant_affine_iff_of_check affChecks_ok a x k g

end DoubleDeal.Security.CovariantAffine
