/-
  HEAVY (not in the default build target): the unconditional forms of the
  transposition results of DoubleDealSecurity/CovariantNarrow.lean.
  * Check A, `pairsCheck cell0Pairs` (shared by `Cov0Checks` and
    `CovariantAffine.AffChecks`), one `decide!` per pair, and check B, one `decide!` per
    representative `e`, are the generated file `CovariantNarrowChecks.lean`
    (`pair_ok_*`, `cell0PairsCheck_ok`; `check_e1` … `check_e51`, `checks_all`). This
    module runs no `decide!`.
  Timing and memory: see `../README.md` (module table) for the measured figures and
  their scope. Built and audited by the `doubledeal-security-heavy` CI job.
  Python reproduction: `analysis/v12-covariant/cell0_witness.py`.
-/
import DoubleDealSecurity.CovariantNarrow
import DoubleDealSecurityHeavy.CovariantNarrowChecks

namespace DoubleDeal.Security.CovariantNarrow

open DoubleDeal Relabel

/-- (PROVED) Both finite checks. -/
theorem cov0Checks_ok : Cov0Checks := ⟨cell0PairsCheck_ok, checks_all⟩

/-- (PROVED, unconditional) The covariant round statement holds for every
    transposition: for all card values `a ≠ b` there is NO relabelling `τ` with
    `unkeyedWithMix (swap a b · m) = τ · unkeyedWithMix m` on every deck. This is
    the statement of `roundBody_covariant_iff_id` restricted to `σ = swap a b`; the
    general statement (all σ) is `roundBody_covariant_iff_id` (`V10Sym.lean`). -/
theorem roundBody_not_covariant_swap (a b : Fin 52) (hab : a ≠ b) :
    ¬ Covariant (Equiv.swap a b) unkeyedWithMix :=
  not_covariant_swap_of_check cov0Checks_ok a b hab

/-- (PROVED, unconditional) The commuting case (τ = σ) of
    `roundBody_not_covariant_swap`: no transposition commutes with the unkeyed
    round body on every deck. -/
theorem roundBody_not_commutes_swap (a b : Fin 52) (hab : a ≠ b) :
    ¬ CommutesOnDecks (Equiv.swap a b) unkeyedWithMix :=
  fun hc => roundBody_not_covariant_swap a b hab ⟨_, hc⟩

/-- (PROVED, a reduction, unconditional) The covariant round statement follows from
    `PrimeNonSwapCase`: its special case for σ of prime order `p ≤ 52` that are
    neither a transposition nor a `v10Sym`. That case is the HYPOTHESIS `h` here; it is
    proved in `V10Sym.lean` (`CovariantNarrow.primeNonSwapCase`). The excluded σ are proved non-covariant for every τ: transpositions
    by `roundBody_not_covariant_swap`, nontrivial `v10Sym` by
    `roundBody_not_covariant_of_stem`. -/
theorem roundBody_covariant_iff_id_of_prime_nonswap (h : PrimeNonSwapCase) (σ : Relabel) :
    Covariant σ unkeyedWithMix ↔ σ = 1 :=
  roundBody_covariant_iff_id_of_prime_nonswap_of_check cov0Checks_ok h σ

/-- (PROVED, unconditional) `PrimeNonSwapCase` is EQUIVALENT to the covariant round
    statement `roundBody_covariant_iff_id` (for all σ). -/
theorem prime_nonswap_case_iff :
    PrimeNonSwapCase ↔ (∀ σ : Relabel, Covariant σ unkeyedWithMix ↔ σ = 1) :=
  prime_nonswap_case_iff_of_check cov0Checks_ok

end DoubleDeal.Security.CovariantNarrow
