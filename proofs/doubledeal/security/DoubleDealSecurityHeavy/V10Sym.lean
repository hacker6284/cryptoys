/-
  HEAVY (not in the default build target): the unconditional forms of steps 2-4 of the
  seat-26 argument (DoubleDealSecurity/RankAffine.lean, TauEq.lean, LabelStep.lean).
  * The finite checks are `RankChecks` (`RankPartitionChecks.lean`), `AffChecks`
    (`CovariantAffineChecks.lean`) and the generated `V10SymChecks.lean` (`AffRankChecks`,
    `TauChecks`, `LabelChecks`); this module runs no `decide!`.
  Scope: every σ with the seat-26 condition `Cell0Cov σ τ` (some τ) is a `v10Sym a x` and
  τ = σ (`LabelStep.cell0Cov_mem_v10Sym`); hence the covariant round statement
  `roundBody_covariant_iff_id` (only the identity is covariant for the unkeyed round body;
  a one-round symmetry result, not a security bound), and from it, through the
  default-library reductions `fullRound_commutes_iff_id_of_covariant` and
  `encrypt6_commutes_iff_id_of_covariant` (hypothesis `CovariantOnlyId`, discharged here by
  `fun σ => (roundBody_covariant_iff_id σ).1`), the unconditional `fullRound_commutes_iff_id`
  and `encrypt6_commutes_iff_id`. The default library states none of these three without
  a hypothesis and has no `sorry`.
  Timing and memory: see `../README.md` (module table). Built and audited by the
  `doubledeal-security-heavy` CI job.
  Python reproduction: `analysis/v12-primenonswap/v10sym_witness.py`.
-/
import DoubleDealSecurity.LabelStep
import DoubleDealSecurityHeavy.RankPartitionChecks
import DoubleDealSecurityHeavy.CovariantNarrow
import DoubleDealSecurityHeavy.CovariantAffine
import DoubleDealSecurityHeavy.V10SymChecks

namespace DoubleDeal.Security

open DoubleDeal Relabel
open DoubleDeal.Security.CovariantNarrow (Cell0Cov)

/-- (PROVED, unconditional) If `Cell0Cov σ τ`, the rank map of σ is affine. -/
theorem RankAffine.cell0Cov_rk_affine {σ τ : Relabel} (h : Cell0Cov σ τ) :
    ∃ l u : ZMod 13, l ≠ 0 ∧ ∀ c, rk (σ c) = l * rk c + u :=
  RankAffine.cell0Cov_rk_affine_of_checks RankPartition.rankChecks_ok
    RankAffine.affRankChecks_ok h

/-- (PROVED, unconditional) If `Cell0Cov σ τ`, then τ = σ and the rank map of σ is a
    shift. -/
theorem TauEq.cell0Cov_tau {σ τ : Relabel} (h : Cell0Cov σ τ) :
    τ = σ ∧ ∃ u : ZMod 13, ∀ c, rk (σ c) = rk c + u :=
  TauEq.cell0Cov_tau_of_checks RankPartition.rankChecks_ok RankAffine.affRankChecks_ok
    TauEq.tauChecks_ok h

/-- (PROVED) All the finite checks of steps 1-4. -/
theorem LabelStep.v10SymChecks_ok : LabelStep.V10SymChecks :=
  ⟨RankPartition.rankChecks_ok, CovariantAffine.affChecks_ok, RankAffine.affRankChecks_ok,
    TauEq.tauChecks_ok, LabelStep.labelChecks_ok⟩

/-- (PROVED, unconditional) If `Cell0Cov σ τ`, then σ is a `v10Sym a x` and τ = σ. -/
theorem LabelStep.cell0Cov_mem_v10Sym {σ τ : Relabel} (h : Cell0Cov σ τ) :
    (∃ (a : Fin 13) (x : Fin 4), σ = v10Sym a x) ∧ τ = σ :=
  LabelStep.cell0Cov_mem_v10Sym_of_checks LabelStep.v10SymChecks_ok h

/-- (PROVED, unconditional) The seat-26 condition holds exactly for the pairs
    `(v10Sym a x, v10Sym a x)`. -/
theorem LabelStep.cell0Cov_iff (σ τ : Relabel) :
    Cell0Cov σ τ ↔ (∃ (a : Fin 13) (x : Fin 4), σ = v10Sym a x) ∧ τ = σ :=
  LabelStep.cell0Cov_iff_of_checks LabelStep.v10SymChecks_ok σ τ

/-- (PROVED, unconditional) The covariant round statement: σ is covariant for the unkeyed
    round body (for some output relabelling τ, `F(σ·m) = τ·F(m)` on every deck,
    `F = GridCycle ∘ stem`) iff σ = 1. A one-round symmetry statement, not a security
    bound. Default library: `LabelStep.roundBody_covariant_iff_id_of_checks`, given
    `V10SymChecks`. -/
theorem roundBody_covariant_iff_id (σ : Relabel) :
    Covariant σ unkeyedWithMix ↔ σ = 1 :=
  LabelStep.roundBody_covariant_iff_id_of_checks LabelStep.v10SymChecks_ok σ

/-- (PROVED, unconditional) No nontrivial σ commutes with the full round for all keys. -/
theorem fullRound_commutes_iff_id (σ : Relabel) :
    (∀ pos, CommutesOnDecks σ (fun m => fullRound m pos)) ↔ σ = 1 :=
  fullRound_commutes_iff_id_of_covariant (fun σ => (roundBody_covariant_iff_id σ).1) σ

/-- (PROVED, unconditional) No nontrivial σ gives `E_K(σM) = σ E_K(M)` for all permutation
    round keys and decks (`encrypt6` with permutation keys; a symmetry statement, not a
    security bound). -/
theorem encrypt6_commutes_iff_id (σ : Relabel) :
    (∀ k0 kMix kF, CommutesOnDecks σ (fun m => encrypt6P m k0 kMix kF)) ↔ σ = 1 :=
  encrypt6_commutes_iff_id_of_covariant (fun σ => (roundBody_covariant_iff_id σ).1) σ

/-- (PROVED, unconditional) `PrimeNonSwapCase`: no σ of prime order `p ≤ 52` that is neither
    a transposition nor a `v10Sym` is covariant (from `roundBody_covariant_iff_id` via
    `CovariantNarrow.prime_nonswap_case_iff`). -/
theorem CovariantNarrow.primeNonSwapCase : CovariantNarrow.PrimeNonSwapCase :=
  CovariantNarrow.prime_nonswap_case_iff.2 roundBody_covariant_iff_id

end DoubleDeal.Security
