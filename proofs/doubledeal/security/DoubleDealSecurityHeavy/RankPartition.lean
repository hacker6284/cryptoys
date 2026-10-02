/-
  HEAVY (not in the default build target): the unconditional forms of the rank-partition
  results of DoubleDealSecurity/RankPartition.lean.
  * The finite checks `RankChecks` (family structure and the 27 stem-cell-0 values) are
    the generated file `RankPartitionChecks.lean` (`fam_struct_D`, `fam_c0_D_k_i`,
    `rankChecks_ok`); this module runs no `decide!`.
  Scope: these say only that a σ with `Cell0Cov σ τ` (in particular every covariant σ)
  permutes the 13 rank classes. They do NOT say σ is affine, that τ = σ, or anything about
  suits; `roundBody_covariant_iff_id` stays open and keeps its `sorry`.
  Timing and memory: see `../README.md` (module table). Built and audited by the
  `doubledeal-security-heavy` CI job.
  Python reproduction: `analysis/v12-primenonswap/rank_family.py`.
-/
import DoubleDealSecurity.RankPartition
import DoubleDealSecurityHeavy.RankPartitionChecks

namespace DoubleDeal.Security.RankPartition

open DoubleDeal Relabel
open DoubleDeal.Security.CovariantNarrow (Cell0Cov cell0Subgroup)

/-- (PROVED, unconditional) If `Cell0Cov σ τ`, σ maps cards of equal rank (`c % 13`) to
    cards of equal rank. -/
theorem cell0Cov_rank {σ τ : Relabel} (h : Cell0Cov σ τ) {a b : Fin 52}
    (hab : a.val % 13 = b.val % 13) : (σ a).val % 13 = (σ b).val % 13 :=
  cell0Cov_rank_of_checks rankChecks_ok h hab

/-- (PROVED, unconditional) If `Cell0Cov σ τ`, two cards have equal rank iff their
    σ-images do. -/
theorem cell0Cov_rank_iff {σ τ : Relabel} (h : Cell0Cov σ τ) (a b : Fin 52) :
    (σ a).val % 13 = (σ b).val % 13 ↔ a.val % 13 = b.val % 13 :=
  cell0Cov_rank_iff_of_checks rankChecks_ok h a b

/-- (PROVED, unconditional) Every σ covariant for the unkeyed round body (for some output
    relabelling τ) maps cards of equal rank to cards of equal rank. One step toward
    `PrimeNonSwapCase`; NOT the conjecture `roundBody_covariant_iff_id`. -/
theorem covariant_rank {σ : Relabel} (h : Covariant σ unkeyedWithMix) {a b : Fin 52}
    (hab : a.val % 13 = b.val % 13) : (σ a).val % 13 = (σ b).val % 13 :=
  covariant_rank_of_checks rankChecks_ok h hab

/-- (PROVED, unconditional) `cell0Subgroup` lies in the rank-partition stabiliser
    `rankStab` (S4 ≀ S13; that identification is not a Lean theorem). Nothing is proved
    about the induced map on the 13 rank classes or about the suit parts. -/
theorem cell0Subgroup_le_rankStab : cell0Subgroup ≤ rankStab :=
  cell0Subgroup_le_rankStab_of_checks rankChecks_ok

end DoubleDeal.Security.RankPartition
