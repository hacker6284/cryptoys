/-
  Step 3 toward `PrimeNonSwapCase` (NOT `PrimeNonSwapCase` by itself, NOT the covariant round
  conjecture `roundBody_covariant_iff_id`, which keeps its `sorry`): for a relabelling with
  the seat-26 condition, the output relabelling is the input one, and the rank map is a shift.

  Statement (`cell0Cov_tau_of_checks`, GIVEN the finite checks `RankChecks`, `AffRankChecks`
  and `TauChecks`; unconditional in the heavy library): if `Cell0Cov σ τ`, then `τ = σ` and
  for some `u`, `rk (σ c) = rk c + u` for every card `c`. Nothing is claimed about labels.

  A. Symbolic: the row amounts of a packet depend only on its ranks mod 13
     (`rowAmts_congr`), so by `StemPosition.stemPos_zero` stem cell 0 of `σ·m` is σ of the
     card of `m` at the seat `(ρ, rowAmts (scaleP l m) ρ % 13)` for some row `ρ`, where
     `scaleP l m` is a packet with ranks `l · rank` (mod 13) and `rk ∘ σ = l · rk`.
  B. `tau_step`: on the two decks of `V10SymLists.lean` (stem cell 0 = card 0 on both), the
     four candidate cards of the two decks meet only in card 0 if `l = 1` and are disjoint
     otherwise (`TauChecks`). So `l = 1` and `σ 0 = τ 0`.
  C. `cell0Cov_tau_of_checks`: by `RankAffine` the rank map is `l · rk + u`; composing with
     the rank shift `v10Sym a 0`, `l · a = -u`, makes it linear, so `l = 1` by B; conjugating
     by the `v10Sym r y` that sends card 0 to any card `c` (`exists_v10Sym_zero`) gives
     `σ c = τ c`.

  Write-up: `../analysis/v12-primenonswap/NOTES.md`; data: `v10sym_witness.py`.
-/
import DoubleDealSecurity.RankAffine

namespace DoubleDeal.Security.TauEq

open DoubleDeal Relabel
open DoubleDeal.Security (permDeck isDeck_permDeck rel_permDeck)
open DoubleDeal.Security.CovariantNarrow (Cell0Cov cell0Cov_mul cell0Cov_v10Sym cell0Cov_conj
  g0 g0_eq exists_v10Sym_zero)
open DoubleDeal.Security.StemPosition (rowAmts c0Row rowSeat stemPos_zero)
open DoubleDeal.Security.StemCoupling (rowRead readAmt nextRow rowAmts_eq_iff rowTotal_eq_sum)
open DoubleDeal.Security.RankPartition (swapsPerm RankChecks)
open DoubleDeal.Security.RankAffine (AffRankChecks cell0Cov_rk_affine_of_checks)

/-! ## A. Row amounts read ranks mod 13 only -/

theorem rowTurnV10_congr {x x' : Fin 13 → Nat}
    (h : ∀ j, ((rank (x j) : ℕ) : ZMod 13) = ((rank (x' j) : ℕ) : ZMod 13)) :
    rowTurnV10 x = rowTurnV10 x' := by
  unfold rowTurnV10
  rw [← ZMod.natCast_eq_natCast_iff', rowTotal_eq_sum, rowTotal_eq_sum]
  push_cast
  exact Finset.sum_congr rfl fun j _ => by rw [h j]

/-- (PROVED) Two packets with the same ranks mod 13 at every seat have the same row
    amounts. -/
theorem rowAmts_congr {m m' : Fin 52 → Nat}
    (h : ∀ s, ((rank (m s) : ℕ) : ZMod 13) = ((rank (m' s) : ℕ) : ZMod 13)) :
    rowAmts m = rowAmts m' := by
  have hm := (rowAmts_eq_iff m (rowAmts m)).mp fun _ => rfl
  funext r
  refine ((rowAmts_eq_iff m' (rowAmts m)).mpr (fun ρ => ?_) r).symm
  rw [← hm ρ]
  exact rowTurnV10_congr fun j => (h _).symm

-- `scaleP l m` (ranks `l · rank`, via `cardOfRk`) and `rank_scaleP`: `SumRanksV10.lean`.

/-- (PROVED) If `rk ∘ σ = l · rk`, the σ-image of `permDeck π` has the row amounts of
    `scaleP l (permDeck π)`. -/
theorem rowAmts_rel_scale {σ : Relabel} {l : ZMod 13} (hl : ∀ c, rk (σ c) = l * rk c)
    (π : Relabel) : rowAmts (permDeck (σ * π)) = rowAmts (scaleP l (permDeck π)) :=
  rowAmts_congr fun s => by
    rw [rank_scaleP]
    exact hl (π s)

/-- The candidate card of row `ρ` of deck `π` for the rank scaling `l`. -/
def candCard (l : ZMod 13) (π : Relabel) (ρ : Fin 4) : Fin 52 :=
  π (rowSeat (rowAmts (scaleP l (permDeck π))) ρ)

/-- (PROVED) If `rk ∘ σ = l · rk`, then stem cell 0 of `σ · permDeck π` is σ of a candidate
    card. -/
theorem cand_of_cell0Cov {σ τ : Relabel} (h : Cell0Cov σ τ) {l : ZMod 13}
    (hl : ∀ c, rk (σ c) = l * rk c) (π : Relabel) :
    ∃ ρ, (σ (candCard l π ρ)).val = τ.app (unkeyedNoMix (permDeck π) 0) := by
  refine ⟨c0Row (permDeck (σ * π)), ?_⟩
  rw [← h _ (isDeck_permDeck π), rel_permDeck, stemPos_zero, rowAmts_rel_scale hl]
  rfl

/-! ## B. The two decks -/

/-- Deck `i` of step 3, as a permutation (seat ↦ card). -/
def tauPerm (i : Fin 2) : Relabel := swapsPerm (tauSwaps.getD i.val [])

/-- Stem cell 0 of deck `i` is card 0. -/
abbrev tauG0 (i : Fin 2) : Prop := g0 (permDeck (tauPerm i)) = 0

/-- The candidate cards of the two decks for `l` meet only in card 0, and only if `l = 1`. -/
abbrev tauCand (l : ZMod 13) : Prop :=
  ∀ ρ ρ' : Fin 4, candCard l (tauPerm 0) ρ = candCard l (tauPerm 1) ρ' →
    l = 1 ∧ candCard l (tauPerm 0) ρ = 0

/-- The finite checks of step 3 (discharged by kernel `decide!` in the heavy library,
    `TauEq.tauChecks_ok`). -/
abbrev TauChecks : Prop := (∀ i, tauG0 i) ∧ ∀ l : ZMod 13, l ≠ 0 → tauCand l

/-- (PROVED, GIVEN `TauChecks`) If `Cell0Cov σ τ` and `rk ∘ σ = l · rk` with `l ≠ 0`, then
    `l = 1` and `σ 0 = τ 0`. -/
theorem tau_step (hT : TauChecks) {σ τ : Relabel} (h : Cell0Cov σ τ) {l : ZMod 13}
    (hl0 : l ≠ 0) (hl : ∀ c, rk (σ c) = l * rk c) : l = 1 ∧ σ 0 = τ 0 := by
  have hc : ∀ i, ∃ ρ, σ (candCard l (tauPerm i) ρ) = τ 0 := by
    intro i
    obtain ⟨ρ, hρ⟩ := cand_of_cell0Cov h hl (tauPerm i)
    rw [← g0_eq, hT.1 i, show (0 : Nat) = (0 : Fin 52).val from rfl, app_fin] at hρ
    exact ⟨ρ, Fin.ext hρ⟩
  obtain ⟨ρ0, h0⟩ := hc 0
  obtain ⟨ρ1, h1⟩ := hc 1
  obtain ⟨hl1, hz⟩ := hT.2 l hl0 ρ0 ρ1 (σ.injective (h0.trans h1.symm))
  exact ⟨hl1, by rw [hz] at h0; exact h0⟩

/-! ## C. τ = σ -/

/-- (PROVED, GIVEN `TauChecks`) If `Cell0Cov σ τ` and σ preserves `rk`, then `τ = σ`. -/
theorem tau_eq_of_rk (hT : TauChecks) {σ τ : Relabel} (h : Cell0Cov σ τ)
    (hl : ∀ c, rk (σ c) = rk c) : τ = σ := by
  ext1 c
  obtain ⟨r, y, hr⟩ := exists_v10Sym_zero c
  set w := v10Sym r y with hw
  have hc : Cell0Cov (w⁻¹ * σ * w) (w⁻¹ * τ * w) := cell0Cov_conj (sumRanksV10_commutes_v10Sym r y)
    (by simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] using h)
  have hl' : ∀ x, rk ((w⁻¹ * σ * w) x) = 1 * rk x := by
    intro x
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, hw, rk_v10Sym_inv, hl, rk_v10Sym]
    ring
  have := (tau_step hT hc one_ne_zero hl').2
  simp only [Equiv.Perm.mul_apply] at this
  have hw0 : w 0 = c := hr
  rw [hw0] at this
  exact (w⁻¹.injective this).symm

theorem exists_shift : ∀ l u : ZMod 13, l ≠ 0 → ∃ a : Fin 13, l * (a.val : ZMod 13) + u = 0 := by
  decide

/-- (PROVED, GIVEN the finite checks `RankChecks`, `AffRankChecks`, `TauChecks` as hypotheses)
    If `Cell0Cov σ τ`, then `τ = σ` and the rank map of σ is a shift. Unconditional form:
    heavy library, `TauEq.cell0Cov_tau`. -/
theorem cell0Cov_tau_of_checks (hR : RankChecks) (hA : AffRankChecks) (hT : TauChecks)
    {σ τ : Relabel} (h : Cell0Cov σ τ) : τ = σ ∧ ∃ u : ZMod 13, ∀ c, rk (σ c) = rk c + u := by
  obtain ⟨l, u, hl0, hlu⟩ := cell0Cov_rk_affine_of_checks hR hA h
  obtain ⟨a, ha⟩ := exists_shift l u hl0
  set v := v10Sym a 0 with hv
  have hc : Cell0Cov (σ * v) (τ * v) :=
    cell0Cov_mul h (cell0Cov_v10Sym a 0)
  have hl : ∀ c, rk ((σ * v) c) = l * rk c := by
    intro c
    rw [Equiv.Perm.mul_apply, hlu, hv, rk_v10Sym]
    linear_combination ha
  have hl1 := (tau_step hT hc hl0 hl).1
  subst hl1
  have heq := tau_eq_of_rk hT hc (fun c => by rw [hl]; ring)
  refine ⟨mul_right_cancel heq, u, fun c => ?_⟩
  rw [hlu]; ring

end DoubleDeal.Security.TauEq
