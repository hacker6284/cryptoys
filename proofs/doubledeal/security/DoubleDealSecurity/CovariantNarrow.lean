/-
  Narrowing the covariant round conjecture `roundBody_covariant_iff_id`
  (`Rounds.lean`, DRAFT-SORRY; roadmap milestone M4 (security README, Roadmap)).

  The conjecture itself is NOT proved here, and its statement, name and `sorry` are
  not touched. This file proves separate theorems around it (`F = unkeyedWithMix`,
  the unkeyed round body, GridCycle ∘ stem):

  A. Algebra of covariance (no computation).
     * `covPair_unique`: the output relabelling τ in `Covariant σ F` is unique.
     * `covPair_one_iff`: τ = 1 ↔ σ = 1.
     * `covPair_mul`, `covPair_inv`, `covSubgroup`: the covariant σ form a subgroup
       of the 52! relabellings; likewise the commuting σ (`commSubgroup`).
     * `roundBody_covariant_iff_id_of_prime`: the conjecture follows from its
       special case for σ of prime order p ≤ 52 (the hypothesis `h`; not proved).
       `prime_case_iff` proves that `h` is EQUIVALENT to the conjecture, so this is
       a reformulation, not a weaker target. Same for the commuting case:
       `roundBody_commutes_iff_id_of_prime`.
  B. The commuting case (τ = σ) and survival.
     * `commutes_sr_iff_gc`: if `F` commutes with σ on every deck, then at every
       deck SumRanks commutes with σ iff GridCycle commutes with σ at the stem
       output, and so (`commutes_card_survivors_eq`) the SumRanks and GridCycle
       survivor sets of σ have the same size.
  C. The covariant case for every transposition (any τ), GIVEN `Cov0Checks`
     (`not_covariant_swap_of_check`; unconditional in the heavy library:
     `roundBody_not_covariant_swap`, and its commuting corollary
     `roundBody_not_commutes_swap`), via the seat-26 condition `Cell0Cov`.
     `roundBody_covariant_iff_id_of_prime_nonswap_of_check`: given `Cov0Checks`,
     the conjecture follows from its special case for σ of prime order p ≤ 52 that
     are neither a transposition nor a `v10Sym` (the hypothesis; not proved;
     `prime_nonswap_case_iff_of_check`: equivalent to the conjecture). Unconditional
     form in the heavy library: `roundBody_covariant_iff_id_of_prime_nonswap`.
  D. `roundBody_covariant_iff_id_of_cell0` and `…_of_cell0_prime`: the conjecture
     follows from a single-cell SumRanks statement `hcell` (all σ, resp. σ of prime
     order p ≤ 52). `hcell` is a SUFFICIENT condition, not known to be true or
     necessary: `hcell` implies the conjecture; the converse is not known (`Cell0Cov`
     is weaker than covariance, so `hcell` might be false even if the conjecture is true).

  Open after this file: the conjecture for σ of prime order p ≤ 52 that are neither
  a transposition nor a `v10Sym` (exactly the hypothesis of
  `roundBody_covariant_iff_id_of_prime_nonswap`). Write-up:
  `../analysis/v12-covariant/NOTES.md`. The affine relabellings inside that case are
  handled in `CovariantAffine.lean` (`../analysis/v12-primenonswap/NOTES.md`).
-/
import DoubleDealSecurity.GridCycleSurvival
import DoubleDealSecurity.SumRanksDP.Main
import DoubleDealSecurity.PermKeys
import DoubleDealSecurity.CovariantNarrowLists
import DoubleDeal.Concrete
import Mathlib

namespace DoubleDeal.Security.CovariantNarrow

open DoubleDeal Relabel Finset
open DoubleDeal.Security (isDeck_rel isDeck_unkeyedNoMix isDeck_unkeyedWithMix)
/- The one name used from `GridCycleSurvival.lean`, kept to this single `open` line. -/
open DoubleDeal.Security.GridCycleSurvival (gcSurvivors)

/-! ## A. Algebra of covariance -/

/-- `F(σ·m) = τ·F(m)` on every deck (the witness form of `Covariant σ F`). -/
def CovPair (σ τ : Relabel) : Prop :=
  ∀ m, IsDeck m → unkeyedWithMix (rel σ m) = rel τ (unkeyedWithMix m)

theorem covariant_iff_exists (σ : Relabel) :
    Covariant σ unkeyedWithMix ↔ ∃ τ, CovPair σ τ := Iff.rfl

theorem commutesOnDecks_iff_covPair (σ : Relabel) :
    CommutesOnDecks σ unkeyedWithMix ↔ CovPair σ σ := Iff.rfl

/-- A relabelling that fixes some deck is the identity. -/
theorem eq_one_of_rel_eq {σ : Relabel} {m : Fin 52 → Nat} (hm : IsDeck m) (h : rel σ m = m) :
    σ = 1 := by
  apply Equiv.ext; intro c
  obtain ⟨i, hi⟩ := isDeck_surj hm c.isLt
  have := congrFun h i
  simp only [rel, hi, app_fin] at this
  exact Fin.ext this

/-- (PROVED) The output relabelling is unique. -/
theorem covPair_unique {σ τ τ' : Relabel} (h : CovPair σ τ) (h' : CovPair σ τ') : τ = τ' := by
  apply Equiv.ext; intro c
  have hd := isDeck_unkeyedWithMix isDeck_idDeck
  obtain ⟨i, hi⟩ := isDeck_surj hd c.isLt
  have e := (h idDeck isDeck_idDeck).symm.trans (h' idDeck isDeck_idDeck)
  have := congrFun e i
  simp only [rel, hi, app_fin] at this
  exact Fin.ext this

theorem covPair_one : CovPair 1 1 := fun m _ => by rw [rel_one, rel_one]

theorem covPair_mul {σ τ σ' τ' : Relabel} (h : CovPair σ τ) (h' : CovPair σ' τ') :
    CovPair (σ * σ') (τ * τ') := by
  intro m hm
  rw [rel_mul, h _ (isDeck_rel σ' hm), h' m hm, rel_mul]

theorem covPair_inv {σ τ : Relabel} (h : CovPair σ τ) : CovPair σ⁻¹ τ⁻¹ := by
  intro m hm
  have hm' := isDeck_rel σ⁻¹ hm
  have e := h _ hm'
  rw [← rel_mul, mul_inv_cancel, rel_one] at e
  rw [e, ← rel_mul, inv_mul_cancel, rel_one]

/-- (PROVED) τ = 1 exactly when σ = 1. -/
theorem covPair_one_iff {σ τ : Relabel} (h : CovPair σ τ) : τ = 1 ↔ σ = 1 := by
  constructor
  · rintro rfl
    have e := h idDeck isDeck_idDeck
    rw [rel_one] at e
    exact eq_one_of_rel_eq isDeck_idDeck (unkeyedWithMix_injective e)
  · rintro rfl
    exact covPair_unique h covPair_one

/-- (PROVED) The σ that make the round body covariant form a subgroup. -/
def covSubgroup : Subgroup Relabel where
  carrier := {σ | Covariant σ unkeyedWithMix}
  one_mem' := ⟨1, covPair_one⟩
  mul_mem' := fun ⟨τ, h⟩ ⟨τ', h'⟩ => ⟨τ * τ', covPair_mul h h'⟩
  inv_mem' := fun ⟨τ, h⟩ => ⟨τ⁻¹, covPair_inv h⟩

/-- (PROVED) The σ that commute with the round body on every deck form a subgroup. -/
def commSubgroup : Subgroup Relabel where
  carrier := {σ | CommutesOnDecks σ unkeyedWithMix}
  one_mem' := covPair_one
  mul_mem' := fun h h' => covPair_mul h h'
  inv_mem' := fun h => covPair_inv h

/-- A subgroup of the relabellings with no element of prime order `p ≤ 52` is trivial. -/
theorem eq_one_of_no_prime_order (H : Subgroup Relabel)
    (h : ∀ σ ∈ H, ∀ p : ℕ, p.Prime → p ≤ 52 → orderOf σ = p → False) :
    ∀ σ ∈ H, σ = 1 := by
  intro σ hσ
  by_contra hne
  have hbot : H ≠ ⊥ := fun hb => hne (by rw [hb] at hσ; exact (Subgroup.mem_bot).1 hσ)
  have h1 : 1 < Nat.card H := (Subgroup.one_lt_card_iff_ne_bot H).2 hbot
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (Nat.ne_of_gt h1)
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hpd
  have hdvd : p ∣ Nat.factorial 52 := by
    have h2 := Subgroup.card_subgroup_dvd_card H
    rw [Nat.card_eq_fintype_card (α := Relabel), Fintype.card_perm, Fintype.card_fin] at h2
    exact hpd.trans h2
  have hp52 : p ≤ 52 := (Nat.Prime.dvd_factorial hp).1 hdvd
  exact h (x : Relabel) x.2 p hp hp52 ((Subgroup.orderOf_coe x).trans hx)

/-- (PROVED, a reduction) The covariant round conjecture follows from its special
    case for relabellings of prime order `p ≤ 52`. The special case is the
    HYPOTHESIS `h`; it is not proved here. -/
theorem roundBody_covariant_iff_id_of_prime
    (h : ∀ σ : Relabel, ∀ p : ℕ, p.Prime → p ≤ 52 → orderOf σ = p →
      ¬ Covariant σ unkeyedWithMix)
    (σ : Relabel) : Covariant σ unkeyedWithMix ↔ σ = 1 := by
  constructor
  · intro hc
    exact eq_one_of_no_prime_order covSubgroup
      (fun τ hτ p hp hp52 ho => h τ p hp hp52 ho hτ) σ hc
  · rintro rfl
    exact ⟨1, covPair_one⟩

/-- An element of prime order is not the identity. -/
theorem ne_one_of_orderOf_prime {σ : Relabel} {p : ℕ} (hp : p.Prime) (ho : orderOf σ = p) :
    σ ≠ 1 := by
  rintro rfl
  rw [orderOf_one] at ho
  exact hp.one_lt.ne ho

/-- (PROVED) The hypothesis of `roundBody_covariant_iff_id_of_prime` is EQUIVALENT to
    the conjecture (the statement of `roundBody_covariant_iff_id`, for all σ). -/
theorem prime_case_iff :
    (∀ σ : Relabel, ∀ p : ℕ, p.Prime → p ≤ 52 → orderOf σ = p →
      ¬ Covariant σ unkeyedWithMix) ↔
    (∀ σ : Relabel, Covariant σ unkeyedWithMix ↔ σ = 1) := by
  constructor
  · exact fun h σ => roundBody_covariant_iff_id_of_prime h σ
  · intro h σ p hp _ ho hc
    exact ne_one_of_orderOf_prime hp ho ((h σ).1 hc)

/-- (PROVED, a reduction) The commuting case likewise reduces to prime order `p ≤ 52`. -/
theorem roundBody_commutes_iff_id_of_prime
    (h : ∀ σ : Relabel, ∀ p : ℕ, p.Prime → p ≤ 52 → orderOf σ = p →
      ¬ CommutesOnDecks σ unkeyedWithMix)
    (σ : Relabel) : CommutesOnDecks σ unkeyedWithMix ↔ σ = 1 := by
  constructor
  · intro hc
    exact eq_one_of_no_prime_order commSubgroup
      (fun τ hτ p hp hp52 ho => h τ p hp hp52 ho hτ) σ hc
  · rintro rfl
    exact covPair_one

/-! ## B. The commuting case and survival -/

/-- The stem commutes with σ at `m` when SumRanks does at `layColumnMajor m`. -/
theorem stem_rel_of_sr {σ : Relabel} {m : Fin 52 → Nat}
    (h : sumRanksV10 (relG σ (layColumnMajor m)) = relG σ (sumRanksV10 (layColumnMajor m))) :
    unkeyedNoMix (rel σ m) = rel σ (unkeyedNoMix m) := by
  simp only [unkeyedNoMix]
  rw [layColumnMajor_rel, h]
  rfl

/-- Conversely, the stem commuting at `m` forces SumRanks to commute there. -/
theorem sr_of_stem_rel {σ : Relabel} {m : Fin 52 → Nat}
    (h : unkeyedNoMix (rel σ m) = rel σ (unkeyedNoMix m)) :
    sumRanksV10 (relG σ (layColumnMajor m)) = relG σ (sumRanksV10 (layColumnMajor m)) := by
  simp only [unkeyedNoMix] at h
  rw [layColumnMajor_rel, ← scoopColumnMajor_rel, ← shiftRows_rel] at h
  have h2 := congrArg (fun x => invShiftRows (layColumnMajor x)) h
  simp only [lay_scoop_columnMajor, invShiftRows_shiftRows] at h2
  exact h2

/-- (PROVED) If the round body commutes with σ on every deck, then at every deck
    SumRanks commutes with σ iff GridCycle commutes with σ at the stem output. -/
theorem commutes_sr_iff_gc {σ : Relabel} (hc : CommutesOnDecks σ unkeyedWithMix)
    {m : Fin 52 → Nat} (hm : IsDeck m) :
    sumRanksV10 (relG σ (layColumnMajor m)) = relG σ (sumRanksV10 (layColumnMajor m)) ↔
      mixColumns (rel σ (unkeyedNoMix m)) = rel σ (mixColumns (unkeyedNoMix m)) := by
  have e := hc m hm
  simp only [unkeyedWithMix] at e
  constructor
  · intro h
    rw [stem_rel_of_sr h] at e
    exact e
  · intro h
    apply sr_of_stem_rel
    exact mixColumns_separates (e.trans h.symm)

/-- (PROVED) Under the same hypothesis the SumRanks survivors (`SumRanksDP.survivors`)
    and the GridCycle survivors (`gcSurvivors`, GridCycleSurvival.lean) of σ are equinumerous:
    the stem maps one set onto the other. -/
theorem commutes_card_survivors_eq {σ : Relabel} (hc : CommutesOnDecks σ unkeyedWithMix) :
    (SumRanksDP.survivors σ).card = (gcSurvivors σ).card := by
  let f : Equiv.Perm (Fin 52) → Equiv.Perm (Fin 52) := fun π =>
    deckPerm (unkeyedNoMix (permDeck π)) (isDeck_unkeyedNoMix (isDeck_permDeck π))
  have hf : ∀ π, permDeck (f π) = unkeyedNoMix (permDeck π) :=
    fun π => funext fun i => deckPerm_val _ _ i
  apply card_bij (fun π _ => f π)
  · intro π hπ
    simp only [SumRanksDP.survivors, gcSurvivors, mem_filter, mem_univ,
      true_and] at hπ ⊢
    show mixColumns (rel σ (permDeck (f π))) = rel σ (mixColumns (permDeck (f π)))
    rw [hf]
    exact (commutes_sr_iff_gc hc (isDeck_permDeck π)).1 hπ
  · intro π₁ _ π₂ _ h
    have h' : unkeyedNoMix (permDeck π₁) = unkeyedNoMix (permDeck π₂) := by
      rw [← hf, ← hf, h]
    have h'' : permDeck π₁ = permDeck π₂ := by
      rw [← invUnkeyedNoMix_unkeyedNoMix (permDeck π₁), h', invUnkeyedNoMix_unkeyedNoMix]
    exact Equiv.ext fun i => Fin.ext (congrFun h'' i)
  · intro x hx
    obtain ⟨m, hm, hmx⟩ := unkeyedNoMix_onto_decks (permDeck x) (isDeck_permDeck x)
    refine ⟨deckPerm m hm, ?_, ?_⟩
    · have hpm : permDeck (deckPerm m hm) = m := funext fun i => deckPerm_val m hm i
      simp only [SumRanksDP.survivors, gcSurvivors, mem_filter, mem_univ,
        true_and] at hx ⊢
      show sumRanksV10 (relG σ (layColumnMajor (permDeck (deckPerm m hm)))) =
        relG σ (sumRanksV10 (layColumnMajor (permDeck (deckPerm m hm))))
      rw [hpm]
      refine (commutes_sr_iff_gc hc hm).2 ?_
      rw [hmx]
      exact hx
    · apply Equiv.ext; intro i
      apply Fin.ext
      show (f (deckPerm m hm) i).val = (x i).val
      rw [deckPerm_val]
      have hpm : permDeck (deckPerm m hm) = m := funext fun i => deckPerm_val m hm i
      rw [hpm, hmx]
      rfl

/-- (PROVED) Commuting case, σ outside `v10Sym`: GridCycle must then commute with σ
    on at most `52!/64` decks. (A consequence, not a contradiction.) -/
theorem commutes_gc_le_of_not_v10Sym {σ : Relabel} (hc : CommutesOnDecks σ unkeyedWithMix)
    (h : ¬ ∃ a x, σ = v10Sym a x) :
    64 * (gcSurvivors σ).card ≤ Nat.factorial 52 := by
  have hs := SumRanksDP.sumRanksV10_survival_le σ h
  rw [Fintype.card_perm, Fintype.card_fin, commutes_card_survivors_eq hc] at hs
  exact hs

/-! ## C. The covariant case for transpositions (any output relabelling) -/

/-- The suit-label shift sending card 0's suit to suit `s` (from `ddport.v10sym`). -/
def yOf (s : Nat) : Fin 4 := if s = 0 then 0 else if s = 1 then 2 else if s = 2 then 3 else 1

theorem v10SymFn_zero_table :
    ∀ a : Fin 52, v10SymFn ⟨a.val % 13, Nat.mod_lt _ (by decide)⟩ (yOf (a.val / 13)) 0 = a := by
  decide

theorem exists_v10Sym_zero (a : Fin 52) : ∃ r : Fin 13, ∃ y : Fin 4, v10SymFn r y 0 = a :=
  ⟨_, _, v10SymFn_zero_table a⟩

/-- The necessary condition read off GridCycle's output seat 26 (walk card 0):
    `stem(σ·m)₀ = τ(stem(m)₀)` on every deck. -/
def Cell0Cov (σ τ : Relabel) : Prop :=
  ∀ m, IsDeck m → unkeyedNoMix (rel σ m) 0 = τ.app (unkeyedNoMix m 0)

/-- (PROVED) Covariance implies the seat-26 condition. -/
theorem cell0Cov_of_covPair {σ τ : Relabel} (h : CovPair σ τ) : Cell0Cov σ τ := by
  intro m hm
  have e := congrFun (h m hm) 26
  simp only [unkeyedWithMix, rel] at e
  rwa [mixColumns_seat26, mixColumns_seat26] at e

theorem app_inv_app (ρ : Relabel) (n : Nat) : ρ⁻¹.app (ρ.app n) = n := by
  rw [← app_mul, inv_mul_cancel, app_one]

/-- (PROVED) The seat-26 condition is invariant under conjugation by any relabelling
    that commutes with SumRanks (e.g. every `v10Sym a x`). -/
theorem cell0Cov_conj {ρ σ τ : Relabel} (hsr : CommutesG ρ sumRanksV10)
    (h : Cell0Cov (ρ * σ * ρ⁻¹) τ) : Cell0Cov σ (ρ⁻¹ * τ * ρ) := by
  intro m hm
  have hM := h (rel ρ m) (isDeck_rel ρ hm)
  have e1 : rel (ρ * σ * ρ⁻¹) (rel ρ m) = rel ρ (rel σ m) := by
    rw [← rel_mul, ← rel_mul]
    simp only [mul_assoc, inv_mul_cancel, mul_one]
  have hs : Cards (rel σ m) := fun i => app_lt _ (hm.1 i)
  rw [e1, unkeyedNoMix_commutes ρ hsr (rel σ m) hs,
    unkeyedNoMix_commutes ρ hsr m hm.1] at hM
  simp only [rel] at hM
  have := congrArg ρ⁻¹.app hM
  rw [app_inv_app] at this
  rw [this, app_mul, app_mul]

/-- Two decks with the same stem cell 0 whose σ-images have different stem cell 0
    rule out the seat-26 condition for every τ. -/
theorem not_cell0Cov_of_witness {σ : Relabel} {m1 m2 : Fin 52 → Nat} (h1 : IsDeck m1)
    (h2 : IsDeck m2) (hsame : unkeyedNoMix m1 0 = unkeyedNoMix m2 0)
    (hdiff : unkeyedNoMix (rel σ m1) 0 ≠ unkeyedNoMix (rel σ m2) 0) (τ : Relabel) :
    ¬ Cell0Cov σ τ := by
  intro h
  apply hdiff
  rw [h m1 h1, h m2 h2, hsame]

/-- Stem cell 0, evaluated through snapshots (for kernel `decide!`). -/
def g0 (m : Fin 52 → Nat) : Nat := arrAt (unkeyedNoMixOnce (arrFn (snap m))) 0

theorem g0_eq (m : Fin 52 → Nat) : g0 m = unkeyedNoMix m 0 := by
  unfold g0 unkeyedNoMixOnce
  rw [arrAt_snap, arrFn_snap]

/-- The identity deck with seats `i` and `j` exchanged. -/
def posSwapDeck (i j : Fin 52) : Fin 52 → Nat := permDeck (Equiv.swap i j)

/-! `goodPairs` and `covW` are generated data in `CovariantNarrowLists.lean`
    (`analysis/v12-covariant/cell0_witness.py --lean`). -/

/-- Finite check A: each used position swap keeps stem cell 0 of the identity deck. -/
def goodPairsCheck : Bool :=
  goodPairs.all fun p => g0 (posSwapDeck p.1 p.2) == g0 idDeck

/-- Finite check B for `e`: the witness pair is one of `goodPairs`, and the
    `swap 0 e`-images of the two decks have different stem cell 0. -/
def cov0Check (e : Fin 52) : Bool :=
  let p := covW.getD e.val (0, 0)
  goodPairs.contains p &&
    !(g0 (rel (Equiv.swap 0 e) idDeck) == g0 (rel (Equiv.swap 0 e) (posSwapDeck p.1 p.2)))

/-- Both finite checks (discharged by kernel `decide!` in the heavy library). -/
def Cov0Checks : Prop := goodPairsCheck = true ∧ ∀ e : Fin 52, e ≠ 0 → cov0Check e = true

/-- (PROVED, given the finite checks `Cov0Checks` as a hypothesis) No transposition
    of two card values is covariant for the unkeyed round body, for ANY output
    relabelling: the conjecture `roundBody_covariant_iff_id` holds for every
    transposition. (Unconditional form: heavy library,
    `roundBody_not_covariant_swap`.) -/
theorem not_covariant_swap_of_check (hchk : Cov0Checks) (a b : Fin 52) (hab : a ≠ b) :
    ¬ Covariant (Equiv.swap a b) unkeyedWithMix := by
  rintro ⟨τ, hτ⟩
  obtain ⟨r, y, hr⟩ := exists_v10Sym_zero a
  set ρ := v10Sym r y with hρdef
  have hρ0 : ρ 0 = a := hr
  set e := ρ⁻¹ b with he
  have hρe : ρ e = b := by rw [he, Equiv.Perm.apply_inv_self]
  have he0 : e ≠ 0 := by
    intro h0; apply hab; rw [← hρ0, ← hρe, h0]
  have hσ : Equiv.swap a b = ρ * Equiv.swap 0 e * ρ⁻¹ := by
    rw [← hρ0, ← hρe]; exact Equiv.swap_apply_apply ρ 0 e
  have hsr : CommutesG ρ sumRanksV10 := sumRanksV10_commutes_v10Sym r y
  have hc0 : Cell0Cov (ρ * Equiv.swap 0 e * ρ⁻¹) τ := hσ ▸ cell0Cov_of_covPair hτ
  have hc := cell0Cov_conj hsr hc0
  -- the witness
  have hB := hchk.2 e he0
  unfold cov0Check at hB
  set p := covW.getD e.val (0, 0)
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne] at hB
  obtain ⟨hmem, hne⟩ := hB
  have hA := hchk.1
  unfold goodPairsCheck at hA
  rw [List.all_eq_true] at hA
  have hsame := hA p (List.elem_iff.1 hmem)
  rw [beq_iff_eq, g0_eq, g0_eq] at hsame
  rw [g0_eq, g0_eq] at hne
  exact not_cell0Cov_of_witness isDeck_idDeck (isDeck_permDeck _) hsame.symm hne _ hc

/-- The prime-order case left open after the transpositions and the `v10Sym`:
    no σ of prime order `p ≤ 52` that is neither a transposition nor a `v10Sym` is
    covariant. -/
def PrimeNonSwapCase : Prop :=
  ∀ σ : Relabel, ∀ p : ℕ, p.Prime → p ≤ 52 → orderOf σ = p →
    (∀ a b : Fin 52, σ ≠ Equiv.swap a b) → (∀ (a : Fin 13) (x : Fin 4), σ ≠ v10Sym a x) →
    ¬ Covariant σ unkeyedWithMix

/-- (PROVED, a reduction; GIVEN the finite checks `Cov0Checks` as a hypothesis) The
    conjecture follows from `PrimeNonSwapCase` (the hypothesis `h`; not proved).
    Transpositions are handled by `not_covariant_swap_of_check`, nontrivial `v10Sym`
    by `roundBody_not_covariant_of_stem` (every τ), and the rest of the argument is
    `roundBody_covariant_iff_id_of_prime`. Unconditional form (heavy library):
    `roundBody_covariant_iff_id_of_prime_nonswap`. -/
theorem roundBody_covariant_iff_id_of_prime_nonswap_of_check (hchk : Cov0Checks)
    (h : PrimeNonSwapCase) (σ : Relabel) : Covariant σ unkeyedWithMix ↔ σ = 1 := by
  refine roundBody_covariant_iff_id_of_prime (fun σ p hp hp52 ho => ?_) σ
  have hne := ne_one_of_orderOf_prime hp ho
  by_cases hs : ∃ a b : Fin 52, σ = Equiv.swap a b
  · obtain ⟨a, b, rfl⟩ := hs
    have hab : a ≠ b := by
      rintro rfl
      exact hne (Equiv.swap_self a)
    exact not_covariant_swap_of_check hchk a b hab
  by_cases hv : ∃ (a : Fin 13) (x : Fin 4), σ = v10Sym a x
  · obtain ⟨a, x, rfl⟩ := hv
    exact roundBody_not_covariant_of_stem _ hne (sumRanksV10_commutes_v10Sym a x)
  push_neg at hs hv
  exact h σ p hp hp52 ho hs hv

/-- (PROVED; GIVEN `Cov0Checks`) `PrimeNonSwapCase` is EQUIVALENT to the conjecture. -/
theorem prime_nonswap_case_iff_of_check (hchk : Cov0Checks) :
    PrimeNonSwapCase ↔ (∀ σ : Relabel, Covariant σ unkeyedWithMix ↔ σ = 1) := by
  constructor
  · exact fun h σ => roundBody_covariant_iff_id_of_prime_nonswap_of_check hchk h σ
  · intro h σ p hp _ ho _ _ hc
    exact ne_one_of_orderOf_prime hp ho ((h σ).1 hc)

/-! ## D. Sufficient single-cell conditions (not known to be true or necessary) -/

/-- (PROVED, a reduction) The conjecture follows from the single-cell statement
    `hcell`: every σ satisfying the seat-26 condition `Cell0Cov σ τ` for some τ is a
    `v10Sym`. `hcell` is a HYPOTHESIS and is NOT proved. It is a SUFFICIENT
    condition, not known to be true or necessary: `hcell` implies the conjecture;
    the converse is not known (`Cell0Cov` is weaker than covariance, so `hcell`
    might be false even if the conjecture is true). -/
theorem roundBody_covariant_iff_id_of_cell0
    (hcell : ∀ σ τ : Relabel, Cell0Cov σ τ → ∃ a x, σ = v10Sym a x)
    (σ : Relabel) : Covariant σ unkeyedWithMix ↔ σ = 1 := by
  constructor
  · rintro ⟨τ, hτ⟩
    obtain ⟨a, x, rfl⟩ := hcell σ τ (cell0Cov_of_covPair hτ)
    by_contra hne
    exact roundBody_not_covariant_of_stem _ hne (sumRanksV10_commutes_v10Sym a x) ⟨τ, hτ⟩
  · rintro rfl
    exact ⟨1, covPair_one⟩

/-- (PROVED, a reduction) As `roundBody_covariant_iff_id_of_cell0`, with `hcell`
    only for σ of prime order `p ≤ 52`. `hcell` is a HYPOTHESIS, NOT proved, and a
    SUFFICIENT condition not known to be true or necessary (as above). It is the
    statement sampled by `../analysis/v12-covariant/cell0_sample.py`: a seat-26
    witness for a sampled σ refutes `Cell0Cov σ τ` for every τ for that σ only. -/
theorem roundBody_covariant_iff_id_of_cell0_prime
    (hcell : ∀ σ τ : Relabel, ∀ p : ℕ, p.Prime → p ≤ 52 → orderOf σ = p →
      Cell0Cov σ τ → ∃ a x, σ = v10Sym a x)
    (σ : Relabel) : Covariant σ unkeyedWithMix ↔ σ = 1 := by
  refine roundBody_covariant_iff_id_of_prime (fun σ p hp hp52 ho => ?_) σ
  rintro ⟨τ, hτ⟩
  obtain ⟨a, x, rfl⟩ := hcell σ τ p hp hp52 ho (cell0Cov_of_covPair hτ)
  exact roundBody_not_covariant_of_stem _ (ne_one_of_orderOf_prime hp ho)
    (sumRanksV10_commutes_v10Sym a x) ⟨τ, hτ⟩

end DoubleDeal.Security.CovariantNarrow
