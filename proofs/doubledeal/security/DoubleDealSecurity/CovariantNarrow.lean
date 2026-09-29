/-
  Narrowing the covariant round conjecture `roundBody_covariant_iff_id`
  (`Rounds.lean`, DRAFT-SORRY; milestone 4 of the AES-style roadmap).

  The conjecture itself is NOT proved here, and its statement and name are not
  touched. This file proves separate theorems around it (`F = unkeyedWithMix`,
  the unkeyed round body, GridCycle ∘ stem):

  A. Algebra of covariance (no computation).
     * `covPair_unique`: the output relabelling τ in `Covariant σ F` is unique.
     * `covPair_one_iff`: τ = 1 ↔ σ = 1.
     * `covPair_mul`, `covPair_inv`, `covSubgroup`: the covariant σ form a subgroup
       of the 52! relabellings; likewise the commuting σ (`commSubgroup`).
     * `roundBody_covariant_iff_id_of_prime`: the conjecture FOLLOWS from its
       special case for σ of prime order p ≤ 52 (a reduction, taken as a
       hypothesis; the special case is not proved). Same for the commuting case:
       `roundBody_commutes_iff_id_of_prime`.
  B. The commuting case (τ = σ) and survival.
     * `commutes_sr_iff_gc`: if `F` commutes with σ on every deck, then at every
       deck SumRanks commutes with σ iff GridCycle commutes with σ at the stem
       output, and so (`commutes_card_survivors_eq`) the SumRanks and GridCycle
       survivor sets of σ have the same size.
  C. The commuting case for every transposition.
     * `not_commutes_swap_of_check`: GIVEN the finite check `SwapChecks` (51 kernel
       evaluations, discharged by `decide!` in the heavy library,
       `DoubleDealSecurityHeavy/CovariantNarrow.lean`), no transposition of two
       card values commutes with `F` on every deck. The argument: put the swapped
       pair at walk positions 50, 51 of the GridCycle input, where swapping them
       never changes the seat walk (`BranchNumber.seatW_swap_tail`), so GridCycle
       commutes there, which forces the stem to commute; v10Sym-conjugation
       (SumRanks and the stem commute with `v10Sym`, which acts simply
       transitively on the cards) reduces the 1326 pairs to the 51 pairs `(0, e)`.

  D. The covariant case for every transposition (any τ), GIVEN `Cov0Checks`
     (heavy: `roundBody_not_covariant_swap`), via the seat-26 condition `Cell0Cov`.
  E. `roundBody_covariant_iff_id_of_cell0`: the conjecture follows from a
     single-cell SumRanks statement (hypothesis, not proved).

  Open after this file: the conjecture (covariance, any τ) and even its commuting
  case (τ = σ) for every σ that is neither a transposition nor in `v10Sym`; by A it
  suffices to treat σ of prime order p ≤ 52, and by E it would suffice to prove the
  single-cell statement. Write-up: `../analysis/v12-covariant/NOTES.md`.
-/
import DoubleDealSecurity.GridCycleSurvival
import DoubleDealSecurity.SumRanksDP.Main
import DoubleDealSecurity.PermKeys
import DoubleDeal.Concrete
import Mathlib

namespace DoubleDeal.Security.CovNarrow

open DoubleDeal Relabel Finset
open DoubleDeal.Security (isDeck_rel isDeck_unkeyedNoMix isDeck_unkeyedWithMix)
/- The one name used from `GridCycleSurvival.lean`. Its namespace is renamed
   (`GCSurvival` → `GridCycleSurvival`) by an open PR, so the dependency is kept to
   this single `open` line. -/
open DoubleDeal.Security.GCSurvival (gcSurvivors)

/-! ## A. Algebra of covariance -/

/-- `F(σ·m) = τ·F(m)` on every deck (the witness form of `Covariant σ F`). -/
def CovPair (σ τ : Relabel) : Prop :=
  ∀ m, IsDeck m → unkeyedWithMix (rel σ m) = rel τ (unkeyedWithMix m)

theorem covariant_iff_exists (σ : Relabel) :
    Covariant σ unkeyedWithMix ↔ ∃ τ, CovPair σ τ := Iff.rfl

theorem commutesOnDecks_iff_covPair (σ : Relabel) :
    CommutesOnDecks σ unkeyedWithMix ↔ CovPair σ σ := Iff.rfl

theorem unkeyedWithMix_injective : Function.Injective unkeyedWithMix :=
  Function.LeftInverse.injective invUnkeyedWithMix_rt

/-- The identity deck `i ↦ i`. -/
def idDeck' : Fin 52 → Nat := fun i => i.val

theorem isDeck_idDeck' : IsDeck idDeck' := ⟨fun i => i.isLt, fun _ _ h => Fin.ext h⟩

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
  have hd := isDeck_unkeyedWithMix isDeck_idDeck'
  obtain ⟨i, hi⟩ := isDeck_surj hd c.isLt
  have e := (h idDeck' isDeck_idDeck').symm.trans (h' idDeck' isDeck_idDeck')
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
    have e := h idDeck' isDeck_idDeck'
    rw [rel_one] at e
    exact eq_one_of_rel_eq isDeck_idDeck' (unkeyedWithMix_injective e)
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

/-! ## C. The commuting case for transpositions -/

/-- GridCycle input for the representative pair `(0, e)`, `1 ≤ e ≤ 51`: the other
    50 cards in increasing order, then `0`, then `e` at walk positions 50, 51. -/
def xE (e : Nat) : Fin 52 → Nat := fun i =>
  if i.val = 50 then 0 else if i.val = 51 then e else if i.val + 1 < e then i.val + 1
  else i.val + 2

theorem isDeck_xE {e : Nat} (h0 : e ≠ 0) (h52 : e < 52) : IsDeck (xE e) := by
  constructor
  · intro i
    have := i.isLt
    simp only [xE]
    split_ifs <;> omega
  · intro i j h
    have hi := i.isLt
    have hj := j.isLt
    apply Fin.ext
    simp only [xE] at h
    split_ifs at h <;> omega

/-- The finite check for `e`: the stem does NOT commute with `swap 0 e` at
    `invUnkeyedNoMix (xE e)`. Snapshots (`snap`) keep kernel evaluation linear. -/
def swapCheck (e : Fin 52) : Bool :=
  !(decide (unkeyedNoMixOnce (rel (Equiv.swap 0 e) (arrFn (snap (invUnkeyedNoMix (xE e.val))))) =
    snap (rel (Equiv.swap 0 e) (xE e.val))))

/-- All 51 checks. Discharged by kernel `decide!` in the heavy library. -/
def SwapChecks : Prop := ∀ e : Fin 52, e ≠ 0 → swapCheck e = true

theorem swapCheck_spec {e : Fin 52} (h : swapCheck e = true) :
    unkeyedNoMix (rel (Equiv.swap 0 e) (invUnkeyedNoMix (xE e.val))) ≠
      rel (Equiv.swap 0 e) (xE e.val) := by
  intro heq
  unfold swapCheck unkeyedNoMixOnce at h
  rw [arrFn_snap, heq] at h
  simp only [decide_True, Bool.not_true, Bool.false_eq_true] at h

/-- (PROVED) Swapping the two cards at walk positions 50 and 51 commutes with GridCycle. -/
theorem mixColumns_rel_swap_tail {x : Fin 52 → Nat} (hx : IsDeck x) {a b : Fin 52}
    (ha : x 50 = a.val) (hb : x 51 = b.val) :
    mixColumns (rel (Equiv.swap a b) x) = rel (Equiv.swap a b) (mixColumns x) := by
  have hab : a ≠ b := by
    intro e; rw [e] at ha
    exact absurd (hx.2 (ha.trans hb.symm)) (by decide)
  have hrel : rel (Equiv.swap a b) x = swapAt x 50 51 := by
    funext i
    simp only [rel, swapAt, Function.comp]
    by_cases h50 : i = 50
    · subst h50
      rw [Equiv.swap_apply_left, ha, app_fin, Equiv.swap_apply_left, hb]
    · by_cases h51 : i = 51
      · subst h51
        rw [Equiv.swap_apply_right, hb, app_fin, Equiv.swap_apply_right, ha]
      · rw [Equiv.swap_apply_of_ne_of_ne h50 h51]
        obtain ⟨c, hc⟩ : ∃ c : Fin 52, x i = c.val := ⟨⟨x i, hx.1 i⟩, rfl⟩
        rw [hc, app_fin]
        have hca : c ≠ a := by
          intro e; subst e
          exact h50 (hx.2 (hc.trans ha.symm))
        have hcb : c ≠ b := by
          intro e; subst e
          exact h51 (hx.2 (hc.trans hb.symm))
        rw [Equiv.swap_apply_of_ne_of_ne hca hcb]
  refine (mixColumns_rel_iff_walk _ x hx).2 ?_
  intro n hn
  rw [hrel, walkSeat_eq, walkSeat_eq]
  exact seatW_swap_tail chooseSeat! freeChooser x n hn

/-- The suit-label shift sending card 0's suit to suit `s` (from `ddport.v10sym`). -/
def yOf (s : Nat) : Fin 4 := if s = 0 then 0 else if s = 1 then 2 else if s = 2 then 3 else 1

theorem v10SymFn_zero_table :
    ∀ a : Fin 52, v10SymFn ⟨a.val % 13, Nat.mod_lt _ (by decide)⟩ (yOf (a.val / 13)) 0 = a := by
  decide

theorem exists_v10Sym_zero (a : Fin 52) : ∃ r : Fin 13, ∃ y : Fin 4, v10SymFn r y 0 = a :=
  ⟨_, _, v10SymFn_zero_table a⟩

theorem rel_inj (ρ : Relabel) {m m' : Fin 52 → Nat} (h : rel ρ m = rel ρ m') : m = m' := by
  have := congrArg (rel ρ⁻¹) h
  rwa [← rel_mul, ← rel_mul, inv_mul_cancel, rel_one, rel_one] at this

/-- (PROVED, given the 51 finite checks as the hypothesis `hchk`) No transposition
    of two card values commutes with the unkeyed round body on every deck. -/
theorem not_commutes_swap_of_check (hchk : SwapChecks) (a b : Fin 52) (hab : a ≠ b) :
    ¬ CommutesOnDecks (Equiv.swap a b) unkeyedWithMix := by
  intro hc
  obtain ⟨r, y, hr⟩ := exists_v10Sym_zero a
  set ρ := v10Sym r y with hρdef
  have hρ0 : ρ 0 = a := hr
  set e := ρ⁻¹ b with he
  have hρe : ρ e = b := by rw [he, Equiv.Perm.apply_inv_self]
  have he0 : e ≠ 0 := by
    intro h0; apply hab; rw [← hρ0, ← hρe, h0]
  have hσ : Equiv.swap a b = ρ * Equiv.swap 0 e * ρ⁻¹ := by
    rw [← hρ0, ← hρe]; exact Equiv.swap_apply_apply ρ 0 e
  set s := Equiv.swap (0 : Fin 52) e
  have hsr : CommutesG ρ sumRanksV10 := sumRanksV10_commutes_v10Sym r y
  -- the representative decks
  have hx0 : IsDeck (xE e.val) := isDeck_xE (fun h => he0 (Fin.ext h)) e.isLt
  obtain ⟨m1, hm1, hm1x⟩ := unkeyedNoMix_onto_decks (xE e.val) hx0
  have hm0eq : invUnkeyedNoMix (xE e.val) = m1 := by
    rw [← hm1x, invUnkeyedNoMix_unkeyedNoMix]
  have hm0 : IsDeck (invUnkeyedNoMix (xE e.val)) := hm0eq ▸ hm1
  set m0 := invUnkeyedNoMix (xE e.val)
  have hstem0 : unkeyedNoMix m0 = xE e.val := unkeyedNoMix_invUnkeyedNoMix _
  -- move to the pair (a, b) by ρ
  have hm : IsDeck (rel ρ m0) := isDeck_rel ρ hm0
  have hstem : unkeyedNoMix (rel ρ m0) = rel ρ (xE e.val) := by
    rw [unkeyedNoMix_commutes ρ hsr m0 hm0.1, hstem0]
  have hx : IsDeck (rel ρ (xE e.val)) := isDeck_rel ρ hx0
  have h50 : rel ρ (xE e.val) 50 = a.val := by
    have hx50 : xE e.val 50 = (0 : Fin 52).val := rfl
    show ρ.app (xE e.val 50) = a.val
    rw [hx50, app_fin, hρ0]
  have h51 : rel ρ (xE e.val) 51 = b.val := by
    have hx51 : xE e.val 51 = e.val := rfl
    show ρ.app (xE e.val 51) = b.val
    rw [hx51, app_fin, hρe]
  have hgc := mixColumns_rel_swap_tail hx h50 h51
  have hcm := hc _ hm
  simp only [unkeyedWithMix] at hcm
  rw [hstem, ← hgc] at hcm
  have hstemσ := mixColumns_separates hcm
  -- rewrite both sides through ρ
  have hconj : ∀ z : Fin 52 → Nat, rel (Equiv.swap a b) (rel ρ z) = rel ρ (rel s z) := by
    intro z
    rw [hσ, ← rel_mul, ← rel_mul]
    simp only [mul_assoc, inv_mul_cancel, mul_one]
  rw [hconj, hconj] at hstemσ
  have hs0 : Cards (rel s m0) := fun i => app_lt _ (hm0.1 i)
  rw [unkeyedNoMix_commutes ρ hsr _ hs0] at hstemσ
  exact swapCheck_spec (hchk e he0) (rel_inj ρ hstemσ)

/-! ## D. The covariant case for transpositions (any output relabelling) -/

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

/-- `n mod 52` as a seat (local helper, so this file does not depend on the
    GridCycle-survival list helpers). -/
def seat52 (n : Nat) : Fin 52 := ⟨n % 52, Nat.mod_lt _ (by decide)⟩

/-- The identity deck with seats `i` and `j` exchanged. -/
def posSwapDeck (i j : Nat) : Fin 52 → Nat := permDeck (Equiv.swap (seat52 i) (seat52 j))

/-- The four position pairs used (from `analysis/v12-covariant/cell0_witness.py`). -/
def goodPairs : List (Nat × Nat) := [(1, 2), (1, 3), (1, 5), (1, 34)]

/-- The witness position pair for each representative `e` (entry 0 unused). -/
def covW : List (Nat × Nat) := [(1, 2), (1, 5), (1, 5), (1, 34), (1, 2), (1, 2), (1, 3), (1, 2), (1, 2), (1, 2), (1, 3), (1, 5), (1, 2), (1, 2), (1, 2), (1, 3), (1, 2), (1, 2), (1, 3), (1, 3), (1, 2), (1, 2), (1, 2), (1, 3), (1, 3), (1, 2), (1, 2), (1, 3), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 5), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 3), (1, 2), (1, 2), (1, 3), (1, 5), (1, 2), (1, 2), (1, 3), (1, 2), (1, 2), (1, 2), (1, 3), (1, 5)]

/-- Finite check A: each used position swap keeps stem cell 0 of the identity deck. -/
def goodPairsCheck : Bool :=
  goodPairs.all fun p => g0 (posSwapDeck p.1 p.2) == g0 idDeck'

/-- Finite check B for `e`: the witness pair is one of `goodPairs`, and the
    `swap 0 e`-images of the two decks have different stem cell 0. -/
def cov0Check (e : Fin 52) : Bool :=
  let p := covW.getD e.val (0, 0)
  goodPairs.contains p &&
    !(g0 (rel (Equiv.swap 0 e) idDeck') == g0 (rel (Equiv.swap 0 e) (posSwapDeck p.1 p.2)))

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
  exact not_cell0Cov_of_witness isDeck_idDeck' (isDeck_permDeck _) hsame.symm hne _ hc

/-! ## E. Reduction to a single-cell SumRanks statement -/

/-- (PROVED, a reduction) The covariant round conjecture follows from the
    single-cell statement `hcell`: every σ satisfying the seat-26 condition for some
    τ is a `v10Sym`. `hcell` is a HYPOTHESIS here and is NOT proved (it is the open
    core; measured consistent in `../analysis/v12-covariant/cell0_sample.py`). -/
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

end DoubleDeal.Security.CovNarrow
