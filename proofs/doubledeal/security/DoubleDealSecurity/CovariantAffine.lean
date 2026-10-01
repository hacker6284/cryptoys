/-
  The covariant round conjecture `roundBody_covariant_iff_id` (`Rounds.lean`,
  DRAFT-SORRY) for the AFFINE relabellings: a finite, structured family inside the
  open case `CovariantNarrow.PrimeNonSwapCase`. The conjecture itself, its statement,
  name and `sorry` are not touched, and `PrimeNonSwapCase` is not proved here.

  Affine relabellings. A card is (rank index r = c % 13 ∈ Z13 (A = 0), GF(4) suit
  label l = `suitLabel c`). For `k : Fin 12`
  (unit `u = k + 1` of Z13) and `g : Fin 6` (an element of GL(2,2) acting on the two
  label bits, table `glTab`, `g = 0` the identity), `linSym k g` is
  `(r, l) ↦ (u r, A_g l)`. The affine relabellings are `v10Sym a x * linSym k g`:
  `(r, l) ↦ (u r + a, A_g l ⊕ x)`. These 3744 relabellings form the normalizer of
  `v10Sym` (the 52 translations) in the 52! relabellings (stated here for orientation;
  not a Lean theorem). Those with `(k, g) ≠ (0, 0)` are the 3692 outside `v10Sym`.

  Proved:
  * `cell0Cov_mul`, `cell0Cov_inv`, `cell0Cov_self_of_commutes`: the seat-26
    condition `CovariantNarrow.Cell0Cov` is closed under products and inverses, and
    every relabelling that commutes with SumRanks (e.g. `v10Sym a x`) satisfies it
    with τ = itself.
  * `not_cell0Cov_lin_of_check` (given the finite checks `AffChecks`): for every
    nontrivial linear part `(k, g)`, `linSym k g` fails the seat-26 condition for
    every τ (two decks witness it; `affW`).
  * `not_covariant_affine_of_check`, `not_covariant_affine_right_of_check` (given
    `AffChecks`): `v10Sym a x * linSym k g` and `linSym k g * v10Sym a x` are not
    covariant for ANY τ when `(k, g) ≠ (0, 0)`. Unconditional forms in the heavy
    library (`DoubleDealSecurityHeavy/CovariantAffine.lean`).
  * `covariant_affine_iff_of_check`: given `AffChecks`, an affine relabelling is
    covariant iff it is the identity.

  This covers every element of prime order of the normalizer outside `v10Sym`, but it
  is NOT `PrimeNonSwapCase`: almost all prime-order relabellings are not affine.
  Write-up: `../analysis/v12-primenonswap/NOTES.md`.
-/
import DoubleDealSecurity.CovariantNarrow
import DoubleDealSecurity.CovariantAffineLists

namespace DoubleDeal.Security.CovariantAffine

open DoubleDeal Relabel
open DoubleDeal.Security.CovariantNarrow (Cell0Cov CovPair g0 g0_eq posSwapDeck
  cell0Cov_of_covPair not_cell0Cov_of_witness app_inv_app)

/-! ## The seat-26 condition is a group condition -/

/-- (PROVED) Products. -/
theorem cell0Cov_mul {σ τ σ' τ' : Relabel} (h : Cell0Cov σ τ) (h' : Cell0Cov σ' τ') :
    Cell0Cov (σ * σ') (τ * τ') := by
  intro m hm
  rw [rel_mul, h _ (isDeck_rel σ' hm), h' m hm, app_mul]

/-- (PROVED) Inverses. -/
theorem cell0Cov_inv {σ τ : Relabel} (h : Cell0Cov σ τ) : Cell0Cov σ⁻¹ τ⁻¹ := by
  intro m hm
  have e := h _ (isDeck_rel σ⁻¹ hm)
  rw [← rel_mul, mul_inv_cancel, rel_one] at e
  rw [e, app_inv_app]

/-- (PROVED) A relabelling that commutes with SumRanks (e.g. every `v10Sym a x`)
    satisfies the seat-26 condition with τ = itself. -/
theorem cell0Cov_self_of_commutes {ρ : Relabel} (hsr : CommutesG ρ sumRanksV10) :
    Cell0Cov ρ ρ := by
  intro m hm
  rw [unkeyedNoMix_commutes ρ hsr m hm.1]
  rfl

theorem cell0Cov_v10Sym (a : Fin 13) (x : Fin 4) : Cell0Cov (v10Sym a x) (v10Sym a x) :=
  cell0Cov_self_of_commutes (sumRanksV10_commutes_v10Sym a x)

/-! ## The linear parts -/

/-- GL(2,2) on GF(4) labels `0..3` (bit 0 = `l % 2`, bit 1 = `l / 2`): row `g` lists
    the images of labels 0, 1, 2, 3. Row 0 is the identity. -/
def glTab : List (List Nat) :=
  [[0, 1, 2, 3], [0, 2, 1, 3], [0, 1, 3, 2], [0, 3, 2, 1], [0, 2, 3, 1], [0, 3, 1, 2]]

def glApp (g : Fin 6) (l : Nat) : Nat := (glTab.getD g.val []).getD l 0

/-- The inverse matrix (rows 4 and 5 are the two elements of order 3). -/
def glInv (g : Fin 6) : Fin 6 := if g = 4 then 5 else if g = 5 then 4 else g

/-- `k ↦ k'` with `(k + 1)(k' + 1) ≡ 1 (mod 13)`. -/
def unitInv (k : Fin 12) : Fin 12 :=
  (([0, 6, 8, 9, 7, 10, 1, 4, 2, 3, 5, 11] : List (Fin 12)).getD k.val 0)

/-- The linear relabelling `(r, l) ↦ ((k + 1) r, A_g l)`. -/
def linFn (k : Fin 12) (g : Fin 6) (c : Fin 52) : Fin 52 :=
  ⟨13 * (suitOfLabel (glApp g (suitLabel c.val)) % 4) + ((k.val + 1) * (c.val % 13)) % 13,
    by omega⟩

theorem linFn_left : ∀ (k : Fin 12) (g : Fin 6) (c : Fin 52),
    linFn (unitInv k) (glInv g) (linFn k g c) = c := by decide!

theorem linFn_right : ∀ (k : Fin 12) (g : Fin 6) (c : Fin 52),
    linFn k g (linFn (unitInv k) (glInv g) c) = c := by decide!

def linSym (k : Fin 12) (g : Fin 6) : Relabel where
  toFun := linFn k g
  invFun := linFn (unitInv k) (glInv g)
  left_inv := linFn_left k g
  right_inv := linFn_right k g

theorem linFn_zero (c : Fin 52) : linFn 0 0 c = c := by
  revert c; decide!

/-- `linSym 0 0` is the identity relabelling. -/
theorem linSym_zero_zero : linSym 0 0 = 1 :=
  Equiv.ext fun c => linFn_zero c

/-- (PROVED) The linear part multiplies the rank index `c % 13` (A = 0) by `k + 1`. -/
theorem linFn_rank : ∀ (k : Fin 12) (g : Fin 6) (c : Fin 52),
    (linFn k g c).val % 13 = ((k.val + 1) * (c.val % 13)) % 13 := by decide!

/-- (PROVED) The linear part acts on suit labels by `glApp g`. -/
theorem linFn_label : ∀ (k : Fin 12) (g : Fin 6) (c : Fin 52),
    suitLabel (linFn k g c).val = glApp g (suitLabel c.val) := by decide!

/-! ## The finite checks -/

/-- Finite check A: each used position swap keeps stem cell 0 of the identity deck. -/
def affPairsCheck : Bool :=
  affPairs.all fun p => g0 (posSwapDeck p.1 p.2) == g0 idDeck

/-- Finite check B for `(k, g)`: the witness pair is one of `affPairs`, and the
    `linSym k g`-images of the two decks have different stem cell 0. -/
def linCheck (k : Fin 12) (g : Fin 6) : Bool :=
  let p := affW.getD (6 * k.val + g.val) (0, 0)
  affPairs.contains p &&
    !(g0 (rel (linSym k g) idDeck) == g0 (rel (linSym k g) (posSwapDeck p.1 p.2)))

/-- Both finite checks (discharged by kernel `decide!` in the heavy library). -/
def AffChecks : Prop :=
  affPairsCheck = true ∧ ∀ (k : Fin 12) (g : Fin 6), (k, g) ≠ (0, 0) → linCheck k g = true

/-- (PROVED, given the finite checks `AffChecks`) A nontrivial linear part fails the
    seat-26 condition for every τ. -/
theorem not_cell0Cov_lin_of_check (hchk : AffChecks) (k : Fin 12) (g : Fin 6)
    (hkg : (k, g) ≠ (0, 0)) (τ : Relabel) : ¬ Cell0Cov (linSym k g) τ := by
  have hB := hchk.2 k g hkg
  unfold linCheck at hB
  set p := affW.getD (6 * k.val + g.val) (0, 0)
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne] at hB
  obtain ⟨hmem, hne⟩ := hB
  have hA := hchk.1
  unfold affPairsCheck at hA
  rw [List.all_eq_true] at hA
  have hsame := hA p (List.elem_iff.1 hmem)
  rw [beq_iff_eq, g0_eq, g0_eq] at hsame
  rw [g0_eq, g0_eq] at hne
  exact not_cell0Cov_of_witness isDeck_idDeck (isDeck_permDeck _) hsame.symm hne τ

/-! ## Affine relabellings -/

/-- (PROVED, given `AffChecks`) No affine relabelling `v10Sym a x * linSym k g` with
    a nontrivial linear part is covariant for the unkeyed round body, for ANY output
    relabelling τ. (Unconditional form: heavy library,
    `roundBody_not_covariant_affine`.) -/
theorem not_covariant_affine_of_check (hchk : AffChecks) (a : Fin 13) (x : Fin 4)
    (k : Fin 12) (g : Fin 6) (hkg : (k, g) ≠ (0, 0)) :
    ¬ Covariant (v10Sym a x * linSym k g) unkeyedWithMix := by
  rintro ⟨τ, hτ⟩
  have h := cell0Cov_mul (cell0Cov_inv (cell0Cov_v10Sym a x)) (cell0Cov_of_covPair hτ)
  rw [← mul_assoc, inv_mul_cancel, one_mul] at h
  exact not_cell0Cov_lin_of_check hchk k g hkg _ h

/-- (PROVED, given `AffChecks`) The same with the translation on the other side. -/
theorem not_covariant_affine_right_of_check (hchk : AffChecks) (a : Fin 13) (x : Fin 4)
    (k : Fin 12) (g : Fin 6) (hkg : (k, g) ≠ (0, 0)) :
    ¬ Covariant (linSym k g * v10Sym a x) unkeyedWithMix := by
  rintro ⟨τ, hτ⟩
  have h := cell0Cov_mul (cell0Cov_of_covPair hτ) (cell0Cov_inv (cell0Cov_v10Sym a x))
  rw [mul_assoc, mul_inv_cancel, mul_one] at h
  exact not_cell0Cov_lin_of_check hchk k g hkg _ h

/-- (PROVED, given `AffChecks`) An affine relabelling is covariant for the unkeyed
    round body iff it is the identity: the statement of `roundBody_covariant_iff_id`
    restricted to the affine σ (the `(k, g) = (0, 0)` case is the existing
    `roundBody_not_covariant_of_stem` for `v10Sym`). -/
theorem covariant_affine_iff_of_check (hchk : AffChecks) (a : Fin 13) (x : Fin 4)
    (k : Fin 12) (g : Fin 6) :
    Covariant (v10Sym a x * linSym k g) unkeyedWithMix ↔ v10Sym a x * linSym k g = 1 := by
  constructor
  · intro hc
    by_cases hkg : (k, g) = (0, 0)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hkg
      rw [linSym_zero_zero, mul_one] at hc ⊢
      by_contra hne
      exact roundBody_not_covariant_of_stem _ hne (sumRanksV10_commutes_v10Sym a x) hc
    · exact absurd hc (not_covariant_affine_of_check hchk a x k g hkg)
  · intro h
    rw [h]
    exact ⟨1, fun m _ => by rw [rel_one, rel_one]⟩

end DoubleDeal.Security.CovariantAffine
