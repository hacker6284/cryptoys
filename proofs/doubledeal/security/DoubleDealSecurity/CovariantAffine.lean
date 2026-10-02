/-
  The covariant round statement `roundBody_covariant_iff_id` (proved in the heavy library,
  `DoubleDealSecurityHeavy/V10Sym.lean`) for the AFFINE relabellings: a finite, structured
  family. The general statement and `CovariantNarrow.PrimeNonSwapCase` are not proved here
  (both are proved in the heavy library: `roundBody_covariant_iff_id`,
  `CovariantNarrow.primeNonSwapCase`).

  Affine relabellings. A card is (rank index r = c % 13 ∈ Z13 (A = 0), GF(4) suit
  label l = `suitLabel c`). For `k : Fin 12` (unit `u = k + 1` of Z13) and `g : Fin 6`
  (an element of GL(2,2) acting on the two label bits, generated table `glTab`, `g = 0`
  the identity), `linSym k g` is `(r, l) ↦ (u r, A_g l)`. The affine relabellings are
  `v10Sym a x * linSym k g`: `(r, l) ↦ (u r + a, A_g l ⊕ x)`. The 3744 parameter
  tuples give pairwise distinct relabellings (`affine_params_inj`); the 3692 with
  `(k, g) ≠ (0, 0)` are the ones outside `v10Sym`. The affine relabellings are the
  normalizer of `v10Sym` in the 52! relabellings (true by the holomorph count, not a
  Lean theorem).

  Proved here (the `Cell0Cov` group lemmas and the generic witness check
  `not_cell0Cov_of_checks` are in `CovariantNarrow.lean`):
  * `linFn_left`, `linFn_right` (so `linSym k g` is a relabelling), `glApp_gfAdd`
    (each `glTab` row is GF(2)-linear), `linFn_rank`, `linFn_label`,
    `affine_params_inj`.
  * `not_cell0Cov_lin_of_check` (given the finite checks `AffChecks`): for every
    nontrivial linear part `(k, g)`, `linSym k g` fails the seat-26 condition for
    every τ (two decks witness it; `affW`).
  * `not_covariant_affine_of_check`, `not_covariant_affine_right_of_check` (given
    `AffChecks`): `v10Sym a x * linSym k g` and `linSym k g * v10Sym a x` are not
    covariant for ANY τ when `(k, g) ≠ (0, 0)`. Unconditional forms in the heavy
    library (`DoubleDealSecurityHeavy/CovariantAffine.lean`).
  * `covariant_affine_iff_of_check`: given `AffChecks`, an affine relabelling is
    covariant iff it is the identity.

  This covers all 3692 affine relabellings outside `v10Sym`, of any order; the ones of prime
  order are the part that lies inside `PrimeNonSwapCase`. It is NOT
  `PrimeNonSwapCase`: almost all prime-order relabellings are not affine.
  Write-up: `../analysis/v12-primenonswap/NOTES.md`.
-/
import DoubleDealSecurity.CovariantNarrow
import DoubleDealSecurity.CovariantAffineLists

namespace DoubleDeal.Security.CovariantAffine

open DoubleDeal Relabel
open DoubleDeal.Security.CovariantNarrow (Cell0Cov cell0Pairs pairsCheck witnessCheck
  not_cell0Cov_of_checks cell0Cov_of_covPair cell0Cov_mul cell0Cov_inv cell0Cov_v10Sym)

/-! ## The linear parts (tables generated in `CovariantAffineLists.lean`) -/

def glApp (g : Fin 6) (l : Nat) : Nat := (glTab.getD g.val []).getD l 0

theorem glApp_lt : ∀ (g : Fin 6) (l : Fin 4), glApp g l.val < 4 := by decide

/-- The inverse matrix (table `glInvTab`). -/
def glInv (g : Fin 6) : Fin 6 := glInvTab.getD g.val 0

/-- `k ↦ k'` with `(k + 1)(k' + 1) ≡ 1 (mod 13)` (table `unitInvTab`). -/
def unitInv (k : Fin 12) : Fin 12 := unitInvTab.getD k.val 0

/-- (PROVED) Each `glTab` row is linear over GF(2) on the labels (`gfAdd` is XOR). -/
theorem glApp_gfAdd : ∀ (g : Fin 6) (l l' : Fin 4),
    glApp g (gfAdd l.val l'.val) = gfAdd (glApp g l.val) (glApp g l'.val) := by decide

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

/-! ## The affine maps are pairwise distinct -/

theorem linFn_card0 : ∀ (k : Fin 12) (g : Fin 6), linFn k g 0 = 0 := by decide

theorem v10SymFn_card0_inj : ∀ (a a' : Fin 13) (x x' : Fin 4),
    v10SymFn a x 0 = v10SymFn a' x' 0 → a = a' ∧ x = x' := by decide!

/-- The images of A♣ (1), A♥ (13, label 2) and A♦ (39, label 1) determine `(k, g)`. -/
theorem linFn_params_inj : ∀ (k k' : Fin 12) (g g' : Fin 6),
    linFn k g 1 = linFn k' g' 1 → linFn k g 13 = linFn k' g' 13 →
    linFn k g 39 = linFn k' g' 39 → k = k' ∧ g = g' := by decide!

/-- (PROVED) Distinct parameter tuples give distinct affine relabellings. -/
theorem affine_params_inj {a a' : Fin 13} {x x' : Fin 4} {k k' : Fin 12} {g g' : Fin 6}
    (h : v10Sym a x * linSym k g = v10Sym a' x' * linSym k' g') :
    a = a' ∧ x = x' ∧ k = k' ∧ g = g' := by
  have h0 := congrArg (fun σ : Relabel => σ 0) h
  simp only [Equiv.Perm.mul_apply] at h0
  change v10SymFn a x (linFn k g 0) = v10SymFn a' x' (linFn k' g' 0) at h0
  rw [linFn_card0, linFn_card0] at h0
  obtain ⟨rfl, rfl⟩ := v10SymFn_card0_inj a a' x x' h0
  have hl := mul_left_cancel h
  have e : ∀ c, linFn k g c = linFn k' g' c := fun c => congrArg (fun σ : Relabel => σ c) hl
  obtain ⟨rfl, rfl⟩ := linFn_params_inj k k' g g' (e 1) (e 13) (e 39)
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## The finite checks -/

/-- Finite check B for `(k, g)`: the generic witness check for `linSym k g` with the
    witness pair `affW[6 k + g]`. -/
def linCheck (k : Fin 12) (g : Fin 6) : Bool :=
  witnessCheck cell0Pairs (linSym k g) (affW.getD (6 * k.val + g.val) (0, 0))

/-- Both finite checks (discharged by kernel `decide!` in the heavy library; check A
    is the one shared with `CovariantNarrow.Cov0Checks`). -/
def AffChecks : Prop :=
  pairsCheck cell0Pairs = true ∧ ∀ (k : Fin 12) (g : Fin 6), (k, g) ≠ (0, 0) → linCheck k g = true

/-- (PROVED, given the finite checks `AffChecks`) A nontrivial linear part fails the
    seat-26 condition for every τ. -/
theorem not_cell0Cov_lin_of_check (hchk : AffChecks) (k : Fin 12) (g : Fin 6)
    (hkg : (k, g) ≠ (0, 0)) (τ : Relabel) : ¬ Cell0Cov (linSym k g) τ :=
  not_cell0Cov_of_checks hchk.1 (hchk.2 k g hkg) τ

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

/-- (PROVED, given `AffChecks`) The same with the translation on the other side.
    These are the same relabellings as in `not_covariant_affine_of_check`
    (`linSym k g * v10Sym a x = v10Sym ((k+1)·a) (A_g x) * linSym k g`; that identity
    is not a Lean theorem, so both forms are stated). -/
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
