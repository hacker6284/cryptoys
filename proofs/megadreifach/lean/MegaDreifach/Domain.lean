/-
  M7 — HashDeckBody domain: reject non-permutations (`require_permutation`).
  Zero sorry. No native_decide.
-/
import MegaDreifach.Basic

namespace MegaDreifach

/-- A 52-card deal is a permutation of ids `0..51`. -/
def isPermutation52 (deal : List Nat) : Prop :=
  deal.length = 52 ∧ deal.Nodup ∧ ∀ x ∈ deal, x < 52

/-- Software `require_permutation`: `some deal` iff the deal is a 52-perm. -/
def requirePermutation (deal : List Nat) : Option (List Nat) :=
  if decide (deal.length = 52) && decide deal.Nodup && deal.all (· < 52) then
    some deal
  else
    none

theorem all_lt_52_iff (deal : List Nat) :
    (deal.all (· < 52) = true) ↔ ∀ x ∈ deal, x < 52 := by
  simp [List.all_eq_true]

theorem requirePermutation_eq (deal : List Nat) :
    requirePermutation deal =
      if deal.length = 52 ∧ deal.Nodup ∧ ∀ x ∈ deal, x < 52 then some deal else none := by
  simp [requirePermutation, all_lt_52_iff]
  by_cases hlen : deal.length = 52
  · by_cases hnodup : deal.Nodup
    · by_cases hbound : ∀ x ∈ deal, x < 52
      · simp [hlen, hnodup, hbound]
      · simp [hlen, hnodup, hbound]
    · simp [hlen, hnodup]
  · simp [hlen]

/-- M7: `requirePermutation` returns `some deal` exactly on 52-card permutations. -/
theorem requirePermutation_iff (deal : List Nat) :
    requirePermutation deal = some deal ↔ isPermutation52 deal := by
  rw [requirePermutation_eq]
  constructor
  · intro h
    split at h
    · next ht => exact ht
    · cases h
  · intro h
    split
    · rfl
    · next hf => exact (hf h).elim

/-- M7: non-permutations are rejected. -/
theorem requirePermutation_reject (deal : List Nat) (h : ¬ isPermutation52 deal) :
    requirePermutation deal = none := by
  rw [requirePermutation_eq]
  split
  · next ht => exact (h ht).elim
  · rfl

theorem requirePermutation_isSome_iff (deal : List Nat) :
    (requirePermutation deal).isSome ↔ isPermutation52 deal := by
  constructor
  · intro h
    cases hopt : requirePermutation deal with
    | none => simp [hopt] at h
    | some w =>
        rw [requirePermutation_eq] at hopt
        split at hopt
        · next ht =>
            exact ht
        · cases hopt
  · intro h
    have : requirePermutation deal = some deal := (requirePermutation_iff deal).mpr h
    simp [this]

end MegaDreifach
