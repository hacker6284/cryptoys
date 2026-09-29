/-
  Multi-round characteristic ("trail") bound for relabelling differences, under
  INDEPENDENT UNIFORM ROUND KEYS (roadmap milestone M2; `security/README.md`, "Roadmap").

  Model (read this before the theorems). A round with key `k : Key` sends a deck
  `y` to `unkeyedWithMix (compose y k)`: Compose with the key, then lay
  column-major, SumRanks, ShiftRows, scoop column-major, GridCycle. `rounds R y K`
  applies `R` such rounds with the key tuple `K : Fin R → Key`. Relative to
  `encryptN nMix m pos0 posMix posFinal`, `rounds R m K` with `K = (pos0, posMix 0,
  …, posMix (R-2))` is the first `R` mix rounds WITHOUT the trailing Compose of the
  last one, and WITHOUT the final no-mix round. The dropped Compose commutes
  with every relabelling. The final no-mix round contains SumRanks, so extending
  the event through it gives a sub-event (the same upper bound applies). Neither
  that step nor the link to `encryptN` is formalised here.

  Event. For a relabelling `σ`, the pair `(y, σ·y)` follows the constant-σ
  characteristic through `R` rounds (`Trail σ R y K`) when in EVERY round, at the
  state `x` after Compose, SumRanks commutes with `σ` at `x` and GridCycle commutes
  with `σ` at the stem output. It implies the output pair is `(z, σ·z)`
  (`trail_rounds_rel`). It is ONE characteristic: the differential probability
  `P[out difference = σ | in difference = σ]` also counts pairs whose difference
  changes in the middle and comes back, which this file does not bound, and
  nothing here bounds `σ → β` for `β ≠ σ`.

  Probability. The count is over ALL `(52!)^R` key tuples, i.e. independent
  uniform round keys (the Markov-cipher assumption, built into the counting).
  The real cipher derives its round keys by the PassKey chain; they are NOT
  independent, and nothing here applies to them.

  Proved:
  * `trail_card_le_of_round`: if one round's characteristic set has at most
    `52!/p` decks, then for EVERY deck `y`, `p^R · #{K | Trail σ R y K} ≤ (52!)^R`.
  * `round_le_of_v10Sym`: the one-round `σ ≠ 1` case split, for any `p ≤ 64`
    (SumRanks outside `v10Sym`, a supplied bound on the nontrivial `v10Sym`).
  * `trail_card_le_26`: for every `σ ≠ 1` (unconditional), `26^R · # ≤ (52!)^R`.
  * `trail_card_le_64_of_not_v10Sym`: `σ ∉ v10Sym`, `64^R · # ≤ (52!)^R`.
  * `trail_card_le_64_of_check`: every `σ ≠ 1`, `64^R · # ≤ (52!)^R`, GIVEN the two
    finite GridCycle checks as hypotheses (discharged in the heavy library:
    `DoubleDealSecurityHeavy/TrailBound.lean`, `trail_card_le_64`).
  * `trail_card_le_4420_v10Sym_of_check`: nontrivial `v10Sym`, `4420^R · # ≤ (52!)^R`.

  Not a bit-security claim; not a statement about the real key schedule.
-/
import DoubleDealSecurity.GridCycleSurvival
import DoubleDealSecurity.SumRanksDP.Main
import DoubleDealSecurity.PermKeys
import Mathlib

namespace DoubleDeal.Security.TrailBound

open DoubleDeal Relabel Finset
open DoubleDeal.Security (Key isDeck_compose isDeck_unkeyedWithMix isDeck_unkeyedNoMix)
open DoubleDeal.Security.GridCycleSurvival (GCSurvives gcSurvivors Check3 LKC LKS)

/-- One round's characteristic at the post-Compose state `x`: SumRanks and
    GridCycle both commute with `σ` there. -/
def RoundChar (σ : Relabel) (x : Fin 52 → Nat) : Prop :=
  sumRanksV10 (relG σ (layColumnMajor x)) = relG σ (sumRanksV10 (layColumnMajor x)) ∧
    mixColumns (rel σ (unkeyedNoMix x)) = rel σ (mixColumns (unkeyedNoMix x))

instance (σ : Relabel) : DecidablePred (RoundChar σ) :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _))

/-- (PROVED) Under the one-round characteristic the unkeyed round maps the pair
    `(x, σ·x)` to a pair with the same difference. -/
theorem roundChar_unkeyedWithMix {σ : Relabel} {x : Fin 52 → Nat} (h : RoundChar σ x) :
    unkeyedWithMix (rel σ x) = rel σ (unkeyedWithMix x) := by
  have e1 : unkeyedNoMix (rel σ x) = rel σ (unkeyedNoMix x) := by
    simp only [unkeyedNoMix]
    rw [layColumnMajor_rel, h.1]
    rfl
  simp only [unkeyedWithMix]
  rw [e1, h.2]

/-- `R` rounds with keys `K 0, …, K (R-1)` (Compose, then the unkeyed round). -/
def rounds : (R : ℕ) → (Fin 52 → Nat) → (Fin R → Key) → (Fin 52 → Nat)
  | 0, y, _ => y
  | R + 1, y, K => rounds R (unkeyedWithMix (composeVec 52 Nat y (K 0))) (Fin.tail K)

/-- The constant-`σ` characteristic through `R` rounds. -/
def Trail (σ : Relabel) : (R : ℕ) → (Fin 52 → Nat) → (Fin R → Key) → Prop
  | 0, _, _ => True
  | R + 1, y, K => RoundChar σ (composeVec 52 Nat y (K 0)) ∧
      Trail σ R (unkeyedWithMix (composeVec 52 Nat y (K 0))) (Fin.tail K)

instance decTrail (σ : Relabel) : (R : ℕ) → (y : Fin 52 → Nat) → (K : Fin R → Key) →
    Decidable (Trail σ R y K)
  | 0, _, _ => isTrue trivial
  | R + 1, _, _ =>
      @instDecidableAnd _ _ (inferInstanceAs (Decidable (RoundChar σ _))) (decTrail σ R _ _)

/-- (PROVED) Following the characteristic, the output pair has difference `σ`:
    `rounds R (σ·y) K = σ · rounds R y K`. -/
theorem trail_rounds_rel (σ : Relabel) :
    ∀ (R : ℕ) (y : Fin 52 → Nat) (K : Fin R → Key), Trail σ R y K →
      rounds R (rel σ y) K = rel σ (rounds R y K)
  | 0, _, _, _ => rfl
  | R + 1, y, K, h => by
      simp only [rounds]
      rw [compose_rel, roundChar_unkeyedWithMix h.1]
      exact trail_rounds_rel σ R _ _ h.2

/-! ## One round: counting over the key -/

/-- Decks (as permutations) on which one round's characteristic holds. -/
def roundCharCount (σ : Relabel) : ℕ :=
  (univ.filter fun π : Equiv.Perm (Fin 52) => RoundChar σ (permDeck π)).card

theorem compose_permDeck (ρ k : Equiv.Perm (Fin 52)) :
    composeVec 52 Nat (permDeck ρ) k = permDeck (ρ * k) := rfl

/-- (PROVED) For a fixed deck `y`, the round keys that make the characteristic hold
    number exactly `roundCharCount σ` (Compose with a uniform key is a uniform deck). -/
theorem card_keys_roundChar (σ : Relabel) {y : Fin 52 → Nat} (hy : IsDeck y) :
    (univ.filter fun k : Key => RoundChar σ (composeVec 52 Nat y k)).card = roundCharCount σ := by
  set ρ := deckPerm y hy
  have hyρ : y = permDeck ρ := funext fun i => (deckPerm_val y hy i).symm
  unfold roundCharCount
  rw [hyρ]
  apply card_nbij' (fun k => ρ * k) (fun π => ρ⁻¹ * π)
  · intro k hk
    simp only [coe_filter, Set.mem_setOf_eq, mem_filter, mem_univ, true_and] at hk ⊢
    rwa [compose_permDeck] at hk
  · intro π hπ
    simp only [coe_filter, Set.mem_setOf_eq, mem_filter, mem_univ, true_and] at hπ ⊢
    rwa [compose_permDeck, mul_inv_cancel_left]
  · intro k _; simp only [inv_mul_cancel_left]
  · intro π _; simp only [mul_inv_cancel_left]

/-! ## R rounds -/

theorem card_trail_zero (σ : Relabel) (y : Fin 52 → Nat) :
    (univ.filter fun K : Fin 0 → Key => Trail σ 0 y K).card = 1 := by
  have : (univ.filter fun K : Fin 0 → Key => Trail σ 0 y K) = univ :=
    filter_true_of_mem (fun _ _ => trivial)
  rw [this, card_univ, Fintype.card_unique]

/-- The `R + 1`-round count splits over the first key. -/
theorem card_trail_succ (σ : Relabel) (R : ℕ) (y : Fin 52 → Nat) :
    (univ.filter fun K : Fin (R + 1) → Key => Trail σ (R + 1) y K).card =
      ∑ k ∈ univ.filter (fun k : Key => RoundChar σ (composeVec 52 Nat y k)),
        (univ.filter fun K : Fin R → Key =>
          Trail σ R (unkeyedWithMix (composeVec 52 Nat y k)) K).card := by
  rw [card_eq_sum_card_fiberwise (f := fun K : Fin (R + 1) → Key => K 0)
    (t := univ.filter (fun k : Key => RoundChar σ (composeVec 52 Nat y k)))
    (fun K hK => by
      simp only [mem_filter, mem_univ, true_and] at hK ⊢
      exact hK.1)]
  apply sum_congr rfl
  intro k hk
  simp only [mem_filter, mem_univ, true_and] at hk
  apply card_nbij' (fun K => Fin.tail K) (fun K => Fin.cons k K)
  · intro K hK
    simp only [coe_filter, Set.mem_setOf_eq, mem_filter, mem_univ, true_and, Trail] at hK ⊢
    obtain ⟨⟨_, h2⟩, h0⟩ := hK
    rw [h0] at h2
    exact h2
  · intro K hK
    simp only [coe_filter, Set.mem_setOf_eq, mem_filter, mem_univ, true_and, Trail,
      Fin.cons_zero, Fin.tail_cons] at hK ⊢
    exact ⟨⟨hk, hK⟩, trivial⟩
  · intro K hK
    simp only [coe_filter, Set.mem_setOf_eq, mem_filter, mem_univ, true_and] at hK
    rw [← hK.2]
    exact Fin.cons_self_tail K
  · intro K _; exact Fin.tail_cons _ _

/-- (PROVED) The general induction: if one round's characteristic holds on at most
    `52!/p` decks, then from every starting deck `y` at most `(52!/p)^R` of the
    `(52!)^R` key tuples follow the characteristic for `R` rounds. -/
theorem trail_card_le_of_round (σ : Relabel) (p : ℕ)
    (hround : p * roundCharCount σ ≤ Nat.factorial 52) :
    ∀ (R : ℕ) (y : Fin 52 → Nat), IsDeck y →
      p ^ R * (univ.filter fun K : Fin R → Key => Trail σ R y K).card ≤
        Nat.factorial 52 ^ R
  | 0, y, _ => by rw [card_trail_zero, pow_zero, pow_zero]; exact Nat.le_refl 1
  | R + 1, y, hy => by
      rw [card_trail_succ, Finset.mul_sum]
      have hle : ∀ k ∈ univ.filter (fun k : Key => RoundChar σ (composeVec 52 Nat y k)),
          p ^ (R + 1) * (univ.filter fun K : Fin R → Key =>
            Trail σ R (unkeyedWithMix (composeVec 52 Nat y k)) K).card ≤
            p * Nat.factorial 52 ^ R := by
        intro k _
        rw [pow_succ, Nat.mul_comm (p ^ R) p, Nat.mul_assoc]
        exact Nat.mul_le_mul_left p (trail_card_le_of_round σ p hround R _
          (isDeck_unkeyedWithMix (isDeck_compose hy k)))
      calc _ ≤ ∑ _k ∈ univ.filter (fun k : Key => RoundChar σ (composeVec 52 Nat y k)),
              p * Nat.factorial 52 ^ R := sum_le_sum hle
        _ = roundCharCount σ * (p * Nat.factorial 52 ^ R) := by
              rw [sum_const_nat (fun _ _ => rfl), card_keys_roundChar σ hy]
        _ = (p * roundCharCount σ) * Nat.factorial 52 ^ R := by
              rw [← Nat.mul_assoc, Nat.mul_comm (roundCharCount σ) p]
        _ ≤ Nat.factorial 52 * Nat.factorial 52 ^ R := Nat.mul_le_mul_right _ hround
        _ = Nat.factorial 52 ^ (R + 1) := by rw [pow_succ, Nat.mul_comm]

/-! ## One-round bounds from the layer theorems -/

/-- (PROVED) The round characteristic needs SumRanks to commute at the deck. -/
theorem roundCharCount_le_sumRanks (σ : Relabel) :
    roundCharCount σ ≤ (SumRanksDP.survivors σ).card := by
  apply card_le_card
  intro π hπ
  simp only [SumRanksDP.survivors, mem_filter, mem_univ, true_and] at hπ ⊢
  exact hπ.1

/-- (PROVED) The round characteristic needs GridCycle to commute at the stem
    output; the stem is injective on decks, so this is at most the GridCycle
    survivor count. -/
theorem roundCharCount_le_gridCycle (σ : Relabel) :
    roundCharCount σ ≤ (gcSurvivors σ).card := by
  let f : Equiv.Perm (Fin 52) → Equiv.Perm (Fin 52) := fun π =>
    deckPerm (unkeyedNoMix (permDeck π)) (isDeck_unkeyedNoMix (isDeck_permDeck π))
  have hf : ∀ π, permDeck (f π) = unkeyedNoMix (permDeck π) :=
    fun π => funext fun i => deckPerm_val _ _ i
  apply card_le_card_of_injOn f
  · intro π hπ
    simp only [coe_filter, Set.mem_setOf_eq, mem_filter, mem_univ, true_and, gcSurvivors,
      mem_coe] at hπ ⊢
    show mixColumns (rel σ (permDeck (f π))) = rel σ (mixColumns (permDeck (f π)))
    rw [hf]
    exact hπ.2
  · intro π₁ _ π₂ _ h
    have h' : unkeyedNoMix (permDeck π₁) = unkeyedNoMix (permDeck π₂) := by
      rw [← hf, ← hf, h]
    have h'' : permDeck π₁ = permDeck π₂ := by
      rw [← invUnkeyedNoMix_unkeyedNoMix (permDeck π₁), h', invUnkeyedNoMix_unkeyedNoMix]
    exact Equiv.ext fun i => Fin.ext (congrFun h'' i)

/-- (PROVED) `σ ∉ v10Sym`: one round's characteristic on at most `52!/64` decks. -/
theorem round_le_64_of_not_v10Sym (σ : Relabel) (h : ¬ ∃ a x, σ = v10Sym a x) :
    64 * roundCharCount σ ≤ Nat.factorial 52 := by
  have hs := SumRanksDP.sumRanksV10_survival_le σ h
  rw [Fintype.card_perm, Fintype.card_fin] at hs
  exact (Nat.mul_le_mul_left 64 (roundCharCount_le_sumRanks σ)).trans hs

/-- (PROVED) Nontrivial `v10Sym`: one round's characteristic on at most `52!/26` decks
    (from GridCycle; unconditional). -/
theorem round_le_26_v10Sym (a : Fin 13) (x : Fin 4) (hne : ¬ (a = 0 ∧ x = 0)) :
    26 * roundCharCount (v10Sym a x) ≤ Nat.factorial 52 := by
  refine (Nat.mul_le_mul_left 26 (roundCharCount_le_gridCycle _)).trans ?_
  by_cases h03 : a = 0 ∧ x = 3
  · obtain ⟨rfl, rfl⟩ := h03
    exact GridCycleSurvival.gc_survival_v10Sym03
  · rw [GridCycleSurvival.gcSurvivors_v10Sym_eq_empty a x hne h03, card_empty, Nat.mul_zero]
    exact Nat.zero_le _

/-- (PROVED, given the two finite GridCycle checks) Nontrivial `v10Sym`: one round's
    characteristic on at most `52!/4420` decks. -/
theorem round_le_4420_v10Sym_of_check (hKC : Check3 KC LKC) (hKS : Check3 KS LKS)
    (a : Fin 13) (x : Fin 4) (hne : ¬ (a = 0 ∧ x = 0)) :
    4420 * roundCharCount (v10Sym a x) ≤ Nat.factorial 52 :=
  (Nat.mul_le_mul_left 4420 (roundCharCount_le_gridCycle _)).trans
    (GridCycleSurvival.gc_survival_v10Sym_le_of_check hKC hKS a x hne)

/-- `σ ≠ 1` and `σ = v10Sym a x` force `(a, x) ≠ (0, 0)`. -/
theorem ne_zero_of_ne_one {σ : Relabel} (h1 : σ ≠ 1) {a : Fin 13} {x : Fin 4}
    (h : σ = v10Sym a x) : ¬ (a = 0 ∧ x = 0) := by
  rintro ⟨rfl, rfl⟩
  exact h1 (h.trans v10Sym_zero_zero)

/-- (PROVED) The one-round case split shared by the `σ ≠ 1` statements: for any
    `p ≤ 64`, if every nontrivial `v10Sym a x` has one-round characteristic count
    at most `52!/p`, then so does every `σ ≠ 1` (outside `v10Sym` the SumRanks
    bound `52!/64` applies). -/
theorem round_le_of_v10Sym (p : ℕ) (hp : p ≤ 64)
    (hsym : ∀ (a : Fin 13) (x : Fin 4), ¬ (a = 0 ∧ x = 0) →
      p * roundCharCount (v10Sym a x) ≤ Nat.factorial 52)
    (σ : Relabel) (h1 : σ ≠ 1) :
    p * roundCharCount σ ≤ Nat.factorial 52 := by
  by_cases hs : ∃ a x, σ = v10Sym a x
  · obtain ⟨a, x, rfl⟩ := hs
    exact hsym a x (ne_zero_of_ne_one h1 rfl)
  · exact (Nat.mul_le_mul_right _ hp).trans (round_le_64_of_not_v10Sym σ hs)

/-- (PROVED, unconditional) One round, every `σ ≠ 1`: the characteristic count is at
    most `52!/26`. -/
theorem round_le_26 (σ : Relabel) (h1 : σ ≠ 1) :
    26 * roundCharCount σ ≤ Nat.factorial 52 :=
  round_le_of_v10Sym 26 (by norm_num) round_le_26_v10Sym σ h1

/-- (PROVED, given the two finite GridCycle checks as hypotheses) One round, every
    `σ ≠ 1`: the characteristic count is at most `52!/64`. -/
theorem round_le_64_of_check (hKC : Check3 KC LKC) (hKS : Check3 KS LKS)
    (σ : Relabel) (h1 : σ ≠ 1) :
    64 * roundCharCount σ ≤ Nat.factorial 52 :=
  round_le_of_v10Sym 64 le_rfl (fun a x hne =>
    (Nat.mul_le_mul_right _ (by norm_num : (64 : ℕ) ≤ 4420)).trans
      (round_le_4420_v10Sym_of_check hKC hKS a x hne)) σ h1

/-! ## R-round statements -/

/-- (PROVED, unconditional) Every `σ ≠ 1`, independent uniform round keys: from every
    deck `y`, `26^R · #{K | Trail σ R y K} ≤ (52!)^R`, i.e. the constant-`σ`
    characteristic over `R` rounds has probability at most `(1/26)^R`. -/
theorem trail_card_le_26 (σ : Relabel) (h1 : σ ≠ 1) (R : ℕ) (y : Fin 52 → Nat)
    (hy : IsDeck y) :
    26 ^ R * (univ.filter fun K : Fin R → Key => Trail σ R y K).card ≤
      Nat.factorial 52 ^ R :=
  trail_card_le_of_round σ 26 (round_le_26 σ h1) R y hy

/-- (PROVED, unconditional) `σ ∉ v10Sym`: probability at most `(1/64)^R`. -/
theorem trail_card_le_64_of_not_v10Sym (σ : Relabel) (h : ¬ ∃ a x, σ = v10Sym a x)
    (R : ℕ) (y : Fin 52 → Nat) (hy : IsDeck y) :
    64 ^ R * (univ.filter fun K : Fin R → Key => Trail σ R y K).card ≤
      Nat.factorial 52 ^ R :=
  trail_card_le_of_round σ 64 (round_le_64_of_not_v10Sym σ h) R y hy

/-- (PROVED, given the two finite GridCycle checks as hypotheses) Nontrivial
    `v10Sym`: probability at most `(1/4420)^R`. -/
theorem trail_card_le_4420_v10Sym_of_check (hKC : Check3 KC LKC) (hKS : Check3 KS LKS)
    (a : Fin 13) (x : Fin 4) (hne : ¬ (a = 0 ∧ x = 0))
    (R : ℕ) (y : Fin 52 → Nat) (hy : IsDeck y) :
    4420 ^ R * (univ.filter fun K : Fin R → Key => Trail (v10Sym a x) R y K).card ≤
      Nat.factorial 52 ^ R :=
  trail_card_le_of_round _ 4420 (round_le_4420_v10Sym_of_check hKC hKS a x hne) R y hy

/-- (PROVED, given the two finite GridCycle checks as hypotheses) Every `σ ≠ 1`:
    probability at most `(1/64)^R`. -/
theorem trail_card_le_64_of_check (hKC : Check3 KC LKC) (hKS : Check3 KS LKS)
    (σ : Relabel) (h1 : σ ≠ 1) (R : ℕ) (y : Fin 52 → Nat) (hy : IsDeck y) :
    64 ^ R * (univ.filter fun K : Fin R → Key => Trail σ R y K).card ≤
      Nat.factorial 52 ^ R :=
  trail_card_le_of_round σ 64 (round_le_64_of_check hKC hKS σ h1) R y hy

end DoubleDeal.Security.TrailBound
