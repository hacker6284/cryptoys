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
  the event through it gives a sub-event (the same upper bound applies). That step
  and the link to `encryptN` are proved in `FullCipher` (roadmap M7:
  `encryptN_eq_rounds`, `card_fullTrail_le`), not here. These are the proof's mix rounds,
  not SPEC's rounds; the mapping to SPEC's rounds is in the `FullCipher` header.

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
  independent, and nothing here applies to them (the real schedule, `RealSchedule`, M5,
  gets the bound of the proof's first mix round (key `K_0`) only).

  Proved:
  * `trail_card_le_of_round`: if one round's characteristic set has at most
    `52!/p` decks, then for EVERY deck `y`, `p^R · #{K | Trail σ R y K} ≤ (52!)^R`.
  * `round_le_of_v10Sym`: the one-round `σ ≠ 1` case split, for any `p ≤ 64`
    (SumRanks outside `v10Sym`, a supplied bound on the nontrivial `v10Sym`).
  * `round_le_26`: one round, every `σ ≠ 1` (unconditional), `26 · roundCharCount σ ≤ 52!`.
  * `round_le_64_of_check`: one round, every `σ ≠ 1`, `64 · roundCharCount σ ≤ 52!`, GIVEN
    the two finite GridCycle checks as hypotheses.
  * `trail_card_le_26`: for every `σ ≠ 1` (unconditional), `26^R · # ≤ (52!)^R`.
  * `trail_card_le_64_of_not_v10Sym`: `σ ∉ v10Sym`, `64^R · # ≤ (52!)^R`.
  * `trail_card_le_64_of_check`: every `σ ≠ 1`, `64^R · # ≤ (52!)^R`, GIVEN the two
    finite GridCycle checks as hypotheses (discharged in the heavy library:
    `DoubleDealSecurityHeavy/TrailBound.lean`, `trail_card_le_64`).
  * `trail_card_le_4420_v10Sym_of_check`: nontrivial `v10Sym`, `4420^R · # ≤ (52!)^R`.
  * Shared with `FullCipher`: `SumRanksChar σ x` (SumRanks commutes with `σ` at the deck
    `x`; `RoundChar` is `SumRanksChar` plus the GridCycle condition, and
    `survives_iff_sumRanksChar` bridges to `SumRanksDP.Survives`), `unkeyedNoMix_rel_iff`
    (`SumRanksChar σ x` iff the no-mix round maps `(x, σ·x)` to `(z, σ·z)`), and
    `card_filter_snoc` (splitting a count over `Fin (n+1)` tuples by the last entry,
    next to `card_filter_succ`, which splits by the first).

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

/-- SumRanks commutes with `σ` at the state `x` (laid column-major). This is the SumRanks
    half of `RoundChar`, and the whole characteristic of the final no-mix round
    (`FullCipher`); on decks it is `SumRanksDP.Survives` (`survives_iff_sumRanksChar`). -/
def SumRanksChar (σ : Relabel) (x : Fin 52 → Nat) : Prop :=
  sumRanksV10 (relG σ (layColumnMajor x)) = relG σ (sumRanksV10 (layColumnMajor x))

instance (σ : Relabel) : DecidablePred (SumRanksChar σ) :=
  fun _ => inferInstanceAs (Decidable (_ = _))

/-- (PROVED) `SumRanksDP.Survives` is `SumRanksChar` on the deck of a permutation. -/
theorem survives_iff_sumRanksChar (σ : Relabel) (π : Equiv.Perm (Fin 52)) :
    SumRanksDP.Survives σ π ↔ SumRanksChar σ (permDeck π) := Iff.rfl

/-- (PROVED) The stem without GridCycle maps `(x, σ·x)` to a pair with difference `σ`
    exactly when SumRanks commutes with `σ` at `x`. -/
theorem unkeyedNoMix_rel_iff (σ : Relabel) (x : Fin 52 → Nat) :
    unkeyedNoMix (rel σ x) = rel σ (unkeyedNoMix x) ↔ SumRanksChar σ x := by
  constructor
  · intro h
    have h2 := congrArg (fun c => invShiftRows (layColumnMajor c)) h
    simp only [unkeyedNoMix] at h2
    rw [lay_scoop_columnMajor, invShiftRows_shiftRows, ← scoopColumnMajor_rel,
      lay_scoop_columnMajor, ← shiftRows_rel, invShiftRows_shiftRows] at h2
    exact h2
  · intro h
    simp only [unkeyedNoMix]
    rw [layColumnMajor_rel, h]
    rfl

/-- One round's characteristic at the post-Compose state `x`: SumRanks and
    GridCycle both commute with `σ` there. -/
def RoundChar (σ : Relabel) (x : Fin 52 → Nat) : Prop :=
  SumRanksChar σ x ∧ mixColumns (rel σ (unkeyedNoMix x)) = rel σ (mixColumns (unkeyedNoMix x))

instance (σ : Relabel) : DecidablePred (RoundChar σ) :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _))

/-- (PROVED) Under the one-round characteristic the unkeyed round maps the pair
    `(x, σ·x)` to a pair with the same difference. -/
theorem roundChar_unkeyedWithMix {σ : Relabel} {x : Fin 52 → Nat} (h : RoundChar σ x) :
    unkeyedWithMix (rel σ x) = rel σ (unkeyedWithMix x) := by
  simp only [unkeyedWithMix]
  rw [(unkeyedNoMix_rel_iff σ x).2 h.1, h.2]

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

/-- (PROVED) `rounds` maps decks to decks. -/
theorem isDeck_rounds : ∀ (R : ℕ) (y : Fin 52 → Nat) (K : Fin R → Key), IsDeck y →
    IsDeck (rounds R y K)
  | 0, _, _, hy => hy
  | R + 1, _, K, hy =>
      isDeck_rounds R _ (Fin.tail K) (isDeck_unkeyedWithMix (isDeck_compose hy (K 0)))

/-! ## One round: counting over the key -/

/-- Decks (as permutations) on which one round's characteristic holds. -/
def roundCharCount (σ : Relabel) : ℕ :=
  (univ.filter fun π : Equiv.Perm (Fin 52) => RoundChar σ (permDeck π)).card

theorem compose_permDeck (ρ k : Equiv.Perm (Fin 52)) :
    composeVec 52 Nat (permDeck ρ) k = permDeck (ρ * k) := rfl

/-- Relabelling the deck of `π` by `α` is the deck of `α * π`. -/
theorem rel_permDeck (α π : Equiv.Perm (Fin 52)) : rel α (permDeck π) = permDeck (α * π) :=
  funext fun i => app_fin α (π i)

theorem permDeck_apply_eq (π : Equiv.Perm (Fin 52)) (s c : Fin 52) :
    permDeck π s = c.val ↔ π s = c := Fin.val_inj

theorem rel_permDeck_apply_eq (α π : Equiv.Perm (Fin 52)) (s c : Fin 52) :
    rel α (permDeck π) s = c.val ↔ α (π s) = c := by
  rw [rel_permDeck, permDeck_apply_eq, Equiv.Perm.mul_apply]

/-- (PROVED) Compose with a uniform key makes any fixed deck uniform: for a deck `z`, summing
    `F (z ∘ k)` over all keys `k` is summing `F` over all decks (as permutations). -/
theorem sum_keys_compose {M : Type} [AddCommMonoid M] (F : (Fin 52 → Nat) → M)
    {z : Fin 52 → Nat} (hz : IsDeck z) :
    ∑ k : Key, F (composeVec 52 Nat z k) = ∑ π : Equiv.Perm (Fin 52), F (permDeck π) := by
  set ρ := deckPerm z hz
  have hzρ : z = permDeck ρ := funext fun i => (deckPerm_val z hz i).symm
  rw [hzρ]
  exact Fintype.sum_equiv (Equiv.mulLeft ρ) _ _ fun _ => rfl

/-- (PROVED) The counting form of `sum_keys_compose`: for a deck `y`, the keys `k` with
    `P (y ∘ k)` number exactly the decks (as permutations) with `P`. -/
theorem card_keys_compose (P : (Fin 52 → Nat) → Prop) [DecidablePred P]
    {y : Fin 52 → Nat} (hy : IsDeck y) :
    (univ.filter fun k : Key => P (composeVec 52 Nat y k)).card =
      (univ.filter fun π : Equiv.Perm (Fin 52) => P (permDeck π)).card := by
  rw [card_filter, card_filter]
  exact sum_keys_compose (fun w => if P w then 1 else 0) hy

/-- (PROVED) For a fixed deck `y`, the round keys that make the characteristic hold
    number exactly `roundCharCount σ` (Compose with a uniform key is a uniform deck). -/
theorem card_keys_roundChar (σ : Relabel) {y : Fin 52 → Nat} (hy : IsDeck y) :
    (univ.filter fun k : Key => RoundChar σ (composeVec 52 Nat y k)).card = roundCharCount σ :=
  card_keys_compose (RoundChar σ) hy

/-! ## R rounds -/

theorem card_trail_zero (σ : Relabel) (y : Fin 52 → Nat) :
    (univ.filter fun K : Fin 0 → Key => Trail σ 0 y K).card = 1 := by
  have : (univ.filter fun K : Fin 0 → Key => Trail σ 0 y K) = univ :=
    filter_true_of_mem (fun _ _ => trivial)
  rw [this, card_univ, Fintype.card_unique]

/-- (PROVED) Counting `R + 1` key tuples by their first key:
    `#{K | P K} = ∑ k, #{K' | P (Fin.cons k K')}`. -/
theorem card_filter_succ {R : ℕ} (P : (Fin (R + 1) → Key) → Prop) [DecidablePred P] :
    (univ.filter P).card =
      ∑ k : Key, (univ.filter fun K : Fin R → Key => P (Fin.cons k K)).card := by
  rw [card_eq_sum_card_fiberwise (f := fun K : Fin (R + 1) → Key => K 0) (t := univ)
    (fun _ _ => mem_univ _)]
  refine sum_congr rfl fun k _ => ?_
  apply card_nbij' (fun K => Fin.tail K) (fun K => Fin.cons k K)
  · intro K hK
    simp only [coe_filter, Set.mem_setOf_eq, mem_filter, mem_univ, true_and] at hK ⊢
    obtain ⟨h1, h0⟩ := hK
    rw [← h0, Fin.cons_self_tail]
    exact h1
  · intro K hK
    simp only [coe_filter, Set.mem_setOf_eq, mem_filter, mem_univ, true_and] at hK ⊢
    exact ⟨hK, Fin.cons_zero _ _⟩
  · intro K hK
    simp only [coe_filter, Set.mem_setOf_eq, mem_filter, mem_univ, true_and] at hK
    rw [← hK.2]
    exact Fin.cons_self_tail K
  · intro K _; exact Fin.tail_cons _ _

/-- (PROVED) Counting `R + 1` key tuples by their LAST key:
    `#{K | P K} = ∑ k, #{K' | P (Fin.snoc K' k)}`. -/
theorem card_filter_snoc {R : ℕ} (P : (Fin (R + 1) → Key) → Prop) [DecidablePred P] :
    (univ.filter P).card =
      ∑ k : Key, (univ.filter fun K : Fin R → Key => P (Fin.snoc K k)).card := by
  rw [card_eq_sum_card_fiberwise (f := fun K : Fin (R + 1) → Key => K (Fin.last R)) (t := univ)
    (fun _ _ => mem_univ _)]
  refine sum_congr rfl fun k _ => ?_
  apply card_nbij' (fun K => Fin.init K) (fun K => Fin.snoc K k)
  · intro K hK
    simp only [coe_filter, Set.mem_setOf_eq, mem_filter, mem_univ, true_and] at hK ⊢
    obtain ⟨h1, h0⟩ := hK
    rw [← h0, Fin.snoc_init_self]
    exact h1
  · intro K hK
    simp only [coe_filter, Set.mem_setOf_eq, mem_filter, mem_univ, true_and] at hK ⊢
    exact ⟨hK, Fin.snoc_last _ _⟩
  · intro K hK
    simp only [coe_filter, Set.mem_setOf_eq, mem_filter, mem_univ, true_and] at hK
    rw [← hK.2]
    exact Fin.snoc_init_self K
  · intro K _
    exact Fin.init_snoc _ _

/-- The `R + 1`-round count splits over the first key. -/
theorem card_trail_succ (σ : Relabel) (R : ℕ) (y : Fin 52 → Nat) :
    (univ.filter fun K : Fin (R + 1) → Key => Trail σ (R + 1) y K).card =
      ∑ k ∈ univ.filter (fun k : Key => RoundChar σ (composeVec 52 Nat y k)),
        (univ.filter fun K : Fin R → Key =>
          Trail σ R (unkeyedWithMix (composeVec 52 Nat y k)) K).card := by
  rw [card_filter_succ, sum_filter]
  refine sum_congr rfl fun k _ => ?_
  have e : ∀ K : Fin R → Key, Trail σ (R + 1) y (Fin.cons k K) ↔
      RoundChar σ (composeVec 52 Nat y k) ∧
        Trail σ R (unkeyedWithMix (composeVec 52 Nat y k)) K := fun K => by
    simp only [Trail, Fin.cons_zero, Fin.tail_cons]
  rw [filter_congr (fun K _ => e K)]
  split_ifs with hk
  · exact congrArg card (filter_congr fun K _ => and_iff_right hk)
  · rw [card_eq_zero, filter_eq_empty_iff]
    exact fun K _ h => hk h.1

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
  exact (survives_iff_sumRanksChar σ π).2 hπ.1

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
