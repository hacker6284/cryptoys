/-
  Structure of the full relabelling DIFFERENTIAL (roadmap milestone M6; security README,
  "Roadmap"). Measurement notes: `../analysis/v12-differential/NOTES.md`.

  NO NUMERIC BOUND ON THE FULL DIFFERENTIAL IS PROVED HERE. Read this before citing
  anything below.

  Model. Same rounds as `TrailBound`: a round with key `k` sends a deck `y` to
  `unkeyedWithMix (compose y k)`, and `rounds R y K` applies `R` of them. The pair
  `(y, α·y)` has input difference `α` (a relabelling). `Diff α β R y K` is the event that
  the output pair after `R` rounds has difference `β`: `rounds R (α·y) K = β · rounds R y K`.
  Unlike `Trail`, the difference may change in between rounds. `diffCount α β R y` counts
  the key tuples `K : Fin R → Key` (all `(52!)^R` of them, i.e. INDEPENDENT UNIFORM round
  keys) with `Diff α β R y K`; `dp1Count α β` is the one-round count over decks. The
  differential probability is `diffCount / (52!)^R`.

  NOT covered here: the final no-mix round, and any link from `rounds` to `encryptN` (as in
  `TrailBound`); both are in `FullCipher` (roadmap M7), which adds one exact Markov step
  for the final round and still no numeric bound. The real PassKey schedule gets only the
  `R = 1` identity (`realDiffCount_one`) and the bound of the proof's first mix round (key
  `K_0`) on paths inside the `v10Sym` cluster (`realStaysInV10_card_le_26`, for
  `(a, x) ≠ (0, 0)` only); nothing for the real schedule at `R ≥ 2` beyond that.

  Proved:
  * D0 `card_trail_le_diffCount` (from `trail_rounds_rel`): the characteristic is one path
    of the differential, so `Trail` counts are LOWER bounds for `diffCount σ σ`, not upper
    bounds.
  * D1 `diffCount_eq_of_isDeck`: `diffCount α β R y` does not depend on the deck `y`.
  * D2 `diffCount_succ`: the Markov recursion
    `diffCount α β (R+1) y = ∑ γ, dp1Count α γ * diffCount γ β R z` (any decks `y`, `z`).
  * D3 `sum_dp1Count`, `sum_diffCount` (rows sum to `52!`, `(52!)^R`), `dp1Count_one_left`,
    `diffCount_one_left` (difference `1` stays `1`), `dp1Count_to_one`,
    `diffCount_to_one` (a difference `α ≠ 1` never becomes `1`), `diffCount_zero`,
    `diffCount_one`.
  * D4 `dp1Count_v10Sym_le_agree`: for input `v10Sym a x`, the one-round count to `β` is at
    most `52!/52` times the number of cards on which `v10Sym a x` and `β` agree (the first
    card placed by GridCycle is not moved). Corollaries `dp1Count_v10Sym_eq_zero`,
    `dp1Count_v10Sym_v10Sym_eq_zero`: `v10Sym a x → v10Sym a' x'` with
    `(a', x') ≠ (a, x)` has one-round count `0`.
  * D5 `staysInV10_iff_trail`: a path whose difference stays a `v10Sym a' x'` after every
    round (`StaysInV10`) is exactly the constant characteristic. Hence, for
    `(a, x) ≠ (0, 0)` only: `staysInV10_card_le_26` (`26^R · # ≤ (52!)^R`, no further
    hypothesis), `staysInV10_card_le_4420_of_check` (given the two finite GridCycle
    checks; without them in the heavy library, `staysInV10_card_le_4420`), and for the real
    schedule the bounds of the proof's first mix round (key `K_0`) alone:
    `realStaysInV10_card_le_26`, `realStaysInV10_card_le_4420_of_check` (heavy:
    `realStaysInV10_card_le_4420`).
    (For `(a, x) = (0, 0)`, `v10Sym 0 0 = 1` and these bounds are false.)
    These cover ONLY paths that stay inside `v10Sym`; a path that leaves `v10Sym` and
    comes back is not bounded.
  * D6 `realDiffCount_one`: under the real schedule, one round is the same count as with
    an independent key. Nothing for `R ≥ 2`.
  * Generic one-step counts: `dpCount U α β` (decks `x` with `U (α·x) = β · U x`, for any
    round map `U`; `dp1Count` is `dpCount unkeyedWithMix`, and `FullCipher.dpFCount` is
    `dpCount unkeyedNoMix`), with `sum_dpCount` (rows sum to `52!` when `U` maps decks to
    decks) and `sum_dpCount_left` (columns sum to `52!` when `U` has a two-sided inverse
    `V` and both map decks to decks), `dpCount_one_left` (`1` goes only to `1` when `U` maps
    decks to decks) and `dpCount_to_one` (nothing else reaches `1` when `U` is injective;
    the hypothesis is needed). `dp1Count_one_left`, `dp1Count_to_one` and
    `FullCipher.dpFCount_one_left`, `FullCipher.dpFCount_to_one` are these at DoubleDeal's
    layers.
    `relDiff_eq_iff`: for decks `x`, `x'`, `relDiff x x' = γ ↔ rel γ x = x'`.

  The measured one- and two-round values in the notes are EMPIRICAL (sampled), not
  proved, and no theorem uses them. Not a bit-security claim.
-/
import DoubleDealSecurity.TrailBound
import DoubleDealSecurity.RealSchedule

namespace DoubleDeal.Security.Differential

open DoubleDeal Relabel Finset
open DoubleDeal.Security (Key isDeck_compose isDeck_rel isDeck_unkeyedWithMix
  isDeck_unkeyedNoMix cardsG_lay)
open DoubleDeal.Security.TrailBound (rounds Trail RoundChar trail_rounds_rel isDeck_rounds
  card_keys_compose card_filter_succ)
open DoubleDeal.Security.GridCycleSurvival (Check3 LKC LKS card_first_mem)
open DoubleDeal.Security.RealSchedule (roundKey roundKeys card_roundKey)

/-! ## The difference of two decks -/

open Classical in
/-- The relabelling taking deck `x` to deck `x'` (`1` if either is not a deck). -/
noncomputable def relDiff (x x' : Fin 52 → Nat) : Relabel :=
  if h : IsDeck x ∧ IsDeck x' then deckPerm x' h.2 * (deckPerm x h.1)⁻¹ else 1

theorem rel_relDiff {x x' : Fin 52 → Nat} (hx : IsDeck x) (hx' : IsDeck x') :
    rel (relDiff x x') x = x' := by
  unfold relDiff
  rw [dif_pos ⟨hx, hx'⟩]
  funext i
  show app (deckPerm x' hx' * (deckPerm x hx)⁻¹) (deckPerm x hx i).val = x' i
  rw [app_fin, Equiv.Perm.mul_apply, Equiv.Perm.inv_apply_self, deckPerm_val]

/-- (PROVED) `relDiff x x'` is the unique relabelling taking the deck `x` to the deck `x'`. -/
theorem relDiff_eq_iff {x x' : Fin 52 → Nat} (hx : IsDeck x) (hx' : IsDeck x') (γ : Relabel) :
    relDiff x x' = γ ↔ rel γ x = x' :=
  ⟨fun h => h ▸ rel_relDiff hx hx',
    fun h => (rel_left_inj hx).1 ((rel_relDiff hx hx').trans h.symm)⟩

/-! ## The events and counts -/

/-- After `R` rounds with keys `K`, the pair `(y, α·y)` has output difference `β`. The
    difference may change between rounds (unlike `Trail`). -/
def Diff (α β : Relabel) (R : ℕ) (y : Fin 52 → Nat) (K : Fin R → Key) : Prop :=
  rounds R (rel α y) K = rel β (rounds R y K)

instance (α β : Relabel) (R : ℕ) (y : Fin 52 → Nat) : DecidablePred (Diff α β R y) :=
  fun _ => inferInstanceAs (Decidable (_ = _))

/-- Key tuples (independent uniform round keys) for which the differential `α → β`
    holds after `R` rounds from deck `y`. -/
def diffCount (α β : Relabel) (R : ℕ) (y : Fin 52 → Nat) : ℕ :=
  (univ.filter fun K : Fin R → Key => Diff α β R y K).card

/-- One step of a deck map `U` (a round without its key): decks `x` (as permutations) with
    `U(α·x) = β·U(x)`. -/
def dpCount (U : (Fin 52 → Nat) → Fin 52 → Nat) (α β : Relabel) : ℕ :=
  (univ.filter fun π : Equiv.Perm (Fin 52) =>
    U (rel α (permDeck π)) = rel β (U (permDeck π))).card

/-- One unkeyed round (`U = unkeyedWithMix`): decks `x` (as permutations) with
    `U(α·x) = β·U(x)`. -/
def dp1Count (α β : Relabel) : ℕ := dpCount unkeyedWithMix α β

/-- The output difference of one unkeyed round at the deck `x`, input difference `α`. -/
noncomputable def stepDiff (α : Relabel) (x : Fin 52 → Nat) : Relabel :=
  relDiff (unkeyedWithMix x) (unkeyedWithMix (rel α x))

theorem stepDiff_spec (α : Relabel) {x : Fin 52 → Nat} (hx : IsDeck x) :
    unkeyedWithMix (rel α x) = rel (stepDiff α x) (unkeyedWithMix x) :=
  (rel_relDiff (isDeck_unkeyedWithMix hx) (isDeck_unkeyedWithMix (isDeck_rel α hx))).symm

theorem stepDiff_eq_iff (α γ : Relabel) {x : Fin 52 → Nat} (hx : IsDeck x) :
    stepDiff α x = γ ↔ unkeyedWithMix (rel α x) = rel γ (unkeyedWithMix x) :=
  (relDiff_eq_iff (isDeck_unkeyedWithMix hx) (isDeck_unkeyedWithMix (isDeck_rel α hx)) γ).trans
    eq_comm

/-! ## D0: the characteristic is one path of the differential -/

/-- (PROVED) Trail counts are LOWER bounds for the differential count `σ → σ`. -/
theorem card_trail_le_diffCount (σ : Relabel) (R : ℕ) (y : Fin 52 → Nat) :
    (univ.filter fun K : Fin R → Key => Trail σ R y K).card ≤ diffCount σ σ R y := by
  apply card_le_card
  intro K hK
  simp only [mem_filter, mem_univ, true_and] at hK ⊢
  exact trail_rounds_rel σ R y K hK

/-! ## One round, counting over the key -/

theorem card_keys_stepDiff (α γ : Relabel) {y : Fin 52 → Nat} (hy : IsDeck y) :
    (univ.filter fun k : Key => stepDiff α (composeVec 52 Nat y k) = γ).card =
      dp1Count α γ := by
  rw [filter_congr (fun k _ => stepDiff_eq_iff α γ (isDeck_compose hy k))]
  exact card_keys_compose (fun x => unkeyedWithMix (rel α x) = rel γ (unkeyedWithMix x)) hy

theorem sum_keys_stepDiff (α : Relabel) {y : Fin 52 → Nat} (hy : IsDeck y)
    (f : Relabel → ℕ) :
    ∑ k : Key, f (stepDiff α (composeVec 52 Nat y k)) = ∑ γ, dp1Count α γ * f γ := by
  rw [← Finset.sum_fiberwise' univ (fun k : Key => stepDiff α (composeVec 52 Nat y k)) f]
  refine sum_congr rfl fun γ _ => ?_
  rw [sum_const, smul_eq_mul, card_keys_stepDiff α γ hy]

/-! ## D1, D2: the Markov recursion under independent keys -/

theorem diff_succ_iff (α β : Relabel) (R : ℕ) {y : Fin 52 → Nat} (hy : IsDeck y)
    (K : Fin (R + 1) → Key) :
    Diff α β (R + 1) y K ↔
      Diff (stepDiff α (composeVec 52 Nat y (K 0))) β R
        (unkeyedWithMix (composeVec 52 Nat y (K 0))) (Fin.tail K) := by
  simp only [Diff, rounds]
  rw [compose_rel, stepDiff_spec α (isDeck_compose hy (K 0))]

/-- (PROVED) Zero rounds: the count is `1` if `α = β`, else `0`. -/
theorem diffCount_zero (α β : Relabel) {y : Fin 52 → Nat} (hy : IsDeck y) :
    diffCount α β 0 y = if α = β then 1 else 0 := by
  unfold diffCount
  split_ifs with h
  · subst h
    rw [filter_true_of_mem (p := fun K : Fin 0 → Key => Diff α α 0 y K) (fun _ _ => rfl),
      card_univ, Fintype.card_unique]
  · rw [card_eq_zero, filter_eq_empty_iff]
    intro K _ hK
    exact h ((rel_left_inj hy).1 hK)

/-- The `R + 1`-round count splits over the first key. -/
theorem diffCount_succ_sum_keys (α β : Relabel) (R : ℕ) {y : Fin 52 → Nat} (hy : IsDeck y) :
    diffCount α β (R + 1) y =
      ∑ k : Key, diffCount (stepDiff α (composeVec 52 Nat y k)) β R
        (unkeyedWithMix (composeVec 52 Nat y k)) := by
  unfold diffCount
  rw [card_filter_succ]
  refine sum_congr rfl fun k _ => congrArg card (filter_congr fun K _ => ?_)
  rw [diff_succ_iff α β R hy, Fin.cons_zero, Fin.tail_cons]

/-- The `R + 1`-round recursion, given that the `R`-round counts into `β` do not depend
    on the deck (the induction step shared by D1 and D2). -/
theorem diffCount_succ_of_indep (α β : Relabel) (R : ℕ) {y z : Fin 52 → Nat}
    (hy : IsDeck y)
    (ih : ∀ (γ : Relabel) {w : Fin 52 → Nat}, IsDeck w →
      diffCount γ β R w = diffCount γ β R z) :
    diffCount α β (R + 1) y = ∑ γ, dp1Count α γ * diffCount γ β R z := by
  rw [diffCount_succ_sum_keys α β R hy,
    sum_congr rfl fun (k : Key) _ => ih _ (isDeck_unkeyedWithMix (isDeck_compose hy k))]
  exact sum_keys_stepDiff α hy (fun γ => diffCount γ β R z)

/-- (PROVED) D1: under independent uniform round keys the differential count does not
    depend on the starting deck. -/
theorem diffCount_eq_of_isDeck : ∀ (R : ℕ) (α β : Relabel) {y z : Fin 52 → Nat},
    IsDeck y → IsDeck z → diffCount α β R y = diffCount α β R z
  | 0, α, β, _, _, hy, hz => by rw [diffCount_zero α β hy, diffCount_zero α β hz]
  | R + 1, α, β, _, z, hy, hz => by
      have ih : ∀ (γ : Relabel) {w : Fin 52 → Nat}, IsDeck w →
          diffCount γ β R w = diffCount γ β R z :=
        fun γ _ hw => diffCount_eq_of_isDeck R γ β hw hz
      rw [diffCount_succ_of_indep α β R hy ih, diffCount_succ_of_indep α β R hz ih]

/-- (PROVED) D2: the Markov recursion. For any decks `y`, `z`,
    `diffCount α β (R+1) y = ∑ γ, dp1Count α γ * diffCount γ β R z`. -/
theorem diffCount_succ (α β : Relabel) (R : ℕ) {y z : Fin 52 → Nat} (hy : IsDeck y)
    (hz : IsDeck z) :
    diffCount α β (R + 1) y = ∑ γ, dp1Count α γ * diffCount γ β R z :=
  diffCount_succ_of_indep α β R hy fun γ _ hw => diffCount_eq_of_isDeck R γ β hw hz

/-- (PROVED) One round, independent key: the count is `dp1Count`. -/
theorem diffCount_one (α β : Relabel) {y : Fin 52 → Nat} (hy : IsDeck y) :
    diffCount α β 1 y = dp1Count α β := by
  rw [diffCount_succ α β 0 hy hy]
  simp only [diffCount_zero _ β hy, mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, if_true]

/-! ## D3: row sums and the trivial difference -/

/-- (PROVED) Row sums for any deck map `U` that maps decks to decks: from each `α`, the
    counts `dpCount U α β` over all `β` add up to `52!`. -/
theorem sum_dpCount (U : (Fin 52 → Nat) → Fin 52 → Nat)
    (hU : ∀ {x : Fin 52 → Nat}, IsDeck x → IsDeck (U x)) (α : Relabel) :
    ∑ β, dpCount U α β = Nat.factorial 52 := by
  have e : ∀ β, dpCount U α β = (univ.filter fun π : Equiv.Perm (Fin 52) =>
      relDiff (U (permDeck π)) (U (rel α (permDeck π))) = β).card := fun β => by
    unfold dpCount
    refine congrArg card (filter_congr fun π _ => ?_)
    have hd := isDeck_permDeck π
    rw [relDiff_eq_iff (hU hd) (hU (isDeck_rel α hd)), eq_comm]
  simp only [e]
  rw [← card_eq_sum_card_fiberwise (fun _ _ => mem_univ _), card_univ, Fintype.card_perm,
    Fintype.card_fin]

/-- (PROVED) Column sums for a deck map `U` with a two-sided inverse `V`, both mapping decks
    to decks: into each `β`, the counts `dpCount U α β` over all `α` add up to `52!`. -/
theorem sum_dpCount_left (U V : (Fin 52 → Nat) → Fin 52 → Nat)
    (hU : ∀ {x : Fin 52 → Nat}, IsDeck x → IsDeck (U x))
    (hV : ∀ {x : Fin 52 → Nat}, IsDeck x → IsDeck (V x))
    (hVU : ∀ x, V (U x) = x) (hUV : ∀ x, U (V x) = x) (β : Relabel) :
    ∑ α, dpCount U α β = Nat.factorial 52 := by
  have e : ∀ α, dpCount U α β = (univ.filter fun π : Equiv.Perm (Fin 52) =>
      relDiff (permDeck π) (V (rel β (U (permDeck π)))) = α).card := fun α => by
    unfold dpCount
    refine congrArg card (filter_congr fun π _ => ?_)
    have hd := isDeck_permDeck π
    rw [relDiff_eq_iff hd (hV (isDeck_rel β (hU hd)))]
    exact ⟨fun h => by rw [← h, hVU], fun h => by rw [h, hUV]⟩
  simp only [e]
  rw [← card_eq_sum_card_fiberwise (fun _ _ => mem_univ _), card_univ, Fintype.card_perm,
    Fintype.card_fin]

/-- (PROVED) One round: the counts `α → β` over all `β` add up to `52!`. -/
theorem sum_dp1Count (α : Relabel) : ∑ β, dp1Count α β = Nat.factorial 52 :=
  sum_dpCount unkeyedWithMix isDeck_unkeyedWithMix α

/-- (PROVED) `R` rounds: the counts `α → β` over all `β` add up to `(52!)^R`. -/
theorem sum_diffCount (α : Relabel) : ∀ (R : ℕ) {y : Fin 52 → Nat}, IsDeck y →
    ∑ β, diffCount α β R y = Nat.factorial 52 ^ R
  | 0, _, hy => by simp only [diffCount_zero α _ hy, sum_ite_eq, mem_univ, if_true, pow_zero]
  | R + 1, y, hy => by
      simp only [diffCount_succ α _ R hy hy]
      rw [sum_comm]
      simp only [← mul_sum, sum_diffCount _ R hy]
      rw [← sum_mul, sum_dp1Count, pow_succ, Nat.mul_comm]

/-- (PROVED) Generic: for ANY deck map `U` sending decks to decks, the trivial difference
    goes only to itself, on every deck: `dpCount U 1 β` is `52!` if `β = 1`, else `0`.
    No injectivity is needed. -/
theorem dpCount_one_left (U : (Fin 52 → Nat) → Fin 52 → Nat)
    (hU : ∀ {x : Fin 52 → Nat}, IsDeck x → IsDeck (U x)) (β : Relabel) :
    dpCount U 1 β = if β = 1 then Nat.factorial 52 else 0 := by
  unfold dpCount
  split_ifs with h
  · subst h
    rw [filter_true_of_mem (fun π _ => by simp only [rel_one]), card_univ, Fintype.card_perm,
      Fintype.card_fin]
  · rw [card_eq_zero, filter_eq_empty_iff]
    intro π _ hπ
    rw [rel_one] at hπ
    exact h ((rel_left_inj (hU (isDeck_permDeck π))).1 (hπ.symm.trans (rel_one _).symm))

/-- (PROVED) Generic: for an INJECTIVE deck map `U`, a nontrivial difference never becomes
    trivial: `dpCount U α 1 = 0` for `α ≠ 1`. The hypothesis `hinj` is needed: for a
    non-injective `U` (e.g. a constant map) the count can be `52!`. -/
theorem dpCount_to_one (U : (Fin 52 → Nat) → Fin 52 → Nat) (hinj : Function.Injective U)
    {α : Relabel} (hα : α ≠ 1) : dpCount U α 1 = 0 := by
  unfold dpCount
  rw [card_eq_zero, filter_eq_empty_iff]
  intro π _ hπ
  rw [rel_one] at hπ
  have h2 : rel α (permDeck π) = rel 1 (permDeck π) := by rw [rel_one]; exact hinj hπ
  exact hα ((rel_left_inj (isDeck_permDeck π)).1 h2)

/-- (PROVED) The trivial difference stays trivial in one round (`dpCount_one_left`). -/
theorem dp1Count_one_left (β : Relabel) :
    dp1Count 1 β = if β = 1 then Nat.factorial 52 else 0 :=
  dpCount_one_left unkeyedWithMix isDeck_unkeyedWithMix β

/-- (PROVED) The trivial difference stays trivial over `R` rounds. -/
theorem diffCount_one_left (β : Relabel) (R : ℕ) {y : Fin 52 → Nat} (hy : IsDeck y) :
    diffCount 1 β R y = if β = 1 then Nat.factorial 52 ^ R else 0 := by
  unfold diffCount
  split_ifs with h
  · subst h
    rw [filter_true_of_mem (fun K _ => by simp only [Diff, rel_one]), card_univ,
      Fintype.card_fun, Fintype.card_perm, Fintype.card_fin, Fintype.card_fin]
  · rw [card_eq_zero, filter_eq_empty_iff]
    intro K _ hK
    simp only [Diff, rel_one] at hK
    exact h ((rel_left_inj (isDeck_rounds R y K hy)).1 (hK.symm.trans (rel_one _).symm))

/-- (PROVED) A nontrivial difference never becomes trivial in one round
    (`dpCount_to_one`, with the core `DoubleDeal.unkeyedWithMix_injective`). -/
theorem dp1Count_to_one {α : Relabel} (hα : α ≠ 1) : dp1Count α 1 = 0 :=
  dpCount_to_one unkeyedWithMix unkeyedWithMix_injective hα

/-- (PROVED) A nontrivial difference never becomes trivial over `R` rounds. -/
theorem diffCount_to_one {α : Relabel} (hα : α ≠ 1) : ∀ (R : ℕ) {y : Fin 52 → Nat},
    IsDeck y → diffCount α 1 R y = 0
  | 0, _, hy => by rw [diffCount_zero α 1 hy, if_neg hα]
  | R + 1, y, hy => by
      rw [diffCount_succ α 1 R hy hy]
      refine sum_eq_zero fun γ _ => ?_
      by_cases hγ : γ = 1
      · rw [hγ, dp1Count_to_one hα, Nat.zero_mul]
      · rw [diffCount_to_one hγ R hy, Nat.mul_zero]

/-! ## D4: out of `v10Sym`, one round (first-card argument) -/

theorem unkeyedNoMix_rel_v10Sym (a : Fin 13) (x : Fin 4) {m : Fin 52 → Nat} (hm : Cards m) :
    unkeyedNoMix (rel (v10Sym a x) m) = rel (v10Sym a x) (unkeyedNoMix m) :=
  unkeyedNoMix_commutes _ (sumRanksV10_commutes_v10Sym a x) m hm

/-- (PROVED) If one round sends `(x₀, v10Sym a x · x₀)` to difference `β`, then
    `v10Sym a x` and `β` agree on the first card `c` of the stem output. -/
theorem v10Sym_step_agree (a : Fin 13) (x : Fin 4) (β : Relabel) {x₀ : Fin 52 → Nat}
    (hx₀ : IsDeck x₀)
    (h : unkeyedWithMix (rel (v10Sym a x) x₀) = rel β (unkeyedWithMix x₀)) :
    v10Sym a x ⟨unkeyedNoMix x₀ ⟨0, by decide⟩, (isDeck_unkeyedNoMix hx₀).1 _⟩ =
      β ⟨unkeyedNoMix x₀ ⟨0, by decide⟩, (isDeck_unkeyedNoMix hx₀).1 _⟩ := by
  simp only [unkeyedWithMix] at h
  rw [unkeyedNoMix_rel_v10Sym a x hx₀.1] at h
  have e := congrFun h ⟨26, by decide⟩
  simp only [rel] at e
  rw [mixColumns_at_AS, mixColumns_at_AS] at e
  simp only [rel] at e
  apply Fin.ext
  rw [← app_fin, ← app_fin]
  exact e

/-- GF(4) addition by a fixed `l` is injective on `Fin 4`. -/
theorem gfAdd_cancel (l : Nat) {x x' : Fin 4} (h : gfAdd l x.val = gfAdd l x'.val) :
    x = x' := by
  unfold gfAdd at h
  omega

/-- (PROVED) Two different `v10Sym` agree on no card. -/
theorem eq_of_v10Sym_apply_eq {a a' : Fin 13} {x x' : Fin 4} (c : Fin 52)
    (h : v10Sym a x c = v10Sym a' x' c) : a = a' ∧ x = x' := by
  have hr := v10SymFn_rank a x c
  have hr' := v10SymFn_rank a' x' c
  have hl := v10SymFn_label a x c
  have hl' := v10SymFn_label a' x' c
  change v10SymFn a x c = v10SymFn a' x' c at h
  rw [h] at hr hl
  refine ⟨Fin.ext ?_, gfAdd_cancel _ (hl.symm.trans hl')⟩
  have := hr.symm.trans hr'
  omega

/-- (PROVED) D4. Input difference `v10Sym a x`: the one-round count to `β` is at most
    `52!/52` times the number of cards on which `v10Sym a x` and `β` agree. -/
theorem dp1Count_v10Sym_le_agree (a : Fin 13) (x : Fin 4) (β : Relabel) :
    52 * dp1Count (v10Sym a x) β ≤
      (univ.filter fun c : Fin 52 => v10Sym a x c = β c).card * Nat.factorial 52 := by
  rw [← card_first_mem]
  refine Nat.mul_le_mul_left 52 ?_
  let f : Equiv.Perm (Fin 52) → Equiv.Perm (Fin 52) := fun π =>
    deckPerm (unkeyedNoMix (permDeck π)) (isDeck_unkeyedNoMix (isDeck_permDeck π))
  have hf : ∀ π, permDeck (f π) = unkeyedNoMix (permDeck π) :=
    fun π => funext fun i => deckPerm_val _ _ i
  apply card_le_card_of_injOn f
  · intro π hπ
    simp only [coe_filter, Set.mem_setOf_eq, mem_filter, mem_univ, true_and, mem_coe] at hπ ⊢
    have e := v10Sym_step_agree a x β (isDeck_permDeck π) hπ
    have e0 : f π ⟨0, by decide⟩ =
        ⟨unkeyedNoMix (permDeck π) ⟨0, by decide⟩,
          (isDeck_unkeyedNoMix (isDeck_permDeck π)).1 _⟩ :=
      Fin.ext (deckPerm_val _ _ _)
    rw [show (0 : Fin 52) = ⟨0, by decide⟩ from rfl, e0]
    exact e
  · intro π₁ _ π₂ _ h
    have h' : unkeyedNoMix (permDeck π₁) = unkeyedNoMix (permDeck π₂) := by
      rw [← hf, ← hf, h]
    have h'' : permDeck π₁ = permDeck π₂ := by
      rw [← invUnkeyedNoMix_unkeyedNoMix (permDeck π₁), h', invUnkeyedNoMix_unkeyedNoMix]
    exact Equiv.ext fun i => Fin.ext (congrFun h'' i)

/-- (PROVED) If `β` agrees with `v10Sym a x` on no card, the one-round count is `0`. -/
theorem dp1Count_v10Sym_eq_zero (a : Fin 13) (x : Fin 4) (β : Relabel)
    (h : ∀ c, v10Sym a x c ≠ β c) : dp1Count (v10Sym a x) β = 0 := by
  have hle := dp1Count_v10Sym_le_agree a x β
  rw [filter_false_of_mem (fun c _ => h c), card_empty, Nat.zero_mul] at hle
  omega

/-- (PROVED) One round never takes `v10Sym a x` to a DIFFERENT `v10Sym a' x'`. -/
theorem dp1Count_v10Sym_v10Sym_eq_zero {a a' : Fin 13} {x x' : Fin 4}
    (hdiff : ¬ (a = a' ∧ x = x')) : dp1Count (v10Sym a x) (v10Sym a' x') = 0 :=
  dp1Count_v10Sym_eq_zero a x _ fun c hc => hdiff (eq_of_v10Sym_apply_eq c hc)

/-! ## D5: paths that stay inside `v10Sym` -/

/-- The pair `(y, α·y)` follows a path whose difference after EVERY round is some
    `v10Sym a' x'` (possibly different each round). Only these paths are covered by the
    D5 bounds; a path leaving `v10Sym` is not. -/
def StaysInV10 : (R : ℕ) → Relabel → (Fin 52 → Nat) → (Fin R → Key) → Prop
  | 0, _, _, _ => True
  | R + 1, α, y, K => ∃ (a' : Fin 13) (x' : Fin 4),
      unkeyedWithMix (rel α (composeVec 52 Nat y (K 0))) =
        rel (v10Sym a' x') (unkeyedWithMix (composeVec 52 Nat y (K 0))) ∧
      StaysInV10 R (v10Sym a' x') (unkeyedWithMix (composeVec 52 Nat y (K 0))) (Fin.tail K)

/-- (PROVED) For a `v10Sym` difference the round characteristic is exactly
    "the round maps the difference to itself" (SumRanks always commutes). -/
theorem roundChar_v10Sym_iff (a : Fin 13) (x : Fin 4) {x₀ : Fin 52 → Nat}
    (hx₀ : IsDeck x₀) :
    RoundChar (v10Sym a x) x₀ ↔
      unkeyedWithMix (rel (v10Sym a x) x₀) = rel (v10Sym a x) (unkeyedWithMix x₀) := by
  have hs := unkeyedNoMix_rel_v10Sym a x hx₀.1
  constructor
  · intro h; exact TrailBound.roundChar_unkeyedWithMix h
  · intro h
    refine ⟨sumRanksV10_commutes_v10Sym a x _ (cardsG_lay hx₀.1), ?_⟩
    simp only [unkeyedWithMix] at h
    rwa [hs] at h

/-- (PROVED) D5. Paths inside `v10Sym` are exactly the constant characteristic: the
    difference cannot move to a different `v10Sym` (`v10Sym_step_agree`). -/
theorem staysInV10_iff_trail (a : Fin 13) (x : Fin 4) : ∀ (R : ℕ) (y : Fin 52 → Nat)
    (K : Fin R → Key), IsDeck y → (StaysInV10 R (v10Sym a x) y K ↔ Trail (v10Sym a x) R y K)
  | 0, _, _, _ => Iff.rfl
  | R + 1, y, K, hy => by
      have hx₀ := isDeck_compose hy (K 0)
      have ih := staysInV10_iff_trail a x R _ (Fin.tail K) (isDeck_unkeyedWithMix hx₀)
      simp only [StaysInV10, Trail]
      constructor
      · rintro ⟨a', x', h1, h2⟩
        obtain ⟨rfl, rfl⟩ := eq_of_v10Sym_apply_eq _ (v10Sym_step_agree a x _ hx₀ h1)
        exact ⟨(roundChar_v10Sym_iff a x hx₀).2 h1, ih.1 h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨a, x, (roundChar_v10Sym_iff a x hx₀).1 h1, ih.2 h2⟩

open Classical in
/-- For any family of key tuples `f i`, counting the `i` whose path stays inside `v10Sym`
    is counting the `i` that follow the characteristic (`staysInV10_iff_trail`). -/
theorem card_staysInV10_eq (a : Fin 13) (x : Fin 4) (R : ℕ) {y : Fin 52 → Nat}
    (hy : IsDeck y) {ι : Type} [Fintype ι] (f : ι → Fin R → Key) :
    (univ.filter fun i : ι => StaysInV10 R (v10Sym a x) y (f i)).card =
      (univ.filter fun i : ι => Trail (v10Sym a x) R y (f i)).card :=
  congrArg card (filter_congr fun i _ => staysInV10_iff_trail a x R y (f i) hy)

open Classical in
/-- (PROVED; no hypothesis beyond `(a, x) ≠ (0, 0)`) Nontrivial `v10Sym a x`, independent uniform
    round keys: at most `(52!)^R / 26^R` key tuples keep the difference inside `v10Sym` for `R`
    rounds. Only paths inside `v10Sym`; NOT a bound on the differential. -/
theorem staysInV10_card_le_26 (a : Fin 13) (x : Fin 4) (hne : ¬ (a = 0 ∧ x = 0))
    (R : ℕ) {y : Fin 52 → Nat} (hy : IsDeck y) :
    26 ^ R * (univ.filter fun K : Fin R → Key => StaysInV10 R (v10Sym a x) y K).card ≤
      Nat.factorial 52 ^ R := by
  rw [card_staysInV10_eq a x R hy fun K : Fin R → Key => K]
  exact TrailBound.trail_card_le_of_round _ 26 (TrailBound.round_le_26_v10Sym a x hne) R y hy

open Classical in
/-- (PROVED, given the two finite GridCycle checks as hypotheses) As
    `staysInV10_card_le_26` with `4420^R`. Without the check hypotheses in the heavy library
    (`staysInV10_card_le_4420`). Only paths inside `v10Sym`. -/
theorem staysInV10_card_le_4420_of_check (hKC : Check3 KC LKC) (hKS : Check3 KS LKS)
    (a : Fin 13) (x : Fin 4) (hne : ¬ (a = 0 ∧ x = 0)) (R : ℕ) {y : Fin 52 → Nat}
    (hy : IsDeck y) :
    4420 ^ R * (univ.filter fun K : Fin R → Key => StaysInV10 R (v10Sym a x) y K).card ≤
      Nat.factorial 52 ^ R := by
  rw [card_staysInV10_eq a x R hy fun K : Fin R → Key => K]
  exact TrailBound.trail_card_le_4420_v10Sym_of_check hKC hKS a x hne R y hy

/-! ## D5 and D6 under the real PassKey schedule (one round only) -/

open Classical in
/-- (PROVED; no hypothesis beyond `(a, x) ≠ (0, 0)`) Real PassKey schedule, uniform master key,
    nontrivial `v10Sym a x`, every `R ≥ 1`, every deck `y`: at most `52!/26` master keys keep the
    difference inside `v10Sym` for `R` rounds. The bound of the proof's first mix round (key
    `K_0`; not `(1/26)^R`); only paths inside `v10Sym`. -/
theorem realStaysInV10_card_le_26 (a : Fin 13) (x : Fin 4) (hne : ¬ (a = 0 ∧ x = 0))
    (R : ℕ) (hR : 0 < R) {y : Fin 52 → Nat} (hy : IsDeck y) :
    26 * (univ.filter fun π : Equiv.Perm (Fin 52) =>
      StaysInV10 R (v10Sym a x) y (roundKeys R π)).card ≤ Nat.factorial 52 := by
  rw [card_staysInV10_eq a x R hy (roundKeys R)]
  exact RealSchedule.realTrail_card_le_of_round _ 26 (TrailBound.round_le_26_v10Sym a x hne)
    R hR y hy

open Classical in
/-- (PROVED, given the two finite GridCycle checks as hypotheses) As
    `realStaysInV10_card_le_26` with `52!/4420`. The bound of the proof's first mix round.
    Without the check hypotheses in the heavy library (`realStaysInV10_card_le_4420`). -/
theorem realStaysInV10_card_le_4420_of_check (hKC : Check3 KC LKC) (hKS : Check3 KS LKS)
    (a : Fin 13) (x : Fin 4) (hne : ¬ (a = 0 ∧ x = 0)) (R : ℕ) (hR : 0 < R)
    {y : Fin 52 → Nat} (hy : IsDeck y) :
    4420 * (univ.filter fun π : Equiv.Perm (Fin 52) =>
      StaysInV10 R (v10Sym a x) y (roundKeys R π)).card ≤ Nat.factorial 52 := by
  rw [card_staysInV10_eq a x R hy (roundKeys R)]
  exact RealSchedule.realTrail_card_le_of_round _ 4420
    (TrailBound.round_le_4420_v10Sym_of_check hKC hKS a x hne) R hR y hy

/-- (PROVED) D6. Real PassKey schedule, the proof's first mix round (key `K_0`) only: the count over
    master keys equals the independent-key count `dp1Count α β` (round key `K_0` alone is
    uniform). Nothing is proved for the real schedule at `R ≥ 2`. -/
theorem realDiffCount_one (α β : Relabel) {y : Fin 52 → Nat} (hy : IsDeck y) :
    (univ.filter fun π : Equiv.Perm (Fin 52) => Diff α β 1 y (roundKeys 1 π)).card =
      dp1Count α β := by
  have e : ∀ π, Diff α β 1 y (roundKeys 1 π) ↔
      (fun k : Key => unkeyedWithMix (rel α (composeVec 52 Nat y k)) =
        rel β (unkeyedWithMix (composeVec 52 Nat y k))) (roundKey 0 π) := fun π => by
    simp only [Diff, rounds]
    rw [compose_rel]
    rfl
  rw [filter_congr (fun π _ => e π)]
  refine (card_roundKey 0 (fun k : Key => unkeyedWithMix (rel α (composeVec 52 Nat y k)) =
    rel β (unkeyedWithMix (composeVec 52 Nat y k)))).trans ?_
  exact card_keys_compose (fun x => unkeyedWithMix (rel α x) = rel β (unkeyedWithMix x)) hy

end DoubleDeal.Security.Differential
