/-
  GridCycle (v12 = the v11 walk) survival of card relabellings, counted over decks.

  Notion ("relabelling survival", the differential notion the SumRanks bound
  `SumRanksDP.sumRanksV10_survival_le` uses): a relabelling `τ` of card values
  *survives* GridCycle on the deck `π` when
      `mixColumns (τ · π) = τ · mixColumns π`,
  i.e. the value difference `τ` between the pair `(π, τ·π)` is the same
  difference after the layer. Equivalently the seat walk is unchanged
  (`mixColumns_rel_iff_walk`).

  Proved here, for every relabelling `τ` and counting over all `52!` decks:
  * `gcSurvives_first`: surviving forces the first card `π 0` into the small set
    `gcExc τ` (fixed points of `τ`, plus K♣/K♠ when `τ` exchanges them), because
    the second seat is an injective function of the first card except for the
    single collision K♣/K♠ (`seat2_inj`, kernel `decide!`).
  * `gcSurvivors_card_le`: `52 · #survivors ≤ #gcExc τ · 52!`.
  * `gc_survival_le_fixfree`: a fixed-point-free `τ` survives on at most `52!/26` decks.
  * `gcSurvivors_v10Sym_eq_empty`: every nontrivial `v10Sym a x` except `v10Sym 0 3`
    survives on NO deck; `gc_survival_v10Sym03`: `v10Sym 0 3` on at most `52!/26`.
  * `gc_survival_v10Sym03_le_of_check` / `gc_survival_v10Sym_le_of_check`: GIVEN the two
    finite checks `Check3 KC LKC` and `Check3 KS LKS` (hypotheses; the first three
    seats, 2 · 52 · 52 walk evaluations), `v10Sym 0 3` and hence every nontrivial
    `v10Sym a x` survives on at most `52!/4420` decks (30 surviving first-card
    triples out of 52 · 51 · 50). The checks are discharged by kernel `decide!` in
    the heavy library (`DoubleDealSecurityHeavy/GridCycleSurvival.lean`,
    `gc_survival_v10Sym03_le` / `gc_survival_v10Sym_le`, unconditional there); this
    default library only carries the conditional form.

  Scope: one layer (GridCycle alone), exact relabelling survival only (not the
  distribution of output differences for a non-surviving pair), a first-step
  or three-step argument (the true survival probabilities are much smaller; exact
  prefix values and sampled full-survival values are measurements in
  `../analysis/v12-diffusion/`). No statement about keyed
  rounds or the cipher here; not a bit-security claim.
-/
import DoubleDealSecurity.GridCycle
import DoubleDealSecurity.SumRanksV10
import DoubleDealSecurity.SumRanksDP.ThreeCycle
import DoubleDealSecurity.BranchNumber
import Mathlib

namespace DoubleDeal.Security.GCSurvival

open DoubleDeal Relabel Finset

/-- `τ` survives GridCycle on the deck `π` (card `π k` at walk position `k`). -/
def GCSurvives (τ : Relabel) (π : Equiv.Perm (Fin 52)) : Prop :=
  mixColumns (rel τ (permDeck π)) = rel τ (mixColumns (permDeck π))

instance (τ : Relabel) : DecidablePred (GCSurvives τ) :=
  fun _ => inferInstanceAs (Decidable (_ = _))

/-- The decks on which `τ` survives GridCycle. -/
def gcSurvivors (τ : Relabel) : Finset (Equiv.Perm (Fin 52)) := univ.filter (GCSurvives τ)

/-- First cards compatible with survival: fixed points of `τ`, and K♣ / K♠ when
    `τ` sends one to the other. -/
def gcExc (τ : Relabel) : Finset (Fin 52) :=
  univ.filter fun c => τ c = c ∨ (c = KC ∧ τ c = KS) ∨ (c = KS ∧ τ c = KC)

/-- (PROVED) Survival forces the first card into `gcExc τ`. -/
theorem gcSurvives_first (τ : Relabel) (π : Equiv.Perm (Fin 52)) (h : GCSurvives τ π) :
    π 0 ∈ gcExc τ := by
  have hw := (mixColumns_rel_iff_walk τ (permDeck π) (isDeck_permDeck π)).1 h 1 (by decide)
  rw [walkSeat_one, walkSeat_one] at hw
  have e1 : rel τ (permDeck π) ⟨0, by decide⟩ = (τ (π 0)).val := by
    simp only [rel, permDeck, app_fin]; rfl
  have e2 : permDeck π ⟨0, by decide⟩ = (π 0).val := rfl
  rw [e1, e2] at hw
  simp only [gcExc, mem_filter, mem_univ, true_and]
  rcases seat2_inj (τ (π 0)) (π 0) hw with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inr ⟨h2, h2 ▸ h1⟩)
  · exact Or.inr (Or.inl ⟨h2, h2 ▸ h1⟩)

/-! ## Counting decks by their first card -/

theorem card_first_eq (c c' : Fin 52) :
    (univ.filter fun π : Equiv.Perm (Fin 52) => π 0 = c).card =
      (univ.filter fun π : Equiv.Perm (Fin 52) => π 0 = c').card := by
  apply card_nbij' (fun π => Equiv.swap c c' * π) (fun π => Equiv.swap c c' * π)
  · intro π hπ
    simp only [coe_filter, Set.mem_setOf_eq, mem_filter, mem_univ, true_and,
      Equiv.Perm.mul_apply] at hπ ⊢
    rw [hπ, Equiv.swap_apply_left]
  · intro π hπ
    simp only [coe_filter, Set.mem_setOf_eq, mem_filter, mem_univ, true_and,
      Equiv.Perm.mul_apply] at hπ ⊢
    rw [hπ, Equiv.swap_apply_right]
  · intro π _; simp [← mul_assoc]
  · intro π _; simp [← mul_assoc]

/-- Exactly `52!/52` decks start with a given card. -/
theorem card_first (c : Fin 52) :
    52 * (univ.filter fun π : Equiv.Perm (Fin 52) => π 0 = c).card = Nat.factorial 52 := by
  have hsum := card_eq_sum_card_fiberwise (s := (univ : Finset (Equiv.Perm (Fin 52))))
    (t := (univ : Finset (Fin 52))) (f := fun π : Equiv.Perm (Fin 52) => π (0 : Fin 52)) (fun _ _ => mem_univ _)
  have hc : ∀ c' ∈ (univ : Finset (Fin 52)),
      ((univ : Finset (Equiv.Perm (Fin 52))).filter fun π => π 0 = c').card =
        (univ.filter fun π : Equiv.Perm (Fin 52) => π 0 = c).card :=
    fun c' _ => card_first_eq c' c
  rw [sum_congr rfl hc, sum_const, Finset.card_fin, smul_eq_mul] at hsum
  have h52 : (univ : Finset (Equiv.Perm (Fin 52))).card = Nat.factorial 52 := by
    rw [card_univ, Fintype.card_perm, Fintype.card_fin]
  omega

/-- Decks whose first card lies in `E`: exactly `#E · 52!/52`. -/
theorem card_first_mem (E : Finset (Fin 52)) :
    52 * (univ.filter fun π : Equiv.Perm (Fin 52) => π 0 ∈ E).card =
      E.card * Nat.factorial 52 := by
  have hsum := card_eq_sum_card_fiberwise
    (s := univ.filter fun π : Equiv.Perm (Fin 52) => π 0 ∈ E) (t := E) (f := fun π : Equiv.Perm (Fin 52) => π (0 : Fin 52))
    (fun π hπ => by simpa using hπ)
  have hc : ∀ c ∈ E, ((univ.filter fun π : Equiv.Perm (Fin 52) => π 0 ∈ E).filter
      fun π => π 0 = c).card = (univ.filter fun π : Equiv.Perm (Fin 52) => π 0 = c).card := by
    intro c hc
    rw [filter_filter]
    congr 1
    apply filter_congr
    intro π _
    constructor
    · exact fun h => h.2
    · intro h; exact ⟨h ▸ hc, h⟩
  rw [hsum, sum_congr rfl hc, Finset.mul_sum, sum_congr rfl (fun c _ => card_first c),
    sum_const, smul_eq_mul]

/-! ## The survival bounds -/

/-- (PROVED) `τ` survives GridCycle on at most `#gcExc τ · 52!/52` decks. -/
theorem gcSurvivors_card_le (τ : Relabel) :
    52 * (gcSurvivors τ).card ≤ (gcExc τ).card * Nat.factorial 52 := by
  rw [← card_first_mem]
  apply Nat.mul_le_mul_left
  apply card_le_card
  intro π hπ
  simp only [gcSurvivors, mem_filter, mem_univ, true_and] at hπ ⊢
  exact gcSurvives_first τ π hπ

/-- `#gcExc τ ≤ #fixed points of τ + 2`. -/
theorem gcExc_card_le (τ : Relabel) :
    (gcExc τ).card ≤ (univ.filter fun c => τ c = c).card + 2 := by
  have hsub : gcExc τ ⊆ (univ.filter fun c => τ c = c) ∪ {KC, KS} := by
    intro c hc
    simp only [gcExc, mem_filter, mem_univ, true_and] at hc
    simp only [mem_union, mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
    rcases hc with h | ⟨h, _⟩ | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  calc (gcExc τ).card ≤ ((univ.filter fun c => τ c = c) ∪ {KC, KS}).card := card_le_card hsub
    _ ≤ (univ.filter fun c => τ c = c).card + ({KC, KS} : Finset (Fin 52)).card :=
        card_union_le _ _
    _ ≤ (univ.filter fun c => τ c = c).card + 2 := by
        have := card_insert_le KC ({KS} : Finset (Fin 52))
        rw [card_singleton] at this
        omega

/-- (PROVED) A relabelling with no fixed point survives GridCycle on at most
    `52!/26` of the `52!` decks. -/
theorem gc_survival_le_fixfree (τ : Relabel) (h : ∀ c, τ c ≠ c) :
    26 * (gcSurvivors τ).card ≤ Nat.factorial 52 := by
  have h0 : (univ.filter fun c => τ c = c) = ∅ := by
    ext c; simp [h c]
  have hE := gcExc_card_le τ
  rw [h0, card_empty] at hE
  have := gcSurvivors_card_le τ
  have h52 : 52 * (gcSurvivors τ).card ≤ 2 * Nat.factorial 52 :=
    this.trans (Nat.mul_le_mul_right _ (by omega))
  omega

/-! ## The SumRanks symmetries `v10Sym` -/

theorem v10SymFn_KC_KS : ∀ (a : Fin 13) (x : Fin 4),
    v10SymFn a x KC = KS → a = 0 ∧ x = 3 := by decide!

theorem v10SymFn_KS_KC : ∀ (a : Fin 13) (x : Fin 4),
    v10SymFn a x KS = KC → a = 0 ∧ x = 3 := by decide!

theorem v10Sym_fixfree (a : Fin 13) (x : Fin 4) (hne : ¬ (a = 0 ∧ x = 0)) (c : Fin 52) :
    v10Sym a x c ≠ c := fun h => hne (v10SymFn_fixed a x c h)

/-- (PROVED) Every nontrivial `v10Sym a x` other than `v10Sym 0 3` survives GridCycle on
    no deck at all. (These are exactly the relabellings on which the SumRanks bound
    `sumRanksV10_survival_le` says nothing, since they commute with SumRanks on
    every deck.) -/
theorem gcSurvivors_v10Sym_eq_empty (a : Fin 13) (x : Fin 4) (hne : ¬ (a = 0 ∧ x = 0))
    (h03 : ¬ (a = 0 ∧ x = 3)) : gcSurvivors (v10Sym a x) = ∅ := by
  have hE : gcExc (v10Sym a x) = ∅ := by
    ext c
    simp only [gcExc, mem_filter, mem_univ, true_and, not_mem_empty, iff_false]
    rintro (h | ⟨rfl, h⟩ | ⟨rfl, h⟩)
    · exact v10Sym_fixfree a x hne c h
    · exact h03 (v10SymFn_KC_KS a x h)
    · exact h03 (v10SymFn_KS_KC a x h)
  have := gcSurvivors_card_le (v10Sym a x)
  rw [hE, card_empty, zero_mul] at this
  exact card_eq_zero.1 (by omega)

/-- (PROVED) `v10Sym 0 3` (♣↔♠, ♥↔♦, same rank) survives GridCycle on at most `52!/26`
    decks. This is a first-step bound; the exact prefix values are measured in
    `../analysis/v12-diffusion/prefix_survival.log`. -/
theorem gc_survival_v10Sym03 : 26 * (gcSurvivors (v10Sym 0 3)).card ≤ Nat.factorial 52 :=
  gc_survival_le_fixfree _ (v10Sym_fixfree 0 3 (by decide))

/-! ## Three walk steps for `v10Sym 0 3`

`v10Sym 0 3` is the one nontrivial SumRanks symmetry that the first-step bound
does not kill. Looking at the seats of walk cards 1, 2 and 3 (which depend only
on the first three cards), exactly 30 ordered triples of distinct first cards
keep them unchanged (kernel `decide!`); every deck survives only if its first
three cards form one of them. Hence at most `30 · 49! = 52!/4420` decks survive.
This matches the exhaustive count `A_4 = 1/4420` in
`../analysis/v12-diffusion/prefix_survival.log`. -/

/-- A hand whose first three cards are `c0, c1, c2` (the rest is `c2`, never read). -/
def hand3 (c0 c1 c2 : Nat) : Fin 52 → Nat := fun i =>
  if i.val = 0 then c0 else if i.val = 1 then c1 else c2

/-- The seats of walk cards 1, 2, 3 as a function of the first three cards. -/
def seats3 (c0 c1 c2 : Nat) : (Fin 4 × Fin 13) × (Fin 4 × Fin 13) × (Fin 4 × Fin 13) :=
  (walkSeat (hand3 c0 c1 c2) 1, walkSeat (hand3 c0 c1 c2) 2, walkSeat (hand3 c0 c1 c2) 3)

theorem walkSeat_prefix3 (hand : Fin 52 → Nat) (n : Nat) (hn : n ≤ 3) :
    walkSeat hand n = walkSeat (hand3 (hand 0) (hand 1) (hand 2)) n := by
  rw [walkSeat_eq, walkSeat_eq]
  apply seatW_depends_on_prefix
  intro k hk
  rcases (by omega : k.val = 0 ∨ k.val = 1 ∨ k.val = 2) with h | h | h
  · have : k = 0 := Fin.ext h
    subst this; simp [hand3]
  · have : k = 1 := Fin.ext h
    subst this; simp [hand3]
  · have : k = 2 := Fin.ext h
    subst this; simp [hand3]

/-- (PROVED) Survival fixes the seats of walk cards 1, 2, 3. -/
theorem gcSurvives_seats3 (τ : Relabel) (π : Equiv.Perm (Fin 52)) (h : GCSurvives τ π) :
    seats3 (τ (π 0)).val (τ (π 1)).val (τ (π 2)).val = seats3 (π 0).val (π 1).val (π 2).val := by
  have hw := (mixColumns_rel_iff_walk τ (permDeck π) (isDeck_permDeck π)).1 h
  have e : ∀ i : Fin 52, rel τ (permDeck π) i = (τ (π i)).val := fun i => by
    simp only [rel, permDeck, app_fin]
  have hn : ∀ n, n ≤ 3 → 0 < n → walkSeat (hand3 (τ (π 0)).val (τ (π 1)).val (τ (π 2)).val) n =
      walkSeat (hand3 (π 0).val (π 1).val (π 2).val) n := by
    intro n hn3 hn0
    have := hw n (by omega)
    rw [walkSeat_prefix3 _ n hn3, walkSeat_prefix3 (permDeck π) n hn3, e, e, e] at this
    exact this
  simp only [seats3]
  rw [hn 1 (by omega) (by omega), hn 2 (by omega) (by omega), hn 3 (by omega) (by omega)]

/-- Second and third cards keeping seats 1..3 unchanged under `v10Sym 0 3`, first card K♣. -/
def LKC : List (Nat × Nat) := [(0, 38), (1, 38), (2, 38), (3, 38), (4, 38), (5, 38), (6, 38), (7, 38), (8, 38), (9, 38), (10, 38), (11, 38), (13, 24), (50, 13), (51, 25)]

/-- The same with first card K♠. -/
def LKS : List (Nat × Nat) := [(24, 39), (25, 51), (26, 12), (27, 12), (28, 12), (29, 12), (30, 12), (31, 12), (32, 12), (33, 12), (34, 12), (35, 12), (36, 12), (37, 12), (39, 50)]

/-- The finite check behind the three-step bound for first card `c0`: every
    `(c1, c2)` that keeps seats 1..3 unchanged under `v10Sym 0 3` (with `c0, c1, c2`
    distinct) is listed in `L`. Evaluated by kernel `decide!` in the heavy library
    (`DoubleDealSecurityHeavy/GridCycleSurvival.lean`, about 3-4 min), not here. -/
def check3 (c0 : Fin 52) (L : List (Nat × Nat)) (c1 c2 : Fin 52) : Bool :=
  !(decide (seats3 (v10SymFn 0 3 c0).val (v10SymFn 0 3 c1).val (v10SymFn 0 3 c2).val =
      seats3 c0.val c1.val c2.val)) || decide (c1 = c0) || decide (c2 = c0) || decide (c1 = c2) ||
    decide ((c1.val, c2.val) ∈ L)

/-- `check3` holds for every pair. -/
def Check3 (c0 : Fin 52) (L : List (Nat × Nat)) : Prop := ∀ c1 c2 : Fin 52, check3 c0 L c1 c2 = true

theorem of_check3 {c0 : Fin 52} {L : List (Nat × Nat)} (h : Check3 c0 L) (c1 c2 : Fin 52)
    (hs : seats3 (v10SymFn 0 3 c0).val (v10SymFn 0 3 c1).val (v10SymFn 0 3 c2).val =
      seats3 c0.val c1.val c2.val) (h1 : c1 ≠ c0) (h2 : c2 ≠ c0) (h12 : c1 ≠ c2) :
    (c1.val, c2.val) ∈ L := by
  have := h c1 c2
  simpa [check3, hs, h1, h2, h12] using this

/-- `n` as a card (`n % 52`). -/
def finOf (n : Nat) : Fin 52 := ⟨n % 52, Nat.mod_lt _ (by decide)⟩

theorem finOf_val (c : Fin 52) : finOf c.val = c := Fin.ext (Nat.mod_eq_of_lt c.isLt)

/-- The 30 first-card triples (card ids) that keep seats 1..3 unchanged under
    `v10Sym 0 3`: `LKC` and `LKS` with the first card (K♣ = 12, K♠ = 38) prepended. -/
def T03N : List (Nat × Nat × Nat) :=
  [(12, 0, 38), (12, 1, 38), (12, 2, 38), (12, 3, 38), (12, 4, 38), (12, 5, 38), (12, 6, 38), (12, 7, 38), (12, 8, 38), (12, 9, 38), (12, 10, 38), (12, 11, 38), (12, 13, 24), (12, 50, 13), (12, 51, 25), (38, 24, 39), (38, 25, 51), (38, 26, 12), (38, 27, 12), (38, 28, 12), (38, 29, 12), (38, 30, 12), (38, 31, 12), (38, 32, 12), (38, 33, 12), (38, 34, 12), (38, 35, 12), (38, 36, 12), (38, 37, 12), (38, 39, 50)]

def toFin3 (t : Nat × Nat × Nat) : Fin 52 × Fin 52 × Fin 52 := (finOf t.1, finOf t.2.1, finOf t.2.2)

def T03 : Finset (Fin 52 × Fin 52 × Fin 52) := (T03N.map toFin3).toFinset

theorem card_T03_le : T03.card ≤ 30 :=
  (List.toFinset_card_le _).trans (by simp [T03N])

theorem T03N_ok : ∀ t ∈ T03N, t.1 < 52 ∧ t.2.1 < 52 ∧ t.2.2 < 52 ∧
    t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 := by decide

theorem T03_distinct : ∀ t ∈ T03, t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 := by
  intro t ht
  simp only [T03, List.mem_toFinset, List.mem_map] at ht
  obtain ⟨n, hn, rfl⟩ := ht
  obtain ⟨h0, h1, h2, d01, d02, d12⟩ := T03N_ok n hn
  simp only [toFin3, finOf, ne_eq, Fin.mk.injEq, Nat.mod_eq_of_lt h0, Nat.mod_eq_of_lt h1,
    Nat.mod_eq_of_lt h2]
  exact ⟨d01, d02, d12⟩

theorem LKC_sub : ∀ p ∈ LKC, (12, p.1, p.2) ∈ T03N := by decide

theorem LKS_sub : ∀ p ∈ LKS, (38, p.1, p.2) ∈ T03N := by decide

theorem mem_T03_of_lists (c0 c1 c2 : Fin 52)
    (h : (c0 = KC ∧ (c1.val, c2.val) ∈ LKC) ∨ (c0 = KS ∧ (c1.val, c2.val) ∈ LKS)) :
    (c0, c1, c2) ∈ T03 := by
  simp only [T03, List.mem_toFinset, List.mem_map]
  rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩
  · exact ⟨(12, c1.val, c2.val), LKC_sub _ h, by simp [toFin3, finOf_val]; rfl⟩
  · exact ⟨(38, c1.val, c2.val), LKS_sub _ h, by simp [toFin3, finOf_val]; rfl⟩

/-- (PROVED) A deck on which `v10Sym 0 3` survives GridCycle starts with a triple of `T03`. -/
theorem gcSurvives_v03_T03 (hKC : Check3 KC LKC) (hKS : Check3 KS LKS)
    (π : Equiv.Perm (Fin 52)) (h : GCSurvives (v10Sym 0 3) π) :
    (π 0, π 1, π 2) ∈ T03 := by
  have h1 := gcSurvives_first _ π h
  have h3 := gcSurvives_seats3 _ π h
  have hfix := v10Sym_fixfree 0 3 (by decide)
  have d01 : π 1 ≠ π 0 := fun e => absurd (π.injective e) (by decide)
  have d02 : π 2 ≠ π 0 := fun e => absurd (π.injective e) (by decide)
  have d12 : π 1 ≠ π 2 := fun e => absurd (π.injective e) (by decide)
  simp only [gcExc, mem_filter, mem_univ, true_and] at h1
  apply mem_T03_of_lists
  rcases h1 with h1 | ⟨h0, _⟩ | ⟨h0, _⟩
  · exact absurd h1 (hfix _)
  · rw [h0] at h3 d01 d02
    exact Or.inl ⟨h0, of_check3 hKC (π 1) (π 2) h3 d01 d02 d12⟩
  · rw [h0] at h3 d01 d02
    exact Or.inr ⟨h0, of_check3 hKS (π 1) (π 2) h3 d01 d02 d12⟩

/-! ### Counting decks by their first three cards -/

/-- Decks with first cards `(0, 1, 2)`; every distinct triple has as many. -/
@[irreducible] def F3 : ℕ := (univ.filter fun π : Equiv.Perm (Fin 52) => (π 0, π 1, π 2) = ((0 : Fin 52), (1 : Fin 52), (2 : Fin 52))).card

theorem fibre3_card (t : Fin 52 × Fin 52 × Fin 52)
    (ht : t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2) :
    (univ.filter fun π : Equiv.Perm (Fin 52) => (π 0, π 1, π 2) = t).card = F3 := by
  obtain ⟨t0, t1, t2⟩ := t
  dsimp only at ht
  obtain ⟨ρ, h0, h1, h2⟩ := SumRanksDP.exists_perm_three (0 : Fin 52) 1 2 t0 t1 t2
    (by decide) (by decide) (by decide) ht.1 ht.2.1 ht.2.2
  unfold F3
  apply card_nbij' (fun π => ρ⁻¹ * π) (fun π => ρ * π)
  · intro π hπ
    simp only [coe_filter, Set.mem_setOf_eq, mem_filter, mem_univ, true_and, Prod.mk.injEq,
      Equiv.Perm.mul_apply, mem_coe] at hπ ⊢
    obtain ⟨a, b, c⟩ := hπ
    rw [a, b, c, Equiv.Perm.inv_eq_iff_eq, Equiv.Perm.inv_eq_iff_eq, Equiv.Perm.inv_eq_iff_eq]
    exact ⟨h0.symm, h1.symm, h2.symm⟩
  · intro π hπ
    simp only [coe_filter, Set.mem_setOf_eq, mem_filter, mem_univ, true_and, Prod.mk.injEq,
      Equiv.Perm.mul_apply, mem_coe] at hπ ⊢
    obtain ⟨a, b, c⟩ := hπ
    rw [a, b, c]
    exact ⟨h0, h1, h2⟩
  · intro π _; simp only [mul_inv_cancel_left]
  · intro π _; simp only [inv_mul_cancel_left]

/-- Decks with first cards `(0, 1)`. -/
@[irreducible] def F2 : ℕ := (univ.filter fun π : Equiv.Perm (Fin 52) => π 0 = 0 ∧ π 1 = 1).card

theorem card_first2_eq (b : Fin 52) (hb : b ≠ 0) :
    (univ.filter fun π : Equiv.Perm (Fin 52) => π 0 = 0 ∧ π 1 = b).card = F2 := by
  unfold F2
  have hs0 : Equiv.swap (1 : Fin 52) b 0 = 0 :=
    Equiv.swap_apply_of_ne_of_ne (by decide) (Ne.symm hb)
  apply card_nbij' (fun π => Equiv.swap 1 b * π) (fun π => Equiv.swap 1 b * π)
  · intro π hπ
    simp only [coe_filter, Set.mem_setOf_eq, mem_filter, mem_univ, true_and,
      Equiv.Perm.mul_apply, mem_coe] at hπ ⊢
    rw [hπ.1, hπ.2, hs0, Equiv.swap_apply_right]; exact ⟨rfl, rfl⟩
  · intro π hπ
    simp only [coe_filter, Set.mem_setOf_eq, mem_filter, mem_univ, true_and,
      Equiv.Perm.mul_apply, mem_coe] at hπ ⊢
    rw [hπ.1, hπ.2, hs0, Equiv.swap_apply_left]; exact ⟨rfl, rfl⟩
  · intro π _; simp [← mul_assoc]
  · intro π _; simp [← mul_assoc]

theorem card_pos2 : (univ.filter fun b : Fin 52 => b ≠ 0).card = 51 := by decide

theorem card_pos3 : (univ.filter fun c : Fin 52 => c ≠ 0 ∧ c ≠ 1).card = 50 := by decide

/-- `51 · F2` decks start with card 0. -/
theorem F1_eq : (univ.filter fun π : Equiv.Perm (Fin 52) => π 0 = 0).card = 51 * F2 := by
  have hsum := card_eq_sum_card_fiberwise
    (s := univ.filter fun π : Equiv.Perm (Fin 52) => π 0 = 0)
    (t := univ.filter fun b : Fin 52 => b ≠ 0)
    (f := fun π : Equiv.Perm (Fin 52) => π (1 : Fin 52))
    (fun π hπ => by
      simp only [mem_filter, mem_univ, true_and] at hπ ⊢
      intro e; rw [← hπ] at e; exact absurd (π.injective e) (by decide))
  rw [hsum]
  have hc : ∀ b ∈ (univ.filter fun b : Fin 52 => b ≠ 0),
      ((univ.filter fun π : Equiv.Perm (Fin 52) => π 0 = 0).filter
        fun π => π 1 = b).card = F2 := by
    intro b hb
    simp only [mem_filter, mem_univ, true_and] at hb
    rw [filter_filter]
    exact card_first2_eq b hb
  rw [sum_const_nat hc, card_pos2]

theorem card_first3_eq (c : Fin 52) (hc : c ≠ 0 ∧ c ≠ 1) :
    (univ.filter fun π : Equiv.Perm (Fin 52) => (π 0 = 0 ∧ π 1 = 1) ∧ π 2 = c).card = F3 := by
  refine Eq.trans ?_ (fibre3_card ((0 : Fin 52), (1 : Fin 52), c)
    ⟨(by decide : (0 : Fin 52) ≠ 1), Ne.symm hc.1, Ne.symm hc.2⟩)
  exact congrArg Finset.card (filter_congr (fun π _ => by simp only [Prod.mk.injEq, and_assoc]))

/-- `50 · F3 = F2`. -/
theorem F2_eq : F2 = 50 * F3 := by
  have hsum := card_eq_sum_card_fiberwise
    (s := univ.filter fun π : Equiv.Perm (Fin 52) => π 0 = 0 ∧ π 1 = 1)
    (t := univ.filter fun c : Fin 52 => c ≠ 0 ∧ c ≠ 1)
    (f := fun π : Equiv.Perm (Fin 52) => π (2 : Fin 52))
    (fun π hπ => by
      simp only [mem_filter, mem_univ, true_and] at hπ ⊢
      constructor
      · intro e; rw [← hπ.1] at e; exact absurd (π.injective e) (by decide)
      · intro e; rw [← hπ.2] at e; exact absurd (π.injective e) (by decide))
  unfold F2
  rw [hsum]
  have hc : ∀ c ∈ (univ.filter fun c : Fin 52 => c ≠ 0 ∧ c ≠ 1),
      ((univ.filter fun π : Equiv.Perm (Fin 52) => π 0 = 0 ∧ π 1 = 1).filter
        fun π => π 2 = c).card = F3 := by
    intro c hc
    simp only [mem_filter, mem_univ, true_and] at hc
    rw [filter_filter]
    exact card_first3_eq c hc
  rw [sum_const_nat hc, card_pos3]

/-- `52 · 51 · 50 · F3 = 52!`. -/
theorem F3_eq : 132600 * F3 = Nat.factorial 52 := by
  have h1 := card_first 0
  rw [F1_eq, F2_eq] at h1
  have e : (132600 : ℕ) = 52 * 51 * 50 := by norm_num
  rw [e, Nat.mul_assoc, Nat.mul_assoc]
  exact h1

/-- Decks whose first three cards lie in a set `T` of distinct triples: `#T · F3`. -/
theorem card_first3_mem (T : Finset (Fin 52 × Fin 52 × Fin 52))
    (hT : ∀ t ∈ T, t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2) :
    (univ.filter fun π : Equiv.Perm (Fin 52) => (π 0, π 1, π 2) ∈ T).card = T.card * F3 := by
  have hsum := card_eq_sum_card_fiberwise
    (s := univ.filter fun π : Equiv.Perm (Fin 52) => (π 0, π 1, π 2) ∈ T) (t := T)
    (f := fun π : Equiv.Perm (Fin 52) => (π (0 : Fin 52), π (1 : Fin 52), π (2 : Fin 52)))
    (fun π hπ => by simpa using hπ)
  rw [hsum]
  have hc : ∀ t ∈ T, ((univ.filter fun π : Equiv.Perm (Fin 52) => (π 0, π 1, π 2) ∈ T).filter
      fun π => (π 0, π 1, π 2) = t).card = F3 := by
    intro t ht
    rw [filter_filter]
    refine Eq.trans ?_ (fibre3_card t (hT t ht))
    exact congrArg Finset.card (filter_congr (fun π _ =>
      ⟨fun h => h.2, fun h => ⟨h ▸ ht, h⟩⟩))
  rw [sum_congr rfl hc, sum_const, smul_eq_mul]

/-- (PROVED, given the two finite checks) `v10Sym 0 3` (♣↔♠, ♥↔♦, same rank)
    survives GridCycle on at most `52!/4420` of the `52!` decks (30 surviving
    first-card triples out of `52 · 51 · 50`). The checks are discharged by kernel
    `decide!` in the heavy library (`gc_survival_v10Sym03_le`). -/
theorem gc_survival_v10Sym03_le_of_check (hKC : Check3 KC LKC) (hKS : Check3 KS LKS) :
    4420 * (gcSurvivors (v10Sym 0 3)).card ≤ Nat.factorial 52 := by
  have hsub : gcSurvivors (v10Sym 0 3) ⊆
      univ.filter fun π : Equiv.Perm (Fin 52) => (π 0, π 1, π 2) ∈ T03 := by
    intro π hπ
    simp only [gcSurvivors, mem_filter, mem_univ, true_and] at hπ ⊢
    exact gcSurvives_v03_T03 hKC hKS π hπ
  have h := card_le_card hsub
  rw [card_first3_mem T03 T03_distinct] at h
  have h30 : (gcSurvivors (v10Sym 0 3)).card ≤ 30 * F3 :=
    h.trans (Nat.mul_le_mul_right _ card_T03_le)
  have h4420 : (4420 : ℕ) * 30 = 132600 := by norm_num
  calc 4420 * (gcSurvivors (v10Sym 0 3)).card ≤ 4420 * (30 * F3) := Nat.mul_le_mul_left _ h30
    _ = 4420 * 30 * F3 := (Nat.mul_assoc _ _ _).symm
    _ = 132600 * F3 := by rw [h4420]
    _ = Nat.factorial 52 := F3_eq

/-- (PROVED, given the two finite checks) Every nontrivial SumRanks symmetry
    `v10Sym a x` survives GridCycle on at most `52!/4420` decks (on none at all
    unless `(a, x) = (0, 3)`). -/
theorem gc_survival_v10Sym_le_of_check (hKC : Check3 KC LKC) (hKS : Check3 KS LKS)
    (a : Fin 13) (x : Fin 4) (hne : ¬ (a = 0 ∧ x = 0)) :
    4420 * (gcSurvivors (v10Sym a x)).card ≤ Nat.factorial 52 := by
  by_cases h03 : a = 0 ∧ x = 3
  · obtain ⟨rfl, rfl⟩ := h03
    exact gc_survival_v10Sym03_le_of_check hKC hKS
  · rw [gcSurvivors_v10Sym_eq_empty a x hne h03, card_empty, Nat.mul_zero]
    exact Nat.zero_le _

end DoubleDeal.Security.GCSurvival
