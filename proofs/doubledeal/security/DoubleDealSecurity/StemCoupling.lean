import DoubleDealSecurity.StemPosition
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-
  A coupling bound for decks with a prescribed conjugate and prescribed row amounts (second
  slice towards the off-diagonal stem column bound; security README, "Roadmap",
  the M7 row). One counting lemma.

  NO BOUND ON `dpFCount` (OR ANY OTHER DIFFERENTIAL COUNT) IS PROVED HERE, and nothing here
  proves any part of the off-diagonal stem bound (`StemUnion.dpFCount_le_of_ne`).

  Proved:
  * `rowAmts_eq_iff`: `StemPosition.rowAmts m = t` (as functions on `Fin 4`) iff four row
    conditions hold, each reading one row: row `ρ` of `m` (laid column-major), turned left by
    `readAmt t ρ` (`0` for row 0, `t ρ` for rows 1, 2, 3), has v10 row total `t (nextRow ρ)`
    (`nextRow ρ = ρ + 1 mod 4`). The amounts are the ones v10 SumRanks uses (the previously
    turned row in the chain 1, 2, 3, 0 sets the next amount).
  * `card_hit_le_three`: for nonzero `D0, D1, D2 : ZMod 13` and any `b, τ`, at most 3 of the
    8 sums `b + ε0 D0 + ε1 D1 + ε2 D2` (`ε ∈ {0,1}^3`) equal `τ`.
  * `double_count`: if, for a finite index type `G`, each `act g` maps `E` into itself and is
    an involution on `E`, and for each `x ∈ E` at most `K` of the `g` send `x` into `P`, then
    `|G| · #(E ∩ P) ≤ K · #E`.
  * `card_cond_act_le`: for any `q π` such that `q` moves at most one position of row `ρ`,
    at most 3 of the 8 decks `act q ρ g (π)` (`g ∈ Bool³`: apply a chosen subset of three
    disjoint swaps of cards with different ranks, the pairs chosen by `choosePairs` from
    `content q π ρ`, the cards of `π` at the `q`-fixed positions of row `ρ`) satisfy row
    `ρ`'s condition `cond t ρ`.
  * `coupling`: for every `q δ : Perm (Fin 52)` such that `q` moves at most one position of
    each row (`(movedInRow q ρ).card ≤ 1`, where `movedInRow q ρ` is the set of columns `i`
    with `q (cmFlat ρ i) ≠ cmFlat ρ i`), and every `t : Fin 4 → ℕ`,
      `4096 · #{π | π⁻¹ δ π = q ∧ rowAmts (permDeck π) = t} ≤ 81 · #{π | π⁻¹ δ π = q}`,
    i.e. the fraction is at most `(3/8)^4 = 81/4096 ≈ 0.0198`.

  Proof idea. The cards at `q`-fixed positions of row `ρ` are fixed by `δ`, so swapping two of
  them (left multiplication of `π` by a transposition of values) keeps `π⁻¹ δ π = q` and does
  not change any other row. Swapping two cards of ranks `r_a ≠ r_b` at columns `j_a ≠ j_b`
  of row `ρ` changes the row total by `(w_a − w_b)(r_b − r_a) ≠ 0` mod 13 (weights
  `w_j = 13 − j`, turned by the row's read amount). Three disjoint such pairs exist in any
  12 cards (each rank has at most 4 cards), and they are chosen from the row's set of free
  cards, which the swaps preserve, so the choice is the same along each orbit. The 8 orbit
  points of each row then contain at most 3 decks meeting that row's condition; the four
  rows act independently.

  Not proved here (the rest of the 4-card case of the off-diagonal stem bound, proved in `StemSupportFour`, third
  slice: `ratio_eq_qPerm_of_support_four`, `ratio_moves_le_one_of_support_four`,
  `card_conjSet_le_odd`, `card_conjSet_le_two`, `dpFCount_le_of_support_four`):
  * that the ratio `q = stemPerm x * (stemPerm (β·x))⁻¹` of `StemPosition.conj_of_stem_rel`
    moves at most one position per row when `γ⁻¹β` moves 4 cards (support 4, i.e.
    `(zRows, zCols) = (4, 12)`); the moved positions are `cmFlat ρ ((c + t ρ) % 13)`, one per
    row, for a column `c`;
  * that `q` is determined by `(rowAmts x, c, d)`, and upper bounds on `#{π | π⁻¹ δ π = q}`;
  * the assembly `64 · dpFCount β γ ≤ 52!` for support 4. The union bound for the other
    support sizes (at least 8) is `StemUnion`.

  Caveats. The constant 81/4096 comes from 3 swap pairs per row, not from the exact per-row
  maximum: an exhaustive enumeration over residue multisets (enumeration, not proof;
  `analysis/v12-fullcipher/NOTES.md` §5) gives the per-row maximum fraction
  13/165 ≈ 0.0788, so one row alone (at least 1/13 for the worst target) could not give the
  ≈ 0.0342 per cell that `StemSupportFour`'s assembly needs (both cycle types), but two
  rows could. About the stem's SumRanks row amounts only.
-/

namespace DoubleDeal.Security.StemCoupling

open DoubleDeal Relabel Finset StemPosition

/-! ## Row amounts as four row conditions -/

/-- (PROVED) The v10 row total as a sum: `Σ_j (13 - j) · rank (y j)`. -/
theorem rowTotal_eq_sum (y : Fin 13 → Nat) :
    rowTotal y = ∑ j : Fin 13, (13 - j.val) * rank (y j) := by
  simp [rowTotal, rowPref, toList13, Fin.sum_univ_succ]
  ring_nf
  rfl

/-- Row `ρ` of the packet `m` (laid column-major) turned left by `a`: column `j` reads
    column `(j + a) % 13`. -/
def rowRead (m : Fin 52 → Nat) (ρ : Fin 4) (a : Nat) : Fin 13 → Nat :=
  fun j => m (cmFlat ρ ⟨(j.val + a % 13) % 13, Nat.mod_lt _ (by decide)⟩)

/-- The turn row `ρ` has made when v10 SumRanks reads its total: row 0 is read before it
    turns (for row 1's amount); rows 1, 2, 3 are read after turning by their own amount. -/
def readAmt (t : Fin 4 → Nat) (ρ : Fin 4) : Nat := if ρ.val = 0 then 0 else t ρ

/-- The row after `ρ` (the one whose amount row `ρ`'s total sets). -/
def nextRow (ρ : Fin 4) : Fin 4 := ⟨(ρ.val + 1) % 4, Nat.mod_lt _ (by decide)⟩

/-- (PROVED) Each row amount is the turn total of the previous row, read after that row's own
    turn (row 0 unturned). -/
theorem rowAmts_prev (m : Fin 52 → Nat) (r : Fin 4) :
    rowAmts m r = rowTurnV10 (rowRead m (prevRow r)
      (if (prevRow r).val = 0 then 0 else rowAmts m (prevRow r))) := by
  have key : ∀ r : Fin 4, rowAmts m r = rowTurnV10 (rowsDone rowTurnV10 (layColumnMajor m)
      (rowStepOf r - 1) (prevRow r)) := fun _ => rfl
  rw [key r, rowsDone_eq_partial _ _ _ (by unfold rowStepOf; split <;> omega)]
  congr 1
  funext j
  rw [rowRotate_apply]
  fin_cases r <;> simp (config := {decide := true}) [rowRead, rowStepOf, prevRow, layColumnMajor,
    rowAmts]

/-- (PROVED) `rowAmts m = t` iff four conditions, one per row: the turn total of row `ρ`,
    read after its turn `readAmt t ρ`, is `t (nextRow ρ)`. Each condition reads one row. -/
theorem rowAmts_eq_iff (m : Fin 52 → Nat) (t : Fin 4 → Nat) :
    (∀ r, rowAmts m r = t r) ↔
      ∀ ρ, rowTurnV10 (rowRead m ρ (readAmt t ρ)) = t (nextRow ρ) := by
  have hp := rowAmts_prev m
  constructor
  · intro h ρ
    have e := hp (nextRow ρ)
    rw [h, h] at e
    have hpn : prevRow (nextRow ρ) = ρ := by
      apply Fin.ext; simp only [prevRow, nextRow]; omega
    rw [hpn] at e
    rw [e]
    rfl
  · intro h
    have p0 : prevRow 0 = 3 := by decide
    have p1 : prevRow 1 = 0 := by decide
    have p2 : prevRow 2 = 1 := by decide
    have p3 : prevRow 3 = 2 := by decide
    have n0 : nextRow 0 = 1 := by decide
    have n1 : nextRow 1 = 2 := by decide
    have n2 : nextRow 2 = 3 := by decide
    have n3 : nextRow 3 = 0 := by decide
    have r0 : readAmt t 0 = 0 := if_pos rfl
    have r1 : readAmt t 1 = t 1 := if_neg (by decide)
    have r2 : readAmt t 2 = t 2 := if_neg (by decide)
    have r3 : readAmt t 3 = t 3 := if_neg (by decide)
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    have h3 := h 3
    rw [r0, n0] at h0
    rw [r1, n1] at h1
    rw [r2, n2] at h2
    rw [r3, n3] at h3
    have e1 : rowAmts m 1 = t 1 := by rw [hp 1, p1, if_pos (by decide)]; exact h0
    have e2 : rowAmts m 2 = t 2 := by rw [hp 2, p2, if_neg (by decide), e1]; exact h1
    have e3 : rowAmts m 3 = t 3 := by rw [hp 3, p3, if_neg (by decide), e2]; exact h2
    have e0 : rowAmts m 0 = t 0 := by rw [hp 0, p0, if_neg (by decide), e3]; exact h3
    intro r; fin_cases r
    exacts [e0, e1, e2, e3]

/-! ## The row total mod 13, and one swap of two cards in a row -/

/-- The rank of a card, mod 13. -/
def rk (v : Fin 52) : ZMod 13 := (rank v.val : ZMod 13)

/-- The weight `13 - j` of read index `j`, mod 13. -/
def wt (j : Fin 13) : ZMod 13 := ((13 - j.val : ℕ) : ZMod 13)

/-- The row total mod 13 of a row of cards. -/
def wsum (y : Fin 13 → Fin 52) : ZMod 13 := ∑ j, wt j * rk (y j)

/-- (PROVED) The turn total, cast to `ZMod 13`, is `wsum`. -/
theorem rowTurnV10_cast (y : Fin 13 → Fin 52) :
    ((rowTurnV10 (fun j => (y j).val) : ℕ) : ZMod 13) = wsum y := by
  simp only [rowTurnV10, ZMod.natCast_mod, rowTotal_eq_sum, wsum, wt, rk, Nat.cast_sum,
    Nat.cast_mul]

/-- (PROVED) Swapping the cards at two read indices `j1 ≠ j2` of an injective row changes the
    total by `(wt j1 - wt j2) * (rk (y j2) - rk (y j1))`. -/
theorem wsum_swap (y : Fin 13 → Fin 52) (hy : Function.Injective y) {j1 j2 : Fin 13}
    (hj : j1 ≠ j2) :
    wsum (fun j => Equiv.swap (y j1) (y j2) (y j)) =
      wsum y + (wt j1 - wt j2) * (rk (y j2) - rk (y j1)) := by
  have hpt : ∀ j, wt j * rk (Equiv.swap (y j1) (y j2) (y j)) = wt j * rk (y j) +
      ((if j = j1 then wt j1 * (rk (y j2) - rk (y j1)) else 0) +
        (if j = j2 then wt j2 * (rk (y j1) - rk (y j2)) else 0)) := by
    intro j
    by_cases h1 : j = j1
    · subst h1; rw [Equiv.swap_apply_left, if_pos rfl, if_neg hj]; ring
    · by_cases h2 : j = j2
      · subst h2; rw [Equiv.swap_apply_right, if_neg h1, if_pos rfl]; ring
      · rw [Equiv.swap_apply_of_ne_of_ne (fun e => h1 (hy e)) (fun e => h2 (hy e)), if_neg h1,
          if_neg h2]
        ring
  unfold wsum
  rw [Finset.sum_congr rfl (fun j _ => hpt j), Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  ring

theorem wt_sub_ne {j1 j2 : Fin 13} (h : j1 ≠ j2) : wt j1 - wt j2 ≠ 0 := by
  intro e
  have e' := sub_eq_zero.mp e
  unfold wt at e'
  rw [ZMod.natCast_eq_natCast_iff'] at e'
  apply h
  apply Fin.ext
  have := j1.isLt
  have := j2.isLt
  omega

theorem rk_sub_ne {u v : Fin 52} (h : rank u.val ≠ rank v.val) : rk v - rk u ≠ 0 := by
  intro e
  have e' := sub_eq_zero.mp e
  unfold rk at e'
  rw [ZMod.natCast_eq_natCast_iff'] at e'
  apply h
  unfold rank at e' ⊢
  omega

theorem zmod13_mul_ne : ∀ a b : ZMod 13, a ≠ 0 → b ≠ 0 → a * b ≠ 0 := by decide

theorem zmod13_two : ∀ a : ZMod 13, a + a = 0 → a = 0 := by decide

/-! ## Three independent swaps hit a target at most 3 times out of 8 -/

theorem ite_pair (p q : Prop) [Decidable p] [Decidable q] (h : ¬ (p ∧ q)) :
    (if p then 1 else 0) + (if q then 1 else 0) ≤ 1 := by
  split_ifs with hp hq <;> simp_all

theorem ite_four (p q r s : Prop) [Decidable p] [Decidable q] [Decidable r] [Decidable s]
    (h : ¬ (p ∧ q ∧ r ∧ s)) :
    (if p then 1 else 0) + (if q then 1 else 0) + (if r then 1 else 0) + (if s then 1 else 0)
      ≤ 3 := by
  split_ifs <;> simp_all

/-- (PROVED) For nonzero `D0, D1, D2` mod 13, at most 3 of the 8 sums
    `b + ε0 D0 + ε1 D1 + ε2 D2` (`ε ∈ {0,1}³`) equal a given `τ`. Sharp, e.g. `D0 = D1 = D2`,
    `τ = b + D0` (not formalised). -/
theorem card_hit_le_three (b τ D0 D1 D2 : ZMod 13) (h0 : D0 ≠ 0) (h1 : D1 ≠ 0) (h2 : D2 ≠ 0) :
    (univ.filter fun g : Bool × Bool × Bool =>
      b + (if g.1 then D0 else 0) + (if g.2.1 then D1 else 0) + (if g.2.2 then D2 else 0) = τ).card
        ≤ 3 := by
  rw [card_filter]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, ↓reduceIte, Bool.false_eq_true, add_zero]
  have a1 := ite_pair (b + D0 + D1 + D2 = τ) (b + D1 + D2 = τ)
    (fun ⟨x, y⟩ => h0 (by linear_combination x - y))
  have a2 := ite_pair (b + D0 + D1 = τ) (b + D1 = τ) (fun ⟨x, y⟩ => h0 (by linear_combination x - y))
  have a3 := ite_pair (b + D0 + D2 = τ) (b + D2 = τ) (fun ⟨x, y⟩ => h0 (by linear_combination x - y))
  have a4 := ite_pair (b + D0 = τ) (b = τ) (fun ⟨x, y⟩ => h0 (by linear_combination x - y))
  have b1 := ite_pair (b + D0 + D1 + D2 = τ) (b + D0 + D2 = τ)
    (fun ⟨x, y⟩ => h1 (by linear_combination x - y))
  have b2 := ite_pair (b + D0 + D1 = τ) (b + D0 = τ) (fun ⟨x, y⟩ => h1 (by linear_combination x - y))
  have b3 := ite_pair (b + D1 + D2 = τ) (b + D2 = τ) (fun ⟨x, y⟩ => h1 (by linear_combination x - y))
  have b4 := ite_pair (b + D1 = τ) (b = τ) (fun ⟨x, y⟩ => h1 (by linear_combination x - y))
  have c1 := ite_pair (b + D0 + D1 + D2 = τ) (b + D0 + D1 = τ)
    (fun ⟨x, y⟩ => h2 (by linear_combination x - y))
  have c2 := ite_pair (b + D0 + D2 = τ) (b + D0 = τ) (fun ⟨x, y⟩ => h2 (by linear_combination x - y))
  have c3 := ite_pair (b + D1 + D2 = τ) (b + D1 = τ) (fun ⟨x, y⟩ => h2 (by linear_combination x - y))
  have c4 := ite_pair (b + D2 = τ) (b = τ) (fun ⟨x, y⟩ => h2 (by linear_combination x - y))
  have ev := ite_four (b = τ) (b + D0 + D1 = τ) (b + D0 + D2 = τ) (b + D1 + D2 = τ)
    (fun ⟨x0, x1, x2, x3⟩ => h2 (zmod13_two _ (by linear_combination x2 + x3 - x1 - x0)))
  have od := ite_four (b + D0 = τ) (b + D1 = τ) (b + D2 = τ) (b + D0 + D1 + D2 = τ)
    (fun ⟨x0, x1, x2, x3⟩ => h0 (zmod13_two _ (by linear_combination x3 - x1 + x0 - x2)))
  generalize (if b + D0 + D1 + D2 = τ then 1 else 0) = n7 at *
  generalize (if b + D0 + D1 = τ then 1 else 0) = n6 at *
  generalize (if b + D0 + D2 = τ then 1 else 0) = n5 at *
  generalize (if b + D0 = τ then 1 else 0) = n4 at *
  generalize (if b + D1 + D2 = τ then 1 else 0) = n3 at *
  generalize (if b + D1 = τ then 1 else 0) = n2 at *
  generalize (if b + D2 = τ then 1 else 0) = n1 at *
  generalize (if b = τ then 1 else 0) = n0 at *
  omega

/-! ## Double counting through an involution action -/

/-- (PROVED) If every `act g` maps `E` into itself and is an involution on `E`, and each `x ∈ E`
    has at most `K` elements `g` with `P (act g x)`, then `|G| · #(E ∩ P) ≤ K · #E`. -/
theorem double_count {X G : Type} [Fintype G] [DecidableEq X] (E : Finset X) (P : X → Prop)
    [DecidablePred P] (act : G → X → X) (hE : ∀ g, ∀ x ∈ E, act g x ∈ E)
    (hinv : ∀ g, ∀ x ∈ E, act g (act g x) = x) (K : ℕ)
    (hK : ∀ x ∈ E, (univ.filter fun g => P (act g x)).card ≤ K) :
    Fintype.card G * (E.filter P).card ≤ K * E.card := by
  have h1 : ∀ g, (E.filter fun x => P (act g x)).card = (E.filter P).card := by
    intro g
    refine Finset.card_nbij' (act g) (act g) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter] at hx ⊢
      exact ⟨hE g x hx.1, hx.2⟩
    · intro x hx
      simp only [Finset.mem_filter] at hx ⊢
      exact ⟨hE g x hx.1, by rw [hinv g x hx.1]; exact hx.2⟩
    · intro x hx
      simp only [Finset.mem_filter] at hx
      exact hinv g x hx.1
    · intro x hx
      simp only [Finset.mem_filter] at hx
      exact hinv g x hx.1
  calc Fintype.card G * (E.filter P).card
      = ∑ g : G, (E.filter fun x => P (act g x)).card := by
        rw [Finset.sum_congr rfl (fun g _ => h1 g), Finset.sum_const, Finset.card_univ,
          smul_eq_mul]
    _ = ∑ x ∈ E, (univ.filter fun g => P (act g x)).card := by
        simp only [Finset.card_filter]
        exact Finset.sum_comm
    _ ≤ ∑ _x ∈ E, K := Finset.sum_le_sum hK
    _ = K * E.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]

/-! ## Three swaps of disjoint card pairs -/

/-- Six cards, read as three pairs `(u0, v0)`, `(u1, v1)`, `(u2, v2)`. -/
structure Pairs where
  u0 : Fin 52
  v0 : Fin 52
  u1 : Fin 52
  v1 : Fin 52
  u2 : Fin 52
  v2 : Fin 52

/-- Swap `u v` or do nothing. -/
def swapIf (b : Bool) (u v : Fin 52) : Equiv.Perm (Fin 52) := if b then Equiv.swap u v else 1

/-- The swaps of the pairs selected by `g`. -/
def swapsOf (p : Pairs) (g : Bool × Bool × Bool) : Equiv.Perm (Fin 52) :=
  swapIf g.1 p.u0 p.v0 * (swapIf g.2.1 p.u1 p.v1 * swapIf g.2.2 p.u2 p.v2)

theorem swapIf_of_ne (b : Bool) {u v x : Fin 52} (hu : x ≠ u) (hv : x ≠ v) :
    swapIf b u v x = x := by
  cases b
  · rfl
  · exact Equiv.swap_apply_of_ne_of_ne hu hv

theorem swapIf_mem (b : Bool) {u v x : Fin 52} (h : x = u ∨ x = v) :
    swapIf b u v x = u ∨ swapIf b u v x = v := by
  cases b
  · exact h
  · rcases h with rfl | rfl
    · right; exact Equiv.swap_apply_left _ _
    · left; exact Equiv.swap_apply_right _ _

theorem swapIf_swapIf (b : Bool) (u v x : Fin 52) : swapIf b u v (swapIf b u v x) = x := by
  cases b
  · rfl
  · exact Equiv.swap_apply_self _ _ _

/-- Six pairwise distinct cards. -/
def Pairs.Distinct (p : Pairs) : Prop :=
  [p.u0, p.v0, p.u1, p.v1, p.u2, p.v2].Nodup

theorem nodup6 {α : Type} {a b c d e f : α} (h : [a, b, c, d, e, f].Nodup) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧ a ≠ f ∧ b ≠ c ∧ b ≠ d ∧ b ≠ e ∧ b ≠ f ∧
    c ≠ d ∧ c ≠ e ∧ c ≠ f ∧ d ≠ e ∧ d ≠ f ∧ e ≠ f := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true] at h
  tauto

theorem nodup6_of {α : Type} {a b c d e f : α} (h : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧ a ≠ f ∧
    b ≠ c ∧ b ≠ d ∧ b ≠ e ∧ b ≠ f ∧ c ≠ d ∧ c ≠ e ∧ c ≠ f ∧ d ≠ e ∧ d ≠ f ∧ e ≠ f) :
    [a, b, c, d, e, f].Nodup := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  exact ⟨⟨h1, h2, h3, h4, h5⟩, ⟨h6, h7, h8, h9⟩, ⟨h10, h11, h12⟩, ⟨h13, h14⟩, h15⟩

theorem Pairs.Distinct.ne {p : Pairs} (h : p.Distinct) :
    p.u0 ≠ p.v0 ∧ p.u0 ≠ p.u1 ∧ p.u0 ≠ p.v1 ∧ p.u0 ≠ p.u2 ∧ p.u0 ≠ p.v2 ∧
    p.v0 ≠ p.u1 ∧ p.v0 ≠ p.v1 ∧ p.v0 ≠ p.u2 ∧ p.v0 ≠ p.v2 ∧
    p.u1 ≠ p.v1 ∧ p.u1 ≠ p.u2 ∧ p.u1 ≠ p.v2 ∧ p.v1 ≠ p.u2 ∧ p.v1 ≠ p.v2 ∧ p.u2 ≠ p.v2 :=
  nodup6 h

/-- (PROVED) The swaps fix every card outside the six. -/
theorem swapsOf_of_not_mem (p : Pairs) (g : Bool × Bool × Bool) {x : Fin 52}
    (h : x ≠ p.u0 ∧ x ≠ p.v0 ∧ x ≠ p.u1 ∧ x ≠ p.v1 ∧ x ≠ p.u2 ∧ x ≠ p.v2) :
    swapsOf p g x = x := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := h
  simp only [swapsOf, Equiv.Perm.mul_apply]
  rw [swapIf_of_ne _ h4 h5, swapIf_of_ne _ h2 h3, swapIf_of_ne _ h0 h1]

/-- (PROVED) For six distinct cards the swaps are an involution. -/
theorem swapsOf_swapsOf (p : Pairs) (hp : p.Distinct) (g : Bool × Bool × Bool) (x : Fin 52) :
    swapsOf p g (swapsOf p g x) = x := by
  obtain ⟨d01, d02, d03, d04, d05, d12, d13, d14, d15, d23, d24, d25, d34, d35, d45⟩ := hp.ne
  simp only [swapsOf, Equiv.Perm.mul_apply]
  set A := swapIf g.1 p.u0 p.v0
  set B := swapIf g.2.1 p.u1 p.v1
  set C := swapIf g.2.2 p.u2 p.v2
  by_cases h2 : x = p.u2 ∨ x = p.v2
  · have hx : x ≠ p.u0 ∧ x ≠ p.v0 ∧ x ≠ p.u1 ∧ x ≠ p.v1 := by
      rcases h2 with rfl | rfl <;> exact ⟨by tauto, by tauto, by tauto, by tauto⟩
    have hy : C x ≠ p.u0 ∧ C x ≠ p.v0 ∧ C x ≠ p.u1 ∧ C x ≠ p.v1 := by
      rcases swapIf_mem g.2.2 h2 with e | e <;> rw [e] <;>
        exact ⟨by tauto, by tauto, by tauto, by tauto⟩
    have eB : B (C x) = C x := swapIf_of_ne _ hy.2.2.1 hy.2.2.2
    have eA : A (C x) = C x := swapIf_of_ne _ hy.1 hy.2.1
    rw [eB, eA, swapIf_swapIf, swapIf_of_ne _ hx.2.2.1 hx.2.2.2, swapIf_of_ne _ hx.1 hx.2.1]
  · have eC : C x = x := swapIf_of_ne _ (fun e => h2 (Or.inl e)) (fun e => h2 (Or.inr e))
    by_cases h1 : x = p.u1 ∨ x = p.v1
    · have hx : x ≠ p.u0 ∧ x ≠ p.v0 := by
        rcases h1 with rfl | rfl <;> exact ⟨by tauto, by tauto⟩
      have hy : B x ≠ p.u0 ∧ B x ≠ p.v0 ∧ B x ≠ p.u2 ∧ B x ≠ p.v2 := by
        rcases swapIf_mem g.2.1 h1 with e | e <;> rw [e] <;>
          exact ⟨by tauto, by tauto, by tauto, by tauto⟩
      have eA : A (B x) = B x := swapIf_of_ne _ hy.1 hy.2.1
      have eC' : C (B x) = B x := swapIf_of_ne _ hy.2.2.1 hy.2.2.2
      rw [eC, eA, eC', swapIf_swapIf, swapIf_of_ne _ hx.1 hx.2]
    · have eB : B x = x := swapIf_of_ne _ (fun e => h1 (Or.inl e)) (fun e => h1 (Or.inr e))
      by_cases h0 : x = p.u0 ∨ x = p.v0
      · have hy : A x ≠ p.u1 ∧ A x ≠ p.v1 ∧ A x ≠ p.u2 ∧ A x ≠ p.v2 := by
          rcases swapIf_mem g.1 h0 with e | e <;> rw [e] <;>
            exact ⟨by tauto, by tauto, by tauto, by tauto⟩
        rw [eC, eB, swapIf_of_ne _ hy.2.2.1 hy.2.2.2, swapIf_of_ne _ hy.1 hy.2.1, swapIf_swapIf]
      · have eA : A x = x := swapIf_of_ne _ (fun e => h0 (Or.inl e)) (fun e => h0 (Or.inr e))
        rw [eC, eB, eA, eC, eB, eA]

/-! ## The row total under the three swaps -/

theorem wsum_step (y : Fin 13 → Fin 52) (hy : Function.Injective y) {a b : Fin 13} (hab : a ≠ b)
    (e : Bool) :
    wsum (fun j => swapIf e (y a) (y b) (y j)) =
      wsum y + (if e then (wt a - wt b) * (rk (y b) - rk (y a)) else 0) := by
  cases e
  · simp [swapIf]
  · simpa [swapIf] using wsum_swap y hy hab

/-- (PROVED) Swapping the pairs of read indices `(a_i, b_i)` selected by `g` adds
    `D_i = (wt a_i - wt b_i) · (rk (y b_i) - rk (y a_i))` for each selected pair. -/
theorem wsum_three (y : Fin 13 → Fin 52) (hy : Function.Injective y)
    {a0 b0 a1 b1 a2 b2 : Fin 13} (hd : [a0, b0, a1, b1, a2, b2].Nodup) (g : Bool × Bool × Bool) :
    wsum (fun j => swapsOf ⟨y a0, y b0, y a1, y b1, y a2, y b2⟩ g (y j)) =
      wsum y + (if g.1 then (wt a0 - wt b0) * (rk (y b0) - rk (y a0)) else 0) +
        (if g.2.1 then (wt a1 - wt b1) * (rk (y b1) - rk (y a1)) else 0) +
        (if g.2.2 then (wt a2 - wt b2) * (rk (y b2) - rk (y a2)) else 0) := by
  obtain ⟨d01, d02, d03, d04, d05, d12, d13, d14, d15, d23, d24, d25, d34, d35, d45⟩ := nodup6 hd
  simp only [swapsOf, Equiv.Perm.mul_apply]
  set y2 : Fin 13 → Fin 52 := fun j => swapIf g.2.2 (y a2) (y b2) (y j) with hy2def
  have h2 := wsum_step y hy d45 g.2.2
  have hy2 : Function.Injective y2 := (swapIf g.2.2 (y a2) (y b2)).injective.comp hy
  have f2 : ∀ {j}, j ≠ a2 → j ≠ b2 → y2 j = y j := fun ha hb =>
    swapIf_of_ne _ (hy.ne ha) (hy.ne hb)
  have h1 := wsum_step y2 hy2 d23 g.2.1
  rw [f2 d24 d25, f2 d34 d35] at h1
  set y1 : Fin 13 → Fin 52 := fun j => swapIf g.2.1 (y a1) (y b1) (y2 j) with hy1def
  have hy1 : Function.Injective y1 := (swapIf g.2.1 (y a1) (y b1)).injective.comp hy2
  have f1 : ∀ {j}, j ≠ a1 → j ≠ b1 → j ≠ a2 → j ≠ b2 → y1 j = y j := fun ha hb hc hd => by
    show swapIf g.2.1 (y a1) (y b1) (y2 _) = _
    rw [f2 hc hd]; exact swapIf_of_ne _ (hy.ne ha) (hy.ne hb)
  have h0 := wsum_step y1 hy1 d01 g.1
  rw [f1 d02 d03 d04 d05, f1 d12 d13 d14 d15] at h0
  show wsum (fun j => swapIf g.1 (y a0) (y b0) (y1 j)) = _
  rw [h0, h1, h2]
  ring

/-! ## A row's free cards, and three pairs of them with different ranks -/

/-- The columns `i` of row `ρ` whose position `cmFlat ρ i` the permutation `q` moves. -/
def movedInRow (q : Equiv.Perm (Fin 52)) (ρ : Fin 4) : Finset (Fin 13) :=
  univ.filter fun i : Fin 13 => q (cmFlat ρ i) ≠ cmFlat ρ i

/-- The free cards of row `ρ` under `π`: the cards at the positions of row `ρ` that `q` fixes. -/
def content (q π : Equiv.Perm (Fin 52)) (ρ : Fin 4) : Finset (Fin 52) :=
  (univ.filter fun i : Fin 13 => q (cmFlat ρ i) = cmFlat ρ i).image fun i => π (cmFlat ρ i)

theorem cmFlat_col_injective (ρ : Fin 4) : Function.Injective fun i : Fin 13 => cmFlat ρ i :=
  fun i j h => (Prod.mk.inj (cmFlat_inj2 (p := (ρ, i)) (q := (ρ, j)) h)).2

theorem mem_content {q π : Equiv.Perm (Fin 52)} {ρ : Fin 4} {u : Fin 52} :
    u ∈ content q π ρ ↔ ∃ i, q (cmFlat ρ i) = cmFlat ρ i ∧ π (cmFlat ρ i) = u := by
  simp [content]

theorem card_content (q π : Equiv.Perm (Fin 52)) (ρ : Fin 4)
    (hq : (movedInRow q ρ).card ≤ 1) :
    12 ≤ (content q π ρ).card := by
  rw [content, card_image_of_injective _
    (show Function.Injective (fun i => π (cmFlat ρ i)) from
      π.injective.comp (cmFlat_col_injective ρ))]
  have e := filter_card_add_filter_neg_card_eq_card (s := (univ : Finset (Fin 13)))
    (fun i => q (cmFlat ρ i) = cmFlat ρ i)
  simp only [card_univ, Fintype.card_fin] at e
  simp only [movedInRow, ne_eq] at hq
  omega

/-- (PROVED) Each rank has at most 4 cards. -/
theorem card_rank_fibre (u : Fin 52) :
    (univ.filter fun v : Fin 52 => rank v.val = rank u.val).card ≤ 4 := by
  calc (univ.filter fun v : Fin 52 => rank v.val = rank u.val).card
      ≤ ((univ : Finset (Fin 4)).image fun k : Fin 4 =>
          (⟨u.val % 13 + 13 * k.val, by have := k.isLt; omega⟩ : Fin 52)).card := by
        refine card_le_card fun v hv => ?_
        simp only [mem_filter, mem_univ, true_and, rank] at hv
        simp only [mem_image, mem_univ, true_and]
        exact ⟨⟨v.val / 13, by have := v.isLt; omega⟩, Fin.ext (by simp only; omega)⟩
    _ ≤ 4 := card_image_le.trans (by simp)

theorem exists_pair (S : Finset (Fin 52)) (h : 5 ≤ S.card) :
    ∃ u ∈ S, ∃ v ∈ S, rank u.val ≠ rank v.val := by
  obtain ⟨u, hu⟩ : S.Nonempty := card_pos.mp (by omega)
  have hF : (S.filter fun v => rank v.val = rank u.val).card ≤ 4 :=
    (card_le_card (filter_subset_filter _ (subset_univ S))).trans (card_rank_fibre u)
  have e := filter_card_add_filter_neg_card_eq_card (s := S) (fun v => rank v.val = rank u.val)
  obtain ⟨v, hv⟩ : (S.filter fun v => ¬ rank v.val = rank u.val).Nonempty :=
    card_pos.mp (by omega)
  rw [mem_filter] at hv
  exact ⟨u, hu, v, hv.1, fun e => hv.2 e.symm⟩

/-- Three pairs of distinct cards of `S`, each pair of two different ranks. -/
def Pairs.Good (S : Finset (Fin 52)) (p : Pairs) : Prop :=
  p.Distinct ∧ p.u0 ∈ S ∧ p.v0 ∈ S ∧ p.u1 ∈ S ∧ p.v1 ∈ S ∧ p.u2 ∈ S ∧ p.v2 ∈ S ∧
    rank p.u0.val ≠ rank p.v0.val ∧ rank p.u1.val ≠ rank p.v1.val ∧ rank p.u2.val ≠ rank p.v2.val

theorem exists_good (S : Finset (Fin 52)) (h : 12 ≤ S.card) : ∃ p : Pairs, p.Good S := by
  obtain ⟨u0, hu0, v0, hv0, r0⟩ := exists_pair S (by omega)
  have n0 : u0 ≠ v0 := fun e => r0 (e ▸ rfl)
  have hv0' : v0 ∈ S.erase u0 := mem_erase.mpr ⟨n0.symm, hv0⟩
  have c1 : 10 ≤ ((S.erase u0).erase v0).card := by
    rw [card_erase_of_mem hv0', card_erase_of_mem hu0]; omega
  obtain ⟨u1, hu1, v1, hv1, r1⟩ := exists_pair ((S.erase u0).erase v0) (by omega)
  have n1 : u1 ≠ v1 := fun e => r1 (e ▸ rfl)
  have hv1' : v1 ∈ ((S.erase u0).erase v0).erase u1 := mem_erase.mpr ⟨n1.symm, hv1⟩
  have c2 : 8 ≤ ((((S.erase u0).erase v0).erase u1).erase v1).card := by
    rw [card_erase_of_mem hv1', card_erase_of_mem hu1]; omega
  obtain ⟨u2, hu2, v2, hv2, r2⟩ := exists_pair ((((S.erase u0).erase v0).erase u1).erase v1)
    (by omega)
  have n2 : u2 ≠ v2 := fun e => r2 (e ▸ rfl)
  simp only [mem_erase] at hu1 hv1 hu2 hv2
  refine ⟨⟨u0, v0, u1, v1, u2, v2⟩, nodup6_of ?_, hu0, hv0, hu1.2.2, hv1.2.2, hu2.2.2.2.2,
    hv2.2.2.2.2, r0, r1, r2⟩
  refine ⟨n0, Ne.symm hu1.2.1, Ne.symm hv1.2.1, Ne.symm hu2.2.2.2.1, Ne.symm hv2.2.2.2.1,
    Ne.symm hu1.1, Ne.symm hv1.1, Ne.symm hu2.2.2.1, Ne.symm hv2.2.2.1, n1, Ne.symm hu2.2.1,
    Ne.symm hv2.2.1, Ne.symm hu2.1, Ne.symm hv2.1, n2⟩

/-- A fixed choice of good pairs of `S` (junk if there are none). -/
noncomputable def choosePairs (S : Finset (Fin 52)) : Pairs :=
  open Classical in
  if h : ∃ p : Pairs, p.Good S then Classical.choose h else ⟨0, 0, 0, 0, 0, 0⟩

theorem choosePairs_good (S : Finset (Fin 52)) (h : 12 ≤ S.card) : (choosePairs S).Good S := by
  have hex := exists_good S h
  unfold choosePairs
  rw [dif_pos hex]
  exact Classical.choose_spec hex

/-! ## The row action -/

/-- `act q ρ g π`: swap, in the deck `π`, the pairs selected by `g` among the free cards of
    row `ρ` (the pairs are `choosePairs` of those free cards). -/
noncomputable def act (q : Equiv.Perm (Fin 52)) (ρ : Fin 4) (g : Bool × Bool × Bool)
    (π : Equiv.Perm (Fin 52)) : Equiv.Perm (Fin 52) :=
  swapsOf (choosePairs (content q π ρ)) g * π

theorem swapIf_mem_set (b : Bool) {S : Finset (Fin 52)} {u v x : Fin 52} (hu : u ∈ S)
    (hv : v ∈ S) (hx : x ∈ S) : swapIf b u v x ∈ S := by
  cases b
  · exact hx
  · show Equiv.swap u v x ∈ S
    by_cases h1 : x = u
    · subst h1; rw [Equiv.swap_apply_left]; exact hv
    · by_cases h2 : x = v
      · subst h2; rw [Equiv.swap_apply_right]; exact hu
      · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]; exact hx

theorem swapsOf_mem_set (p : Pairs) (g : Bool × Bool × Bool) {S : Finset (Fin 52)}
    (h0 : p.u0 ∈ S) (h1 : p.v0 ∈ S) (h2 : p.u1 ∈ S) (h3 : p.v1 ∈ S) (h4 : p.u2 ∈ S)
    (h5 : p.v2 ∈ S) {x : Fin 52} (hx : x ∈ S) : swapsOf p g x ∈ S := by
  simp only [swapsOf, Equiv.Perm.mul_apply]
  exact swapIf_mem_set _ h0 h1 (swapIf_mem_set _ h2 h3 (swapIf_mem_set _ h4 h5 hx))

theorem content_act (q π : Equiv.Perm (Fin 52)) (ρ : Fin 4) (g : Bool × Bool × Bool)
    (hq : (movedInRow q ρ).card ≤ 1) :
    content q (act q ρ g π) ρ = content q π ρ := by
  have hP := choosePairs_good _ (card_content q π ρ hq)
  obtain ⟨hd, h0, h1, h2, h3, h4, h5, -⟩ := hP
  set P := choosePairs (content q π ρ)
  have e : content q (act q ρ g π) ρ = (content q π ρ).image (swapsOf P g) := by
    simp only [content, act, image_image]
    rfl
  rw [e]
  ext x
  simp only [mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact swapsOf_mem_set P g h0 h1 h2 h3 h4 h5 hy
  · intro hx
    exact ⟨swapsOf P g x, swapsOf_mem_set P g h0 h1 h2 h3 h4 h5 hx, swapsOf_swapsOf P hd g x⟩

/-- (PROVED) `act q ρ g` is an involution. -/
theorem act_act (q π : Equiv.Perm (Fin 52)) (ρ : Fin 4) (g : Bool × Bool × Bool)
    (hq : (movedInRow q ρ).card ≤ 1) :
    act q ρ g (act q ρ g π) = π := by
  have hd := (choosePairs_good _ (card_content q π ρ hq)).1
  have e := content_act q π ρ g hq
  unfold act at e ⊢
  rw [e]
  exact Equiv.ext fun x => by simp only [Equiv.Perm.mul_apply]; exact swapsOf_swapsOf _ hd g _

/-- The six cards as a finset. -/
def Pairs.set (p : Pairs) : Finset (Fin 52) := {p.u0, p.v0, p.u1, p.v1, p.u2, p.v2}

theorem swapsOf_commute (p : Pairs) (g : Bool × Bool × Bool)
    (δ : Equiv.Perm (Fin 52)) (hδ : ∀ x ∈ p.set, δ x = x) :
    δ * swapsOf p g = swapsOf p g * δ := by
  have m : ∀ {x}, x ∈ p.set ↔ (x = p.u0 ∨ x = p.v0 ∨ x = p.u1 ∨ x = p.v1 ∨ x = p.u2 ∨ x = p.v2) :=
    by intro x; simp [Pairs.set]
  refine Equiv.ext fun x => ?_
  simp only [Equiv.Perm.mul_apply]
  by_cases hx : x ∈ p.set
  · have hs : swapsOf p g x ∈ p.set :=
      swapsOf_mem_set p g (m.mpr (Or.inl rfl)) (m.mpr (Or.inr (Or.inl rfl)))
        (m.mpr (Or.inr (Or.inr (Or.inl rfl)))) (m.mpr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
        (m.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
        (m.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))) hx
    rw [hδ _ hs, hδ _ hx]
  · have hx' : ¬ (x = p.u0 ∨ x = p.v0 ∨ x = p.u1 ∨ x = p.v1 ∨ x = p.u2 ∨ x = p.v2) :=
      fun h => hx (m.mpr h)
    have hδx : δ x ∉ p.set := by
      intro h
      apply hx
      have e := hδ _ h
      rw [← δ.injective e]
      exact h
    have hδx' : ¬ (δ x = p.u0 ∨ δ x = p.v0 ∨ δ x = p.u1 ∨ δ x = p.v1 ∨ δ x = p.u2 ∨
        δ x = p.v2) := fun h => hδx (m.mpr h)
    push_neg at hx' hδx'
    rw [swapsOf_of_not_mem p g hx', swapsOf_of_not_mem p g hδx']

theorem fix_of_content {q δ π : Equiv.Perm (Fin 52)} (h : π⁻¹ * δ * π = q) {ρ : Fin 4}
    {u : Fin 52} (hu : u ∈ content q π ρ) : δ u = u := by
  obtain ⟨i, hi, rfl⟩ := mem_content.mp hu
  have e := congrArg (fun f : Equiv.Perm (Fin 52) => f (cmFlat ρ i)) h
  simp only [Equiv.Perm.mul_apply, hi] at e
  exact (Equiv.Perm.inv_eq_iff_eq.mp e)

/-- (PROVED) `act` keeps `π⁻¹ δ π = q`: the swapped cards are fixed by `δ`. -/
theorem conj_act {q δ π : Equiv.Perm (Fin 52)} (h : π⁻¹ * δ * π = q) (ρ : Fin 4)
    (g : Bool × Bool × Bool)
    (hq : (movedInRow q ρ).card ≤ 1) :
    (act q ρ g π)⁻¹ * δ * (act q ρ g π) = q := by
  obtain ⟨hd, h0, h1, h2, h3, h4, h5, -⟩ := choosePairs_good _ (card_content q π ρ hq)
  set P := choosePairs (content q π ρ)
  have hδ : ∀ x ∈ P.set, δ x = x := by
    intro x hx
    simp only [Pairs.set, mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> exact fix_of_content h ‹_›
  have hc := swapsOf_commute P g δ hδ
  have hc' : (swapsOf P g)⁻¹ * δ * swapsOf P g = δ := by
    rw [mul_assoc, hc, ← mul_assoc, inv_mul_cancel, one_mul]
  show (swapsOf P g * π)⁻¹ * δ * (swapsOf P g * π) = q
  rw [mul_inv_rev, ← h]
  calc π⁻¹ * (swapsOf P g)⁻¹ * δ * (swapsOf P g * π)
      = π⁻¹ * ((swapsOf P g)⁻¹ * δ * swapsOf P g) * π := by simp only [mul_assoc]
    _ = π⁻¹ * δ * π := by rw [hc']

/-- (PROVED) `act q ρ g` does not move the cards of any other row. -/
theorem act_apply_other (q π : Equiv.Perm (Fin 52)) {ρ ρ' : Fin 4} (hne : ρ' ≠ ρ)
    (g : Bool × Bool × Bool)
    (hq : (movedInRow q ρ).card ≤ 1) (i : Fin 13) :
    act q ρ g π (cmFlat ρ' i) = π (cmFlat ρ' i) := by
  obtain ⟨-, h0, h1, h2, h3, h4, h5, -⟩ := choosePairs_good _ (card_content q π ρ hq)
  have hn : ∀ {u}, u ∈ content q π ρ → π (cmFlat ρ' i) ≠ u := by
    intro u hu e
    obtain ⟨j, -, hj⟩ := mem_content.mp hu
    rw [← hj] at e
    exact hne (Prod.mk.inj (cmFlat_inj2 (p := (ρ', i)) (q := (ρ, j)) (π.injective e))).1
  exact swapsOf_of_not_mem _ g ⟨hn h0, hn h1, hn h2, hn h3, hn h4, hn h5⟩

/-! ## The coupling bound -/

/-- The condition of row `ρ` in `rowAmts_eq_iff`, at the deck `permDeck π`. -/
def cond (t : Fin 4 → Nat) (ρ : Fin 4) (π : Equiv.Perm (Fin 52)) : Prop :=
  rowTurnV10 (rowRead (permDeck π) ρ (readAmt t ρ)) = t (nextRow ρ)

instance (t : Fin 4 → Nat) (ρ : Fin 4) (π : Equiv.Perm (Fin 52)) : Decidable (cond t ρ π) := by
  unfold cond; infer_instance

theorem cond_act_other (q π : Equiv.Perm (Fin 52)) (t : Fin 4 → Nat) {ρ ρ' : Fin 4}
    (hne : ρ' ≠ ρ) (g : Bool × Bool × Bool)
    (hq : (movedInRow q ρ).card ≤ 1) :
    cond t ρ' (act q ρ g π) ↔ cond t ρ' π := by
  have e : rowRead (permDeck (act q ρ g π)) ρ' (readAmt t ρ') =
      rowRead (permDeck π) ρ' (readAmt t ρ') := by
    funext j
    simp only [rowRead, permDeck]
    rw [act_apply_other q π hne g hq]
  simp only [cond, e]

/-- (PROVED) For every deck `π`, at most 3 of the 8 swap choices `g` satisfy row `ρ`'s
    condition after `act q ρ g`. -/
theorem card_cond_act_le (q π : Equiv.Perm (Fin 52)) (t : Fin 4 → Nat) (ρ : Fin 4)
    (hq : (movedInRow q ρ).card ≤ 1) :
    (univ.filter fun g => cond t ρ (act q ρ g π)).card ≤ 3 := by
  have hP := choosePairs_good _ (card_content q π ρ hq)
  unfold act
  generalize choosePairs (content q π ρ) = P at hP ⊢
  obtain ⟨hd, h0, h1, h2, h3, h4, h5, r0, r1, r2⟩ := hP
  obtain ⟨d01, -, -, -, -, -, -, -, -, d23, -, -, -, -, d45⟩ := hd.ne
  let a := readAmt t ρ
  let y : Fin 13 → Fin 52 := fun j => π (cmFlat ρ ⟨(j.val + a % 13) % 13, Nat.mod_lt _ (by decide)⟩)
  have hy : Function.Injective y := by
    intro j1 j2 e
    have e' := congrArg Fin.val (Prod.mk.inj (cmFlat_inj2 (p := (ρ, _)) (q := (ρ, _))
      (π.injective e))).2
    simp only at e'
    apply Fin.ext
    have := j1.isLt
    have := j2.isLt
    have := Nat.mod_lt a (by decide : 0 < 13)
    omega
  have idx : ∀ {u}, u ∈ content q π ρ → ∃ j, y j = u := by
    intro u hu
    obtain ⟨i, -, rfl⟩ := mem_content.mp hu
    refine ⟨⟨(i.val + (13 - a % 13)) % 13, Nat.mod_lt _ (by decide)⟩, ?_⟩
    show π (cmFlat ρ _) = π (cmFlat ρ i)
    congr 2
    apply Fin.ext
    simp only
    have := i.isLt
    have := Nat.mod_lt a (by decide : 0 < 13)
    omega
  obtain ⟨a0, ha0⟩ := idx h0
  obtain ⟨b0, hb0⟩ := idx h1
  obtain ⟨a1, ha1⟩ := idx h2
  obtain ⟨b1, hb1⟩ := idx h3
  obtain ⟨a2, ha2⟩ := idx h4
  obtain ⟨b2, hb2⟩ := idx h5
  have hPe : P = ⟨y a0, y b0, y a1, y b1, y a2, y b2⟩ := by
    rw [ha0, hb0, ha1, hb1, ha2, hb2]
  obtain ⟨e01, e02, e03, e04, e05, e12, e13, e14, e15, e23, e24, e25, e34, e35, e45⟩ := hd.ne
  have ne_of : ∀ {i j : Fin 13} {u v : Fin 52}, y i = u → y j = v → u ≠ v → i ≠ j :=
    fun hi hj huv e => huv (by rw [← hi, ← hj, e])
  have hnd : [a0, b0, a1, b1, a2, b2].Nodup :=
    nodup6_of ⟨ne_of ha0 hb0 e01, ne_of ha0 ha1 e02, ne_of ha0 hb1 e03, ne_of ha0 ha2 e04,
      ne_of ha0 hb2 e05, ne_of hb0 ha1 e12, ne_of hb0 hb1 e13, ne_of hb0 ha2 e14, ne_of hb0 hb2 e15,
      ne_of ha1 hb1 e23, ne_of ha1 ha2 e24, ne_of ha1 hb2 e25, ne_of hb1 ha2 e34, ne_of hb1 hb2 e35,
      ne_of ha2 hb2 e45⟩
  have hD : ∀ {a' b' : Fin 13}, a' ≠ b' → rank (y a').val ≠ rank (y b').val →
      (wt a' - wt b') * (rk (y b') - rk (y a')) ≠ 0 :=
    fun hab hr => zmod13_mul_ne _ _ (wt_sub_ne hab) (rk_sub_ne hr)
  obtain ⟨n01, -, -, -, -, -, -, -, -, n23, -, -, -, -, n45⟩ := nodup6 hnd
  have s0 : rank (y a0).val ≠ rank (y b0).val := by rw [ha0, hb0]; exact r0
  have s1 : rank (y a1).val ≠ rank (y b1).val := by rw [ha1, hb1]; exact r1
  have s2 : rank (y a2).val ≠ rank (y b2).val := by rw [ha2, hb2]; exact r2
  refine (card_le_card fun g hg => ?_).trans (card_hit_le_three (wsum y)
    ((t (nextRow ρ) : ℕ) : ZMod 13) _ _ _ (hD n01 s0) (hD n23 s1) (hD n45 s2))
  simp only [mem_filter, mem_univ, true_and, cond] at hg ⊢
  have hc := congrArg (fun n : ℕ => (n : ZMod 13)) hg
  simp only at hc
  have e : rowRead (permDeck (swapsOf P g * π)) ρ (readAmt t ρ) =
      fun j => (swapsOf P g (y j)).val := rfl
  rw [e, rowTurnV10_cast, hPe, wsum_three y hy hnd g] at hc
  exact hc

/-- (PROVED; the coupling lemma for the 4-card case) Let `q` move at most
    one position in each row of the column-major grid. Then among the decks `π` with
    `π⁻¹ δ π = q`, the fraction whose row amounts are exactly `t` is at most `81/4096`
    (`= (3/8)^4 ≈ 0.0198`):
    `4096 · #{π | π⁻¹ δ π = q ∧ rowAmts (permDeck π) = t} ≤ 81 · #{π | π⁻¹ δ π = q}`.
    Any `δ`, `t`; no hypothesis on `δ`. -/
theorem coupling (q δ : Equiv.Perm (Fin 52))
    (hq : ∀ ρ : Fin 4, (movedInRow q ρ).card ≤ 1)
    (t : Fin 4 → Nat) :
    4096 * (univ.filter fun π : Equiv.Perm (Fin 52) =>
        π⁻¹ * δ * π = q ∧ ∀ r, rowAmts (permDeck π) r = t r).card ≤
      81 * (univ.filter fun π : Equiv.Perm (Fin 52) => π⁻¹ * δ * π = q).card := by
  classical
  let E0 := univ.filter fun π : Equiv.Perm (Fin 52) => π⁻¹ * δ * π = q
  let A : Finset (Fin 4) → Finset (Equiv.Perm (Fin 52)) :=
    fun S => E0.filter fun π => ∀ ρ ∈ S, cond t ρ π
  have step : ∀ ρ S, ρ ∉ S → 8 * (A (insert ρ S)).card ≤ 3 * (A S).card := by
    intro ρ S hρ
    have hAeq : A (insert ρ S) = (A S).filter (cond t ρ) := by
      ext π
      simp only [A, mem_filter, mem_insert, forall_eq_or_imp]
      tauto
    rw [hAeq]
    have key := double_count (A S) (cond t ρ) (act q ρ) ?_ ?_ 3 ?_
    · simpa using key
    · intro g π hπ
      simp only [A, E0, mem_filter, mem_univ, true_and] at hπ ⊢
      refine ⟨conj_act hπ.1 ρ g (hq ρ), fun ρ' hρ' => ?_⟩
      have hne : ρ' ≠ ρ := fun e => hρ (e ▸ hρ')
      exact (cond_act_other q π t hne g (hq ρ)).mpr (hπ.2 ρ' hρ')
    · intro g π _
      exact act_act q π ρ g (hq ρ)
    · intro π _
      exact card_cond_act_le q π t ρ (hq ρ)
  have e0 : (insert 0 ∅ : Finset (Fin 4)) = {0} := by decide
  have h1 := step 0 ∅ (by simp)
  rw [e0] at h1
  have h2 := step 1 {0} (by decide)
  have h3 := step 2 {1, 0} (by decide)
  have h4 := step 3 {2, 1, 0} (by decide)
  have hA0 : A ∅ = E0 := by ext; simp [A]
  rw [hA0] at h1
  have hsub : (univ.filter fun π : Equiv.Perm (Fin 52) =>
      π⁻¹ * δ * π = q ∧ ∀ r, rowAmts (permDeck π) r = t r) ⊆ A {3, 2, 1, 0} := by
    intro π hπ
    simp only [mem_filter, mem_univ, true_and] at hπ
    simp only [A, E0, mem_filter, mem_univ, true_and]
    exact ⟨hπ.1, fun ρ _ => (rowAmts_eq_iff _ _).mp hπ.2 ρ⟩
  have h5 := card_le_card hsub
  have hE0 : E0.card = (univ.filter fun π : Equiv.Perm (Fin 52) => π⁻¹ * δ * π = q).card := rfl
  omega

end DoubleDeal.Security.StemCoupling
