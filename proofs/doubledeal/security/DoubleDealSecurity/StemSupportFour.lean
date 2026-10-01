import DoubleDealSecurity.StemCoupling
import DoubleDealSecurity.FullCipher

/-
  The 4-card case of the off-diagonal stem bound (third slice towards the off-diagonal stem column
  bound; security README, "Roadmap", the M7 row). One bound on `dpFCount`, for one support size.

  THIS IS A BOUND ON ONE ENTRY OF THE FINAL ROUND'S DIFFERENCE TABLE, ONLY WHEN `γ⁻¹ * β`
  MOVES EXACTLY 4 CARDS (and zero for 1–3 and 5–7 cards). It is not a bound on the
  full-cipher differential by itself: the `β` with `γ⁻¹ * β` moving at least 8 cards are the
  next module, `StemUnion`, which assembles the off-diagonal bound
  (`StemUnion.dpFCount_le_of_ne`). No security claim.

  Notation: `x = permDeck π`, `δ = γ⁻¹ * β`, "`δ` moves `k` cards" is `δ.support.card = k`
  (Mathlib's `Equiv.Perm.support`), `q = stemPerm x * (stemPerm (β·x))⁻¹` (the ratio of
  `StemPosition.conj_of_stem_rel`, so `π⁻¹ δ π = q` on every deck counted by `dpFCount β γ`).

  Proved:
  * `qPerm t c d` (`t : Fin 4 → ℕ`, `c : Fin 13`, `d : Fin 4`): the permutation of positions
    sending `pos t c ρ = cmFlat ρ ((c + t ρ) % 13)` to `pos t c (ρ + d)` and fixing every other
    position. `qPerm_moves_le_one`: it moves at most one position of each row.
  * `ratio_eq_qPerm`: if the row amounts of two packets agree mod 13 and their column amounts
    agree mod 4 except at column `c`, the ratio of their position maps is
    `qPerm (rowAmts m) c (colDiff ..)`.
  * `amts_of_support_four`, `ratio_eq_qPerm_of_support_four`: if `δ` moves exactly 4
    cards (so `(zRows, zCols) = (4, 12)`), then `q = qPerm (rowAmts x) c d` for a column `c` and
    `d ≠ 0`; `q` is determined by `(rowAmts x, c, d)`.
  * `ratio_moves_le_one_of_support_four`: then `q` moves at most one position per row.
  * `card_conjSet_le_odd`, `card_conjSet_le_two`: for `δ` moving exactly 4 cards,
    `#{π | π⁻¹ δ π = qPerm t c d} ≤ 4 · 48!` for `d = 1, 3` and `≤ 8 · 48!` for `d = 2`.
    Upper bounds only (the exact values `4 · 48!` and `8 · 48!` when nonempty are not proved;
    no centralizer size is computed).
  * `sum_card_conjSet_le`: over the four `d`, at most `8 · 48!` in total, because `d = 0`
    gives `q = 1`, and `qPerm t c d` squares to `1` for `d = 2` but not for `d = 1, 3`, so
    `δ * δ = 1` allows only `d = 2` and `δ * δ ≠ 1` only `d = 1, 3` (no cycle types used).
  * `dpFCount_bound_of_support_four`, `dpFCount_le_of_support_four`: if `δ` moves exactly 4
    cards, then `4096 · dpFCount β γ ≤ 81 · 13^5 · 8 · 48!` (`≈ 0.00904 · 52!`; a factor of
    about 1.73 below `52!/64`), from `StemCoupling.coupling` on each of the `13^5 · 4` cells
    `(t, c, d)`; so `64 · dpFCount β γ ≤ 52!`.
  * `dpFCount_eq_zero_of_support_lt_eight_ne_four`: if `δ` moves 1–3 or 5–7 cards,
    `dpFCount β γ = 0` (`StemPosition.card_moved_cases`).

  Not proved, and limits:
  * The support-≥ 8 case (not here; it is `StemUnion.dpFCount_le_of_support_ge_eight`, a union
    bound).
  * Anything about `γ` in `v10Sym`, a mix round, several rounds, or the real key schedule.
  * About the stem (final no-mix round) only.
-/

namespace DoubleDeal.Security.StemSupportFour

open DoubleDeal Relabel Finset StemPosition StemCoupling

/-! ## The support-4 ratio, seat by seat -/

/-- The column of row `ρ` that the ratio moves: `(c + t ρ) % 13`. -/
def mcol (t : Fin 4 → Nat) (c : Fin 13) (ρ : Fin 4) : Fin 13 :=
  ⟨(c.val + t ρ % 13) % 13, Nat.mod_lt _ (by decide)⟩

/-- The ratio on seats: the seat `(ρ, mcol t c ρ)` goes to `(ρ + d, mcol t c (ρ + d))`;
    every other seat is fixed. -/
def qSeat (t : Fin 4 → Nat) (c : Fin 13) (d : Fin 4) (p : Fin 4 × Fin 13) : Fin 4 × Fin 13 :=
  if p.2 = mcol t c p.1 then (p.1 + d, mcol t c (p.1 + d)) else p

theorem qSeat_qSeat (t : Fin 4 → Nat) (c : Fin 13) (d : Fin 4) (p : Fin 4 × Fin 13) :
    qSeat t c (-d) (qSeat t c d p) = p := by
  obtain ⟨ρ, i⟩ := p
  by_cases h : i = mcol t c ρ
  · subst h
    simp only [qSeat, if_true, add_neg_cancel_right]
  · simp only [qSeat, if_neg h]

/-- The difference mod 4 of the column amounts `s c`, `s' c`. -/
def colDiff (s s' : Fin 13 → Nat) (c : Fin 13) : Fin 4 :=
  ⟨(s' c % 4 + 4 - s c % 4) % 4, Nat.mod_lt _ (by decide)⟩

/-- (PROVED) If the column amounts `s`, `s'` agree mod 4 except at column `c`, then
    `qSeat t c (colDiff s s' c)` carries the seat map of `s'` to that of `s`. -/
theorem qSeat_seatMap (t : Fin 4 → Nat) (s s' : Fin 13 → Nat) (c : Fin 13)
    (hs : ∀ j, j ≠ c → s j % 4 = s' j % 4) (p : Fin 4 × Fin 13) :
    qSeat t c (colDiff s s' c) (seatMap t s' p) = seatMap t s p := by
  obtain ⟨r, j⟩ := p
  by_cases hj : j = c
  · subst hj
    have key : srcRow s' r j + colDiff s s' j = srcRow s r j := by
      apply Fin.ext
      simp only [srcRow, colDiff, Fin.val_add]
      omega
    have hc : (seatMap t s' (r, j)).2 = mcol t j (seatMap t s' (r, j)).1 := rfl
    rw [qSeat, if_pos hc]
    show (srcRow s' r j + colDiff s s' j, mcol t j (srcRow s' r j + colDiff s s' j)) = _
    rw [key]
    rfl
  · have e : seatMap t s (r, j) = seatMap t s' (r, j) :=
      (seatMap_eq_iff t t s s' r j).mpr ⟨hs j hj, rfl⟩
    rw [← e, qSeat, if_neg]
    intro h
    apply hj
    have h' := congrArg Fin.val h
    simp only [seatMap, mcol] at h'
    apply Fin.ext
    have := j.isLt
    have := c.isLt
    have := Nat.mod_lt (t (srcRow s r j)) (by decide : 0 < 13)
    omega

/-! ## The support-4 ratio as a permutation of positions -/

/-- `qSeat` on positions (column-major seats). -/
def qFun (t : Fin 4 → Nat) (c : Fin 13) (d : Fin 4) (k : Fin 52) : Fin 52 :=
  cmFlat (qSeat t c d (cmRow k, cmCol k)).1 (qSeat t c d (cmRow k, cmCol k)).2

theorem qFun_cmFlat (t : Fin 4 → Nat) (c : Fin 13) (d : Fin 4) (p : Fin 4 × Fin 13) :
    qFun t c d (cmFlat p.1 p.2) = cmFlat (qSeat t c d p).1 (qSeat t c d p).2 := by
  unfold qFun
  rw [(cm_cmFlat _ _).1, (cm_cmFlat _ _).2]

theorem qFun_qFun (t : Fin 4 → Nat) (c : Fin 13) (d : Fin 4) (k : Fin 52) :
    qFun t c (-d) (qFun t c d k) = k := by
  show qFun t c (-d) (cmFlat (qSeat t c d (cmRow k, cmCol k)).1
    (qSeat t c d (cmRow k, cmCol k)).2) = k
  rw [qFun_cmFlat t c (-d) (qSeat t c d (cmRow k, cmCol k)), qSeat_qSeat]
  exact cmFlat_cm k

/-- The candidate ratio `q(t, c, d)` for support 4, as a permutation of the 52 positions. -/
def qPerm (t : Fin 4 → Nat) (c : Fin 13) (d : Fin 4) : Equiv.Perm (Fin 52) where
  toFun := qFun t c d
  invFun := qFun t c (-d)
  left_inv := qFun_qFun t c d
  right_inv := fun k => by
    have := qFun_qFun t c (-d) k
    rwa [neg_neg] at this

theorem qPerm_apply (t : Fin 4 → Nat) (c : Fin 13) (d : Fin 4) (k : Fin 52) :
    qPerm t c d k = qFun t c d k := rfl

/-! ## The ratio of two position maps -/

/-- (PROVED) If the row amounts of the packets `m`, `m'` agree mod 13 and their column amounts
    agree mod 4 except at column `c`, the ratio of their position maps is
    `qPerm (rowAmts m) c (colDiff (colAmts m) (colAmts m') c)`. -/
theorem ratio_eq_qPerm (m m' : Fin 52 → Nat) (c : Fin 13)
    (ht : ∀ r, rowAmts m r % 13 = rowAmts m' r % 13)
    (hs : ∀ j, j ≠ c → colAmts m j % 4 = colAmts m' j % 4) :
    stemPerm m * (stemPerm m')⁻¹ = qPerm (rowAmts m) c (colDiff (colAmts m) (colAmts m') c) := by
  refine Equiv.ext fun k => ?_
  obtain ⟨k', rfl⟩ : ∃ k', stemPerm m' k' = k := ⟨(stemPerm m')⁻¹ k, by simp⟩
  simp only [Equiv.Perm.mul_apply, Equiv.Perm.inv_apply_self]
  rw [qPerm_apply, stemPerm_apply, stemPerm_apply]
  have er : seatMap (rowAmts m') (colAmts m') (inSeat k') =
      seatMap (rowAmts m) (colAmts m') (inSeat k') :=
    ((seatMap_eq_iff _ _ _ _ _ _).mpr ⟨rfl, (ht _).symm⟩)
  show cmFlat (seatMap (rowAmts m) (colAmts m) (inSeat k')).1
      (seatMap (rowAmts m) (colAmts m) (inSeat k')).2 =
    qFun (rowAmts m) c _ (cmFlat (seatMap (rowAmts m') (colAmts m') (inSeat k')).1
      (seatMap (rowAmts m') (colAmts m') (inSeat k')).2)
  rw [qFun_cmFlat, er, qSeat_seatMap _ _ _ c hs]

/-! ## Support 4 forces `(zRows, zCols) = (4, 12)` -/

/-- (PROVED) Under the hypothesis of `conj_of_stem_rel`, if `γ⁻¹ * β` moves exactly 4 cards then
    the two packets `x = permDeck π`, `β·x` have the same row amounts mod 13 and column amounts
    agreeing mod 4 at all but one column `c`. -/
theorem amts_of_support_four {β γ π : Equiv.Perm (Fin 52)}
    (h : unkeyedNoMix (rel β (permDeck π)) = rel γ (unkeyedNoMix (permDeck π)))
    (h4 : (γ⁻¹ * β).support.card = 4) :
    (∀ r, rowAmts (permDeck π) r % 13 = rowAmts (rel β (permDeck π)) r % 13) ∧
    ∃ c : Fin 13, colAmts (permDeck π) c % 4 ≠ colAmts (rel β (permDeck π)) c % 4 ∧
      ∀ j, j ≠ c → colAmts (permDeck π) j % 4 = colAmts (rel β (permDeck π)) j % 4 := by
  have hz : zRows (permDeck π) (rel β (permDeck π)) = 4 ∧
      zCols (permDeck π) (rel β (permDeck π)) = 12 := by
    rcases card_moved_cases h with e | ⟨-, hz⟩ | e
    · omega
    · exact hz
    · omega
  obtain ⟨hr, hc⟩ := hz
  constructor
  · intro r
    have hr' : (univ.filter fun r : Fin 4 => rowAmts (permDeck π) r % 13 =
        rowAmts (rel β (permDeck π)) r % 13).card = 4 := hr
    have hu : (univ.filter fun r : Fin 4 => rowAmts (permDeck π) r % 13 =
        rowAmts (rel β (permDeck π)) r % 13) = univ :=
      Finset.eq_univ_of_card _ (by rw [hr']; rfl)
    have hm : r ∈ (univ.filter fun r : Fin 4 => rowAmts (permDeck π) r % 13 =
        rowAmts (rel β (permDeck π)) r % 13) := by
      rw [hu]; exact mem_univ r
    exact (mem_filter.mp hm).2
  · have ee := filter_card_add_filter_neg_card_eq_card (s := (univ : Finset (Fin 13)))
      (fun j => colAmts (permDeck π) j % 4 = colAmts (rel β (permDeck π)) j % 4)
    have hc' : zCols (permDeck π) (rel β (permDeck π)) =
        (univ.filter fun j : Fin 13 =>
          colAmts (permDeck π) j % 4 = colAmts (rel β (permDeck π)) j % 4).card := rfl
    rw [← hc', hc, card_univ, Fintype.card_fin] at ee
    obtain ⟨c, hc1⟩ := card_eq_one.mp (show (univ.filter fun j : Fin 13 =>
      ¬ colAmts (permDeck π) j % 4 = colAmts (rel β (permDeck π)) j % 4).card = 1 by omega)
    refine ⟨c, ?_, fun j hj => ?_⟩
    · have : c ∈ ({c} : Finset (Fin 13)) := mem_singleton_self c
      rw [← hc1] at this
      exact (mem_filter.mp this).2
    · by_contra hn
      have : j ∈ (univ.filter fun j : Fin 13 =>
          ¬ colAmts (permDeck π) j % 4 = colAmts (rel β (permDeck π)) j % 4) :=
        mem_filter.mpr ⟨mem_univ j, hn⟩
      rw [hc1, mem_singleton] at this
      exact hj this

theorem colDiff_ne_zero {s s' : Fin 13 → Nat} {c : Fin 13} (h : s c % 4 ≠ s' c % 4) :
    colDiff s s' c ≠ 0 := by
  intro e
  have e' := congrArg Fin.val e
  simp only [colDiff, Fin.val_zero] at e'
  omega

/-- (PROVED) When `γ⁻¹ * β` moves exactly 4 cards, the ratio
    `q = stemPerm x * (stemPerm (β·x))⁻¹` of `conj_of_stem_rel` (`x = permDeck π`) is
    `qPerm (rowAmts x) c d` for a column `c` and a nonzero `d : Fin 4`: it is determined by
    the row amounts of `x`, `c` and `d`. -/
theorem ratio_eq_qPerm_of_support_four {β γ π : Equiv.Perm (Fin 52)}
    (h : unkeyedNoMix (rel β (permDeck π)) = rel γ (unkeyedNoMix (permDeck π)))
    (h4 : (γ⁻¹ * β).support.card = 4) :
    ∃ c : Fin 13, ∃ d : Fin 4, d ≠ 0 ∧
      stemPerm (permDeck π) * (stemPerm (rel β (permDeck π)))⁻¹ =
        qPerm (rowAmts (permDeck π)) c d := by
  obtain ⟨ht, c, hc, hs⟩ := amts_of_support_four h h4
  exact ⟨c, _, colDiff_ne_zero hc, ratio_eq_qPerm _ _ c ht hs⟩

/-! ## `qPerm` moves one position per row -/

/-- The position `qPerm t c d` moves in row `ρ`. -/
def pos (t : Fin 4 → Nat) (c : Fin 13) (ρ : Fin 4) : Fin 52 := cmFlat ρ (mcol t c ρ)

theorem qPerm_pos (t : Fin 4 → Nat) (c : Fin 13) (d : Fin 4) (ρ : Fin 4) :
    qPerm t c d (pos t c ρ) = pos t c (ρ + d) := by
  rw [qPerm_apply, pos, qFun_cmFlat t c d (ρ, mcol t c ρ)]
  simp only [qSeat, if_true]
  rfl

theorem qPerm_cmFlat_of_ne (t : Fin 4 → Nat) (c : Fin 13) (d : Fin 4) {ρ : Fin 4} {i : Fin 13}
    (hi : i ≠ mcol t c ρ) : qPerm t c d (cmFlat ρ i) = cmFlat ρ i := by
  rw [qPerm_apply, qFun_cmFlat t c d (ρ, i)]
  simp only [qSeat, if_neg hi]

theorem pos_injective (t : Fin 4 → Nat) (c : Fin 13) : Function.Injective (pos t c) :=
  fun _ _ h => (Prod.mk.inj (cmFlat_inj2 h)).1

/-- (PROVED) `qPerm t c d` moves at most one position of each row `ρ` (the one at column
    `mcol t c ρ`). -/
theorem qPerm_moves_le_one (t : Fin 4 → Nat) (c : Fin 13) (d : Fin 4) (ρ : Fin 4) :
    (movedInRow (qPerm t c d) ρ).card ≤ 1 := by
  refine (card_le_card (t := {mcol t c ρ}) fun i hi => ?_).trans (card_singleton _).le
  rw [movedInRow, mem_filter] at hi
  rw [mem_singleton]
  by_contra hn
  exact hi.2 (qPerm_cmFlat_of_ne t c d hn)

/-- (PROVED) When `γ⁻¹ * β` moves exactly 4 cards
    (`(zRows, zCols) = (4, 12)`), the ratio `q` of `conj_of_stem_rel` moves at most one
    position of each row `ρ` (positions `cmFlat ρ i`). -/
theorem ratio_moves_le_one_of_support_four {β γ π : Equiv.Perm (Fin 52)}
    (h : unkeyedNoMix (rel β (permDeck π)) = rel γ (unkeyedNoMix (permDeck π)))
    (h4 : (γ⁻¹ * β).support.card = 4) (ρ : Fin 4) :
    (movedInRow (stemPerm (permDeck π) * (stemPerm (rel β (permDeck π)))⁻¹) ρ).card ≤ 1 := by
  obtain ⟨c, d, -, e⟩ := ratio_eq_qPerm_of_support_four h h4
  rw [e]
  exact qPerm_moves_le_one _ c d ρ

/-! ## Decks with a prescribed conjugate -/

theorem conj_apply {δ q π : Equiv.Perm (Fin 52)} (h : π⁻¹ * δ * π = q) (y : Fin 52) :
    δ (π y) = π (q y) := by
  rw [← h]
  simp only [Equiv.Perm.mul_apply, Equiv.Perm.apply_inv_self]

/-- (PROVED) Exactly `(52 - #A)!` permutations fix every point of `A`. -/
theorem card_fix_eq (A : Finset (Fin 52)) :
    (univ.filter fun σ : Equiv.Perm (Fin 52) => ∀ x ∈ A, σ x = x).card =
      Nat.factorial (52 - A.card) := by
  rw [← Fintype.card_subtype, ← Fintype.card_congr ((Equiv.Perm.subtypeEquivSubtypePerm (· ∉ A)).trans
    (Equiv.subtypeEquivRight fun σ => by simp)), Fintype.card_perm, Fintype.card_subtype, filter_not,
    filter_mem_eq_inter, univ_inter, card_sdiff (subset_univ _), card_univ, Fintype.card_fin]

/-- (PROVED) At most `(52 - #A)!` permutations agree with a given map `f` on `A`. -/
theorem card_agree_le (A : Finset (Fin 52)) (f : Fin 52 → Fin 52) :
    (univ.filter fun π : Equiv.Perm (Fin 52) => ∀ x ∈ A, π x = f x).card ≤
      Nat.factorial (52 - A.card) := by
  by_cases hne : ∃ π0 : Equiv.Perm (Fin 52), ∀ x ∈ A, π0 x = f x
  · obtain ⟨π0, h0⟩ := hne
    rw [← card_fix_eq A]
    refine card_le_card_of_injOn (fun π => π0⁻¹ * π) ?_ ?_
    · intro π hπ
      simp only [mem_filter, mem_univ, true_and, coe_filter, Set.mem_setOf_eq] at hπ ⊢
      intro x hx
      rw [Equiv.Perm.mul_apply, hπ x hx, ← h0 x hx, Equiv.Perm.inv_apply_self]
    · intro a _ b _ e
      exact mul_left_cancel e
  · rw [filter_false_of_mem fun π _ hπ => hne ⟨π, hπ⟩]
    simp

/-! ## The conjugate `qPerm t c d`: how many decks -/

/-- The four positions `qPerm t c d` moves. -/
def posSet (t : Fin 4 → Nat) (c : Fin 13) : Finset (Fin 52) := univ.image (pos t c)

theorem card_posSet (t : Fin 4 → Nat) (c : Fin 13) : (posSet t c).card = 4 := by
  rw [posSet, card_image_of_injective _ (pos_injective t c), card_univ, Fintype.card_fin]

theorem step_agree {δ π π1 : Equiv.Perm (Fin 52)} {t : Fin 4 → Nat} {c : Fin 13} {d : Fin 4}
    (h : π⁻¹ * δ * π = qPerm t c d) (h1 : π1⁻¹ * δ * π1 = qPerm t c d) {ρ : Fin 4}
    (e : π (pos t c ρ) = π1 (pos t c ρ)) : π (pos t c (ρ + d)) = π1 (pos t c (ρ + d)) := by
  rw [← qPerm_pos t c d ρ, ← conj_apply h, ← conj_apply h1, e]

/-- The decks `π` with `π⁻¹ δ π = q`. -/
def conjSet (δ q : Equiv.Perm (Fin 52)) : Finset (Equiv.Perm (Fin 52)) :=
  univ.filter fun π => π⁻¹ * δ * π = q

theorem mem_supp_of_conj {δ π : Equiv.Perm (Fin 52)} {t : Fin 4 → Nat} {c : Fin 13} {d : Fin 4}
    (hd : d ≠ 0) (h : π⁻¹ * δ * π = qPerm t c d) (ρ : Fin 4) : π (pos t c ρ) ∈ δ.support := by
  rw [Equiv.Perm.mem_support, conj_apply h, qPerm_pos]
  intro e
  have e' := pos_injective t c (π.injective e)
  apply hd
  have := congrArg (· - ρ) e'
  simpa using this

/-- (PROVED) For `d = 1` or `3` (`qPerm t c d` a 4-cycle on its four positions) and `δ` moving
    exactly 4 cards, at most `4 · 48!` decks `π` satisfy `π⁻¹ δ π = qPerm t c d`: `π` on the four
    positions is determined by the card it puts at the first, one of the 4 cards `δ` moves. -/
theorem card_conjSet_le_odd (δ : Equiv.Perm (Fin 52)) (hS : (δ.support).card = 4)
    (t : Fin 4 → Nat) (c : Fin 13) {d : Fin 4} (hd : d = 1 ∨ d = 3) :
    (conjSet δ (qPerm t c d)).card ≤ 4 * Nat.factorial 48 := by
  have hd0 : d ≠ 0 := by rcases hd with rfl | rfl <;> decide
  have hfib : ∀ v ∈ (conjSet δ (qPerm t c d)).image (fun π => π (pos t c 0)),
      ((conjSet δ (qPerm t c d)).filter fun π => π (pos t c 0) = v).card ≤
        Nat.factorial 48 := by
    intro v hv
    obtain ⟨π1, hπ1, rfl⟩ := mem_image.mp hv
    simp only [conjSet, mem_filter, mem_univ, true_and] at hπ1
    calc _ ≤ (univ.filter fun π : Equiv.Perm (Fin 52) => ∀ x ∈ posSet t c, π x = π1 x).card := by
          refine card_le_card fun π hπ => ?_
          simp only [conjSet, mem_filter, mem_univ, true_and] at hπ ⊢
          obtain ⟨hπ, e0⟩ := hπ
          intro x hx
          obtain ⟨ρ, -, rfl⟩ := mem_image.mp hx
          have st := fun ρ (e : π (pos t c ρ) = π1 (pos t c ρ)) => step_agree hπ hπ1 e
          rcases hd with rfl | rfl
          · have e1 := st 0 e0
            have e2 := st 1 e1
            have e3 := st 2 e2
            fin_cases ρ
            exacts [e0, e1, e2, e3]
          · have e3 := st 0 e0
            have e2 := st 3 e3
            have e1 := st 2 e2
            fin_cases ρ
            exacts [e0, e1, e2, e3]
      _ ≤ Nat.factorial (52 - (posSet t c).card) := card_agree_le _ _
      _ = Nat.factorial 48 := by rw [card_posSet]
  have himg : (conjSet δ (qPerm t c d)).image (fun π => π (pos t c 0)) ⊆ δ.support := by
    intro v hv
    obtain ⟨π, hπ, rfl⟩ := mem_image.mp hv
    simp only [conjSet, mem_filter, mem_univ, true_and] at hπ
    exact mem_supp_of_conj hd0 hπ 0
  calc (conjSet δ (qPerm t c d)).card
      ≤ Nat.factorial 48 * ((conjSet δ (qPerm t c d)).image (fun π => π (pos t c 0))).card :=
        card_le_mul_card_image _ _ hfib
    _ ≤ Nat.factorial 48 * 4 := Nat.mul_le_mul_left _ ((card_le_card himg).trans hS.le)
    _ = 4 * Nat.factorial 48 := Nat.mul_comm _ _

/-- (PROVED) For `δ` moving the 4 cards of `S`, at most 8 ordered pairs `(u, v)` of `S` have
    `v ≠ u` and `v ≠ δ u`. -/
theorem card_pairs_le (δ : Equiv.Perm (Fin 52)) (hS : (δ.support).card = 4) :
    ((δ.support ×ˢ δ.support).filter fun uv : Fin 52 × Fin 52 => uv.2 ≠ uv.1 ∧ uv.2 ≠ δ uv.1).card
      ≤ 8 := by
  rw [card_filter, sum_product]
  have hu : ∀ u ∈ δ.support,
      (∑ v ∈ δ.support, if v ≠ u ∧ v ≠ δ u then 1 else 0) = 2 := by
    intro u hu
    rw [← card_filter]
    have e : (δ.support).filter (fun v => v ≠ u ∧ v ≠ δ u) = ((δ.support).erase u).erase (δ u) := by
      ext v
      simp only [mem_filter, mem_erase]
      tauto
    have hδu : δ u ∈ δ.support := by
      rw [Equiv.Perm.mem_support] at hu ⊢
      exact fun e => hu (δ.injective e)
    rw [e, card_erase_of_mem (mem_erase.mpr ⟨(Equiv.Perm.mem_support.mp hu), hδu⟩), card_erase_of_mem hu, hS]
  rw [sum_congr rfl hu, sum_const, hS]
  rfl

/-- (PROVED) For `d = 2` (`qPerm t c 2` two transpositions) and `δ` moving exactly 4 cards, at
    most `8 · 48!` decks `π` satisfy `π⁻¹ δ π = qPerm t c 2`: `π` on the four positions is
    determined by the cards it puts at the first two, and there are at most 8 such pairs. -/
theorem card_conjSet_le_two (δ : Equiv.Perm (Fin 52)) (hS : (δ.support).card = 4)
    (t : Fin 4 → Nat) (c : Fin 13) :
    (conjSet δ (qPerm t c 2)).card ≤ 8 * Nat.factorial 48 := by
  have hfib : ∀ v ∈ (conjSet δ (qPerm t c 2)).image
      (fun π => (π (pos t c 0), π (pos t c 1))),
      ((conjSet δ (qPerm t c 2)).filter
        fun π => (π (pos t c 0), π (pos t c 1)) = v).card ≤ Nat.factorial 48 := by
    intro v hv
    obtain ⟨π1, hπ1, rfl⟩ := mem_image.mp hv
    simp only [conjSet, mem_filter, mem_univ, true_and] at hπ1
    calc _ ≤ (univ.filter fun π : Equiv.Perm (Fin 52) => ∀ x ∈ posSet t c, π x = π1 x).card := by
          refine card_le_card fun π hπ => ?_
          simp only [conjSet, mem_filter, mem_univ, true_and, Prod.mk.injEq] at hπ ⊢
          obtain ⟨hπ, e0, e1⟩ := hπ
          intro x hx
          obtain ⟨ρ, -, rfl⟩ := mem_image.mp hx
          have e2 := step_agree hπ hπ1 e0
          have e3 := step_agree hπ hπ1 e1
          fin_cases ρ
          exacts [e0, e1, e2, e3]
      _ ≤ Nat.factorial (52 - (posSet t c).card) := card_agree_le _ _
      _ = Nat.factorial 48 := by rw [card_posSet]
  have himg : (conjSet δ (qPerm t c 2)).image (fun π => (π (pos t c 0), π (pos t c 1))) ⊆
      (δ.support ×ˢ δ.support).filter fun uv : Fin 52 × Fin 52 => uv.2 ≠ uv.1 ∧ uv.2 ≠ δ uv.1 := by
    intro v hv
    obtain ⟨π, hπ, rfl⟩ := mem_image.mp hv
    simp only [conjSet, mem_filter, mem_univ, true_and] at hπ
    have h01 : pos t c 1 ≠ pos t c 0 := (pos_injective t c).ne (by decide)
    have h12 : pos t c 1 ≠ pos t c 2 := (pos_injective t c).ne (by decide)
    rw [mem_filter, mem_product]
    refine ⟨⟨mem_supp_of_conj (by decide) hπ 0, mem_supp_of_conj (by decide) hπ 1⟩,
      fun e => h01 (π.injective e), fun e => h12 (π.injective ?_)⟩
    simp only at e
    rw [e, conj_apply hπ, qPerm_pos]
    rfl
  calc (conjSet δ (qPerm t c 2)).card
      ≤ Nat.factorial 48 * ((conjSet δ (qPerm t c 2)).image
          (fun π => (π (pos t c 0), π (pos t c 1)))).card := card_le_mul_card_image _ _ hfib
    _ ≤ Nat.factorial 48 * 8 :=
        Nat.mul_le_mul_left _ ((card_le_card himg).trans (card_pairs_le δ hS))
    _ = 8 * Nat.factorial 48 := Nat.mul_comm _ _

/-! ## Which `d` can occur for a given `δ` -/

theorem qPerm_zero (t : Fin 4 → Nat) (c : Fin 13) : qPerm t c 0 = 1 := by
  refine Equiv.ext fun k => ?_
  rw [qPerm_apply, Equiv.Perm.one_apply, qFun]
  by_cases h : cmCol k = mcol t c (cmRow k)
  · simp only [qSeat, if_pos h, add_zero]
    rw [← h]
    exact cmFlat_cm k
  · simp only [qSeat, if_neg h]
    exact cmFlat_cm k

theorem qPerm_two_mul_self (t : Fin 4 → Nat) (c : Fin 13) : qPerm t c 2 * qPerm t c 2 = 1 := by
  refine Equiv.ext fun k => ?_
  rw [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
  have := qFun_qFun t c 2 k
  rwa [show (-2 : Fin 4) = 2 from rfl] at this

theorem qPerm_odd_mul_self_ne (t : Fin 4 → Nat) (c : Fin 13) {d : Fin 4} (hd : d = 1 ∨ d = 3) :
    qPerm t c d * qPerm t c d ≠ 1 := by
  intro e
  have e' := congrArg (fun f : Equiv.Perm (Fin 52) => f (pos t c 0)) e
  simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply, qPerm_pos] at e'
  have := pos_injective t c e'
  rcases hd with rfl | rfl <;> exact absurd this (by decide)

theorem conj_mul_self {δ q π : Equiv.Perm (Fin 52)} (h : π⁻¹ * δ * π = q) :
    π⁻¹ * (δ * δ) * π = q * q := by
  rw [← h]; group

theorem eq_one_of_conj_eq_one {δ π : Equiv.Perm (Fin 52)} (h : π⁻¹ * δ * π = 1) : δ = 1 := by
  calc δ = π * (π⁻¹ * δ * π) * π⁻¹ := by group
    _ = 1 := by rw [h]; group

theorem conjSet_eq_empty_of {δ q : Equiv.Perm (Fin 52)}
    (hn : ∀ π : Equiv.Perm (Fin 52), π⁻¹ * δ * π = q → False) : (conjSet δ q).card = 0 := by
  rw [card_eq_zero, conjSet, filter_eq_empty_iff]
  exact fun π _ h => hn π h

/-- (PROVED) For `δ` moving exactly 4 cards, the four `d` together allow at most `8 · 48!`
    decks: `d = 0` none (`qPerm t c 0 = 1`, `δ ≠ 1`); if `δ * δ = 1`, only `d = 2`
    (`≤ 8 · 48!`), since `qPerm t c d` squares to `1` exactly for `d = 2` (among `d ≠ 0`);
    otherwise only `d = 1, 3` (`≤ 4 · 48!` each). -/
theorem sum_card_conjSet_le (δ : Equiv.Perm (Fin 52)) (hS : (δ.support).card = 4)
    (t : Fin 4 → Nat) (c : Fin 13) :
    ∑ d : Fin 4, (conjSet δ (qPerm t c d)).card ≤ 8 * Nat.factorial 48 := by
  have hδ1 : δ ≠ 1 := by
    rintro rfl
    simp at hS
  have z0 : (conjSet δ (qPerm t c 0)).card = 0 :=
    conjSet_eq_empty_of fun π h => hδ1 (eq_one_of_conj_eq_one (h.trans (qPerm_zero t c)))
  rw [Fin.sum_univ_four, z0]
  by_cases hsq : δ * δ = 1
  · have z1 : (conjSet δ (qPerm t c 1)).card = 0 := conjSet_eq_empty_of fun π h =>
      qPerm_odd_mul_self_ne t c (Or.inl rfl) (by rw [← conj_mul_self h, hsq]; group)
    have z3 : (conjSet δ (qPerm t c 3)).card = 0 := conjSet_eq_empty_of fun π h =>
      qPerm_odd_mul_self_ne t c (Or.inr rfl) (by rw [← conj_mul_self h, hsq]; group)
    have b2 := card_conjSet_le_two δ hS t c
    omega
  · have z2 : (conjSet δ (qPerm t c 2)).card = 0 := conjSet_eq_empty_of fun π h => by
      have e := conj_mul_self h
      rw [qPerm_two_mul_self] at e
      exact hsq (eq_one_of_conj_eq_one e)
    have b1 := card_conjSet_le_odd δ hS t c (Or.inl rfl)
    have b3 := card_conjSet_le_odd δ hS t c (Or.inr rfl)
    omega

/-! ## The support-4 bound -/

theorem rowAmts_lt (m : Fin 52 → Nat) (r : Fin 4) : rowAmts m r < 13 := by
  unfold rowAmts rowAmt rowTurnV10
  exact Nat.mod_lt _ (by decide)

theorem factorial_52_eq : Nat.factorial 52 = 6497400 * Nat.factorial 48 := by
  rw [show (52 : ℕ) = 51 + 1 from rfl, Nat.factorial_succ, show (51 : ℕ) = 50 + 1 from rfl,
    Nat.factorial_succ, show (50 : ℕ) = 49 + 1 from rfl, Nat.factorial_succ,
    show (49 : ℕ) = 48 + 1 from rfl, Nat.factorial_succ]
  ring

/-- Four row amounts given mod 13. -/
def tv (a b e f : Fin 13) : Fin 4 → Nat := ![a.val, b.val, e.val, f.val]

/-- The decks with conjugate `qPerm t c d` and row amounts `t`, `t = tv a b e f`. -/
def cell (δ : Equiv.Perm (Fin 52)) (a b e f c : Fin 13) (d : Fin 4) :
    Finset (Equiv.Perm (Fin 52)) :=
  univ.filter fun π => π⁻¹ * δ * π = qPerm (tv a b e f) c d ∧
    ∀ r, rowAmts (permDeck π) r = tv a b e f r

/-- (PROVED) Under the hypothesis of `conj_of_stem_rel` and support 4, the deck `π` lies in
    the cell of `(rowAmts x, c, d)`. -/
theorem mem_cell {β γ π : Equiv.Perm (Fin 52)}
    (h : unkeyedNoMix (rel β (permDeck π)) = rel γ (unkeyedNoMix (permDeck π)))
    (h4 : (γ⁻¹ * β).support.card = 4) :
    ∃ a b e f c d, π ∈ cell (γ⁻¹ * β) a b e f c d := by
  obtain ⟨c, d, -, e⟩ := ratio_eq_qPerm_of_support_four h h4
  have hc := conj_of_stem_rel h
  have hT : tv ⟨_, rowAmts_lt (permDeck π) 0⟩ ⟨_, rowAmts_lt (permDeck π) 1⟩
      ⟨_, rowAmts_lt (permDeck π) 2⟩ ⟨_, rowAmts_lt (permDeck π) 3⟩ = rowAmts (permDeck π) := by
    funext r
    fin_cases r <;> rfl
  refine ⟨⟨_, rowAmts_lt (permDeck π) 0⟩, ⟨_, rowAmts_lt (permDeck π) 1⟩,
    ⟨_, rowAmts_lt (permDeck π) 2⟩, ⟨_, rowAmts_lt (permDeck π) 3⟩, c, d, ?_⟩
  simp only [cell, mem_filter, mem_univ, true_and]
  rw [hT]
  refine ⟨?_, fun r => rfl⟩
  rw [← e, hc]
  group

/-- `S.card ≤ Σ i, (F i).card` when every element of `S` lies in some `F i`. -/
theorem card_le_sum_of_mem {α ι : Type} [Fintype ι] [DecidableEq α] (S : Finset α)
    (F : ι → Finset α) (h : ∀ x ∈ S, ∃ i, x ∈ F i) : S.card ≤ ∑ i, (F i).card := by
  refine (card_le_card fun x hx => ?_).trans card_biUnion_le
  obtain ⟨i, hi⟩ := h x hx
  exact mem_biUnion.mpr ⟨i, mem_univ _, hi⟩

/-- All the cells, as one set (nested over the small index types). -/
def cells (δ : Equiv.Perm (Fin 52)) : Finset (Equiv.Perm (Fin 52)) :=
  univ.biUnion fun a => univ.biUnion fun b => univ.biUnion fun e => univ.biUnion fun f =>
    univ.biUnion fun c => univ.biUnion fun d => cell δ a b e f c d

/-- (PROVED) For support 4, every deck counted by `dpFCount β γ` lies in a cell. -/
theorem dpFCount_le_card_cells (β γ : Relabel)
    (h4 : (γ⁻¹ * β).support.card = 4) :
    FullCipher.dpFCount β γ ≤ (cells (γ⁻¹ * β)).card := by
  unfold FullCipher.dpFCount Differential.dpCount
  refine card_le_card fun π hπ => ?_
  rw [mem_filter] at hπ
  have hm := mem_cell hπ.2 h4
  simp only [cells, mem_biUnion, mem_univ, true_and]
  exact hm

theorem card_biUnion_mul_le {ι : Type} [Fintype ι] (F : ι → Finset (Equiv.Perm (Fin 52)))
    (B : ℕ) (hB : ∀ i, 4096 * (F i).card ≤ B) :
    4096 * (univ.biUnion F).card ≤ Fintype.card ι * B := by
  calc 4096 * (univ.biUnion F).card ≤ 4096 * ∑ i, (F i).card :=
        Nat.mul_le_mul_left _ card_biUnion_le
    _ = ∑ i, 4096 * (F i).card := mul_sum _ _ _
    _ ≤ ∑ _i : ι, B := sum_le_sum fun i _ => hB i
    _ = Fintype.card ι * B := by rw [sum_const, card_univ, smul_eq_mul]

/-- (PROVED) For `δ` moving exactly 4 cards, `4096 · #cells ≤ 13^5 · 81 · 8 · 48!`. -/
theorem card_cells_le (δ : Equiv.Perm (Fin 52)) (hS : (δ.support).card = 4) :
    4096 * (cells δ).card ≤ 13 * (13 * (13 * (13 * (13 * (81 * (8 * Nat.factorial 48)))))) := by
  have bound : ∀ a b e f c, 4096 * (univ.biUnion fun d => cell δ a b e f c d).card ≤
      81 * (8 * Nat.factorial 48) := by
    intro a b e f c
    calc 4096 * (univ.biUnion fun d => cell δ a b e f c d).card
        ≤ 4096 * ∑ d, (cell δ a b e f c d).card :=
          Nat.mul_le_mul_left _ card_biUnion_le
      _ = ∑ d, 4096 * (cell δ a b e f c d).card := mul_sum _ _ _
      _ ≤ ∑ d, 81 * (conjSet δ (qPerm (tv a b e f) c d)).card :=
          sum_le_sum fun d _ => coupling _ _ (qPerm_moves_le_one _ _ _) _
      _ = 81 * ∑ d, (conjSet δ (qPerm (tv a b e f) c d)).card := (mul_sum _ _ _).symm
      _ ≤ 81 * (8 * Nat.factorial 48) :=
          Nat.mul_le_mul_left _ (sum_card_conjSet_le _ hS _ _)
  unfold cells
  generalize hX : 81 * (8 * Nat.factorial 48) = X at bound ⊢
  refine (card_biUnion_mul_le _ (13 * (13 * (13 * (13 * X)))) fun a => ?_).trans
    (by rw [Fintype.card_fin])
  refine (card_biUnion_mul_le _ (13 * (13 * (13 * X))) fun b => ?_).trans
    (by rw [Fintype.card_fin])
  refine (card_biUnion_mul_le _ (13 * (13 * X)) fun e => ?_).trans (by rw [Fintype.card_fin])
  refine (card_biUnion_mul_le _ (13 * X) fun f => ?_).trans (by rw [Fintype.card_fin])
  refine (card_biUnion_mul_le _ X fun c => ?_).trans (by rw [Fintype.card_fin])
  exact bound a b e f c

/-- (PROVED) The bound the proof of `dpFCount_le_of_support_four` gives: if `γ⁻¹ * β` moves
    exactly 4 cards, `4096 · dpFCount β γ ≤ 81 · 13^5 · 8 · 48!` (about `0.00904 · 52!`). -/
theorem dpFCount_bound_of_support_four (β γ : Relabel)
    (h4 : (γ⁻¹ * β).support.card = 4) :
    4096 * FullCipher.dpFCount β γ ≤ 81 * 13 ^ 5 * 8 * Nat.factorial 48 :=
  ((Nat.mul_le_mul_left 4096 (dpFCount_le_card_cells β γ h4)).trans
    (card_cells_le _ h4)).trans_eq (by ring)

/-- (PROVED; the 4-card case of the off-diagonal stem bound) If `γ⁻¹ * β` moves exactly
    4 cards, then `64 · dpFCount β γ ≤ 52!`: at most 1/64 of the decks `x` have
    `stem(β·x) = γ·stem(x)`. (Exact counting, all in Lean: `x` lies in one of the cells
    `cell δ a b e f c d` (`δ = γ⁻¹β`, `13^5 · 4` of them, `mem_cell`), each at most `81/4096` of
    its conjugate set by `StemCoupling.coupling`, and the conjugate sets sum to at most
    `8 · 48!` over `d` for each `(t, c)` (`sum_card_conjSet_le`). The bound obtained is
    `4096 · dpFCount β γ ≤ 81 · 13^5 · 8 · 48!`, i.e. `dpFCount β γ / 52! ≤ 0.00904`, below
    `1/64 ≈ 0.0156` by a factor of about 1.73.) -/
theorem dpFCount_le_of_support_four (β γ : Relabel)
    (h4 : (γ⁻¹ * β).support.card = 4) :
    64 * FullCipher.dpFCount β γ ≤ Nat.factorial 52 := by
  have h5 := dpFCount_bound_of_support_four β γ h4
  rw [show 81 * 13 ^ 5 * 8 = 240597864 from rfl] at h5
  rw [factorial_52_eq]
  generalize FullCipher.dpFCount β γ = D at h5 ⊢
  generalize Nat.factorial 48 = F at h5 ⊢
  omega

/-! ## Supports 1–3 and 5–7 -/

/-- (PROVED) If `γ⁻¹ * β` moves between 1 and 7 cards but not 4, no deck is counted:
    `dpFCount β γ = 0` (`StemPosition.card_moved_cases`). -/
theorem dpFCount_eq_zero_of_support_lt_eight_ne_four (β γ : Relabel)
    (h0 : 0 < (γ⁻¹ * β).support.card)
    (h4 : (γ⁻¹ * β).support.card ≠ 4)
    (h8 : (γ⁻¹ * β).support.card < 8) :
    FullCipher.dpFCount β γ = 0 := by
  unfold FullCipher.dpFCount Differential.dpCount
  rw [card_eq_zero, filter_eq_empty_iff]
  intro π _ hπ
  rcases card_moved_cases hπ with e | ⟨e, -⟩ | e <;> omega

theorem eq_of_support_zero {β γ : Relabel}
    (h : (γ⁻¹ * β).support.card = 0) : β = γ :=
  (inv_mul_eq_one.mp (Equiv.Perm.support_eq_empty_iff.mp (card_eq_zero.mp h))).symm

end DoubleDeal.Security.StemSupportFour
