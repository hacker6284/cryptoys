import DoubleDealSecurity.StemSupportFour

/-
  The support-≥ 8 case of the off-diagonal stem bound (final slice of the off-diagonal stem
  column bound; security README, "Roadmap", the M7 row), and with it the column bound into
  every `γ` outside `v10Sym`.

  WHAT THIS GIVES, AND ITS LIMITS. For every input difference `α ≠ 1` and every output
  difference `γ` OUTSIDE `v10Sym`, `64 · fullDiffCount α γ n y ≤ (52!)^(n+2)` for every number
  `n` of mix rounds and every deck `y` (`fullDiffCount_le_64`): with independent uniform
  Compose keys, the differential probability of `α → γ` through `encryptN n` is at most 1/64.
  The same 1/64 for every `n` (the bound does not decay; nothing is proved about decay), far
  from any whole-cipher target; not a security claim. NOT proved for the 51 nontrivial `γ` in
  `v10Sym` (`FullCipher.not_col_v10Sym`: this column route cannot give it there). Nothing
  about the real PassKey schedule.

  Notation: `x = permDeck π`, `δ = γ⁻¹ * β`, "`δ` moves `s` cards" is `δ.support.card = s`,
  `q = stemPerm x * (stemPerm (β·x))⁻¹` (`StemPosition.conj_of_stem_rel`: `π⁻¹ δ π = q` on
  every deck counted by `dpFCount β γ`).

  Proved:
  * `ratio_eq_ratioQ`, the general ratio formula: if the row amounts of `m`, `m'` are `T`, `T'`
    (residues mod 13), then `stemPerm m * (stemPerm m')⁻¹ = ratioQ T T' E` with
    `E = colDiff (colAmts m') (colAmts m)` (column amounts' differences mod 4); `ratioQ T T' E`
    is `seatPerm (rowNat T) (colNat E) * (seatPerm (rowNat T') 0)⁻¹` (`StemPosition.seatPerm`;
    `seatMap_shift`: a column rotation by `s` is the unrotated seat map read at `srcRow s`).
  * The cycle-representative bound `card_conjSet_le_reps`: for all `δ q`,
    `#{π | π⁻¹ δ π = q} ≤ s^⌊s/2⌋ · (52 − s)!` with `s = δ.support.card`. Proved directly
    (no centralizer lemmas): `reps q`, the least card of each `q`-cycle in `q.support`;
    `exists_rep` every moved card is `q^k r` for a representative `r`; `apply_rep_not_rep`,
    `two_mul_card_reps_le` `q` maps representatives to moved non-representatives, so
    `2 · #reps ≤ #q.support`; `#q.support = s` (Mathlib's `Equiv.Perm.card_support_conj`);
    `π` is determined on `q.support` by its values at the representatives (Mathlib's
    `conj_pow`), each a card `δ` moves, and `card_agree_le` bounds the rest.
  * `card_agree_eq`: exactly `C(n, b) · (|α| − 1)^(n − b)` functions `Fin n → α` agree with a
    given `g` in exactly `b` places (induction on `n`). `card_zR_eq`, `card_zC_eq`: its two
    instances, `T' : Fin 4 → Fin 13` agreeing with `T` in `a` rows, `E : Fin 13 → Fin 4` zero
    in `b` columns.
  * `card_params`: for each `T`, `paramCount s` pairs `(T', E)` have `52 − zR · zC = s`;
    `paramCount_check` (`decide`, about a second): `64 · 13^4 · paramCount s · s^⌊s/2⌋ ·
    (52 − s)! ≤ 52!` for every `s` from 8 to 52 (largest ratio about 0.173, at `s = 8`).
  * `mem_ratioCell`, `dpFCount_le_union`: every counted deck lies in the cell of its own
    `(T, T', E)`, whose support is `52 − zR · zC` (`StemPosition.card_moved_eq`, through
    `zRows_eq_zR`, `zCols_eq_zC`), so `dpFCount β γ ≤ 13^4 · paramCount s · s^⌊s/2⌋ · (52 − s)!`.
  * `dpFCount_le_of_support_ge_eight`: if `δ` moves at least 8 cards,
    `64 · dpFCount β γ ≤ 52!`.
  * `dpFCount_le_of_ne`: `64 · dpFCount β γ ≤ 52!` for EVERY `β ≠ γ` (supports 4 and 1–7 from
    `StemSupportFour`). `dpFCount_col_le_64`: the column bound, `64 · dpFCount β γ ≤ 52!` for
    every `β ≠ 1` when `γ` is outside `v10Sym` (the diagonal is
    `FullCipher.dpFCount_self_le_64`). `fullDiffCount_le_64`: the full-cipher statement above,
    from `FullCipher.fullDiffCount_le_of_col`, with no remaining hypothesis.

  Not proved, and limits:
  * `γ` in `v10Sym` (the column route fails there; `not_col_v10Sym`).
  * Any bound below 1/64, any bound that decays in `n`, any mix-round (GridCycle) one-round
    bound such as the roadmap's B1 `dp1_le`, the real key schedule.
  * About the final no-mix round's stem; the mix rounds enter only through the Markov
    reduction of `FullCipher`.
-/

namespace DoubleDeal.Security.StemUnion

open DoubleDeal Relabel Finset StemPosition StemCoupling StemSupportFour

/-! ## The ratio of two position maps, in general -/

/-- Row amounts given mod 13, as natural numbers. -/
def rowNat (T : Fin 4 → Fin 13) : Fin 4 → Nat := fun r => (T r).val

/-- Column amounts given mod 4, as natural numbers. -/
def colNat (E : Fin 13 → Fin 4) : Fin 13 → Nat := fun j => (E j).val

/-- The ratio for row amounts `T`, `T'` (mod 13) and column-amount difference `E` (mod 4):
    `seatPerm (rowNat T) (colNat E) * (seatPerm (rowNat T') 0)⁻¹`. -/
noncomputable def ratioQ (T T' : Fin 4 → Fin 13) (E : Fin 13 → Fin 4) : Equiv.Perm (Fin 52) :=
  seatPerm (rowNat T) (colNat E) * (seatPerm (rowNat T') fun _ => 0)⁻¹

theorem srcRow_zero (r : Fin 4) (j : Fin 13) : srcRow (fun _ => 0) r j = r := by
  apply Fin.ext
  have := r.isLt
  simp only [srcRow]
  omega

/-- (PROVED) A column rotation by `s` is the seat map with no column rotation, read at the
    source row `srcRow s r j`. -/
theorem seatMap_shift (t : Fin 4 → Nat) (s : Fin 13 → Nat) (r : Fin 4) (j : Fin 13) :
    seatMap t s (r, j) = seatMap t (fun _ => 0) (srcRow s r j, j) := by
  simp only [seatMap, srcRow_zero]

theorem srcRow_srcRow (s s' : Fin 13 → Nat) (r : Fin 4) (j : Fin 13) :
    srcRow (colNat (colDiff s' s)) (srcRow s' r j) j = srcRow s r j := by
  apply Fin.ext
  have := r.isLt
  simp only [srcRow, colNat, colDiff]
  omega

/-- (PROVED) The general ratio formula: if the row amounts of the packets `m`, `m'` are `T`,
    `T'` (as residues mod 13), the ratio of their position maps is
    `ratioQ T T' (colDiff (colAmts m') (colAmts m))`: it depends on the amounts only through
    `T`, `T'` and the column amounts' differences mod 4. -/
theorem ratio_eq_ratioQ (m m' : Fin 52 → Nat) (T T' : Fin 4 → Fin 13)
    (hT : ∀ r, rowAmts m r = (T r).val) (hT' : ∀ r, rowAmts m' r = (T' r).val) :
    stemPerm m * (stemPerm m')⁻¹ = ratioQ T T' (colDiff (colAmts m') (colAmts m)) := by
  have eT : rowAmts m = rowNat T := funext hT
  have eT' : rowAmts m' = rowNat T' := funext hT'
  refine Equiv.ext fun k => ?_
  obtain ⟨k0, rfl⟩ : ∃ k0, stemPerm m' k0 = k := ⟨(stemPerm m')⁻¹ k, by simp⟩
  rcases hp : inSeat k0 with ⟨r, j⟩
  obtain ⟨k1, hk1⟩ := inSeat_bijective.2 (srcRow (colAmts m') r j, j)
  have e1 : stemPerm m' k0 = seatPerm (rowNat T') (fun _ => 0) k1 := by
    rw [stemPerm_apply, seatPerm_apply]
    unfold stemPos stemPosOf
    rw [eT', hk1, hp, seatMap_shift]
  simp only [ratioQ, Equiv.Perm.mul_apply, Equiv.Perm.inv_apply_self]
  rw [e1, Equiv.Perm.inv_apply_self, stemPerm_apply, seatPerm_apply]
  unfold stemPos stemPosOf
  rw [eT, hk1, hp, seatMap_shift (rowNat T) (colNat _), srcRow_srcRow, ← seatMap_shift]


/-! ## Decks with a prescribed conjugate: one card per cycle -/

/-- The cards of `q.support` that are the least card of their `q`-cycle. -/
noncomputable def reps (q : Equiv.Perm (Fin 52)) : Finset (Fin 52) :=
  q.support.filter fun x => ∀ k ∈ range (orderOf q), x ≤ (q ^ k) x

theorem pow_mod_apply (q : Equiv.Perm (Fin 52)) (n : ℕ) (x : Fin 52) :
    (q ^ (n % orderOf q)) x = (q ^ n) x := by
  rw [pow_mod_orderOf]

/-- (PROVED) Every moved card is `q^k r` for a representative `r`. -/
theorem exists_rep (q : Equiv.Perm (Fin 52)) {y : Fin 52} (hy : y ∈ q.support) :
    ∃ r ∈ reps q, ∃ k : ℕ, (q ^ k) r = y := by
  have hpos := orderOf_pos q
  let O := (range (orderOf q)).image fun k => (q ^ k) y
  have hne : O.Nonempty := ⟨y, mem_image.mpr ⟨0, mem_range.mpr hpos, rfl⟩⟩
  obtain ⟨j, hj, hjr⟩ := mem_image.mp (O.min'_mem hne)
  refine ⟨O.min' hne, ?_, orderOf q - j, ?_⟩
  · simp only [reps, mem_filter]
    refine ⟨?_, fun k _ => ?_⟩
    · rw [← hjr]
      exact (Equiv.Perm.pow_apply_mem_support).mpr hy
    · apply O.min'_le
      rw [← hjr, ← Equiv.Perm.mul_apply, ← pow_add, ← pow_mod_apply]
      exact mem_image.mpr ⟨(k + j) % orderOf q, mem_range.mpr (Nat.mod_lt _ hpos), rfl⟩
  · rw [← hjr, ← Equiv.Perm.mul_apply, ← pow_add, Nat.sub_add_cancel (mem_range.mp hj).le,
      pow_orderOf_eq_one]
    rfl

/-- (PROVED) `q` sends each representative to a moved card that is not a representative. -/
theorem apply_rep_not_rep (q : Equiv.Perm (Fin 52)) {r : Fin 52} (hr : r ∈ reps q) :
    q r ∈ q.support \ reps q := by
  simp only [reps, mem_filter] at hr
  obtain ⟨hs, hmin⟩ := hr
  have hpos := orderOf_pos q
  have h1 : orderOf q ≠ 1 := by
    intro e
    rw [orderOf_eq_one_iff] at e
    subst e
    exact (Equiv.Perm.mem_support.mp hs) rfl
  rw [mem_sdiff]
  refine ⟨Equiv.Perm.apply_mem_support.mpr hs, fun hq => ?_⟩
  simp only [reps, mem_filter] at hq
  have a := hmin 1 (mem_range.mpr (by omega))
  have b := hq.2 (orderOf q - 1) (mem_range.mpr (by omega))
  rw [← Equiv.Perm.mul_apply, ← pow_succ, Nat.sub_add_cancel hpos, pow_orderOf_eq_one] at b
  rw [pow_one] at a
  exact (Equiv.Perm.mem_support.mp hs) (le_antisymm b a)

/-- (PROVED) There are at most half as many representatives as moved cards. -/
theorem two_mul_card_reps_le (q : Equiv.Perm (Fin 52)) : 2 * (reps q).card ≤ q.support.card := by
  have hsub : reps q ∪ (reps q).image q ⊆ q.support := by
    intro x hx
    rcases mem_union.mp hx with h | h
    · exact (mem_filter.mp h).1
    · obtain ⟨r, hr, rfl⟩ := mem_image.mp h
      exact (mem_sdiff.mp (apply_rep_not_rep q hr)).1
  have hdisj : Disjoint (reps q) ((reps q).image q) := by
    rw [disjoint_left]
    intro x hx hx'
    obtain ⟨r, hr, rfl⟩ := mem_image.mp hx'
    exact (mem_sdiff.mp (apply_rep_not_rep q hr)).2 hx
  have := card_le_card hsub
  rw [card_union_of_disjoint hdisj, card_image_of_injective _ q.injective] at this
  omega

/-- (PROVED) The cycle-representative bound: for every `δ q`, at most
    `s^⌊s/2⌋ · (52 − s)!` decks `π` have `π⁻¹ δ π = q`, where `s` is the number of cards `δ`
    moves. (`π` on the moved positions of `q` is determined by its values at one position per
    cycle of `q`, at most `s/2` of them, each a card `δ` moves; the rest by `card_agree_le`.) -/
theorem card_conjSet_le_reps (δ q : Equiv.Perm (Fin 52)) :
    (conjSet δ q).card ≤
      δ.support.card ^ (δ.support.card / 2) * Nat.factorial (52 - δ.support.card) := by
  rcases (conjSet δ q).eq_empty_or_nonempty with h0 | ⟨π0, h0⟩
  · rw [h0, card_empty]; exact Nat.zero_le _
  simp only [conjSet, mem_filter, mem_univ, true_and] at h0
  have hs : q.support.card = δ.support.card := by
    have e := Equiv.Perm.card_support_conj (σ := π0⁻¹) (τ := δ)
    rwa [inv_inv, h0] at e
  have hpow : ∀ {π : Equiv.Perm (Fin 52)}, π⁻¹ * δ * π = q → ∀ (k : ℕ) (y : Fin 52),
      π ((q ^ k) y) = (δ ^ k) (π y) := by
    intro π h k y
    have e := conj_pow (a := π⁻¹) (b := δ) (i := k)
    rw [inv_inv, h] at e
    rw [e]
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.apply_inv_self]
  let F : Equiv.Perm (Fin 52) → (reps q → Fin 52) := fun π r => π r.1
  have hfib : ∀ v ∈ (conjSet δ q).image F,
      ((conjSet δ q).filter fun π => F π = v).card ≤ Nat.factorial (52 - δ.support.card) := by
    intro v hv
    obtain ⟨π1, hπ1, rfl⟩ := mem_image.mp hv
    simp only [conjSet, mem_filter, mem_univ, true_and] at hπ1
    rw [← hs]
    refine (card_le_card fun π hπ => ?_).trans (card_agree_le q.support π1)
    simp only [conjSet, mem_filter, mem_univ, true_and] at hπ ⊢
    obtain ⟨hπ, eF⟩ := hπ
    intro y hy
    obtain ⟨r, hr, k, rfl⟩ := exists_rep q hy
    have er : π r = π1 r := congrFun eF ⟨r, hr⟩
    rw [hpow hπ, hpow hπ1, er]
  have himg : (conjSet δ q).image F ⊆ Fintype.piFinset fun _ => δ.support := by
    intro v hv
    obtain ⟨π, hπ, rfl⟩ := mem_image.mp hv
    simp only [conjSet, mem_filter, mem_univ, true_and] at hπ
    rw [Fintype.mem_piFinset]
    intro r
    have hr := (mem_filter.mp r.2).1
    rw [Equiv.Perm.mem_support] at hr ⊢
    show δ (π r.1) ≠ π r.1
    rw [conj_apply hπ]
    exact fun e => hr (π.injective e)
  have hcard : (Fintype.piFinset fun _ : reps q => δ.support).card =
      δ.support.card ^ (reps q).card := by
    rw [Fintype.card_piFinset, prod_const, card_univ, Fintype.card_coe]
  have hR := two_mul_card_reps_le q
  rw [hs] at hR
  have hpow : δ.support.card ^ (reps q).card ≤ δ.support.card ^ (δ.support.card / 2) := by
    rcases Nat.eq_zero_or_pos δ.support.card with e | e
    · have : (reps q).card = 0 := by omega
      rw [this, e]
    · exact Nat.pow_le_pow_right e (by omega)
  calc (conjSet δ q).card ≤ Nat.factorial (52 - δ.support.card) * ((conjSet δ q).image F).card :=
        card_le_mul_card_image _ _ hfib
    _ ≤ Nat.factorial (52 - δ.support.card) * δ.support.card ^ (δ.support.card / 2) :=
        Nat.mul_le_mul_left _ (((card_le_card himg).trans hcard.le).trans hpow)
    _ = _ := Nat.mul_comm _ _

/-! ## Counting functions by the number of places they agree with a given one -/

theorem card_agree_cons {α : Type} [DecidableEq α] {n : ℕ} (a : α) (f : Fin n → α)
    (g : Fin (n + 1) → α) :
    (univ.filter fun j => (Fin.cons a f : Fin (n + 1) → α) j = g j).card =
      (if a = g 0 then 1 else 0) + (univ.filter fun j : Fin n => f j = g j.succ).card := by
  rw [card_filter, card_filter, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

/-- (PROVED) Exactly `C(n, b) · (|α| − 1)^(n − b)` functions `Fin n → α` agree with a given
    `g` in exactly `b` places. -/
theorem card_agree_eq {α : Type} [Fintype α] [DecidableEq α] :
    ∀ (n : ℕ) (g : Fin n → α) (b : ℕ),
      (univ.filter fun f : Fin n → α => (univ.filter fun j => f j = g j).card = b).card =
        n.choose b * (Fintype.card α - 1) ^ (n - b) := by
  intro n
  induction n with
  | zero =>
    intro g b
    rcases b with _ | b
    · simp
    · simp
  | succ n ih =>
    intro g b
    have e1 : (univ.filter fun f : Fin (n + 1) → α =>
        (univ.filter fun j => f j = g j).card = b).card =
        (univ.filter fun p : α × (Fin n → α) =>
          (if p.1 = g 0 then 1 else 0) +
            (univ.filter fun j : Fin n => p.2 j = g j.succ).card = b).card := by
      refine card_nbij' (fun f => (f 0, Fin.tail f)) (fun p => Fin.cons p.1 p.2) ?_ ?_ ?_ ?_
      · intro f hf
        simp only [mem_filter, mem_univ, true_and] at hf ⊢
        rw [← hf, ← card_agree_cons, Fin.cons_self_tail]
      · intro p hp
        simp only [mem_filter, mem_univ, true_and] at hp ⊢
        rw [card_agree_cons]
        exact hp
      · intro f _
        exact Fin.cons_self_tail f
      · intro p _
        simp only [Fin.cons_zero, Fin.tail_cons]
    rw [e1, card_filter, Fintype.sum_prod_type, Fintype.sum_eq_add_sum_compl (g 0)]
    simp only [if_true]
    have e2 : ∀ a ∈ ({g 0}ᶜ : Finset α),
        (∑ f : Fin n → α, if (if a = g 0 then 1 else 0) +
          (univ.filter fun j : Fin n => f j = g j.succ).card = b then 1 else 0) =
        n.choose b * (Fintype.card α - 1) ^ (n - b) := by
      intro a ha
      have hne : a ≠ g 0 := by simpa using ha
      simp only [hne, if_false, zero_add]
      rw [← card_filter]
      exact ih (fun j => g j.succ) b
    rw [sum_congr rfl e2, sum_const, card_compl, card_singleton, smul_eq_mul, ← card_filter]
    rcases b with _ | c
    · have e3 : (univ.filter fun f : Fin n → α =>
          1 + (univ.filter fun j : Fin n => f j = g j.succ).card = 0) = ∅ :=
        filter_false_of_mem fun f _ => by rw [Nat.add_comm]; exact Nat.succ_ne_zero _
      rw [e3, card_empty, zero_add, Nat.choose_zero_right, Nat.choose_zero_right, Nat.sub_zero,
        Nat.sub_zero, pow_succ]
      ring
    · have e3 : (univ.filter fun f : Fin n → α =>
          1 + (univ.filter fun j : Fin n => f j = g j.succ).card = c + 1) =
          (univ.filter fun f : Fin n → α =>
          (univ.filter fun j : Fin n => f j = g j.succ).card = c) :=
        filter_congr fun f _ => by rw [Nat.add_comm]; exact Nat.add_right_cancel_iff
      rw [e3, ih (fun j => g j.succ) c, Nat.choose_succ_succ, Nat.add_sub_add_right]
      rcases Nat.lt_or_ge c n with hc | hc
      · rw [show n - c = (n - (c + 1)) + 1 by
          rw [Nat.sub_add_eq, Nat.sub_add_cancel (Nat.sub_pos_of_lt hc)], pow_succ]
        ring
      · rw [Nat.choose_eq_zero_of_lt (Nat.lt_succ_of_le hc)]
        ring

/-! ## Counting the ratio parameters by support -/

/-- The number of rows where `T'` agrees with `T`: `StemPosition.zRows` stated on the row
    amounts as parameters (`zRows_eq_zR`), so that the cells can be counted. -/
def zR (T T' : Fin 4 → Fin 13) : ℕ := (univ.filter fun r => T' r = T r).card

/-- The number of columns where `E` is zero: `StemPosition.zCols` stated on the
    column-amount difference as a parameter (`zCols_eq_zC`). -/
def zC (E : Fin 13 → Fin 4) : ℕ := (univ.filter fun j => E j = 0).card

theorem zR_lt (T T' : Fin 4 → Fin 13) : zR T T' < 5 :=
  Nat.lt_succ_of_le ((card_filter_le _ _).trans (by simp))

theorem zC_lt (E : Fin 13 → Fin 4) : zC E < 14 :=
  Nat.lt_succ_of_le ((card_filter_le _ _).trans (by simp))

theorem sum_fiber_range {X : Type} [Fintype X] (g : X → ℕ) (n : ℕ) (hg : ∀ x, g x < n)
    (h : ℕ → ℕ) :
    ∑ x, h (g x) = ∑ b ∈ range n, (univ.filter fun x => g x = b).card * h b := by
  rw [← sum_fiberwise_of_maps_to (s := univ) (t := range n) (g := g)
    (fun x _ => mem_range.mpr (hg x))]
  refine sum_congr rfl fun b _ => ?_
  rw [sum_congr rfl fun x hx => by rw [(mem_filter.mp hx).2], sum_const, smul_eq_mul]

/-- The number of parameters `(T', E)` (for a fixed `T`) with `52 − zR · zC = s`:
    `Σ_{a ≤ 4} C(4,a) 12^(4−a) Σ_{b ≤ 13} C(13,b) 3^(13−b) [52 − ab = s]`. -/
def paramCount (s : ℕ) : ℕ :=
  ∑ a ∈ range 5, Nat.choose 4 a * 12 ^ (4 - a) *
    ∑ b ∈ range 14, Nat.choose 13 b * 3 ^ (13 - b) * (if 52 - a * b = s then 1 else 0)

theorem card_zC_eq (b : ℕ) :
    (univ.filter fun E : Fin 13 → Fin 4 => zC E = b).card = Nat.choose 13 b * 3 ^ (13 - b) := by
  have := card_agree_eq 13 (fun _ : Fin 13 => (0 : Fin 4)) b
  simpa [zC] using this

theorem card_zR_eq (T : Fin 4 → Fin 13) (a : ℕ) :
    (univ.filter fun T' : Fin 4 → Fin 13 => zR T T' = a).card =
      Nat.choose 4 a * 12 ^ (4 - a) := by
  have := card_agree_eq 4 T a
  simpa [zR] using this

/-- (PROVED) For each `T`, `paramCount s` pairs `(T', E)` give support `52 − zR · zC = s`. -/
theorem card_params (T : Fin 4 → Fin 13) (s : ℕ) :
    ∑ T' : Fin 4 → Fin 13, ∑ E : Fin 13 → Fin 4,
      (if 52 - zR T T' * zC E = s then 1 else 0) = paramCount s := by
  have hE : ∀ a, ∑ E : Fin 13 → Fin 4, (if 52 - a * zC E = s then 1 else 0) =
      ∑ b ∈ range 14, Nat.choose 13 b * 3 ^ (13 - b) * (if 52 - a * b = s then 1 else 0) := by
    intro a
    rw [sum_fiber_range zC 14 zC_lt (fun b => if 52 - a * b = s then 1 else 0)]
    refine sum_congr rfl fun b _ => ?_
    rw [card_zC_eq]
  rw [sum_congr rfl fun T' _ => hE (zR T T'),
    sum_fiber_range (zR T) 5 (zR_lt T) (fun a => ∑ b ∈ range 14,
      Nat.choose 13 b * 3 ^ (13 - b) * (if 52 - a * b = s then 1 else 0))]
  refine sum_congr rfl fun a _ => ?_
  rw [card_zR_eq]

/-- (PROVED) The arithmetic: for every support `s` from 8 to 52,
    `64 · 13^4 · paramCount s · s^⌊s/2⌋ · (52 − s)! ≤ 52!`. (`decide`, about a second; the
    largest ratio is about 0.173, at `s = 8`.) -/
theorem paramCount_check : ∀ s, s < 53 → 8 ≤ s →
    64 * (13 ^ 4 * paramCount s * (s ^ (s / 2) * Nat.factorial (52 - s))) ≤
      Nat.factorial 52 := by
  decide

/-! ## The union bound -/

/-- The index of a cell: row amounts `T` of `x`, `T'` of `β·x` (mod 13), and the column-amount
    difference `E` (mod 4). -/
abbrev CellIndex := (Fin 4 → Fin 13) × (Fin 4 → Fin 13) × (Fin 13 → Fin 4)

/-- The decks with conjugate `ratioQ T T' E`, kept only when `52 − zR T T' · zC E = s`. -/
noncomputable def ratioCell (δ : Equiv.Perm (Fin 52)) (s : ℕ) (i : CellIndex) :
    Finset (Equiv.Perm (Fin 52)) :=
  if 52 - zR i.1 i.2.1 * zC i.2.2 = s then conjSet δ (ratioQ i.1 i.2.1 i.2.2) else ∅

theorem colDiff_eq_zero_iff (s s' : Fin 13 → Nat) (j : Fin 13) :
    colDiff s s' j = 0 ↔ s j % 4 = s' j % 4 := by
  rw [Fin.ext_iff]
  simp only [colDiff, Fin.val_zero]
  omega

theorem fin13_eq_iff (u v : Nat) (hu : u < 13) (hv : v < 13) :
    (⟨v, hv⟩ : Fin 13) = ⟨u, hu⟩ ↔ u % 13 = v % 13 := by
  rw [Fin.mk.injEq, Nat.mod_eq_of_lt hu, Nat.mod_eq_of_lt hv]
  exact eq_comm

/-- `zRows` of two packets is `zR` of their row amounts (as residues mod 13). -/
theorem zRows_eq_zR (m m' : Fin 52 → Nat) :
    zRows m m' = zR (fun r => ⟨rowAmts m r, rowAmts_lt _ r⟩)
      (fun r => ⟨rowAmts m' r, rowAmts_lt _ r⟩) := by
  unfold zRows zR
  exact congrArg Finset.card (filter_congr fun r _ => (fin13_eq_iff _ _ _ _).symm)

/-- `zCols` of two packets is `zC` of the differences of their column amounts mod 4. -/
theorem zCols_eq_zC (m m' : Fin 52 → Nat) :
    zCols m m' = zC (colDiff (colAmts m') (colAmts m)) := by
  unfold zCols zC
  exact congrArg Finset.card (filter_congr fun j _ => by rw [colDiff_eq_zero_iff]; exact eq_comm)

/-- (PROVED) Every deck counted by `dpFCount β γ` lies in the cell of its own amounts. -/
theorem mem_ratioCell {β γ π : Equiv.Perm (Fin 52)}
    (h : unkeyedNoMix (rel β (permDeck π)) = rel γ (unkeyedNoMix (permDeck π))) :
    ∃ i, π ∈ ratioCell (γ⁻¹ * β) (γ⁻¹ * β).support.card i := by
  have e := ratio_eq_ratioQ (permDeck π) (rel β (permDeck π))
    (fun r => ⟨rowAmts (permDeck π) r, rowAmts_lt _ r⟩)
    (fun r => ⟨rowAmts (rel β (permDeck π)) r, rowAmts_lt _ r⟩) (fun _ => rfl) (fun _ => rfl)
  have hc := conj_of_stem_rel h
  have hs := card_moved_eq h
  rw [zRows_eq_zR, zCols_eq_zC] at hs
  refine ⟨((fun r => ⟨rowAmts (permDeck π) r, rowAmts_lt _ r⟩),
    (fun r => ⟨rowAmts (rel β (permDeck π)) r, rowAmts_lt _ r⟩),
    colDiff (colAmts (rel β (permDeck π))) (colAmts (permDeck π))), ?_⟩
  unfold ratioCell
  dsimp only
  rw [if_pos]
  · simp only [conjSet, mem_filter, mem_univ, true_and]
    rw [← e, hc]
    group
  · exact hs.symm

theorem card_ratioCell_le (δ : Equiv.Perm (Fin 52)) (i : CellIndex) :
    (ratioCell δ δ.support.card i).card ≤
      (if 52 - zR i.1 i.2.1 * zC i.2.2 = δ.support.card then 1 else 0) *
        (δ.support.card ^ (δ.support.card / 2) * Nat.factorial (52 - δ.support.card)) := by
  unfold ratioCell
  split_ifs
  · rw [one_mul]; exact card_conjSet_le_reps δ _
  · simp

/-- (PROVED) The union bound: `dpFCount β γ ≤ 13^4 · paramCount s · s^⌊s/2⌋ · (52 − s)!` with
    `s` the number of cards `γ⁻¹ * β` moves. -/
theorem dpFCount_le_union (β γ : Relabel) :
    FullCipher.dpFCount β γ ≤
      13 ^ 4 * paramCount (γ⁻¹ * β).support.card *
        ((γ⁻¹ * β).support.card ^ ((γ⁻¹ * β).support.card / 2) *
          Nat.factorial (52 - (γ⁻¹ * β).support.card)) := by
  have h1 : FullCipher.dpFCount β γ ≤
      ∑ i : CellIndex, (ratioCell (γ⁻¹ * β) (γ⁻¹ * β).support.card i).card := by
    unfold FullCipher.dpFCount Differential.dpCount
    exact card_le_sum_of_mem _ _ fun π hπ => mem_ratioCell (mem_filter.mp hπ).2
  refine h1.trans ((sum_le_sum fun i _ => card_ratioCell_le (γ⁻¹ * β) i).trans (le_of_eq ?_))
  generalize (γ⁻¹ * β).support.card = s
  generalize s ^ (s / 2) * Nat.factorial (52 - s) = B
  rw [← sum_mul, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  rw [sum_congr rfl fun T _ => card_params T s, sum_const, card_univ, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_fin, smul_eq_mul]

/-- (PROVED; the support-≥ 8 case of the off-diagonal stem bound) If `γ⁻¹ * β` moves at least 8 cards, then
    `64 · dpFCount β γ ≤ 52!`. -/
theorem dpFCount_le_of_support_ge_eight (β γ : Relabel)
    (h8 : 8 ≤ (γ⁻¹ * β).support.card) :
    64 * FullCipher.dpFCount β γ ≤ Nat.factorial 52 := by
  have h52 : (γ⁻¹ * β).support.card < 53 :=
    Nat.lt_succ_of_le ((card_le_univ _).trans (by simp))
  exact (Nat.mul_le_mul_left 64 (dpFCount_le_union β γ)).trans
    (paramCount_check _ h52 h8)

/-! ## The off-diagonal column bound and the full-cipher bound -/

/-- (PROVED) The off-diagonal stem column bound for EVERY `β ≠ γ` (no `v10Sym` condition):
    `64 · dpFCount β γ ≤ 52!`. Support 0 is `β = γ`; supports 1–3 and 5–7 count no deck;
    support 4 is `dpFCount_le_of_support_four`; supports ≥ 8 are
    `dpFCount_le_of_support_ge_eight`. -/
theorem dpFCount_le_of_ne {β γ : Relabel} (hne : β ≠ γ) :
    64 * FullCipher.dpFCount β γ ≤ Nat.factorial 52 := by
  by_cases h8 : 8 ≤ (γ⁻¹ * β).support.card
  · exact dpFCount_le_of_support_ge_eight β γ h8
  by_cases h4 : (γ⁻¹ * β).support.card = 4
  · exact dpFCount_le_of_support_four β γ h4
  have h0 : 0 < (γ⁻¹ * β).support.card :=
    Nat.pos_of_ne_zero fun e => hne (eq_of_support_zero e)
  rw [dpFCount_eq_zero_of_support_lt_eight_ne_four β γ h0 h4 (by omega)]
  exact Nat.zero_le _

/-- (PROVED) The column bound into every `γ` outside `v10Sym`: `64 · dpFCount β γ ≤ 52!` for
    every `β ≠ 1` (the hypothesis `hcol` of `FullCipher.fullDiffCount_le_of_col` with `p = 64`).
    The diagonal `β = γ` is `FullCipher.dpFCount_self_le_64`; every other `β` is
    `dpFCount_le_of_ne`. -/
theorem dpFCount_col_le_64 {γ : Relabel} (hγ : ¬ ∃ a x, γ = v10Sym a x) :
    ∀ β, β ≠ 1 → 64 * FullCipher.dpFCount β γ ≤ Nat.factorial 52 := by
  intro β _
  by_cases h : β = γ
  · subst h
    exact FullCipher.dpFCount_self_le_64 β hγ
  · exact dpFCount_le_of_ne h

/-- (PROVED) The full-cipher bound, with no remaining hypothesis: for every input difference
    `α ≠ 1`, every output difference `γ` outside `v10Sym`, every number `n` of mix rounds and
    every deck `y`, `64 · fullDiffCount α γ n y ≤ (52!)^(n+2)`, i.e. the differential
    probability of `α → γ` through `n` mix rounds and the final no-mix round is at most 1/64
    (independent uniform round keys; the same 1/64 for every `n`: the bound does not decay,
    and nothing is proved about decay). Not proved for `γ` in `v10Sym`
    (`FullCipher.not_col_v10Sym`: this column route cannot give it there). Not a security
    claim. -/
theorem fullDiffCount_le_64 {α γ : Relabel} (hα : α ≠ 1) (hγ : ¬ ∃ a x, γ = v10Sym a x)
    (n : ℕ) {y : Fin 52 → Nat} (hy : IsDeck y) :
    64 * FullCipher.fullDiffCount α γ n y ≤ Nat.factorial 52 ^ (n + 2) :=
  FullCipher.fullDiffCount_le_of_col hα γ 64 (dpFCount_col_le_64 hγ) n hy

end DoubleDeal.Security.StemUnion
