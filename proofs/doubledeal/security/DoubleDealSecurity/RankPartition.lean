/-
  The rank-partition lemma for the seat-26 condition (one step toward `PrimeNonSwapCase`,
  `CovariantNarrow.lean`; NOT the covariant round conjecture `roundBody_covariant_iff_id`,
  which stays open with its `sorry`, and NOT `PrimeNonSwapCase`, which stays open).

  Statement (`cell0Cov_rank_of_checks`, GIVEN the finite checks `RankChecks`; unconditional
  in the heavy library, `RankPartition.cell0Cov_rank`): if `Cell0Cov σ τ` (stem cell 0 of
  `σ·m` is `τ` of stem cell 0 of `m`, on every deck), then σ maps any two cards of equal
  rank to cards of equal rank. Hence so does every covariant σ
  (`covariant_rank_of_checks`). Nothing is claimed about labels (suits), about the rank map
  σ induces, or about τ.

  A. Symbolic stem facts (no computation; from `StemPosition` / `StemCoupling`):
     * `c0_eq`: stem cell 0 of any packet `d` is `d` at the seat `(ρ, rowAmts d ρ % 13)` for
       the row `ρ = srcRow (colAmts d) 0 0` (column 0 is turned only by the last column
       step; ShiftRows does not move row 0).
     * `rowAmts_eq_of_agree`: the row amounts of rows 1, 2, 3 read only rows 0, 1, 2 of the
       packet (seats `s` with `s % 4 ≠ 3`).
     * `rowAmts_zero`: row 0's amount is the v10 row turn of row 3 read after row 3's turn.
  B. `rank_eq_of_family`: for nine decks `π k i` (k, i : Fin 3) that agree outside row 3,
     whose stem cell 0 is the card at the row-0 seat `(0, col k)` (`col` injective), where
     member `(k, 1)` is member `(k, 0)` with the cards `x ≠ y` exchanged (both in row 3) and
     member `(k, 2)` agrees with member `(k, 0)` in row 3 only at `x` and `y`:
     `Cell0Cov σ τ → rank (σ x) = rank (σ y)`, for EVERY σ, τ. The σ-images of the nine decks
     share rows 0-2, so their row amounts of rows 1-3; so `σ⁻¹ τ (stem cell 0)` sits in one
     of four seats; row 3 is excluded by members 1 and 2, rows 1 and 2 by injectivity across
     the three classes; so for some class the row-0 amounts of members 0 and 1 agree mod 13,
     and the swap formula `StemCoupling.wsum_swap` gives the rank equality.
  C. `cell0Cov_rank_of_checks`: the three families of `RankPartitionLists.lean` (x = card 0,
     y = 13, 26, 39), transported to every equal-rank pair by `v10Sym`
     (`cell0Cov_mul`, `cell0Cov_self_of_commutes`).

  Write-up: `../analysis/v12-primenonswap/NOTES.md`; data: `rank_family.py`.
-/
import DoubleDealSecurity.CovariantNarrow
import DoubleDealSecurity.StemCoupling
import DoubleDealSecurity.RankPartitionLists

namespace DoubleDeal.Security.RankPartition

open DoubleDeal Relabel
open DoubleDeal.Security (permDeck isDeck_permDeck)
open DoubleDeal.Security.CovariantNarrow (Cell0Cov cell0Cov_of_covPair cell0Cov_mul cell0Cov_inv
  cell0Cov_self_of_commutes g0 g0_eq exists_v10Sym_zero)
open DoubleDeal.Security.StemPosition (stemPos stemPosOf seatMap inSeat srcRow rowAmts colAmts
  unkeyedNoMix_eq_comp)
open DoubleDeal.Security.StemCoupling (rowRead rowAmts_prev rk wt wsum rowTurnV10_cast wsum_swap
  wt_sub_ne rk_sub_ne zmod13_mul_ne cmFlat_col_injective)

/-! ## A. Symbolic stem facts -/

/-- The row of column 0 that the last column step brings to the top (seat 0). -/
def c0Row (d : Fin 52 → Nat) : Fin 4 := srcRow (colAmts d) 0 0

/-- The seat `(ρ, t ρ % 13)` of row `ρ`. -/
def rowSeat (t : Fin 4 → Nat) (ρ : Fin 4) : Fin 52 :=
  cmFlat ρ ⟨t ρ % 13, Nat.mod_lt _ (by decide)⟩

/-- (PROVED) Stem cell 0 of any packet `d` is `d` at the seat `(ρ, rowAmts d ρ % 13)` of the
    row `ρ = c0Row d`. -/
theorem c0_eq (d : Fin 52 → Nat) :
    unkeyedNoMix d 0 = d (rowSeat (rowAmts d) (c0Row d)) := by
  rw [unkeyedNoMix_eq_comp]
  show d (cmFlat (seatMap (rowAmts d) (colAmts d) (inSeat 0)).1
    (seatMap (rowAmts d) (colAmts d) (inSeat 0)).2) = _
  have h0 : inSeat 0 = (0, 0) := rfl
  rw [h0]
  unfold rowSeat c0Row seatMap
  congr 2
  apply Fin.ext
  simp only [Fin.val_zero, Nat.zero_add]
  exact Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide))

/-- (PROVED) `rowRead d ρ a` reads only row `ρ` of `d`. -/
theorem rowRead_congr {d d' : Fin 52 → Nat} {ρ : Fin 4}
    (h : ∀ c : Fin 13, d (cmFlat ρ c) = d' (cmFlat ρ c)) (a : Nat) :
    rowRead d ρ a = rowRead d' ρ a := funext fun _ => h _

/-- Two packets agree outside row 3. -/
def AgreeOff3 (d d' : Fin 52 → Nat) : Prop := ∀ s : Fin 52, (cmRow s).val ≠ 3 → d s = d' s

theorem agree_row {d d' : Fin 52 → Nat} (h : AgreeOff3 d d') {ρ : Fin 4} (hρ : ρ.val ≠ 3)
    (c : Fin 13) : d (cmFlat ρ c) = d' (cmFlat ρ c) :=
  h _ (by rw [(cm_cmFlat ρ c).1]; exact hρ)

/-- (PROVED) The row amounts of rows 1, 2, 3 read only rows 0, 1, 2. -/
theorem rowAmts_eq_of_agree {d d' : Fin 52 → Nat} (h : AgreeOff3 d d') :
    rowAmts d 1 = rowAmts d' 1 ∧ rowAmts d 2 = rowAmts d' 2 ∧ rowAmts d 3 = rowAmts d' 3 := by
  have e1 : rowAmts d 1 = rowAmts d' 1 := by
    rw [rowAmts_prev d 1, rowAmts_prev d' 1]
    show rowTurnV10 (rowRead d 0 0) = rowTurnV10 (rowRead d' 0 0)
    rw [rowRead_congr (agree_row h (by decide))]
  have e2 : rowAmts d 2 = rowAmts d' 2 := by
    rw [rowAmts_prev d 2, rowAmts_prev d' 2]
    show rowTurnV10 (rowRead d 1 (rowAmts d 1)) = rowTurnV10 (rowRead d' 1 (rowAmts d' 1))
    rw [e1, rowRead_congr (agree_row h (by decide))]
  have e3 : rowAmts d 3 = rowAmts d' 3 := by
    rw [rowAmts_prev d 3, rowAmts_prev d' 3]
    show rowTurnV10 (rowRead d 2 (rowAmts d 2)) = rowTurnV10 (rowRead d' 2 (rowAmts d' 2))
    rw [e2, rowRead_congr (agree_row h (by decide))]
  exact ⟨e1, e2, e3⟩

/-- (PROVED) Row 0's amount is the v10 row turn of row 3, read after row 3's own turn. -/
theorem rowAmts_zero (d : Fin 52 → Nat) :
    rowAmts d 0 = rowTurnV10 (rowRead d 3 (rowAmts d 3)) :=
  rowAmts_prev d 0

/-! ## B. One family of nine decks -/

theorem rel_permDeck' (σ π : Relabel) : rel σ (permDeck π) = permDeck (σ * π) :=
  funext fun i => app_fin σ (π i)

theorem perm_swap_apply (σ : Relabel) (x y z : Fin 52) :
    σ (Equiv.swap x y z) = Equiv.swap (σ x) (σ y) (σ z) := by
  by_cases hx : z = x
  · subst hx; rw [Equiv.swap_apply_left, Equiv.swap_apply_left]
  · by_cases hy : z = y
    · subst hy; rw [Equiv.swap_apply_right, Equiv.swap_apply_right]
    · rw [Equiv.swap_apply_of_ne_of_ne hx hy,
        Equiv.swap_apply_of_ne_of_ne (fun e => hx (σ.injective e)) (fun e => hy (σ.injective e))]

theorem rowSeat_row (t : Fin 4 → Nat) (ρ : Fin 4) : cmRow (rowSeat t ρ) = ρ := (cm_cmFlat _ _).1

/-- The hypotheses on a family of nine decks `π k i` (`k`: class, `i`: member). -/
structure Family (π : Fin 3 → Fin 3 → Relabel) (col : Fin 3 → Fin 13) (x y : Fin 52) : Prop where
  agree : ∀ k i s, (cmRow s).val ≠ 3 → π k i s = π 0 0 s
  col_inj : Function.Injective col
  c0 : ∀ k i, unkeyedNoMix (permDeck (π k i)) 0 = (π k 0 (cmFlat 0 (col k))).val
  swap1 : ∀ k (c : Fin 13), π k 1 (cmFlat 3 c) = Equiv.swap x y (π k 0 (cmFlat 3 c))
  hasX : ∀ k, ∃ c : Fin 13, π k 0 (cmFlat 3 c) = x
  hasY : ∀ k, ∃ c : Fin 13, π k 0 (cmFlat 3 c) = y
  ne : x ≠ y
  member2 : ∀ k (c : Fin 13), π k 2 (cmFlat 3 c) = π k 0 (cmFlat 3 c) →
    π k 0 (cmFlat 3 c) = x ∨ π k 0 (cmFlat 3 c) = y

section family

variable {π : Fin 3 → Fin 3 → Relabel} {col : Fin 3 → Fin 13} {x y : Fin 52}

/-- Two members showing the same card at seats `(ρ, c)` and `(ρ', c')`, `ρ' ≠ 3`, show it at
    the same seat. -/
theorem Family.seat_eq (hf : Family π col x y) {k i k' i' : Fin 3} {ρ ρ' : Fin 4}
    {c c' : Fin 13} (hρ' : ρ'.val ≠ 3) (h : π k i (cmFlat ρ c) = π k' i' (cmFlat ρ' c')) :
    ρ = ρ' ∧ c = c' := by
  have hs : (cmRow (cmFlat ρ' c')).val ≠ 3 := by rw [(cm_cmFlat ρ' c').1]; exact hρ'
  rw [hf.agree k' i' _ hs, ← hf.agree k i _ hs] at h
  have e := (π k i).injective h
  exact ⟨by simpa [(cm_cmFlat ρ c).1, (cm_cmFlat ρ' c').1] using congrArg cmRow e,
    by simpa [(cm_cmFlat ρ c).2, (cm_cmFlat ρ' c').2] using congrArg cmCol e⟩

/-- (PROVED) For every σ, τ with the seat-26 condition, a family forces
    `rank (σ x) = rank (σ y)`. -/
theorem rank_eq_of_family (hf : Family π col x y) {σ τ : Relabel} (hc : Cell0Cov σ τ) :
    rank (σ x).val = rank (σ y).val := by
  -- the σ-images of the family decks
  set D : Fin 3 → Fin 3 → (Fin 52 → Nat) := fun k i => permDeck (σ * π k i) with hD
  have hagD : ∀ k i, AgreeOff3 (D k i) (D 0 0) := fun k i s hs => by
    simp only [hD, permDeck, Equiv.Perm.mul_apply, hf.agree k i s hs]
  set T := rowAmts (D 0 0) with hT
  have hTr : ∀ k i, rowAmts (D k i) 1 = T 1 ∧ rowAmts (D k i) 2 = T 2 ∧
      rowAmts (D k i) 3 = T 3 := fun k i => rowAmts_eq_of_agree (hagD k i)
  -- the card σ⁻¹ τ (stem cell 0)
  set R : Fin 3 → Fin 52 := fun k => π k 0 (cmFlat 0 (col k)) with hR
  set e : Fin 3 → Fin 52 := fun k => σ.symm (τ (R k)) with he
  set ρ : Fin 3 → Fin 3 → Fin 4 := fun k i => c0Row (D k i) with hρ
  set seat : Fin 3 → Fin 3 → Fin 52 := fun k i => rowSeat (rowAmts (D k i)) (ρ k i) with hseat
  have key : ∀ k i, π k i (seat k i) = e k := by
    intro k i
    have h1 := hc (permDeck (π k i)) (isDeck_permDeck _)
    rw [hf.c0 k i, rel_permDeck', c0_eq] at h1
    have h2 : σ (π k i (seat k i)) = τ (R k) := by
      apply Fin.ext
      rw [← app_fin τ]
      exact h1
    rw [he]; simp only; rw [← h2, Equiv.symm_apply_apply]
  have seatv : ∀ k i, seat k i = cmFlat (ρ k i) ⟨rowAmts (D k i) (ρ k i) % 13, Nat.mod_lt _ (by decide)⟩ :=
    fun _ _ => rfl
  -- row 3 is excluded
  have not3 : ∀ k, (ρ k 0).val ≠ 3 := by
    intro k h3
    have all3 : ∀ i, ρ k i = 3 := by
      intro i
      by_contra hne
      have hne' : (ρ k i).val ≠ 3 := fun h => hne (Fin.ext h)
      have e1 : π k 0 (seat k 0) = π k i (seat k i) := (key k 0).trans (key k i).symm
      rw [seatv, seatv] at e1
      have := (hf.seat_eq hne' e1).1
      exact hne (this ▸ Fin.ext h3)
    have hcol : ∀ i, seat k i = cmFlat 3 ⟨T 3 % 13, Nat.mod_lt _ (by decide)⟩ := by
      intro i; rw [seatv, all3 i, (hTr k i).2.2]
    have e0 := key k 0
    have e1 := key k 1
    have e2 := key k 2
    rw [hcol] at e0 e1 e2
    rw [hf.swap1, e0] at e1
    have hm := hf.member2 k _ (e2.trans e0.symm)
    rw [e0] at hm
    rcases hm with hm | hm
    · rw [hm, Equiv.swap_apply_left] at e1; exact hf.ne e1.symm
    · rw [hm, Equiv.swap_apply_right] at e1; exact hf.ne e1
  -- members 0 and 1 use the same row and column
  have same01 : ∀ k, ρ k 1 = ρ k 0 ∧
      rowAmts (D k 1) (ρ k 1) % 13 = rowAmts (D k 0) (ρ k 0) % 13 := by
    intro k
    have e1 : π k 1 (seat k 1) = π k 0 (seat k 0) := (key k 1).trans (key k 0).symm
    rw [seatv, seatv] at e1
    obtain ⟨h1, h2⟩ := hf.seat_eq (not3 k) e1
    exact ⟨h1, congrArg Fin.val h2⟩
  -- some class reads row 0
  have exists0 : ∃ k, ρ k 0 = 0 := by
    by_contra hno
    push_neg at hno
    have pig : ∀ a b c : Fin 4, a.val ≠ 3 → b.val ≠ 3 → c.val ≠ 3 → a ≠ 0 → b ≠ 0 → c ≠ 0 →
        a = b ∨ a = c ∨ b = c := by decide
    have collide : ∀ k k', k ≠ k' → ρ k 0 ≠ ρ k' 0 := by
      intro k k' hkk' hr
      have hr3 : (ρ k 0).val ≠ 3 := not3 k
      have hr0 : ρ k 0 ≠ 0 := hno k
      have hT1 : ∀ j, rowAmts (D j 0) (ρ k 0) = T (ρ k 0) := by
        intro j
        have := hTr j 0
        have hv := (ρ k 0).isLt
        have hv0 : (ρ k 0).val ≠ 0 := fun h => hr0 (Fin.ext h)
        have h1 : (ρ k 0) = 1 ∨ (ρ k 0) = 2 := by
          have : (ρ k 0).val = 1 ∨ (ρ k 0).val = 2 := by omega
          rcases this with h | h
          · exact Or.inl (Fin.ext h)
          · exact Or.inr (Fin.ext h)
        rcases h1 with h1 | h1 <;> rw [h1] <;> simp [this]
      have ek := key k 0
      have ek' := key k' 0
      rw [seatv, hT1 k] at ek
      rw [seatv, ← hr, hT1 k'] at ek'
      have he' : e k = e k' := by
        rw [← ek, ← ek', hf.agree k 0 _ (by rw [(cm_cmFlat _ _).1]; exact hr3),
          hf.agree k' 0 _ (by rw [(cm_cmFlat _ _).1]; exact hr3)]
      have hRk : R k = R k' := by
        simp only [he] at he'
        exact τ.injective (σ.symm.injective he')
      have := (hf.seat_eq (by decide : (0 : Fin 4).val ≠ 3) hRk).2
      exact hkk' (hf.col_inj this)
    rcases pig _ _ _ (not3 0) (not3 1) (not3 2) (hno 0) (hno 1) (hno 2) with h | h | h
    · exact collide 0 1 (by decide) h
    · exact collide 0 2 (by decide) h
    · exact collide 1 2 (by decide) h
  obtain ⟨k, hk0⟩ := exists0
  obtain ⟨hk1, hamt⟩ := same01 k
  rw [hk1, hk0] at hamt
  -- the row-0 amounts of members 0 and 1 agree
  have hK : rowAmts (D k 1) 3 = rowAmts (D k 0) 3 := ((hTr k 1).2.2).trans ((hTr k 0).2.2).symm
  rw [rowAmts_zero, rowAmts_zero, hK] at hamt
  set K := rowAmts (D k 0) 3
  have hlt : ∀ z : Fin 13 → Nat, rowTurnV10 z < 13 := fun z => Nat.mod_lt _ (by decide)
  rw [Nat.mod_eq_of_lt (hlt _), Nat.mod_eq_of_lt (hlt _)] at hamt
  -- read indices and the swap
  let idx : Fin 13 → Fin 13 := fun j => ⟨(j.val + K % 13) % 13, Nat.mod_lt _ (by decide)⟩
  let yv : Fin 13 → Fin 52 := fun j => (σ * π k 0) (cmFlat 3 (idx j))
  have hyv : Function.Injective yv := by
    intro a b h
    have h1 := cmFlat_col_injective 3 ((σ * π k 0).injective h)
    have h2 := congrArg Fin.val h1
    simp only [idx] at h2
    apply Fin.ext
    have := a.isLt; have := b.isLt; have := Nat.mod_lt K (by decide : 0 < 13)
    omega
  have hpre : ∀ c : Fin 13, ∃ j, idx j = c := by
    intro c
    refine ⟨⟨(c.val + 13 - K % 13) % 13, Nat.mod_lt _ (by decide)⟩, Fin.ext ?_⟩
    simp only [idx]
    have := c.isLt; have := Nat.mod_lt K (by decide : 0 < 13)
    omega
  obtain ⟨cx, hcx⟩ := hf.hasX k
  obtain ⟨cy, hcy⟩ := hf.hasY k
  obtain ⟨j1, hj1⟩ := hpre cx
  obtain ⟨j2, hj2⟩ := hpre cy
  have hy1 : yv j1 = σ x := by simp only [yv, Equiv.Perm.mul_apply, hj1, hcx]
  have hy2 : yv j2 = σ y := by simp only [yv, Equiv.Perm.mul_apply, hj2, hcy]
  have hj : j1 ≠ j2 := by
    intro h; apply hf.ne; apply σ.injective; rw [← hy1, ← hy2, h]
  have r0 : rowRead (D k 0) 3 K = fun j => (yv j).val := rfl
  have r1 : rowRead (D k 1) 3 K = fun j => (Equiv.swap (yv j1) (yv j2) (yv j)).val := by
    funext j
    show ((σ * π k 1) (cmFlat 3 (idx j))).val = _
    rw [Equiv.Perm.mul_apply, hf.swap1, perm_swap_apply, hy1, hy2]
    rfl
  rw [r0, r1] at hamt
  have hz := congrArg (fun n : Nat => (n : ZMod 13)) hamt
  simp only [rowTurnV10_cast] at hz
  rw [wsum_swap yv hyv hj] at hz
  have hprod : (wt j1 - wt j2) * (rk (yv j2) - rk (yv j1)) = 0 := by
    have := congrArg (fun z => z - wsum yv) hz
    simp only [add_sub_cancel_left, sub_self] at this
    exact this
  by_contra hr
  rw [hy1, hy2] at hprod
  exact zmod13_mul_ne _ _ (wt_sub_ne hj) (rk_sub_ne hr) hprod

end family

/-! ## C. The three families of `RankPartitionLists.lean`, and every equal-rank pair -/

/-- The product `t₁ * t₂ * … * tₙ` of a list of seat swaps (so the deck `permDeck` of it
    shows `t₁ (t₂ (… tₙ s))` at seat `s`). -/
def swapsPerm (l : List (Fin 52 × Fin 52)) : Relabel :=
  l.foldr (fun p acc => Equiv.swap p.1 p.2 * acc) 1

/-- Member `i` of class `k` of family `D`, as a permutation (seat ↦ card). -/
def famPerm (D k i : Fin 3) : Relabel := swapsPerm (famSwaps.getD (9 * D.val + 3 * k.val + i.val) [])

/-- The row-0 column holding stem cell 0 for class `k` of family `D`. -/
def famColOf (D k : Fin 3) : Fin 13 := famCol.getD (3 * D.val + k.val) 0

/-- The second card of family `D`: 13, 26, 39 (the first is card 0; all four have rank A). -/
def famY (D : Fin 3) : Fin 52 := ⟨13 * (D.val + 1), by have := D.isLt; omega⟩

/-- The structure of family `D` (no stem evaluation): the hypotheses of `Family` other than
    the stem-cell-0 values. -/
abbrev FamStruct (D : Fin 3) : Prop :=
  (∀ k i : Fin 3, ∀ s : Fin 52, (cmRow s).val ≠ 3 → famPerm D k i s = famPerm D 0 0 s) ∧
  famColOf D 0 ≠ famColOf D 1 ∧ famColOf D 0 ≠ famColOf D 2 ∧ famColOf D 1 ≠ famColOf D 2 ∧
  (∀ k : Fin 3, ∀ c : Fin 13,
    famPerm D k 1 (cmFlat 3 c) = Equiv.swap 0 (famY D) (famPerm D k 0 (cmFlat 3 c))) ∧
  (∀ k : Fin 3, ∃ c : Fin 13, famPerm D k 0 (cmFlat 3 c) = 0) ∧
  (∀ k : Fin 3, ∃ c : Fin 13, famPerm D k 0 (cmFlat 3 c) = famY D) ∧
  (∀ k : Fin 3, ∀ c : Fin 13, famPerm D k 2 (cmFlat 3 c) = famPerm D k 0 (cmFlat 3 c) →
    famPerm D k 0 (cmFlat 3 c) = 0 ∨ famPerm D k 0 (cmFlat 3 c) = famY D)

/-- Stem cell 0 of deck `(D, k, i)` is the card at the row-0 seat `(0, famColOf D k)`. -/
abbrev famC0Check (D k i : Fin 3) : Prop :=
  g0 (permDeck (famPerm D k i)) = (famPerm D k 0 (cmFlat 0 (famColOf D k))).val

/-- The finite checks (discharged by kernel `decide!` in the heavy library,
    `RankPartition.rankChecks_ok`). -/
abbrev RankChecks : Prop := (∀ D, FamStruct D) ∧ ∀ D k i, famC0Check D k i

theorem family_of_checks (h : RankChecks) (D : Fin 3) :
    Family (famPerm D) (famColOf D) 0 (famY D) := by
  obtain ⟨hag, h01, h02, h12, hsw, hx, hy, hm⟩ := h.1 D
  refine ⟨hag, ?_, fun k i => ?_, hsw, hx, hy, ?_, hm⟩
  · intro a b hab
    fin_cases a <;> fin_cases b <;> first
      | rfl
      | exact absurd hab h01 | exact absurd hab.symm h01
      | exact absurd hab h02 | exact absurd hab.symm h02
      | exact absurd hab h12 | exact absurd hab.symm h12
  · rw [← g0_eq]; exact h.2 D k i
  · intro e
    have := congrArg Fin.val e
    simp only [famY] at this
    omega

theorem v10SymFn_mod (r : Fin 13) (y : Fin 4) (c : Fin 52) :
    (v10SymFn r y c).val % 13 = (c.val % 13 + r.val) % 13 := by
  simp only [v10SymFn]
  omega

theorem rank_zero_cards : ∀ c : Fin 52, c.val % 13 = 0 → c ≠ 0 → ∃ D : Fin 3, c = famY D := by
  decide

/-- (PROVED, GIVEN the finite checks `RankChecks` as a hypothesis) If `Cell0Cov σ τ`, then σ
    maps any two cards of equal rank (`c % 13`) to cards of equal rank. Unconditional form:
    heavy library, `RankPartition.cell0Cov_rank`. -/
theorem cell0Cov_rank_of_checks (hchk : RankChecks) {σ τ : Relabel} (h : Cell0Cov σ τ)
    {a b : Fin 52} (hab : a.val % 13 = b.val % 13) : (σ a).val % 13 = (σ b).val % 13 := by
  by_cases heq : a = b
  · rw [heq]
  obtain ⟨r, yy, hr⟩ := exists_v10Sym_zero a
  set v := v10Sym r yy with hv
  have hv0 : v 0 = a := hr
  set b' := v.symm b with hb'
  have hvb : v b' = b := Equiv.apply_symm_apply v b
  have hma : a.val % 13 = (0 + r.val) % 13 := by
    rw [← hv0]; exact v10SymFn_mod r yy 0
  have hmb : b.val % 13 = (b'.val % 13 + r.val) % 13 := by
    rw [← hvb]; exact v10SymFn_mod r yy b'
  have hb0 : b'.val % 13 = 0 := by
    have := Nat.mod_lt b'.val (by decide : 0 < 13)
    have := r.isLt
    omega
  have hbne : b' ≠ 0 := by
    intro e; apply heq; rw [← hv0, ← hvb, e]
  obtain ⟨D, hD⟩ := rank_zero_cards b' hb0 hbne
  have hcv : Cell0Cov (σ * v) (τ * v) :=
    cell0Cov_mul h (cell0Cov_self_of_commutes (sumRanksV10_commutes_v10Sym r yy))
  have := rank_eq_of_family (family_of_checks hchk D) hcv
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hv0, ← hD, hvb] at this
  unfold rank at this
  omega

/-- (PROVED, GIVEN `RankChecks`) The same, as an iff: under `Cell0Cov σ τ`, two cards have
    equal rank exactly when their σ-images do (σ permutes the 13 rank classes). -/
theorem cell0Cov_rank_iff_of_checks (hchk : RankChecks) {σ τ : Relabel} (h : Cell0Cov σ τ)
    (a b : Fin 52) : (σ a).val % 13 = (σ b).val % 13 ↔ a.val % 13 = b.val % 13 := by
  constructor
  · intro e
    have := cell0Cov_rank_of_checks hchk (cell0Cov_inv h) e
    simpa only [Equiv.Perm.inv_apply_self] using this
  · exact cell0Cov_rank_of_checks hchk h

/-- (PROVED, GIVEN `RankChecks`) Every covariant σ (for the unkeyed round body, any output
    relabelling) maps cards of equal rank to cards of equal rank. Unconditional form: heavy
    library, `RankPartition.covariant_rank`. -/
theorem covariant_rank_of_checks (hchk : RankChecks) {σ : Relabel}
    (h : Covariant σ unkeyedWithMix) {a b : Fin 52} (hab : a.val % 13 = b.val % 13) :
    (σ a).val % 13 = (σ b).val % 13 := by
  obtain ⟨τ, hτ⟩ := h
  exact cell0Cov_rank_of_checks hchk (cell0Cov_of_covPair hτ) hab

end DoubleDeal.Security.RankPartition
