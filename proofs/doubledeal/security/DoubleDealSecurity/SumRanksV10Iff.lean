/-
  T1 for v10 SumRanks, "only if" (SPEC §3.3, `DoubleDeal.sumRanksV10`).

  If a relabelling σ commutes with v10 SumRanks on every well-formed deck, then
  σ = `v10Sym a x` for some `a`, `x`. With `sumRanksV10_commutes_v10Sym` this
  gives the full characterisation `sumRanksV10_commutes_iff`.

  Route (mirrors the v9 pair-swap proof in `SumRanks.lean`):
  1. Position map. The chained steps turn every row once and then every column
     once, so `sumRanksChain g = colRotate (rowRotate g (rowAmt g)) (colAmt …)`
     for the amounts actually used (`sumRanksChain_eq`).
  2. Commuting on one deck forces equal amounts (`rot_match`, as for v9), in
     particular row 1's amount (read from the untouched row 0) and column 1's
     amount (read from column 0 and column 1 after the row stage).
  3. Two decks that differ only in the last card of row 0 give a constant rank
     shift mod 13; two decks that differ only in the top card of column 1 give a
     constant GF(4) suit-label shift. Rank and label determine the card.
  No `decide!`; three small `decide`s over Fin 4 (plus trivial numeric side
  goals); no `sorry`.
-/
import DoubleDealSecurity.SumRanksV10

namespace DoubleDeal.Security

open DoubleDeal Relabel

/-! ## 1. Position map of the chained steps -/

section PositionMap
variable {α : Type}

theorem rowRotate_congr (g : Grid α) (t t' : Fin 4 → Nat) (h : ∀ r, t r % 13 = t' r % 13) :
    rowRotate g t = rowRotate g t' := by
  funext r c
  rw [rowRotate_apply, rowRotate_apply, h r]

theorem colRotate_congr (g : Grid α) (s s' : Fin 13 → Nat) (h : ∀ c, s c % 4 = s' c % 4) :
    colRotate g s = colRotate g s' := by
  funext r c
  rw [colRotate_apply, colRotate_apply, h c]

theorem rowRotate_zero (g : Grid α) : rowRotate g (fun _ => 0) = g := by
  funext r c
  rw [rowRotate_apply]
  congr 1
  apply Fin.ext
  simp only [Nat.zero_mod, Nat.add_zero]
  exact Nat.mod_eq_of_lt c.isLt

theorem colRotate_zero (g : Grid α) : colRotate g (fun _ => 0) = g := by
  funext r c
  rw [colRotate_apply]
  congr 1
  apply Fin.ext
  simp only [Nat.zero_mod, Nat.sub_zero]
  omega

theorem turnRow_rowRotate (g : Grid α) (u : Fin 4 → Nat) (i : Fin 4) (k : Nat) (hu : u i = 0) :
    turnRow (rowRotate g u) i k = rowRotate g (fun r => if r = i then k else u r) := by
  funext r c
  unfold turnRow
  rw [rowRotate_apply, rowRotate_apply, rowRotate_apply]
  by_cases h : r = i
  · subst h
    simp only [if_pos rfl, hu]
    congr 1
    apply Fin.ext
    simp only
    omega
  · simp only [if_neg h]
    congr 1
    apply Fin.ext
    simp only
    have := c.isLt
    omega

theorem turnCol_colRotate (g : Grid α) (u : Fin 13 → Nat) (j : Fin 13) (k : Nat) (hu : u j = 0) :
    turnCol (colRotate g u) j k = colRotate g (fun c => if c = j then k else u c) := by
  funext r c
  unfold turnCol
  rw [colRotate_apply, colRotate_apply, colRotate_apply]
  by_cases h : c = j
  · subst h
    simp only [if_pos rfl, hu]
    congr 1
    apply Fin.ext
    simp only
    omega
  · simp only [if_neg h]
    congr 1
    apply Fin.ext
    simp only
    have := r.isLt
    omega

variable (rt : (Fin 13 → α) → Nat) (ct : (Fin 4 → α) → (Fin 4 → α) → Nat)

/-- The step (1–4) at which row `r` turns (order 1, 2, 3, 0). -/
def rowStepOf (r : Fin 4) : Nat := if r.val = 0 then 4 else r.val

/-- The step (1–13) at which column `c` turns (order 1, …, 12, 0). -/
def colStepOf (c : Fin 13) : Nat := if c.val = 0 then 13 else c.val

/-- The amount row `r` actually turns by. -/
def rowAmt (g : Grid α) (r : Fin 4) : Nat := rt (rowsDone rt g (rowStepOf r - 1) (prevRow r))

/-- The amount column `c` actually turns by. -/
def colAmt (g : Grid α) (c : Fin 13) : Nat :=
  ct (column (colsDone ct g (colStepOf c - 1)) (prevCol c))
    (column (colsDone ct g (colStepOf c - 1)) c)

theorem rowsDone_eq_partial (g : Grid α) : ∀ n, n ≤ 4 →
    rowsDone rt g n = rowRotate g (fun r => if rowStepOf r ≤ n then rowAmt rt g r else 0) := by
  intro n hn
  induction n with
  | zero =>
    have : (fun r : Fin 4 => if rowStepOf r ≤ 0 then rowAmt rt g r else 0) = fun _ => 0 := by
      funext r; unfold rowStepOf; split <;> (rw [if_neg]; omega)
    rw [this, rowRotate_zero]; rfl
  | succ n ih =>
    have ih := ih (by omega)
    let i : Fin 4 := ⟨(n + 1) % 4, Nat.mod_lt _ (by decide)⟩
    have hi : rowStepOf i = n + 1 := by
      simp only [rowStepOf, i]; split <;> omega
    have hk : rt (rowsDone rt g n (prevRow i)) = rowAmt rt g i := by
      unfold rowAmt; rw [hi, Nat.add_sub_cancel]
    show turnRow (rowsDone rt g n) i (rt (rowsDone rt g n (prevRow i))) = _
    rw [hk, ih, turnRow_rowRotate _ _ _ _ (by simp only [hi]; rw [if_neg (by omega)])]
    refine congrArg (rowRotate g) (funext fun r => ?_)
    by_cases hr : r = i
    · subst hr; simp only [if_pos rfl, hi, le_refl, if_true]
    · rw [if_neg hr]
      have hne : rowStepOf r ≠ n + 1 := by
        intro e; apply hr; apply Fin.ext
        have := r.isLt
        simp only [rowStepOf, i] at e ⊢; split at e <;> omega
      by_cases hle : rowStepOf r ≤ n
      · rw [if_pos hle, if_pos (by omega)]
      · rw [if_neg hle, if_neg (by omega)]

theorem colsDone_eq_partial (g : Grid α) : ∀ n, n ≤ 13 →
    colsDone ct g n = colRotate g (fun c => if colStepOf c ≤ n then colAmt ct g c else 0) := by
  intro n hn
  induction n with
  | zero =>
    have : (fun c : Fin 13 => if colStepOf c ≤ 0 then colAmt ct g c else 0) = fun _ => 0 := by
      funext c; unfold colStepOf; split <;> (rw [if_neg]; omega)
    rw [this, colRotate_zero]; rfl
  | succ n ih =>
    have ih := ih (by omega)
    let j : Fin 13 := ⟨(n + 1) % 13, Nat.mod_lt _ (by decide)⟩
    have hj : colStepOf j = n + 1 := by
      simp only [colStepOf, j]; split <;> omega
    have hk : ct (column (colsDone ct g n) (prevCol j)) (column (colsDone ct g n) j) =
        colAmt ct g j := by
      unfold colAmt; rw [hj, Nat.add_sub_cancel]
    show turnCol (colsDone ct g n) j
      (ct (column (colsDone ct g n) (prevCol j)) (column (colsDone ct g n) j)) = _
    rw [hk, ih, turnCol_colRotate _ _ _ _ (by simp only [hj]; rw [if_neg (by omega)])]
    refine congrArg (colRotate g) (funext fun c => ?_)
    by_cases hc : c = j
    · subst hc; simp only [if_pos rfl, hj, le_refl, if_true]
    · rw [if_neg hc]
      have hne : colStepOf c ≠ n + 1 := by
        intro e; apply hc; apply Fin.ext
        have := c.isLt
        simp only [colStepOf, j] at e ⊢; split at e <;> omega
      by_cases hle : colStepOf c ≤ n
      · rw [if_pos hle, if_pos (by omega)]
      · rw [if_neg hle, if_neg (by omega)]

theorem rowsDone_eq (g : Grid α) : rowsDone rt g 4 = rowRotate g (rowAmt rt g) := by
  rw [rowsDone_eq_partial rt g 4 le_rfl]
  refine congrArg (rowRotate g) (funext fun r => ?_)
  rw [if_pos (by unfold rowStepOf; split <;> omega)]

theorem colsDone_eq (g : Grid α) : colsDone ct g 13 = colRotate g (colAmt ct g) := by
  rw [colsDone_eq_partial ct g 13 le_rfl]
  refine congrArg (colRotate g) (funext fun c => ?_)
  rw [if_pos (by unfold colStepOf; have := c.isLt; split <;> omega)]

/-- The chained SumRanks is one row rotation followed by one column rotation. -/
theorem sumRanksChain_eq (g : Grid α) :
    sumRanksChain rt ct g =
      colRotate (rowRotate g (rowAmt rt g)) (colAmt ct (rowsDone rt g 4)) := by
  unfold sumRanksChain
  rw [colsDone_eq, rowsDone_eq]

theorem rowAmt_one (g : Grid α) : rowAmt rt g 1 = rt (g 0) := rfl

theorem colAmt_one (g : Grid α) : colAmt ct g 1 = ct (column g 0) (column g 1) := rfl

end PositionMap

/-! ## 2. Commuting on one deck forces equal amounts -/

theorem relG_colRotate_rowRotate (σ : Relabel) (g : Grid Nat) (t : Fin 4 → Nat)
    (s : Fin 13 → Nat) :
    relG σ (colRotate (rowRotate g t) s) = colRotate (rowRotate (relG σ g) t) s := by
  funext r c
  simp only [relG, colRotate_apply, rowRotate_apply]

theorem relG_rowRotate (σ : Relabel) (g : Grid Nat) (t : Fin 4 → Nat) :
    relG σ (rowRotate g t) = rowRotate (relG σ g) t := by
  funext r c
  simp only [relG, rowRotate_apply]

theorem amounts_match (σ : Relabel) (g : Grid Nat) (hg : IsDeck (scoopColumnMajor g))
    (t t' : Fin 4 → Nat) (s s' : Fin 13 → Nat)
    (h : colRotate (rowRotate (relG σ g) t') s' = relG σ (colRotate (rowRotate g t) s)) :
    (∀ ρ, t' ρ % 13 = t ρ % 13) ∧ (∀ c, s' c % 4 = s c % 4) := by
  have key : ∀ r c, _ := fun r c => congrFun (congrFun h r) c
  simp only [colRotate_apply, rowRotate_apply, relG] at key
  have key2 := fun r c => grid_inj hg (σ.app_inj (key r c))
  exact rot_match t t' s s' key2

/-- On a deck where σ commutes with v10 SumRanks: row 1's turn (read from the
    untouched row 0) agrees, the row stage commutes, and column 1's turn (read
    from columns 0 and 1 after the row stage) agrees. -/
theorem sumRanksV10_turns_of_commute (σ : Relabel) (g : Grid Nat)
    (hg : IsDeck (scoopColumnMajor g))
    (hc : sumRanksV10 (relG σ g) = relG σ (sumRanksV10 g)) :
    rowTurnV10 (relG σ g 0) = rowTurnV10 (g 0) ∧
    rowsDone rowTurnV10 (relG σ g) 4 = relG σ (rowsDone rowTurnV10 g 4) ∧
    colTurnV10 (column (relG σ (rowsDone rowTurnV10 g 4)) 0)
        (column (relG σ (rowsDone rowTurnV10 g 4)) 1) =
      colTurnV10 (column (rowsDone rowTurnV10 g 4) 0) (column (rowsDone rowTurnV10 g 4) 1) := by
  unfold sumRanksV10 at hc
  rw [sumRanksChain_eq, sumRanksChain_eq] at hc
  obtain ⟨hr, hs⟩ := amounts_match σ g hg _ _ _ _ hc
  have hrows : rowsDone rowTurnV10 (relG σ g) 4 = relG σ (rowsDone rowTurnV10 g 4) := by
    rw [rowsDone_eq, rowsDone_eq, relG_rowRotate]
    exact rowRotate_congr _ _ _ hr
  refine ⟨?_, hrows, ?_⟩
  · have h1 := hr 1
    rw [rowAmt_one, rowAmt_one] at h1
    unfold rowTurnV10 at h1 ⊢
    simpa only [Nat.mod_mod] using h1
  · have h1 := hs 1
    rw [colAmt_one, colAmt_one, hrows] at h1
    rwa [Nat.mod_eq_of_lt (colTurnV10_lt _ _), Nat.mod_eq_of_lt (colTurnV10_lt _ _)] at h1

/-! ## 3. Pair-swap decks -/

theorem rowTotal_swap12 (x y : Fin 13 → Nat) (h : ∀ c : Fin 13, c ≠ 12 → x c = y c) :
    rowTotal x + rank (y 12) = rowTotal y + rank (x 12) := by
  simp only [rowTotal, rowPref, toList13, List.getD_cons_zero, List.getD_cons_succ,
    h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide),
    h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide),
    h 10 (by decide), h 11 (by decide)]
  omega

/-- Row relation: `rank(σa) − rank a ≡ rank(σb) − rank b (mod 13)`. -/
theorem v10_row_pair (σ : Relabel) (h : CommutesOnDecksG σ sumRanksV10) (a b : Fin 52) :
    (cardRank (σ a).val + cardRank b.val) % 13 = (cardRank (σ b).val + cardRank a.val) % 13 := by
  by_cases hab : a = b
  · subst hab; rfl
  obtain ⟨π, hπa, hπb⟩ := PermCount.exists_perm_two 48 1 a b (by decide) hab
  let g1 := layColumnMajor (permDeck π)
  let g2 := layColumnMajor (permDeck (π * Equiv.swap 48 1))
  have hd1 : IsDeck (scoopColumnMajor g1) := isDeck_lay_permDeck π
  have hd2 : IsDeck (scoopColumnMajor g2) := isDeck_lay_permDeck _
  have A1 := (sumRanksV10_turns_of_commute σ g1 hd1 (h g1 hd1)).1
  have A2 := (sumRanksV10_turns_of_commute σ g2 hd2 (h g2 hd2)).1
  have hrow : ∀ c : Fin 13, c ≠ 12 → g1 0 c = g2 0 c := by
    intro c hc
    simp only [g1, g2, layColumnMajor, permDeck, Equiv.Perm.mul_apply]
    rw [Equiv.swap_apply_of_ne_of_ne]
    · intro e; apply hc; apply Fin.ext
      have := congrArg Fin.val e; simp [cmFlat] at this; omega
    · intro e; have := congrArg Fin.val e; simp [cmFlat] at this
  have B := rowTotal_swap12 (g1 0) (g2 0) hrow
  have B' := rowTotal_swap12 (relG σ g1 0) (relG σ g2 0)
    (fun c hc => by simp only [relG]; rw [hrow c hc])
  have e1 : g1 0 12 = a.val := by
    simp only [g1, layColumnMajor, permDeck]
    rw [show cmFlat 0 12 = 48 from rfl, hπa]
  have e2 : g2 0 12 = b.val := by
    simp only [g2, layColumnMajor, permDeck, Equiv.Perm.mul_apply]
    rw [show cmFlat 0 12 = 48 from rfl, Equiv.swap_apply_left, hπb]
  simp only [relG, e1, e2, σ.app_fin] at B'
  rw [e1, e2] at B
  unfold rowTurnV10 at A1 A2
  simp only [cardRank]
  omega

theorem isDeckG_rowsUndo (H : Grid Nat) (hH : IsDeck (scoopColumnMajor H)) :
    ∀ n, IsDeck (scoopColumnMajor (rowsUndo rowTurnV10 H n))
  | 0 => hH
  | n + 1 => isDeckG_rowRotateInv _ _ (isDeckG_rowsUndo H hH n)

/-- The column-1 relation holds for every deck grid `H` (as the post-row grid). -/
theorem v10_col_turn (σ : Relabel) (h : CommutesOnDecksG σ sumRanksV10) (H : Grid Nat)
    (hH : IsDeck (scoopColumnMajor H)) :
    colTurnV10 (column (relG σ H) 0) (column (relG σ H) 1) =
      colTurnV10 (column H 0) (column H 1) := by
  let g := rowsUndo rowTurnV10 H 4
  have hg : IsDeck (scoopColumnMajor g) := isDeckG_rowsUndo H hH 4
  have hback : rowsDone rowTurnV10 g 4 = H := by
    have := rowsDone_rowsUndo rowTurnV10 H 4 le_rfl
    simpa using this
  have := (sumRanksV10_turns_of_commute σ g hg (h g hg)).2.2
  rwa [hback] at this

/-- `v' ⊕ (a' ⊕ r') = v ⊕ (a ⊕ r)` gives `a' ⊕ a = (v ⊕ v') ⊕ (r ⊕ r')` (`xor4` algebra,
    `SumRanksV10.lean`). -/
theorem xor4_peel {v v' r r' a a' : Fin 4} (h : xor4 v' (xor4 a' r') = xor4 v (xor4 a r)) :
    xor4 a' a = xor4 (xor4 v v') (xor4 r r') := by
  rw [xor4_left_comm] at h
  rw [xor4_eq_iff _ _ _ h]
  simp only [xor4_assoc, xor4_comm, xor4_left_comm, xor4_self, xor4_self_left, xor4_zero,
    zero_xor4]

theorem gfAdd_pair_core (V V' R R' la lb la' lb' : Nat) (hV : V < 4) (hV' : V' < 4)
    (hR : R < 4) (hR' : R' < 4) (ha : la < 4) (hb : lb < 4) (ha' : la' < 4) (hb' : lb' < 4)
    (E1 : gfAdd V' (gfAdd la' R') = gfAdd V (gfAdd la R))
    (E2 : gfAdd V' (gfAdd lb' R') = gfAdd V (gfAdd lb R)) :
    gfAdd la' la = gfAdd lb' lb :=
  congrArg Fin.val ((xor4_peel (v := ⟨V, hV⟩) (v' := ⟨V', hV'⟩) (r := ⟨R, hR⟩) (r' := ⟨R', hR'⟩)
    (a := ⟨la, ha⟩) (a' := ⟨la', ha'⟩) (Fin.ext E1)).trans
    (xor4_peel (v := ⟨V, hV⟩) (v' := ⟨V', hV'⟩) (r := ⟨R, hR⟩) (r' := ⟨R', hR'⟩)
      (a := ⟨lb, hb⟩) (a' := ⟨lb', hb'⟩) (Fin.ext E2)).symm)

theorem colSuits_split (y : Fin 4 → Nat) :
    colSuits y = gfAdd (suitLabel (y 0))
      (gfAdd (gfAdd (suitLabel (y 1)) (suitLabel (y 2))) (suitLabel (y 3))) := by
  unfold colSuits
  rw [gfAdd_assoc, gfAdd_assoc, gfAdd_assoc]

/-- Column relation: `ℓ(σa) ⊕ ℓ(a) = ℓ(σb) ⊕ ℓ(b)` for the GF(4) suit label ℓ. -/
theorem v10_col_pair (σ : Relabel) (h : CommutesOnDecksG σ sumRanksV10) (a b : Fin 52) :
    gfAdd (suitLabel (σ a).val) (suitLabel a.val) =
      gfAdd (suitLabel (σ b).val) (suitLabel b.val) := by
  by_cases hab : a = b
  · subst hab; rfl
  obtain ⟨π, hπa, hπb⟩ := PermCount.exists_perm_two 4 8 a b (by decide) hab
  let H1 := layColumnMajor (permDeck π)
  let H2 := layColumnMajor (permDeck (π * Equiv.swap 4 8))
  have A1 := v10_col_turn σ h H1 (isDeck_lay_permDeck π)
  have A2 := v10_col_turn σ h H2 (isDeck_lay_permDeck _)
  have same : ∀ r c, (r, c) ≠ (0, 1) → c ≠ 2 → H1 r c = H2 r c := by
    intro r c hrc hc2
    simp only [H1, H2, layColumnMajor, permDeck, Equiv.Perm.mul_apply]
    rw [Equiv.swap_apply_of_ne_of_ne]
    · intro e; apply hrc
      have := congrArg Fin.val e; simp [cmFlat] at this
      have hr := r.isLt
      have e1 : r = 0 := Fin.ext (by simp; omega)
      have e2 : c = 1 := Fin.ext (by simp; omega)
      rw [e1, e2]
    · intro e; apply hc2
      have := congrArg Fin.val e; simp [cmFlat] at this
      exact Fin.ext (by simp; omega)
  have c0 : column H1 0 = column H2 0 := funext fun r => same r 0 (by simp) (by decide)
  have c0' : column (relG σ H1) 0 = column (relG σ H2) 0 := by
    funext r; simp only [column, relG]; rw [same r 0 (by simp) (by decide)]
  have e1 : H1 0 1 = a.val := by
    simp only [H1, layColumnMajor, permDeck]
    rw [show cmFlat 0 1 = 4 from rfl, hπa]
  have e2 : H2 0 1 = b.val := by
    simp only [H2, layColumnMajor, permDeck, Equiv.Perm.mul_apply]
    rw [show cmFlat 0 1 = 4 from rfl, Equiv.swap_apply_left, hπb]
  have s1 : H1 1 1 = H2 1 1 := same (1 : Fin 4) (1 : Fin 13) (by decide) (by decide)
  have s2 : H1 2 1 = H2 2 1 := same (2 : Fin 4) (1 : Fin 13) (by decide) (by decide)
  have s3 : H1 3 1 = H2 3 1 := same (3 : Fin 4) (1 : Fin 13) (by decide) (by decide)
  unfold colTurnV10 at A1 A2
  rw [colSuits_split, colSuits_split] at A1 A2
  simp only [column, relG] at A1 A2 c0 c0'
  rw [c0] at A1
  rw [c0'] at A1
  rw [e1, s1, s2, s3] at A1
  rw [e2] at A2
  simp only [σ.app_fin] at A1 A2
  exact gfAdd_pair_core _ _ _ _ _ _ _ _ (by unfold colValue; exact gfAdd_lt _ _)
    (by unfold colValue; exact gfAdd_lt _ _) (gfAdd_lt _ _) (gfAdd_lt _ _)
    (suitLabel_lt _) (suitLabel_lt _) (suitLabel_lt _) (suitLabel_lt _) A1 A2

/-! ## 4. Rank and label determine the card; the characterisation -/

theorem card_eq_of_rank_label (m n : Fin 52) (h1 : cardRank m.val % 13 = cardRank n.val % 13)
    (h2 : suitLabel m.val = suitLabel n.val) : m = n := by
  apply Fin.ext
  have hm := m.isLt; have hn := n.isLt
  simp only [cardRank, rank, suitLabel, suit] at h1 h2
  split_ifs at h2 <;> omega

/-- **v10 SumRanks, "only if"** (PROVED): if σ commutes with v10 SumRanks on
    every well-formed deck, then σ is one of the 52 relabellings `v10Sym a x`. -/
theorem v10Sym_of_sumRanksV10_commutes (σ : Relabel) (h : CommutesOnDecksG σ sumRanksV10) :
    ∃ a x, σ = v10Sym a x := by
  obtain ⟨k, hk⟩ := weightShift_of_pair13 σ cardRank (v10_row_pair σ h)
  let x : Nat := gfAdd (suitLabel (σ 0).val) (suitLabel (0 : Fin 52).val)
  refine ⟨⟨k % 13, Nat.mod_lt _ (by decide)⟩, ⟨x, gfAdd_lt _ _⟩, Equiv.ext fun c => ?_⟩
  apply card_eq_of_rank_label
  · show cardRank (σ c).val % 13 = cardRank (v10SymFn _ _ c).val % 13
    rw [v10SymFn_rank, hk c]
    simp only [Nat.add_mod_mod]
  · show suitLabel (σ c).val = suitLabel (v10SymFn _ _ c).val
    rw [v10SymFn_label]
    have hp := v10_col_pair σ h c 0
    exact congrArg Fin.val
      (xor4_eq_iff (lbl (σ c)) (lbl c) (xor4 (lbl (σ 0)) (lbl 0)) (Fin.ext hp))

/-- **v10 SumRanks characterisation** (PROVED, both directions): a relabelling
    commutes with v10 SumRanks on every well-formed deck iff it is one of the 52
    elements `v10Sym a x` (rank index `+a mod 13`, GF(4) suit label `⊕ x`). -/
theorem sumRanksV10_commutes_iff (σ : Relabel) :
    CommutesOnDecksG σ sumRanksV10 ↔ ∃ a x, σ = v10Sym a x :=
  ⟨v10Sym_of_sumRanksV10_commutes σ,
   fun ⟨a, x, e⟩ => e ▸ (sumRanksV10_commutes_v10Sym a x).onDecks⟩

end DoubleDeal.Security
