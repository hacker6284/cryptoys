/-
  WIP (not built by CI): every relabelling outside `v10Sym` commutes with v10
  SumRanks on at most `52!/64` decks (`sumRanksV10_survival_le`).

  Skeleton of the counting proof in PROOF.md (paper proof of the bound
  `0.012768 · 52!`; Lean target `52!/64`). Each lemma carries the PROOF.md
  section it formalises. Lemmas marked `sorry` are open; see `../../LEMMAS.md`.
  The self-contained combinatorics and numerics are in `Standalone.lean`.

  Decks are counted as position permutations `π : Equiv.Perm (Fin 52)` laid
  column-major (`deckGrid π = layColumnMajor (permDeck π)`), which is a
  bijection onto the well-formed decks. A deck *survives* `τ` if the instance
  of `CommutesOnDecksG τ sumRanksV10` at that deck holds.
-/
import DoubleDealSecurity.SumRanksV10Iff
import DoubleDealSecurityWIP.SumRanksDP.Decomp

namespace DoubleDeal.Security.SumRanksDP

open DoubleDeal Relabel Finset SRDP

/-! ## Decks and survival -/

/-- The grid of the deck with card `π p` in position `p` (column-major). -/
def deckGrid (π : Equiv.Perm (Fin 52)) : Grid Nat := layColumnMajor (permDeck π)

theorem deckGrid_apply (π : Equiv.Perm (Fin 52)) (r : Fin 4) (j : Fin 13) :
    deckGrid π r j = (π (cmFlat r j)).val := rfl

theorem isDeck_deckGrid (π : Equiv.Perm (Fin 52)) : IsDeck (scoopColumnMajor (deckGrid π)) :=
  isDeck_lay_permDeck π

/-- `τ` commutes with v10 SumRanks on the deck `π` (the pointwise instance of
    `CommutesOnDecksG τ sumRanksV10`). -/
def Survives (τ : Relabel) (π : Equiv.Perm (Fin 52)) : Prop :=
  sumRanksV10 (relG τ (deckGrid π)) = relG τ (sumRanksV10 (deckGrid π))

instance (τ : Relabel) : DecidablePred (Survives τ) :=
  fun _ => inferInstanceAs (Decidable (_ = _))

/-- The surviving decks. -/
def survivors (τ : Relabel) : Finset (Equiv.Perm (Fin 52)) := univ.filter (Survives τ)

/-- Sanity link to `CommutesOnDecksG`: a relabelling that commutes on every
    deck (a symmetry, by `sumRanksV10_commutes_iff`) has every deck surviving. -/
theorem survivors_eq_univ_of_commutes (τ : Relabel) :
    CommutesOnDecksG τ sumRanksV10 → survivors τ = univ := by
  intro h
  ext π
  simp only [survivors, mem_filter, mem_univ, true_and, iff_true]
  exact h _ (isDeck_deckGrid π)

/-! ## §0 Difference data -/

/-- Rank index mod 13 (`cardRank c = c % 13 + 1`; the `+1` cancels in `δ`). -/
def rk (c : Fin 52) : ZMod 13 := ((c.val % 13 : ℕ) : ZMod 13)

/-- GF(4) suit label of a card, as `Fin 4`. -/
def lab (c : Fin 52) : Fin 4 := ⟨suitLabel c.val, suitLabel_lt _⟩

/-- `δ(c) = ρ(τ c) − ρ(c)` (PROOF.md §0). -/
def delta (τ : Relabel) (c : Fin 52) : ZMod 13 := rk (τ c) - rk c

/-- `ε(c) = ℓ(τ c) + ℓ(c)` (PROOF.md §0). -/
def eps (τ : Relabel) (c : Fin 52) : Fin 4 := x4 (lab (τ c)) (lab c)

theorem gfAdd_eq_x4 : ∀ a b : Fin 4, gfAdd a.val b.val = (x4 a b).val := by decide

/-- (0.1), "if" half (PROOF.md §0): constant `δ` and constant `ε` give a symmetry. -/
theorem sym_of_const (τ : Relabel) (hδ : ∀ c, delta τ c = delta τ 0)
    (hε : ∀ c, eps τ c = eps τ 0) : ∃ a x, τ = v10Sym a x := by
  refine ⟨delta τ 0, eps τ 0, Equiv.ext fun c => ?_⟩
  apply card_eq_of_rank_label
  · show cardRank (τ c).val % 13 = cardRank (v10SymFn _ _ c).val % 13
    rw [v10SymFn_rank]
    show cardRank (τ c).val % 13 = (cardRank c.val + ZMod.val (delta τ 0)) % 13
    have h : rk (τ c) = rk c + delta τ 0 := by
      have := hδ c; simp only [delta] at this ⊢; linear_combination this
    have key : ((τ c).val % 13 : ℕ) % 13 = (c.val % 13 + ZMod.val (delta τ 0)) % 13 := by
      rw [← ZMod.natCast_eq_natCast_iff']
      push_cast
      rw [ZMod.natCast_zmod_val]
      exact h
    simp only [cardRank, rank]
    omega
  · show suitLabel (τ c).val = suitLabel (v10SymFn _ _ c).val
    rw [v10SymFn_label]
    have h := x4_solve _ _ _ (hε c)
    have := congrArg Fin.val h
    rw [← gfAdd_eq_x4] at this
    simp only [lab] at this
    rw [this, gfAdd_comm]

/-- (0.1) (PROOF.md §0): outside `v10Sym`, `δ` or `ε` is not constant. -/
theorem nonconst_of_not_sym (τ : Relabel) (h : ¬ ∃ a x, τ = v10Sym a x) :
    (∃ c, delta τ c ≠ delta τ 0) ∨ (∃ c, eps τ c ≠ eps τ 0) := by
  by_contra hc
  push_neg at hc
  exact h (sym_of_const τ hc.1 hc.2)

/-- `Σ_c δ(c) = 0` because `τ` is a bijection (PROOF.md §0). -/
theorem sum_delta (τ : Relabel) : ∑ c, delta τ c = 0 := by
  simp only [delta, Finset.sum_sub_distrib]
  rw [Equiv.sum_comp τ rk, sub_self]

/-! ## §0 Row functionals -/

/-- `S(x) = Σ_j j·δ(x_j)` (PROOF.md §0). -/
def rowS (τ : Relabel) (x : Fin 13 → Fin 52) : ZMod 13 := ∑ j : Fin 13, (j.val : ZMod 13) * delta τ (x j)

/-- `D(x) = Σ_j δ(x_j)` (PROOF.md §0). -/
def rowD (τ : Relabel) (x : Fin 13 → Fin 52) : ZMod 13 := ∑ j : Fin 13, delta τ (x j)

theorem rowS_comp (τ : Relabel) (x : Fin 13 → Fin 52) (σ : Equiv.Perm (Fin 13)) :
    rowS τ (x ∘ σ) = wS (fun j => delta τ (x j)) σ := rfl

theorem rowTotal_cast (x : Fin 13 → ℕ) :
    ((rowTotal x : ℕ) : ZMod 13) = -∑ j : Fin 13, (j.val : ZMod 13) * (rank (x j) : ZMod 13) := by
  simp only [rowTotal, rowPref, toList13, List.getD_cons_succ, List.getD_cons_zero]
  rw [Finset.sum_fin_eq_sum_range]
  simp [Finset.sum_range_succ]
  have h13 : (13 : ZMod 13) = 0 := rfl
  linear_combination ((rank (x 0) : ZMod 13) + (rank (x 1) : ZMod 13) + (rank (x 2) : ZMod 13) + (rank (x 3) : ZMod 13) + (rank (x 4) : ZMod 13) + (rank (x 5) : ZMod 13) + (rank (x 6) : ZMod 13) + (rank (x 7) : ZMod 13) + (rank (x 8) : ZMod 13) + (rank (x 9) : ZMod 13) + (rank (x 10) : ZMod 13) + (rank (x 11) : ZMod 13) + (rank (x 12) : ZMod 13)) * h13

/-- (0.2) (PROOF.md §0): the row turn is unchanged by `τ` iff `S = 0`. -/
theorem rowTurn_rel_iff (τ : Relabel) (x : Fin 13 → Fin 52) :
    rowTurnV10 (fun j => τ.app (x j).val) = rowTurnV10 (fun j => (x j).val) ↔ rowS τ x = 0 := by
  have hr : ∀ c : Fin 52, ((rank c.val : ℕ) : ZMod 13) = rk c + 1 := by
    intro c; simp [rank, rk]
  unfold rowTurnV10
  rw [← ZMod.natCast_eq_natCast_iff', rowTotal_cast, rowTotal_cast, neg_inj]
  simp only [app_fin, hr]
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
  unfold rowS delta
  refine Eq.congr_left (Finset.sum_congr rfl fun j _ => ?_)
  ring

/-- (0.3) (PROOF.md §0): `S(L^k x) = S(x) − k·D(x)`. -/
theorem rowS_rotate (τ : Relabel) (x : Fin 13 → Fin 52) (k : Fin 13) :
    rowS τ (fun j => x (j + k)) = rowS τ x - (k.val : ZMod 13) * rowD τ x :=
  sum_seat_shift (fun j => delta τ (x j)) k

/-! ## §1 Per-deck reduction (Lemma 1) -/

/-- **Lemma 1 (1⇔2)** (PROOF.md §1): survival on a deck iff all 17 applied
    amounts agree (rows mod 13, columns mod 4). -/
theorem survives_iff_amounts (τ : Relabel) (g : Grid Nat) (hg : IsDeck (scoopColumnMajor g)) :
    sumRanksV10 (relG τ g) = relG τ (sumRanksV10 g) ↔
      (∀ r, rowAmt rowTurnV10 (relG τ g) r % 13 = rowAmt rowTurnV10 g r % 13) ∧
      (∀ c, colAmt colTurnV10 (rowsDone rowTurnV10 (relG τ g) 4) c % 4 =
        colAmt colTurnV10 (rowsDone rowTurnV10 g 4) c % 4) := by
  unfold sumRanksV10
  rw [sumRanksChain_eq, sumRanksChain_eq]
  constructor
  · intro h
    exact amounts_match τ g hg _ _ _ _ h
  · rintro ⟨hr, hc⟩
    rw [relG_colRotate_rowRotate, rowRotate_congr _ _ _ hr, colRotate_congr _ _ _ hc]

theorem relG_colRotate (σ : Relabel) (g : Grid Nat) (s : Fin 13 → Nat) :
    relG σ (colRotate g s) = colRotate (relG σ g) s := by
  funext r c
  simp only [relG, colRotate_apply]

/-- Row conditions along `G`'s own trajectory (PROOF.md §1, Lemma 1(3)): row `r`
    turns by the same amount in `τ G` as in `G`, read off `τ` of `G`'s state. -/
def RowCondsTraj (τ : Relabel) (g : Grid Nat) : Prop :=
  ∀ r : Fin 4,
    rowTurnV10 (relG τ (rowsDone rowTurnV10 g (rowStepOf r - 1)) (prevRow r)) =
      rowTurnV10 (rowsDone rowTurnV10 g (rowStepOf r - 1) (prevRow r))

instance (τ : Relabel) (g : Grid Nat) : Decidable (RowCondsTraj τ g) := by
  unfold RowCondsTraj; infer_instance

/-- Column conditions along `H`'s own trajectory (PROOF.md §1, Lemma 1(3)). -/
def ColCondsTraj (τ : Relabel) (H : Grid Nat) : Prop :=
  ∀ c : Fin 13,
    colTurnV10 (column (relG τ (colsDone colTurnV10 H (colStepOf c - 1))) (prevCol c))
        (column (relG τ (colsDone colTurnV10 H (colStepOf c - 1))) c) =
      colTurnV10 (column (colsDone colTurnV10 H (colStepOf c - 1)) (prevCol c))
        (column (colsDone colTurnV10 H (colStepOf c - 1)) c)

instance (τ : Relabel) (H : Grid Nat) : Decidable (ColCondsTraj τ H) := by
  unfold ColCondsTraj; infer_instance

/-- **Lemma 1 (1⇒3)** (PROOF.md §1): a surviving deck satisfies the row
    conditions and, on the post-row grid `H`, the column conditions, all read
    along its own trajectory. Proof: `survives_iff_amounts`, then induction on
    the step with `turnRow_rel` / `turnCol_rel` (the `τ G` trajectory is `τ` of
    the `G` trajectory while the amounts agree). Only this direction is needed. -/
theorem traj_of_survives (τ : Relabel) (g : Grid Nat) (hg : IsDeck (scoopColumnMajor g))
    (h : sumRanksV10 (relG τ g) = relG τ (sumRanksV10 g)) :
    RowCondsTraj τ g ∧ ColCondsTraj τ (rowsDone rowTurnV10 g 4) := by
  obtain ⟨hr, hc⟩ := (survives_iff_amounts τ g hg).1 h
  have hrows : ∀ n, n ≤ 4 → rowsDone rowTurnV10 (relG τ g) n = relG τ (rowsDone rowTurnV10 g n) := by
    intro n hn
    rw [rowsDone_eq_partial _ _ _ hn, rowsDone_eq_partial _ _ _ hn, relG_rowRotate]
    apply rowRotate_congr
    intro r
    split_ifs
    · exact hr r
    · rfl
  have hH := hrows 4 le_rfl
  have hcols : ∀ n, n ≤ 13 → colsDone colTurnV10 (relG τ (rowsDone rowTurnV10 g 4)) n =
      relG τ (colsDone colTurnV10 (rowsDone rowTurnV10 g 4) n) := by
    intro n hn
    rw [colsDone_eq_partial _ _ _ hn, colsDone_eq_partial _ _ _ hn, relG_colRotate]
    apply colRotate_congr
    intro c
    split_ifs
    · have := hc c; rw [hH] at this; exact this
    · rfl
  refine ⟨fun r => ?_, fun c => ?_⟩
  · have h1 := hr r
    unfold rowAmt at h1
    rw [hrows _ (by unfold rowStepOf; split <;> omega)] at h1
    unfold rowTurnV10 at h1 ⊢
    simpa only [Nat.mod_mod] using h1
  · have h1 := hc c
    unfold colAmt at h1
    rw [hH, hcols _ (by unfold colStepOf; split <;> omega)] at h1
    rwa [Nat.mod_eq_of_lt (colTurnV10_lt _ _), Nat.mod_eq_of_lt (colTurnV10_lt _ _)] at h1

/-! ## §1 Corollary 1: the row equations -/

/-- Row `r` of the deck `π`. -/
def rowOf (π : Equiv.Perm (Fin 52)) (r : Fin 4) : Fin 13 → Fin 52 := fun j => π (cmFlat r j)

/-- Column `j` of the deck `π`. -/
def colOf (π : Equiv.Perm (Fin 52)) (j : Fin 13) : Fin 4 → Fin 52 := fun r => π (cmFlat r j)

theorem rowStepOf_le : ∀ r : Fin 4, rowStepOf r ≤ 4 := by decide
theorem prevRow_succ : ∀ p : Fin 4, prevRow (p + 1) = p := by decide
theorem rowStep_read_iff : ∀ p : Fin 4, rowStepOf p ≤ rowStepOf (p + 1) - 1 ↔ p ≠ 0 := by decide
theorem rowStepOf_of_ne : ∀ r : Fin 4, r ≠ 0 → rowStepOf r = r.val := by decide
theorem prevRow_val_of_ne : ∀ r : Fin 4, r ≠ 0 → (prevRow r).val = r.val - 1 := by decide

/-- Row `r`'s turn (`1 ≤ r`) depends only on rows `0, …, r-1`. -/
theorem rowAmt_congr (g g' : Grid Nat) : ∀ (m : ℕ) (r : Fin 4), r.val = m → 1 ≤ m →
    (∀ r' : Fin 4, r'.val < m → g r' = g' r') →
    rowAmt rowTurnV10 g r = rowAmt rowTurnV10 g' r := by
  intro m
  induction m with
  | zero => intro r _ h; omega
  | succ m ih =>
    intro r hr _ hrows
    have hr0 : r ≠ 0 := by intro e; rw [e] at hr; simp at hr
    have hstep := rowStepOf_of_ne r hr0
    have hprev := prevRow_val_of_ne r hr0
    unfold rowAmt
    rw [rowsDone_eq_partial _ g _ (by have := r.isLt; omega),
      rowsDone_eq_partial _ g' _ (by have := r.isLt; omega)]
    have hamt : (if rowStepOf (prevRow r) ≤ rowStepOf r - 1 then rowAmt rowTurnV10 g (prevRow r)
        else 0) = (if rowStepOf (prevRow r) ≤ rowStepOf r - 1 then
          rowAmt rowTurnV10 g' (prevRow r) else 0) := by
      by_cases hp0 : prevRow r = 0
      · have h4 : ¬ rowStepOf (prevRow r) ≤ rowStepOf r - 1 := by
          rw [hp0, hstep]; have := r.isLt; simp only [rowStepOf]; simp; omega
        rw [if_neg h4, if_neg h4]
      · have hpv : (prevRow r).val ≠ 0 := fun e => hp0 (Fin.ext e)
        split_ifs
        · exact ih (prevRow r) (by omega) (by omega) (fun r' hr' => hrows r' (by omega))
        · rfl
    have hrow : rowRotate g (fun r' => if rowStepOf r' ≤ rowStepOf r - 1 then
          rowAmt rowTurnV10 g r' else 0) (prevRow r) =
        rowRotate g' (fun r' => if rowStepOf r' ≤ rowStepOf r - 1 then
          rowAmt rowTurnV10 g' r' else 0) (prevRow r) := by
      funext j
      rw [rowRotate_apply, rowRotate_apply, hamt, hrows _ (by omega)]
    rw [hrow]

/-- `θ_r`: how far row `r` has turned when it is read (PROOF.md §1 Cor. 1):
    `θ₀ = 0`, `θ_r = t_r` (row `r`'s own turn) for `r = 1, 2, 3`. -/
def thetaG (π : Equiv.Perm (Fin 52)) (r : Fin 4) : ZMod 13 :=
  if r = 0 then 0 else ((rowAmt rowTurnV10 (deckGrid π) r : ℕ) : ZMod 13)

/-- **Corollary 1** (PROOF.md §1): the row conditions are
    `(R_r) S(A_r) = θ_r · D(A_r)`. Proof: `RowCondsTraj` at row `r + 1`,
    `rowsDone_eq_partial` (row `r` has turned by `θ_r` when read, via
    `rowRotate_apply`), `rowTurn_rel_iff` and `rowS_rotate`. -/
theorem rowEq_of_rowCondsTraj (τ : Relabel) (π : Equiv.Perm (Fin 52))
    (h : RowCondsTraj τ (deckGrid π)) :
    ∀ r, rowS τ (rowOf π r) = thetaG π r * rowD τ (rowOf π r) := by
  intro p
  have hc := h (p + 1)
  rw [prevRow_succ, rowsDone_eq_partial _ _ _ (by have := rowStepOf_le (p + 1); omega)] at hc
  set A := (if rowStepOf p ≤ rowStepOf (p + 1) - 1 then rowAmt rowTurnV10 (deckGrid π) p else 0)
    with hA
  let k : Fin 13 := ⟨A % 13, Nat.mod_lt _ (by decide)⟩
  have hrow : ∀ G : Grid Nat, G = deckGrid π →
      rowRotate G (fun r => if rowStepOf r ≤ rowStepOf (p + 1) - 1 then
        rowAmt rowTurnV10 (deckGrid π) r else 0) p = fun j => (rowOf π p (j + k)).val := by
    intro G hG
    funext j
    rw [rowRotate_apply, hG, deckGrid_apply]
    simp only [rowOf]
    congr 3
  have hrel : ∀ (G : Grid Nat), relG τ G p = fun j => τ.app (G p j) := fun _ => rfl
  rw [hrel, hrow _ rfl] at hc
  have h0 := (rowTurn_rel_iff τ (fun j => rowOf π p (j + k))).1 hc
  rw [rowS_rotate, sub_eq_zero] at h0
  rw [h0]
  congr 1
  simp only [thetaG, k]
  by_cases hp : p = 0
  · rw [if_pos hp]
    have : A = 0 := by rw [hA, if_neg]; rw [rowStep_read_iff]; exact not_not.2 hp
    simp [this]
  · rw [if_neg hp]
    have : A = rowAmt rowTurnV10 (deckGrid π) p := by rw [hA, if_pos ((rowStep_read_iff p).2 hp)]
    rw [this, ZMod.natCast_mod]

/-- `θ_r` depends only on rows `0..r-1` (PROOF.md §1 Cor. 1, used in Lemma 3). -/
theorem thetaG_prefix (π π' : Equiv.Perm (Fin 52)) (r : Fin 4)
    (h : ∀ r' < r, rowOf π r' = rowOf π' r') : thetaG π r = thetaG π' r := by
  unfold thetaG
  split_ifs with hr
  · rfl
  · have hr1 : 1 ≤ r.val := by
      rcases Nat.eq_zero_or_pos r.val with e | e
      · exact absurd (Fin.ext e) hr
      · exact e
    rw [rowAmt_congr _ _ r.val r rfl hr1 fun r' hr' => ?_]
    funext j
    rw [deckGrid_apply, deckGrid_apply]
    exact congrArg Fin.val (congrFun (h r' (Fin.lt_def.2 hr')) j)

/-! ## §2 One row: `ρ` and Lemma 3 -/

/-- `ρ(B)` (PROOF.md §2): `1/13` if `D ≠ 0`, else the fraction of the `13!`
    arrangements of the row with `S = 0`. Depends only on the set of the row. -/
def rho (τ : Relabel) (x : Fin 13 → Fin 52) : ℚ :=
  if rowD τ x ≠ 0 then 1 / 13
  else ((univ.filter fun σ : Equiv.Perm (Fin 13) => rowS τ (x ∘ σ) = 0).card : ℚ) /
    (Nat.factorial 13 : ℕ)

theorem rho_nonneg (τ : Relabel) (x : Fin 13 → Fin 52) : 0 ≤ rho τ x := by
  unfold rho; split_ifs <;> positivity

theorem rowOf_mul_rowShuf (π : Equiv.Perm (Fin 52)) (σ : Fin 4 → Equiv.Perm (Fin 13)) (r : Fin 4) :
    rowOf (π * rowShuf σ) r = rowOf π r ∘ σ r := by
  funext j; simp [rowOf, Equiv.Perm.mul_apply, rowShuf_cmFlat]

theorem colOf_mul_colShuf (π : Equiv.Perm (Fin 52)) (σ : Fin 13 → Equiv.Perm (Fin 4)) (j : Fin 13) :
    colOf (π * colShuf σ) j = colOf π j ∘ σ j := by
  funext r; simp [colOf, Equiv.Perm.mul_apply, colShuf_cmFlat]

theorem rowD_comp (τ : Relabel) (x : Fin 13 → Fin 52) (a : Equiv.Perm (Fin 13)) :
    rowD τ (x ∘ a) = rowD τ x :=
  Equiv.sum_comp a (fun j => delta τ (x j))

/-- **Lemma 3 (row chain)** (PROOF.md §2): with the targets `θ π r` depending
    only on earlier rows, the decks satisfying all four row equations number at
    most `Σ_π Π_r ρ(row r)` (the paper proves equality). Proof: split `π` into
    its row sets and four arrangements (`Equiv.Perm` of each row), then
    `card_filter_product_le` four times with Lemma 2(a) / the definition of `ρ`
    in the innermost row. -/
theorem rowChain_le (τ : Relabel) (θ : Equiv.Perm (Fin 52) → Fin 4 → ZMod 13)
    (hθ : ∀ π π' r, (∀ r' < r, rowOf π r' = rowOf π' r') → θ π r = θ π' r) :
    ((univ.filter fun π : Equiv.Perm (Fin 52) =>
        ∀ r, rowS τ (rowOf π r) = θ π r * rowD τ (rowOf π r)).card : ℚ) ≤
      ∑ π : Equiv.Perm (Fin 52), ∏ r, rho τ (rowOf π r) := by
  classical
  -- per-deck count of good row orders
  let Nr : Equiv.Perm (Fin 52) → Fin 4 → ℕ := fun π r =>
    if rowD τ (rowOf π r) ≠ 0 then Nat.factorial 12
    else (univ.filter fun σ : Equiv.Perm (Fin 13) => rowS τ (rowOf π r ∘ σ) = 0).card
  have hNr : ∀ π r, (Nr π r : ℚ) = (Nat.factorial 13 : ℕ) * rho τ (rowOf π r) := by
    intro π r
    simp only [Nr, rho]
    split_ifs
    · rw [Nat.factorial_succ 12]; push_cast; ring
    · field_simp
  let Q : Equiv.Perm (Fin 52) → Fin 4 → (Fin 4 → Equiv.Perm (Fin 13)) → Prop := fun π r σ =>
    rowS τ (rowOf (π * rowShuf σ) r) = θ (π * rowShuf σ) r * rowD τ (rowOf (π * rowShuf σ) r)
  have hrows : ∀ π σ σ' (r : Fin 4), σ r = σ' r →
      rowOf (π * rowShuf σ) r = rowOf (π * rowShuf σ') r := by
    intro π σ σ' r h
    rw [rowOf_mul_rowShuf, rowOf_mul_rowShuf, h]
  have hper : ∀ π, (univ.filter fun σ : Fin 4 → Equiv.Perm (Fin 13) =>
      ∀ r, Q π r σ).card ≤ ∏ r, Nr π r := by
    intro π
    refine nested_count 4 (Q π) (Nr π) ?_ ?_
    · intro r σ σ' h
      have hθ' : θ (π * rowShuf σ) r = θ (π * rowShuf σ') r :=
        hθ _ _ r fun r' hr' => hrows π σ σ' r' (h r' hr'.le)
      simp only [Q, hθ', hrows π σ σ' r (h r le_rfl)]
    · intro r σ
      set x := rowOf π r
      set t := θ (π * rowShuf σ) r
      have hQa : ∀ a, Q π r (Function.update σ r a) ↔ rowS τ (x ∘ a) = t * rowD τ x := by
        intro a
        have h1 : rowOf (π * rowShuf (Function.update σ r a)) r = x ∘ a := by
          rw [rowOf_mul_rowShuf, Function.update_same]
        have h2 : θ (π * rowShuf (Function.update σ r a)) r = t :=
          hθ _ _ r fun r' hr' => hrows π _ _ r' (Function.update_noteq (ne_of_lt hr') _ _)
        simp only [Q, h1, h2, rowD_comp]
      simp only [hQa]
      simp only [Nr]
      split_ifs with hD
      · have h := lemma2a (fun j => delta τ (x j)) hD (t * rowD τ x)
        rw [Nat.factorial_succ 12] at h
        have : (univ.filter fun a : Equiv.Perm (Fin 13) => rowS τ (x ∘ a) = t * rowD τ x).card =
            Nat.factorial 12 := by
          have h' : 13 * (univ.filter fun a : Equiv.Perm (Fin 13) =>
              rowS τ (x ∘ a) = t * rowD τ x).card = 13 * Nat.factorial 12 := h
          omega
        exact this.le
      · push_neg at hD
        simp only [hD, mul_zero, le_refl]
  -- average over row orders
  have havg := sum_mul_card_shuf rowShuf
    (fun π => if ∀ r, rowS τ (rowOf π r) = θ π r * rowD τ (rowOf π r) then (1 : ℚ) else 0)
  have hcardS : (Fintype.card (Fin 4 → Equiv.Perm (Fin 13)) : ℚ) = ((Nat.factorial 13 : ℕ) : ℚ) ^ 4 := by
    rw [Fintype.card_fun, Fintype.card_perm, Fintype.card_fin, Fintype.card_fin]; push_cast; ring
  rw [hcardS] at havg
  have hlhs : ((univ.filter fun π : Equiv.Perm (Fin 52) =>
      ∀ r, rowS τ (rowOf π r) = θ π r * rowD τ (rowOf π r)).card : ℚ) =
      ∑ π, if ∀ r, rowS τ (rowOf π r) = θ π r * rowD τ (rowOf π r) then (1 : ℚ) else 0 := by
    rw [← sum_boole]
  have hrhs : ∀ π, (∑ σ : Fin 4 → Equiv.Perm (Fin 13),
      if ∀ r, rowS τ (rowOf (π * rowShuf σ) r) = θ (π * rowShuf σ) r *
        rowD τ (rowOf (π * rowShuf σ) r) then (1 : ℚ) else 0) ≤
      ((Nat.factorial 13 : ℕ) : ℚ) ^ 4 * ∏ r, rho τ (rowOf π r) := by
    intro π
    rw [sum_boole]
    have := hper π
    have hq : ((univ.filter fun σ : Fin 4 → Equiv.Perm (Fin 13) => ∀ r, Q π r σ).card : ℚ) ≤
        ∏ r, (Nr π r : ℚ) := by exact_mod_cast this
    simp only [hNr, prod_mul_distrib, prod_const, card_univ, Fintype.card_fin] at hq
    exact hq
  have hf : (0 : ℚ) < ((Nat.factorial 13 : ℕ) : ℚ) ^ 4 := by positivity
  rw [hlhs]
  refine le_of_mul_le_mul_left ?_ hf
  rw [havg, mul_sum]
  exact sum_le_sum fun π _ => hrhs π

/-- `ρ ≤ 1`. -/
theorem rho_le_one (τ : Relabel) (x : Fin 13 → Fin 52) : rho τ x ≤ 1 := by
  unfold rho
  split_ifs
  · norm_num
  · rw [div_le_one (by exact_mod_cast Nat.factorial_pos 13)]
    have := card_filter_le (univ : Finset (Equiv.Perm (Fin 13)))
      (fun σ => rowS τ (x ∘ σ) = 0)
    rw [card_univ, Fintype.card_perm, Fintype.card_fin] at this
    exact_mod_cast this

/-- Pointwise row bound (PROOF.md §3 (A2), from Lemma 2(a),(b)): if the row
    has `z` cards of value `v`, then `ρ ≤ h(z)`. -/
theorem rho_le_hA (τ : Relabel) (x : Fin 13 → Fin 52) (v : ZMod 13) :
    rho τ x ≤ hA (univ.filter fun j => delta τ (x j) = v).card := by
  set z := (univ.filter fun j => delta τ (x j) = v).card with hz
  unfold hA
  split_ifs with h13
  · exact rho_le_one τ x
  · have hz13 : z ≤ 13 := by
      have := card_filter_le (univ : Finset (Fin 13)) (fun j => delta τ (x j) = v)
      simpa using this
    have hnc : ∃ i, delta τ (x i) ≠ v := by
      by_contra hc
      push_neg at hc
      apply h13
      rw [hz, filter_true_of_mem (fun j _ => hc j)]
      simp
    have hz1 : (0 : ℚ) < z + 1 := by positivity
    unfold rho
    split_ifs with hD
    · rw [div_le_div_iff₀ (by norm_num) hz1]
      have : (z : ℚ) ≤ 12 := by exact_mod_cast (by omega : z ≤ 12)
      linarith
    · have hb := lemma2b (fun j => delta τ (x j)) v hnc 0
      have hf : (0 : ℚ) < (Nat.factorial 13 : ℕ) := by exact_mod_cast Nat.factorial_pos 13
      rw [div_le_div_iff₀ hf hz1, one_mul]
      have hb' : ((z + 1) * (univ.filter fun σ : Equiv.Perm (Fin 13) =>
          rowS τ (x ∘ σ) = 0).card : ℕ) ≤ Nat.factorial 13 := hb
      have := (Nat.cast_le (α := ℚ)).2 hb'
      push_cast at this
      linarith

/-- (A3) (PROOF.md §3): a row with a repeated value has `ρ ≤ 1/3`; any row has `ρ ≤ 1`. -/
theorem rho_le_third (τ : Relabel) (x : Fin 13 → Fin 52) (i j : Fin 13) (hij : i ≠ j)
    (he : delta τ (x i) = delta τ (x j)) (hnc : ∃ k, delta τ (x k) ≠ delta τ (x i)) :
    rho τ x ≤ 1 / 3 := by
  have h := rho_le_hA τ x (delta τ (x i))
  set z := (univ.filter fun k => delta τ (x k) = delta τ (x i)).card with hz
  have h2 : 2 ≤ z := by
    rw [hz]
    have : ({i, j} : Finset (Fin 13)) ⊆ univ.filter fun k => delta τ (x k) = delta τ (x i) := by
      intro k hk
      simp only [mem_insert, mem_singleton] at hk
      rcases hk with rfl | rfl <;> simp [he]
    have := card_le_card this
    rwa [card_pair hij] at this
  have h13 : z ≠ 13 := by
    intro e
    obtain ⟨k, hk⟩ := hnc
    have : univ.filter (fun k => delta τ (x k) = delta τ (x i)) = univ :=
      eq_univ_of_card _ (by rw [← hz, e]; rfl)
    have hk' : k ∈ univ.filter fun k => delta τ (x k) = delta τ (x i) := by rw [this]; simp
    simp only [mem_filter] at hk'
    exact hk hk'.2
  unfold hA at h
  rw [if_neg h13] at h
  refine h.trans ?_
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  have : (2 : ℚ) ≤ z := by exact_mod_cast h2
  linarith

/-- (A1) (PROOF.md §3, Lemma 2(c)): a cancelling pair in one row gives `ρ = 0`. -/
theorem rho_eq_zero_of_cancel (τ : Relabel) (x : Fin 13 → Fin 52) (v u : ZMod 13) (hu : u ≠ 0)
    (i₁ i₂ : Fin 13) (h12 : i₁ ≠ i₂) (h₁ : delta τ (x i₁) = v + u) (h₂ : delta τ (x i₂) = v - u)
    (h : ∀ i, i ≠ i₁ → i ≠ i₂ → delta τ (x i) = v) : rho τ x = 0 := by
  have hD : rowD τ x = 0 := sum_of_cancel (fun j => delta τ (x j)) v u i₁ i₂ h12 h₁ h₂ h
  unfold rho
  rw [if_neg (not_not.2 hD)]
  have : (univ.filter fun σ : Equiv.Perm (Fin 13) => rowS τ (x ∘ σ) = 0) = ∅ := by
    apply filter_false_of_mem
    intro σ _
    exact lemma2c (fun j => delta τ (x j)) v u hu i₁ i₂ h12 h₁ h₂ h σ
  rw [this]; simp

/-! ## §3 Case A (`δ` not constant) -/

/-- The `δ`-class of `v`. -/
def cls (τ : Relabel) (v : ZMod 13) : Finset (Fin 52) := univ.filter fun c => delta τ c = v

/-- `n*`: the size of the largest `δ`-class (PROOF.md §3). -/
def nStar (τ : Relabel) : ℕ := univ.sup fun v => (cls τ v).card

theorem exists_vStar (τ : Relabel) : ∃ v, (cls τ v).card = nStar τ := by
  obtain ⟨v, -, hv⟩ := Finset.exists_mem_eq_sup (univ : Finset (ZMod 13)) univ_nonempty
    (fun v => (cls τ v).card)
  exact ⟨v, hv.symm⟩

/-- `n* ≤ 50` when `δ` is not constant: `n* = 52` is excluded by assumption and
    `n* = 51` by `Σ δ = 0` (PROOF.md §3). -/
theorem nStar_le_50 (τ : Relabel) (h : ∃ c, delta τ c ≠ delta τ 0) : nStar τ ≤ 50 :=
  Finset.sup_le fun v _ => maxClass_le_50 (delta τ) (sum_delta τ) h v

/-- The sum bounded in Case A: `Σ_π Π_r ρ(row r)`. -/
def rhoSum (τ : Relabel) : ℚ := ∑ π : Equiv.Perm (Fin 52), ∏ r, rho τ (rowOf π r)

/-- Survivors are bounded by the row sum (PROOF.md §3, via Lemma 1, Cor. 1 and
    Lemma 3). -/
theorem survivors_le_rhoSum (τ : Relabel) : ((survivors τ).card : ℚ) ≤ rhoSum τ := by
  refine le_trans ?_ (rowChain_le τ thetaG thetaG_prefix)
  exact_mod_cast card_le_card fun π hπ => by
    simp only [survivors, mem_filter, mem_univ, true_and] at hπ ⊢
    exact rowEq_of_rowCondsTraj τ π
      (traj_of_survives τ _ (isDeck_deckGrid π) hπ).1

/-! ### Helpers: block counts and factorials -/

theorem cmFlat_row_col (p : Fin 52) (r : Fin 4) (h : p.val % 4 = r.val) : cmFlat r (cmCol p) = p := by
  apply Fin.ext; simp only [cmFlat, cmCol]; omega

theorem cmFlat_col_row (p : Fin 52) (j : Fin 13) (h : p.val / 4 = j.val) : cmFlat (cmRow p) j = p := by
  apply Fin.ext; simp only [cmFlat, cmRow]; omega

theorem card_row_eq_zRow (W : Finset (Fin 52)) (π : Equiv.Perm (Fin 52)) (r : Fin 4)
    (P : Fin 52 → Prop) [DecidablePred P] (hP : ∀ c, P c ↔ c ∈ W) :
    (univ.filter fun j : Fin 13 => P (π (cmFlat r j))).card = zRow W π r := by
  unfold zRow
  apply card_nbij' (fun j => cmFlat r j) (fun p => cmCol p)
  · intro j hj
    simp only [mem_filter, mem_univ, true_and] at hj ⊢
    refine ⟨by simp only [cmFlat]; omega, (hP _).1 hj⟩
  · intro p hp
    simp only [mem_filter, mem_univ, true_and] at hp ⊢
    rw [cmFlat_row_col p r hp.1]; exact (hP _).2 hp.2
  · intro j _
    apply Fin.ext; simp only [cmFlat, cmCol]; omega
  · intro p hp
    simp only [mem_filter, mem_univ, true_and] at hp
    exact cmFlat_row_col p r hp.1

theorem card_col_eq_yCol (W : Finset (Fin 52)) (π : Equiv.Perm (Fin 52)) (j : Fin 13)
    (P : Fin 52 → Prop) [DecidablePred P] (hP : ∀ c, P c ↔ c ∈ W) :
    (univ.filter fun r : Fin 4 => P (π (cmFlat r j))).card = yCol W π j := by
  unfold yCol
  apply card_nbij' (fun r => cmFlat r j) (fun p => cmRow p)
  · intro r hr
    simp only [mem_filter, mem_univ, true_and] at hr ⊢
    refine ⟨by simp only [cmFlat]; omega, (hP _).1 hr⟩
  · intro p hp
    simp only [mem_filter, mem_univ, true_and] at hp ⊢
    rw [cmFlat_col_row p j hp.1]; exact (hP _).2 hp.2
  · intro r _
    apply Fin.ext; simp only [cmFlat, cmRow]; omega
  · intro p hp
    simp only [mem_filter, mem_univ, true_and] at hp
    exact cmFlat_col_row p j hp.1

theorem factorial_split (n : ℕ) (hn : n ≤ 52) (X : ℚ) :
    ((n.factorial * (52 - n).factorial : ℕ) : ℚ) * X =
      (Nat.factorial 52 : ℕ) * (X / (Nat.choose 52 n : ℕ)) := by
  have h := Nat.choose_mul_factorial_mul_factorial hn
  have hc : (0 : ℚ) < (Nat.choose 52 n : ℕ) := by exact_mod_cast Nat.choose_pos hn
  rw [← h]
  push_cast
  field_simp
  ring

/-! ### Helpers for (A3) -/

theorem cmFlat_injective (r : Fin 4) : Function.Injective (cmFlat r) := by
  intro i j h
  have := congrArg Fin.val h
  simp only [cmFlat] at this
  apply Fin.ext; omega

theorem rowOf_injective (π : Equiv.Perm (Fin 52)) (r : Fin 4) :
    Function.Injective (rowOf π r) :=
  π.injective.comp (cmFlat_injective r)

/-- With `n* ≤ 12` no row is `δ`-constant (a constant row is 13 cards of one class). -/
theorem row_nonconst (τ : Relabel) (h : nStar τ ≤ 12) (π : Equiv.Perm (Fin 52)) (r : Fin 4)
    (i : Fin 13) : ∃ k, delta τ (rowOf π r k) ≠ delta τ (rowOf π r i) := by
  classical
  by_contra hc
  push_neg at hc
  have hsub : univ.image (rowOf π r) ⊆ cls τ (delta τ (rowOf π r i)) := by
    intro c hc'
    obtain ⟨k, -, rfl⟩ := mem_image.1 hc'
    simp [cls, hc k]
  have h1 := card_le_card hsub
  rw [card_image_of_injective _ (rowOf_injective π r), card_univ, Fintype.card_fin] at h1
  have h2 : (cls τ (delta τ (rowOf π r i))).card ≤ nStar τ :=
    le_sup (f := fun v => (cls τ v).card) (mem_univ _)
  omega

/-- Row `r` of `π` has pairwise distinct `δ`-values (the predicate of `distinct_row_count`). -/
def rowDistinct (τ : Relabel) (π : Equiv.Perm (Fin 52)) (r : Fin 4) : Prop :=
  ∀ p q : Fin 52, p.val % 4 = r.val → q.val % 4 = r.val → p ≠ q → delta τ (π p) ≠ delta τ (π q)

instance (τ : Relabel) (π : Equiv.Perm (Fin 52)) (r : Fin 4) : Decidable (rowDistinct τ π r) :=
  inferInstanceAs (Decidable (∀ p q : Fin 52, p.val % 4 = r.val → q.val % 4 = r.val → p ≠ q →
    delta τ (π p) ≠ delta τ (π q)))

theorem rho_prod_le_A3 (τ : Relabel) (h : nStar τ ≤ 12) (π : Equiv.Perm (Fin 52)) :
    ∏ r, rho τ (rowOf π r) ≤ 1 / 81 + ∑ r, (if rowDistinct τ π r then (1 : ℚ) else 0) := by
  by_cases hd : ∃ r, rowDistinct τ π r
  · obtain ⟨r0, hr0⟩ := hd
    have hp : ∏ r, rho τ (rowOf π r) ≤ 1 :=
      prod_le_one (fun r _ => rho_nonneg τ _) (fun r _ => rho_le_one τ _)
    have hs : (1 : ℚ) ≤ ∑ r, (if rowDistinct τ π r then (1 : ℚ) else 0) := by
      have := single_le_sum (f := fun r => if rowDistinct τ π r then (1 : ℚ) else 0)
        (fun r _ => by dsimp only; split_ifs <;> norm_num) (mem_univ r0)
      simpa [hr0] using this
    linarith
  · push_neg at hd
    have h3 : ∀ r, rho τ (rowOf π r) ≤ 1 / 3 := by
      intro r
      have := hd r
      unfold rowDistinct at this
      push_neg at this
      obtain ⟨p, q, hp, hq, hpq, he⟩ := this
      have ep : rowOf π r (cmCol p) = π p := by simp only [rowOf]; rw [cmFlat_row_col p r hp]
      have eq' : rowOf π r (cmCol q) = π q := by simp only [rowOf]; rw [cmFlat_row_col q r hq]
      have hne : cmCol p ≠ cmCol q := by
        intro e; apply hpq
        rw [← cmFlat_row_col p r hp, ← cmFlat_row_col q r hq, e]
      exact rho_le_third τ _ _ _ hne (by rw [ep, eq']; exact he) (row_nonconst τ h π r _)
    have hp : ∏ r, rho τ (rowOf π r) ≤ ∏ _r : Fin 4, (1 / 3 : ℚ) :=
      prod_le_prod (fun r _ => rho_nonneg τ _) (fun r _ => h3 r)
    rw [prod_const, card_univ, Fintype.card_fin] at hp
    have hs : (0 : ℚ) ≤ ∑ r, (if rowDistinct τ π r then (1 : ℚ) else 0) :=
      sum_nonneg fun r _ => by split_ifs <;> norm_num
    have : ((1 : ℚ) / 3) ^ 4 = 1 / 81 := by norm_num
    linarith

/-! ### Helpers for (A1): two-card position counts -/

/-- All ordered pairs of distinct seats carry the same number of decks with
    `a` at the first seat and `b` at the second (right-multiply by a seat perm). -/
theorem pairCount_eq (a b p q p' q' : Fin 52) (hpq : p ≠ q) (hpq' : p' ≠ q') :
    (univ.filter fun π : Equiv.Perm (Fin 52) => π p = a ∧ π q = b).card =
      (univ.filter fun π : Equiv.Perm (Fin 52) => π p' = a ∧ π q' = b).card := by
  obtain ⟨σ, hσ1, hσ2⟩ := exists_perm_two p' q' p q hpq' hpq
  have hi1 : σ⁻¹ p = p' := Equiv.Perm.inv_eq_iff_eq.2 hσ1.symm
  have hi2 : σ⁻¹ q = q' := Equiv.Perm.inv_eq_iff_eq.2 hσ2.symm
  apply card_nbij' (fun π => π * σ) (fun π => π * σ⁻¹)
  · intro π hπ
    simp only [coe_filter, Set.mem_setOf_eq, mem_filter, mem_univ, true_and,
      Equiv.Perm.mul_apply] at hπ ⊢
    rw [hσ1, hσ2]; exact hπ
  · intro π hπ
    simp only [coe_filter, Set.mem_setOf_eq, mem_filter, mem_univ, true_and,
      Equiv.Perm.mul_apply] at hπ ⊢
    rw [hi1, hi2]; exact hπ
  · intro π _; simp [mul_assoc]
  · intro π _; simp [mul_assoc]

/-- Fibre count over the seats of two distinct cards `a ≠ b`. -/
theorem card_seat_pairs (a b : Fin 52) (hab : a ≠ b) (R : Fin 52 → Fin 52 → Prop)
    [∀ p q, Decidable (R p q)] (hR : ∀ p q, R p q → p ≠ q) :
    (univ.filter fun π : Equiv.Perm (Fin 52) => R (π⁻¹ a) (π⁻¹ b)).card =
      (univ.filter fun x : Fin 52 × Fin 52 => R x.1 x.2).card *
        (univ.filter fun π : Equiv.Perm (Fin 52) => π 0 = a ∧ π 1 = b).card := by
  rw [card_eq_sum_card_fiberwise (f := fun π : Equiv.Perm (Fin 52) => (π⁻¹ a, π⁻¹ b))
    (t := univ.filter fun x : Fin 52 × Fin 52 => R x.1 x.2)]
  · rw [← smul_eq_mul, ← sum_const]
    apply sum_congr rfl
    intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    rw [← pairCount_eq a b x.1 x.2 0 1 (hR _ _ hx) (by decide)]
    apply congrArg card
    ext π
    simp only [mem_filter, mem_univ, true_and, Prod.ext_iff]
    constructor
    · rintro ⟨-, h1, h2⟩
      exact ⟨(Equiv.Perm.inv_eq_iff_eq.1 h1).symm, (Equiv.Perm.inv_eq_iff_eq.1 h2).symm⟩
    · rintro ⟨h1, h2⟩
      have e1 : π⁻¹ a = x.1 := Equiv.Perm.inv_eq_iff_eq.2 h1.symm
      have e2 : π⁻¹ b = x.2 := Equiv.Perm.inv_eq_iff_eq.2 h2.symm
      exact ⟨by rw [e1, e2]; exact hx, e1, e2⟩
  · intro π hπ
    simpa only [mem_filter, mem_univ, true_and] using hπ

theorem card_filter_prod (R : Fin 52 → Fin 52 → Prop) [∀ p q, Decidable (R p q)] :
    (univ.filter fun x : Fin 52 × Fin 52 => R x.1 x.2).card =
      ∑ p, (univ.filter fun q => R p q).card := by
  simp only [card_eq_sum_ones, sum_filter]
  exact Fintype.sum_prod_type _

theorem card_other_rows : ∀ r : Fin 4,
    (univ.filter fun q : Fin 52 => ¬ r.val = q.val % 4).card = 39 := by decide

theorem card_diffRow_pairs :
    (univ.filter fun x : Fin 52 × Fin 52 => ¬ x.1.val % 4 = x.2.val % 4).card = 2028 := by
  refine (card_filter_prod (fun p q : Fin 52 => ¬ p.val % 4 = q.val % 4)).trans ?_
  have : ∀ p : Fin 52, (univ.filter fun q : Fin 52 => ¬ p.val % 4 = q.val % 4).card = 39 :=
    fun p => card_other_rows (cmRow p)
  simp only [this, sum_const, card_univ, Fintype.card_fin, smul_eq_mul]

theorem card_ne_pairs :
    (univ.filter fun x : Fin 52 × Fin 52 => x.1 ≠ x.2).card = 2652 := by
  refine (card_filter_prod (fun p q : Fin 52 => p ≠ q)).trans ?_
  have : ∀ p : Fin 52, (univ.filter fun q : Fin 52 => p ≠ q).card = 51 := by
    intro p
    rw [filter_ne, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
  simp only [this, sum_const, card_univ, Fintype.card_fin, smul_eq_mul]

/-- A row whose cards all have `δ = v` except one has `D ≠ 0`, hence `ρ = 1/13`. -/
theorem rho_of_single (τ : Relabel) (x : Fin 13 → Fin 52) (v : ZMod 13) (i₁ : Fin 13)
    (h : ∀ j, j ≠ i₁ → delta τ (x j) = v) (hne : delta τ (x i₁) ≠ v) : rho τ x = 1 / 13 := by
  have hD : rowD τ x ≠ 0 := by
    have e : ∑ j, (delta τ (x j) - v) = delta τ (x i₁) - v :=
      Fintype.sum_eq_single i₁ fun j hj => by rw [h j hj, sub_self]
    rw [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at e
    have h13 : ((13 : ℕ) : ZMod 13) = 0 := by decide
    rw [h13, zero_mul, sub_zero] at e
    unfold rowD; rw [e]; exact sub_ne_zero.2 hne
  unfold rho; rw [if_pos hD]

theorem rowOf_ne_of_row (π : Equiv.Perm (Fin 52)) (r : Fin 4) (j : Fin 13) (p : Fin 52)
    (hr : r.val ≠ p.val % 4) : rowOf π r j ≠ π p := by
  intro e
  simp only [rowOf] at e
  have := congrArg Fin.val (π.injective e)
  simp only [cmFlat] at this
  have := r.isLt
  omega

/-- Pointwise (A1) bound: `0` if the two off cards share a row, else `1/169`. -/
theorem rho_prod_le_A1 (τ : Relabel) (v u : ZMod 13) (hu : u ≠ 0) (c₁ c₂ : Fin 52)
    (h12 : c₁ ≠ c₂) (h1 : delta τ c₁ = v + u) (h2 : delta τ c₂ = v - u)
    (hoff : ∀ c, c ≠ c₁ → c ≠ c₂ → delta τ c = v) (π : Equiv.Perm (Fin 52)) :
    ∏ r, rho τ (rowOf π r) ≤
      if (π⁻¹ c₁).val % 4 = (π⁻¹ c₂).val % 4 then 0 else 1 / 169 := by
  classical
  have e₁ : π (π⁻¹ c₁) = c₁ := by simp
  have e₂ : π (π⁻¹ c₂) = c₂ := by simp
  have hu1 : v + u ≠ v := fun e => hu (by linear_combination e)
  have hu2 : v - u ≠ v := fun e => hu (by linear_combination -e)
  split_ifs with hs
  · set r := cmRow (π⁻¹ c₁)
    have hr1 : (π⁻¹ c₁).val % 4 = r.val := rfl
    have hr2 : (π⁻¹ c₂).val % 4 = r.val := by rw [← hs]; rfl
    apply le_of_eq
    apply prod_eq_zero (mem_univ r)
    have x1 : rowOf π r (cmCol (π⁻¹ c₁)) = c₁ := by
      simp only [rowOf]; rw [cmFlat_row_col _ r hr1, e₁]
    have x2 : rowOf π r (cmCol (π⁻¹ c₂)) = c₂ := by
      simp only [rowOf]; rw [cmFlat_row_col _ r hr2, e₂]
    have hne : cmCol (π⁻¹ c₁) ≠ cmCol (π⁻¹ c₂) := fun e => h12 (by rw [← x1, ← x2, e])
    refine rho_eq_zero_of_cancel τ _ v u hu _ _ hne (by rw [x1, h1]) (by rw [x2, h2]) ?_
    intro i hi1 hi2
    apply hoff
    · rw [← x1]; exact fun e => hi1 (rowOf_injective π r e)
    · rw [← x2]; exact fun e => hi2 (rowOf_injective π r e)
  · set r₁ := cmRow (π⁻¹ c₁)
    set r₂ := cmRow (π⁻¹ c₂)
    have hr1 : (π⁻¹ c₁).val % 4 = r₁.val := rfl
    have hr2 : (π⁻¹ c₂).val % 4 = r₂.val := rfl
    have hr12 : r₁ ≠ r₂ := fun e => hs (by rw [hr1, hr2, e])
    have x1 : rowOf π r₁ (cmCol (π⁻¹ c₁)) = c₁ := by
      simp only [rowOf]; rw [cmFlat_row_col _ r₁ hr1, e₁]
    have x2 : rowOf π r₂ (cmCol (π⁻¹ c₂)) = c₂ := by
      simp only [rowOf]; rw [cmFlat_row_col _ r₂ hr2, e₂]
    have hb : ∀ r, rho τ (rowOf π r) ≤
        (if r = r₁ then 1 / 13 else 1) * (if r = r₂ then 1 / 13 else 1) := by
      intro r
      by_cases h1r : r = r₁
      · subst h1r
        rw [if_pos rfl, if_neg hr12, mul_one]
        apply le_of_eq
        refine rho_of_single τ _ v (cmCol (π⁻¹ c₁)) ?_ (by rw [x1, h1]; exact hu1)
        intro j hj
        apply hoff
        · rw [← x1]; exact fun e => hj (rowOf_injective π _ e)
        · rw [← e₂]
          exact rowOf_ne_of_row π _ j _ (by rw [← hr1]; exact hs)
      · by_cases h2r : r = r₂
        · subst h2r
          rw [if_neg h1r, if_pos rfl, one_mul]
          apply le_of_eq
          refine rho_of_single τ _ v (cmCol (π⁻¹ c₂)) ?_ (by rw [x2, h2]; exact hu2)
          intro j hj
          apply hoff
          · rw [← e₁]
            exact rowOf_ne_of_row π _ j _ (by rw [← hr2]; exact fun e => hs e.symm)
          · rw [← x2]; exact fun e => hj (rowOf_injective π _ e)
        · rw [if_neg h1r, if_neg h2r, mul_one]; exact rho_le_one τ _
    calc ∏ r, rho τ (rowOf π r)
        ≤ ∏ r, (if r = r₁ then (1 : ℚ) / 13 else 1) * (if r = r₂ then 1 / 13 else 1) :=
          prod_le_prod (fun r _ => rho_nonneg τ _) (fun r _ => hb r)
      _ = 1 / 169 := by
          rw [prod_mul_distrib, prod_ite_eq' univ r₁ (fun _ => (1 : ℚ) / 13),
            prod_ite_eq' univ r₂ (fun _ => (1 : ℚ) / 13), if_pos (mem_univ _),
            if_pos (mem_univ _)]
          norm_num

/-- **(A1)** (PROOF.md §3): `n* = 50` gives `Σ ≤ 52!/221` (the two off cards
    are `v* ± u`; same row: `ρ = 0` by `rho_eq_zero_of_cancel`; different rows:
    `1/13` each; probability of different rows `39/51`). -/
theorem caseA1 (τ : Relabel) (h : nStar τ = 50) : 221 * rhoSum τ ≤ (Nat.factorial 52 : ℕ) := by
  classical
  obtain ⟨v, hv⟩ := exists_vStar τ
  rw [h] at hv
  have hO : (univ.filter fun c => ¬ delta τ c = v).card = 2 := by
    have := filter_card_add_filter_neg_card_eq_card (s := (univ : Finset (Fin 52)))
      (fun c => delta τ c = v)
    have e : (univ.filter fun c => delta τ c = v).card = 50 := hv
    rw [e, card_univ, Fintype.card_fin] at this
    omega
  obtain ⟨c₁, c₂, h12, hc⟩ := card_eq_two.1 hO
  have hmem : ∀ c, c ∈ univ.filter (fun c => ¬ delta τ c = v) ↔ c ∈ ({c₁, c₂} : Finset _) :=
    fun c => by rw [hc]
  simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton] at hmem
  have hoff : ∀ c, c ≠ c₁ → c ≠ c₂ → delta τ c = v := by
    intro c h1 h2
    by_contra hne
    rcases (hmem c).1 hne with e | e
    · exact h1 e
    · exact h2 e
  have hd1 : delta τ c₁ ≠ v := (hmem c₁).2 (Or.inl rfl)
  have hs : ∑ c, (delta τ c - v) = (delta τ c₁ - v) + (delta τ c₂ - v) :=
    Fintype.sum_eq_add c₁ c₂ h12 fun c hc => by rw [hoff c hc.1 hc.2, sub_self]
  rw [sum_sub_distrib, sum_delta, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  have h52 : ((52 : ℕ) : ZMod 13) = 0 := by decide
  rw [h52, zero_mul, sub_zero] at hs
  obtain ⟨u, hu_def⟩ : ∃ u, u = delta τ c₁ - v := ⟨_, rfl⟩
  have hu : u ≠ 0 := by rw [hu_def]; exact sub_ne_zero.2 hd1
  have e1 : delta τ c₁ = v + u := by linear_combination (-1 : ZMod 13) * hu_def
  have e2 : delta τ c₂ = v - u := by linear_combination (-1 : ZMod 13) * hs + hu_def
  have hpt := rho_prod_le_A1 τ v u hu c₁ c₂ h12 e1 e2 hoff
  unfold rhoSum
  have hsum := sum_le_sum fun π (_ : π ∈ (univ : Finset (Equiv.Perm (Fin 52)))) => hpt π
  have hite : ∀ π : Equiv.Perm (Fin 52),
      (if (π⁻¹ c₁).val % 4 = (π⁻¹ c₂).val % 4 then (0 : ℚ) else 1 / 169) =
        1 / 169 * (if ¬ (π⁻¹ c₁).val % 4 = (π⁻¹ c₂).val % 4 then 1 else 0) := by
    intro π; split_ifs <;> simp
  rw [sum_congr rfl fun π _ => hite π, ← mul_sum, sum_boole] at hsum
  -- seat-pair counts
  set K := (univ.filter fun π : Equiv.Perm (Fin 52) => π 0 = c₁ ∧ π 1 = c₂).card
  have hdiff := card_seat_pairs c₁ c₂ h12 (fun p q => ¬ p.val % 4 = q.val % 4)
    (fun p q h e => h (by rw [e]))
  rw [card_diffRow_pairs] at hdiff
  have htot := card_seat_pairs c₁ c₂ h12 (fun p q => p ≠ q) (fun _ _ h => h)
  beta_reduce at htot hdiff
  have hall : (univ.filter fun π : Equiv.Perm (Fin 52) => π⁻¹ c₁ ≠ π⁻¹ c₂) = univ :=
    eq_univ_iff_forall.2 fun π => mem_filter.2 ⟨mem_univ _, fun e => h12 (π⁻¹.injective e)⟩
  rw [card_ne_pairs, hall, card_univ, Fintype.card_perm, Fintype.card_fin] at htot
  have hdq : ((univ.filter fun π : Equiv.Perm (Fin 52) =>
      ¬ (π⁻¹ c₁).val % 4 = (π⁻¹ c₂).val % 4).card : ℚ) = 2028 * K := by exact_mod_cast hdiff
  have htq : ((Nat.factorial 52 : ℕ) : ℚ) = 2652 * K := by exact_mod_cast htot
  rw [hdq] at hsum
  rw [htq]
  linarith

/-- **(A2)** (PROOF.md §3): `13 ≤ n* ≤ 49` gives `Σ ≤ 52! · E_A(n*)`
    (`rho_le_hA` with `v = v*` and `W = cls τ v*`, then `hyper_rows`, since the
    row-`r` count of `W` is `zRow W π r`). -/
theorem caseA2 (τ : Relabel) (h1 : 13 ≤ nStar τ) (h2 : nStar τ ≤ 49) :
    rhoSum τ ≤ (Nat.factorial 52 : ℕ) * EA (nStar τ) := by
  classical
  obtain ⟨v, hv⟩ := exists_vStar τ
  set W := cls τ v
  have hW : ∀ c, delta τ c = v ↔ c ∈ W := fun c => by simp [W, cls]
  have hpt : ∀ π, ∏ r, rho τ (rowOf π r) ≤ ∏ r, hA (zRow W π r) := by
    intro π
    apply prod_le_prod (fun r _ => rho_nonneg τ _)
    intro r _
    have := rho_le_hA τ (rowOf π r) v
    rwa [show (univ.filter fun j => delta τ (rowOf π r j) = v).card = zRow W π r from
      card_row_eq_zRow W π r _ hW] at this
  refine (sum_le_sum fun π _ => hpt π).trans (le_of_eq ?_)
  rw [hyper_rows W (fun z => ∏ r, hA (z r)), ← hv]
  have hn : W.card ≤ 52 := (card_le_univ _).trans (by simp)
  unfold EA
  rw [← factorial_split _ hn, mul_sum]
  refine sum_congr rfl fun z _ => ?_
  rw [prod_mul_distrib]
  ring

/-- **(A3)** (PROOF.md §3): `n* ≤ 12` gives `Σ ≤ 52! · (1/81 + 4·4¹³/C(52,13))`
    (no constant row; a row with a repeat has `ρ ≤ 1/3`; `distinct_row_count`
    for the rest). -/
theorem caseA3 (τ : Relabel) (h : nStar τ ≤ 12) :
    rhoSum τ ≤ (Nat.factorial 52 : ℕ) * ((1 / 81 : ℚ) + 4 * 4 ^ 13 / (Nat.choose 52 13 : ℕ)) := by
  unfold rhoSum
  refine (sum_le_sum fun π _ => rho_prod_le_A3 τ h π).trans ?_
  rw [sum_add_distrib, sum_const, card_univ, Fintype.card_perm, Fintype.card_fin, sum_comm]
  simp only [sum_boole]
  have hc : (0 : ℚ) < (Nat.choose 52 13 : ℕ) := by exact_mod_cast Nat.choose_pos (by norm_num)
  have hr : ∀ r : Fin 4, ((univ.filter fun π => rowDistinct τ π r).card : ℚ) ≤
      4 ^ 13 * (Nat.factorial 52 : ℕ) / (Nat.choose 52 13 : ℕ) := by
    intro r
    rw [le_div_iff₀ hc]
    exact_mod_cast distinct_row_count (delta τ) r
  have hsum := sum_le_sum fun r (_ : r ∈ (univ : Finset (Fin 4))) => hr r
  rw [sum_const, card_univ, Fintype.card_fin] at hsum
  simp only [nsmul_eq_mul] at hsum ⊢
  have e : ((Nat.factorial 52 : ℕ) : ℚ) * (4 * 4 ^ 13 / (Nat.choose 52 13 : ℕ)) =
      (4 : ℕ) * (4 ^ 13 * (Nat.factorial 52 : ℕ) / (Nat.choose 52 13 : ℕ)) := by
    push_cast; ring
  rw [mul_add, e]
  push_cast at hsum ⊢
  linarith

/-- **Case A** (PROOF.md §3): `δ` not constant ⇒ at most `52!/64` survivors. -/
theorem caseA_bound (τ : Relabel) (h : ∃ c, delta τ c ≠ delta τ 0) :
    64 * (survivors τ).card ≤ Nat.factorial 52 := by
  have hs := survivors_le_rhoSum τ
  have hf : (0 : ℚ) < (Nat.factorial 52 : ℕ) := by exact_mod_cast Nat.factorial_pos 52
  have key : 64 * rhoSum τ ≤ (Nat.factorial 52 : ℕ) := by
    have h50 := nStar_le_50 τ h
    rcases Nat.lt_or_ge (nStar τ) 13 with hlo | hlo
    · have := caseA3 τ (by omega)
      have hc := A3_const
      nlinarith
    · rcases Nat.lt_or_ge (nStar τ) 50 with hhi | hhi
      · have := caseA2 τ hlo (by omega)
        have he := EA_le (nStar τ) hlo (by omega)
        nlinarith
      · have := caseA1 τ (by omega)
        have hr : 0 ≤ rhoSum τ :=
          Finset.sum_nonneg fun π _ => Finset.prod_nonneg fun r _ => rho_nonneg τ _
        nlinarith
  have : ((64 * (survivors τ).card : ℕ) : ℚ) ≤ (Nat.factorial 52 : ℕ) := by
    push_cast; linarith
  exact_mod_cast this

/-! ## §4 Case B (`ε` not constant; columns only) -/

/-- (PROOF.md §0, column functionals): the column turn is unchanged by `τ` iff
    `V(ε(p)) = Σ(ε(y))` (GF(2)-linearity of `V`, `Σ`). -/
theorem colTurn_rel_iff (τ : Relabel) (p y : Fin 4 → Fin 52) :
    colTurnV10 (fun r => τ.app (p r).val) (fun r => τ.app (y r).val) =
        colTurnV10 (fun r => (p r).val) (fun r => (y r).val) ↔
      vLab (fun r => eps τ (p r)) = sLab (fun r => eps τ (y r)) := by
  have hw : ∀ a : Fin 4, gfTimesW a.val = (w4 a).val := by decide
  have hlab : ∀ c : Fin 52, suitLabel c.val = (lab c).val := fun _ => rfl
  have hct : ∀ q z : Fin 4 → Fin 52,
      colTurnV10 (fun r => (q r).val) (fun r => (z r).val) =
        (x4 (vLab fun r => lab (q r)) (sLab fun r => lab (z r))).val := by
    intro q z
    simp only [colTurnV10, colValue, colSuits, hlab, hw, gfAdd_eq_x4, vLab, sLab]
  have happ : (fun r => τ.app (p r).val) = fun r => (τ (p r)).val := funext fun r => app_fin τ _
  have happ' : (fun r => τ.app (y r).val) = fun r => (τ (y r)).val := funext fun r => app_fin τ _
  rw [happ, happ', hct, hct, Fin.val_inj]
  have m4 : ∀ a b c d : Fin 4, x4 (x4 a b) (x4 c d) = x4 (x4 a c) (x4 b d) := by decide
  have wl : ∀ a b : Fin 4, w4 (x4 a b) = x4 (w4 a) (w4 b) := by decide
  have fin : ∀ V' S' V S : Fin 4, x4 V' S' = x4 V S ↔ x4 V' V = x4 S' S := by decide
  rw [fin]
  simp only [vLab, sLab, eps, m4, wl]

/-- `φ(C, σ)` (PROOF.md §4): fraction of the 24 orders of column `p` whose `V(ε)`
    equals the target `Σ(ε(y))` of the next column. -/
def phi (τ : Relabel) (p y : Fin 4 → Fin 52) : ℚ :=
  ((univ.filter fun σ : Equiv.Perm (Fin 4) =>
      vLab (fun r => eps τ (p (σ r))) = sLab (fun r => eps τ (y r))).card : ℚ) / 24

theorem phi_nonneg (τ : Relabel) (p y : Fin 4 → Fin 52) : 0 ≤ phi τ p y := by
  unfold phi; positivity

/-! ### Helpers: decks from grids -/

theorem isDeckG_rowRotate (G : Grid Nat) (t : Fin 4 → Nat) (hG : IsDeck (scoopColumnMajor G)) :
    IsDeck (scoopColumnMajor (rowRotate G t)) := by
  obtain ⟨hc, hi⟩ := (isDeckG_iff G).1 hG
  refine (isDeckG_iff _).2 ⟨fun r c => ?_, fun r c r' c' h => ?_⟩
  · rw [rowRotate_apply]; exact hc _ _
  · rw [rowRotate_apply, rowRotate_apply] at h
    obtain ⟨hr, hcol⟩ := hi _ _ _ _ h
    subst hr
    refine ⟨rfl, Fin.ext ?_⟩
    have := congrArg Fin.val hcol
    simp only at this
    have := c.isLt; have := c'.isLt
    omega

theorem isDeckG_rowsDone4 (π : Equiv.Perm (Fin 52)) :
    IsDeck (scoopColumnMajor (rowsDone rowTurnV10 (deckGrid π) 4)) := by
  rw [rowsDone_eq]; exact isDeckG_rowRotate _ _ (isDeck_deckGrid π)

/-- The deck permutation of a deck grid. -/
noncomputable def gridPerm (G : Grid Nat) (hG : IsDeck (scoopColumnMajor G)) : Equiv.Perm (Fin 52) :=
  deckPerm (scoopColumnMajor G) hG

theorem deckGrid_gridPerm (G : Grid Nat) (hG : IsDeck (scoopColumnMajor G)) :
    deckGrid (gridPerm G hG) = G := by
  have : permDeck (gridPerm G hG) = scoopColumnMajor G := funext fun k => rfl
  unfold deckGrid; rw [this, lay_scoop_columnMajor]

theorem gridPerm_deckGrid (π : Equiv.Perm (Fin 52)) : gridPerm (deckGrid π) (isDeck_deckGrid π) = π := by
  apply Equiv.ext; intro k; apply Fin.ext
  show scoopColumnMajor (layColumnMajor (permDeck π)) k = (π k).val
  rw [scoop_lay_columnMajor]; rfl

theorem gridPerm_congr (G G' : Grid Nat) (hG : IsDeck (scoopColumnMajor G))
    (hG' : IsDeck (scoopColumnMajor G')) (h : G = G') : gridPerm G hG = gridPerm G' hG' := by
  subst h; rfl

theorem card_filter_equiv (e : Equiv.Perm (Fin 52) ≃ Equiv.Perm (Fin 52))
    (P : Equiv.Perm (Fin 52) → Prop) [DecidablePred P] :
    (univ.filter fun a => P (e a)).card = (univ.filter P).card := by
  have : (univ.filter fun a => P (e a)).map e.toEmbedding = univ.filter P := by
    ext a; simp [Finset.mem_map_equiv]
  rw [← this, card_map]

/-- **`H` is uniform** (PROOF.md §4): `π ↦` (post-row grid) is a bijection of
    decks (`rowsUndo_rowsDone`, `rowsDone_rowsUndo`, `isDeckG_rowsUndo`), so
    counting the column conditions on `H` is counting them on `G`. -/
theorem colConds_H_card (τ : Relabel) :
    (univ.filter fun π : Equiv.Perm (Fin 52) =>
        ColCondsTraj τ (rowsDone rowTurnV10 (deckGrid π) 4)).card =
      (univ.filter fun π : Equiv.Perm (Fin 52) => ColCondsTraj τ (deckGrid π)).card := by
  let Φ : Equiv.Perm (Fin 52) ≃ Equiv.Perm (Fin 52) :=
    { toFun := fun π => gridPerm (rowsDone rowTurnV10 (deckGrid π) 4) (isDeckG_rowsDone4 π)
      invFun := fun π => gridPerm (rowsUndo rowTurnV10 (deckGrid π) 4)
        (isDeckG_rowsUndo _ (isDeck_deckGrid π) 4)
      left_inv := fun π => by
        simp only
        rw [gridPerm_congr _ _ _ _ (by rw [deckGrid_gridPerm, rowsUndo_rowsDone _ _ 4 le_rfl])]
        exact gridPerm_deckGrid π
      right_inv := fun π => by
        simp only
        rw [gridPerm_congr _ _ _ _ (by rw [deckGrid_gridPerm, rowsDone_rowsUndo _ _ 4 le_rfl])]
        exact gridPerm_deckGrid π }
  have h := card_filter_equiv Φ (fun π => ColCondsTraj τ (deckGrid π))
  rw [← h]
  apply congrArg Finset.card
  apply filter_congr
  intro π _
  show ColCondsTraj τ (rowsDone rowTurnV10 (deckGrid π) 4) ↔
    ColCondsTraj τ (deckGrid (gridPerm (rowsDone rowTurnV10 (deckGrid π) 4) (isDeckG_rowsDone4 π)))
  rw [deckGrid_gridPerm]

/-! ### Helpers for the column chain -/

/-- GF(4) labels as the additive group `ZMod 2 × ZMod 2`. -/
def toZ (a : Fin 4) : ZMod 2 × ZMod 2 := ((a.val % 2 : ℕ), (a.val / 2 : ℕ))

theorem toZ_x4 : ∀ a b : Fin 4, toZ (x4 a b) = toZ a + toZ b := by decide
theorem toZ_inj : ∀ a b : Fin 4, toZ a = toZ b → a = b := by decide
theorem toZ_zero : toZ 0 = 0 := by decide

theorem toZ_sLab (e : Fin 4 → Fin 4) : toZ (sLab e) = ∑ i, toZ (e i) := by
  simp only [sLab, toZ_x4, Fin.sum_univ_four]

/-- `Σ` of a column does not depend on the order. -/
theorem sLab_comp_perm (e : Fin 4 → Fin 4) (b : Equiv.Perm (Fin 4)) : sLab (e ∘ b) = sLab e :=
  toZ_inj _ _ (by rw [toZ_sLab, toZ_sLab]; exact Equiv.sum_comp b (fun i => toZ (e i)))

theorem colSuits_val (x : Fin 4 → Fin 52) :
    colSuits (fun r => (x r).val) = (sLab fun r => lab (x r)).val := by
  have hlab : ∀ c : Fin 52, suitLabel c.val = (lab c).val := fun _ => rfl
  simp only [colSuits, hlab, gfAdd_eq_x4, sLab]

theorem colSuits_comp_perm (x : Fin 4 → Fin 52) (b : Equiv.Perm (Fin 4)) :
    colSuits (fun r => (x (b r)).val) = colSuits (fun r => (x r).val) := by
  rw [colSuits_val, colSuits_val]
  exact congrArg Fin.val (sLab_comp_perm (fun r => lab (x r)) b)

theorem colStepOf_of_ne : ∀ k : Fin 13, k ≠ 0 → colStepOf k = k.val := by decide
theorem prevCol_val_of_ne : ∀ k : Fin 13, k ≠ 0 → (prevCol k).val = k.val - 1 := by decide
theorem prevCol_succ : ∀ k : Fin 13, prevCol (k + 1) = k := by decide
theorem prevCol_eq_sub_one : ∀ j : Fin 13, prevCol j = j - 1 := by decide
theorem colStep_read_iff : ∀ k : Fin 13, colStepOf k ≤ colStepOf (k + 1) - 1 ↔ k ≠ 0 := by decide
theorem colStepOf_le : ∀ c : Fin 13, colStepOf c ≤ 13 := by decide
theorem colStep_self : ∀ c : Fin 13, ¬ colStepOf c ≤ colStepOf c - 1 := by decide

theorem column_colRotate_zero (g : Grid Nat) (A : Fin 13 → Nat) (k : Fin 13) (h : A k = 0) :
    column (colRotate g A) k = column g k := by
  funext r
  simp only [column, colRotate_apply, h, Nat.zero_mod, Nat.sub_zero]
  congr 1; apply Fin.ext; simp only; omega

/-- The amount column `k` (`1 ≤ k`) turns by depends only on the columns
    `0, …, k-1` and on `Σ` of column `k`. -/
theorem colAmt_congr (g g' : Grid Nat) : ∀ (m : ℕ) (k : Fin 13), k.val = m → 1 ≤ m →
    (∀ r (c : Fin 13), c.val < m → g r c = g' r c) →
    colSuits (column g k) = colSuits (column g' k) →
    colAmt colTurnV10 g k = colAmt colTurnV10 g' k := by
  intro m
  induction m with
  | zero => intro k _ h; omega
  | succ m ih =>
    intro k hk _ hcols hsuits
    have hk0 : k ≠ 0 := by intro e; rw [e] at hk; simp at hk
    have hstep := colStepOf_of_ne k hk0
    have hprev := prevCol_val_of_ne k hk0
    unfold colAmt
    rw [colsDone_eq_partial _ g _ (by omega), colsDone_eq_partial _ g' _ (by omega)]
    have hownA : ∀ G : Grid Nat,
        column (colRotate G fun c => if colStepOf c ≤ colStepOf k - 1 then colAmt colTurnV10 G c
          else 0) k = column G k := fun G =>
      column_colRotate_zero _ _ _ (by rw [if_neg (colStep_self k)])
    rw [hownA g, hownA g']
    have hamt : (if colStepOf (prevCol k) ≤ colStepOf k - 1 then colAmt colTurnV10 g (prevCol k)
        else 0) = (if colStepOf (prevCol k) ≤ colStepOf k - 1 then
          colAmt colTurnV10 g' (prevCol k) else 0) := by
      by_cases hp0 : prevCol k = 0
      · have h13 : ¬ colStepOf (prevCol k) ≤ colStepOf k - 1 := by
          rw [hp0, hstep]; have := k.isLt; simp only [colStepOf]; simp; omega
        rw [if_neg h13, if_neg h13]
      · have hpv : (prevCol k).val ≠ 0 := fun e => hp0 (Fin.ext e)
        split_ifs
        · exact ih (prevCol k) (by omega) (by omega)
            (fun r c hc => hcols r c (by omega))
            (congrArg colSuits (funext fun r => hcols r _ (by omega)))
        · rfl
    have hcol : column (colRotate g fun c => if colStepOf c ≤ colStepOf k - 1 then
          colAmt colTurnV10 g c else 0) (prevCol k) =
        column (colRotate g' fun c => if colStepOf c ≤ colStepOf k - 1 then
          colAmt colTurnV10 g' c else 0) (prevCol k) := by
      funext r
      simp only [column, colRotate_apply]
      rw [hamt]
      exact hcols _ _ (by omega)
    simp only [colTurnV10, hsuits, hcol]

/-- Column `k` read with rotation `s` (`colRotate_apply`). -/
def colRot (y : Fin 4 → Fin 52) (s : ℕ) : Fin 4 → Fin 52 :=
  fun r => y ⟨(r.val + (4 - s % 4)) % 4, Nat.mod_lt _ (by decide)⟩

/-- The rotation as a permutation of the 4 seats. -/
def shiftPerm (s : ℕ) : Equiv.Perm (Fin 4) :=
  Equiv.addRight ⟨(4 - s % 4) % 4, Nat.mod_lt _ (by decide)⟩

theorem colRot_comp (x : Fin 4 → Fin 52) (a : Equiv.Perm (Fin 4)) (s : ℕ) :
    colRot (x ∘ a) s = x ∘ (a * shiftPerm s) := by
  funext r
  simp only [colRot, Function.comp, Equiv.Perm.mul_apply, shiftPerm, Equiv.coe_addRight]
  congr 2
  apply Fin.ext
  simp only [Fin.val_add]
  omega

theorem colRot_zero (y : Fin 4 → Fin 52) : colRot y 0 = y := by
  funext r; simp only [colRot]; congr 1; apply Fin.ext; simp only; omega

theorem column_colRotate_deck (π : Equiv.Perm (Fin 52)) (A : Fin 13 → ℕ) (k : Fin 13) :
    column (colRotate (deckGrid π) A) k = fun r => (colRot (colOf π k) (A k) r).val := by
  funext r; simp only [column, colRotate_apply, deckGrid_apply, colRot, colOf]

theorem card_filter_mul_right (P : Equiv.Perm (Fin 4) → Prop) [DecidablePred P]
    (ρ : Equiv.Perm (Fin 4)) :
    (univ.filter fun a => P (a * ρ)).card = (univ.filter P).card := by
  have : (univ.filter fun a => P (a * ρ)) = (univ.filter P).map (Equiv.mulRight ρ⁻¹).toEmbedding := by
    ext a
    simp [Finset.mem_map_equiv]
  rw [this, card_map]

/-- **Lemma 5 (column chain)** (PROOF.md §4): the decks satisfying the 13
    column conditions number at most `Σ_π Π_j φ(col j−1, col j)` (the paper
    proves equality). Same nesting as `rowChain_le`, over columns 0, 1, …, 12;
    the rotation of column `j−1` before it is read depends only on earlier
    columns, and a fixed rotation is a bijection on orders. -/
theorem colChain_le (τ : Relabel) :
    ((univ.filter fun π : Equiv.Perm (Fin 52) => ColCondsTraj τ (deckGrid π)).card : ℚ) ≤
      ∑ π : Equiv.Perm (Fin 52), ∏ j, phi τ (colOf π (prevCol j)) (colOf π j) := by
  classical
  let sAmt : Equiv.Perm (Fin 52) → (Fin 13 → Equiv.Perm (Fin 4)) → Fin 13 → ℕ := fun π σ k =>
    if k = 0 then 0 else colAmt colTurnV10 (deckGrid (π * colShuf σ)) k
  let Q : Equiv.Perm (Fin 52) → Fin 13 → (Fin 13 → Equiv.Perm (Fin 4)) → Prop := fun π k σ =>
    vLab (fun r => eps τ (colRot (colOf π k ∘ σ k) (sAmt π σ k) r)) =
      sLab (fun r => eps τ (colOf π (k + 1) r))
  let Nc : Equiv.Perm (Fin 52) → Fin 13 → ℕ := fun π k =>
    (univ.filter fun a : Equiv.Perm (Fin 4) =>
      vLab (fun r => eps τ (colOf π k (a r))) = sLab (fun r => eps τ (colOf π (k + 1) r))).card
  have hNc : ∀ π k, (Nc π k : ℚ) = 24 * phi τ (colOf π k) (colOf π (k + 1)) := by
    intro π k; simp only [Nc, phi]; field_simp
  have hcolumn : ∀ π σ (k : Fin 13),
      column (deckGrid (π * colShuf σ)) k = fun r => (colOf π k (σ k r)).val := by
    intro π σ k; funext r
    simp only [column, deckGrid_apply, Equiv.Perm.mul_apply, colShuf_cmFlat, colOf]
  have hsAmt : ∀ π σ σ' (k : Fin 13), (∀ i : Fin 13, i < k → σ i = σ' i) →
      sAmt π σ k = sAmt π σ' k := by
    intro π σ σ' k h
    simp only [sAmt]
    split_ifs with hk
    · rfl
    · have hk1 : 1 ≤ k.val := by
        rcases Nat.eq_zero_or_pos k.val with e | e
        · exact absurd (Fin.ext e) hk
        · exact e
      apply colAmt_congr _ _ k.val k rfl hk1
      · intro r c hc
        simp only [deckGrid_apply, Equiv.Perm.mul_apply, colShuf_cmFlat, h c (Fin.lt_def.2 hc)]
      · rw [hcolumn, hcolumn, colSuits_comp_perm (colOf π k) (σ k),
          colSuits_comp_perm (colOf π k) (σ' k)]
  have hper : ∀ π, (univ.filter fun σ : Fin 13 → Equiv.Perm (Fin 4) =>
      ∀ k, Q π k σ).card ≤ ∏ k, Nc π k := by
    intro π
    refine nested_count 13 (Q π) (Nc π) ?_ ?_
    · intro k σ σ' h
      have h1 : sAmt π σ k = sAmt π σ' k := hsAmt π σ σ' k fun i hi => h i hi.le
      simp only [Q, h1, h k le_rfl]
    · intro k σ
      set s := sAmt π σ k
      have hs : ∀ a, sAmt π (Function.update σ k a) k = s := fun a =>
        hsAmt π _ _ k fun i hi => Function.update_noteq (ne_of_lt hi) _ _
      have hQ : ∀ a, Q π k (Function.update σ k a) ↔
          (fun b : Equiv.Perm (Fin 4) => vLab (fun r => eps τ (colOf π k (b r))) =
            sLab (fun r => eps τ (colOf π (k + 1) r))) (a * shiftPerm s) := by
        intro a
        simp only [Q, hs a, Function.update_same, colRot_comp]
        rfl
      simp only [hQ]
      exact (card_filter_mul_right (fun b : Equiv.Perm (Fin 4) =>
        vLab (fun r => eps τ (colOf π k (b r))) = sLab (fun r => eps τ (colOf π (k + 1) r)))
        (shiftPerm s)).le
  have hlink : ∀ π σ, ColCondsTraj τ (deckGrid (π * colShuf σ)) → ∀ k, Q π k σ := by
    intro π σ h k
    have hc := h (k + 1)
    rw [prevCol_succ, colsDone_eq_partial _ _ _ (by have := colStepOf_le (k + 1); omega)] at hc
    have hrel : ∀ (G : Grid Nat) (j : Fin 13), column (relG τ G) j = fun r => τ.app (column G j r) :=
      fun _ _ => rfl
    simp only [hrel, column_colRotate_deck] at hc
    have hc' := (colTurn_rel_iff τ _ _).1 hc
    simp only [if_neg (colStep_self (k + 1)), colRot_zero, colOf_mul_colShuf] at hc'
    have hA : (if colStepOf k ≤ colStepOf (k + 1) - 1 then
        colAmt colTurnV10 (deckGrid (π * colShuf σ)) k else 0) = sAmt π σ k := by
      simp only [sAmt]
      by_cases hk : k = 0
      · rw [if_pos hk, if_neg (by rw [colStep_read_iff]; exact not_not.2 hk)]
      · rw [if_neg hk, if_pos ((colStep_read_iff k).2 hk)]
    rw [hA] at hc'
    have hsl := sLab_comp_perm (fun r => eps τ (colOf π (k + 1) r)) (σ (k + 1))
    simp only [Q]
    rw [← hsl]
    exact hc'
  -- average over column orders
  have havg := sum_mul_card_shuf colShuf
    (fun π => if ColCondsTraj τ (deckGrid π) then (1 : ℚ) else 0)
  have hcardS : (Fintype.card (Fin 13 → Equiv.Perm (Fin 4)) : ℚ) = (24 : ℚ) ^ 13 := by
    rw [Fintype.card_fun, Fintype.card_perm, Fintype.card_fin, Fintype.card_fin]; rfl
  rw [hcardS] at havg
  have hrhs : ∀ π, (∑ σ : Fin 13 → Equiv.Perm (Fin 4),
      if ColCondsTraj τ (deckGrid (π * colShuf σ)) then (1 : ℚ) else 0) ≤
      (24 : ℚ) ^ 13 * ∏ j, phi τ (colOf π (prevCol j)) (colOf π j) := by
    intro π
    rw [sum_boole]
    have h1 : (univ.filter fun σ : Fin 13 → Equiv.Perm (Fin 4) =>
        ColCondsTraj τ (deckGrid (π * colShuf σ))).card ≤ ∏ k, Nc π k :=
      (card_le_card fun σ hσ => by
        simp only [mem_filter, mem_univ, true_and] at hσ ⊢
        exact hlink π σ hσ).trans (hper π)
    have hq : ((univ.filter fun σ : Fin 13 → Equiv.Perm (Fin 4) =>
        ColCondsTraj τ (deckGrid (π * colShuf σ))).card : ℚ) ≤ ∏ k, (Nc π k : ℚ) := by
      exact_mod_cast h1
    simp only [hNc, prod_mul_distrib, prod_const, card_univ, Fintype.card_fin] at hq
    have hre : ∏ k : Fin 13, phi τ (colOf π k) (colOf π (k + 1)) =
        ∏ j : Fin 13, phi τ (colOf π (prevCol j)) (colOf π j) :=
      Fintype.prod_equiv (Equiv.addRight 1) _ _ (fun k => by simp [prevCol_succ])
    rw [hre] at hq
    exact hq
  have hf : (0 : ℚ) < (24 : ℚ) ^ 13 := by positivity
  rw [← sum_boole]
  refine le_of_mul_le_mul_left ?_ hf
  rw [havg, mul_sum]
  exact sum_le_sum fun π _ => hrhs π

/-- The `ε`-class of `x`. -/
def ecls (τ : Relabel) (x : Fin 4) : Finset (Fin 52) := univ.filter fun c => eps τ c = x

/-- `m'`: the number of cards off the most common `ε`-value (PROOF.md §4). -/
def mStar (τ : Relabel) : ℕ := 52 - univ.sup fun x => (ecls τ x).card

theorem add_self_Z : ∀ x : ZMod 2 × ZMod 2, x + x = 0 := by decide
theorem nsmul51 : ∀ x : ZMod 2 × ZMod 2, (51 : ℕ) • x = x := by decide
theorem add_eq_zero_imp : ∀ a b : ZMod 2 × ZMod 2, a + b = 0 → a = b := by decide

/-- `Σ_c ε(c) = 0` in GF(4) (PROOF.md §0): `τ` is a bijection. -/
theorem sum_toZ_eps (τ : Relabel) : ∑ c, toZ (eps τ c) = 0 := by
  simp only [eps, toZ_x4, sum_add_distrib]
  rw [Equiv.sum_comp τ (fun c => toZ (lab c)), add_self_Z]

/-- `2 ≤ m' ≤ 39` when `ε` is not constant (PROOF.md §4: `m' ≠ 1` by
    `Σ ε = 0`, and the largest class has at least 13 cards). -/
theorem mStar_bounds (τ : Relabel) (h : ∃ c, eps τ c ≠ eps τ 0) : 2 ≤ mStar τ ∧ mStar τ ≤ 39 := by
  classical
  set S := univ.sup fun x => (ecls τ x).card with hS
  obtain ⟨xs, -, hxs⟩ := Finset.exists_mem_eq_sup (univ : Finset (Fin 4)) univ_nonempty
    (fun x => (ecls τ x).card)
  rw [← hS] at hxs
  have hle52 : S ≤ 52 := by
    rw [hxs]; exact (card_le_univ _).trans (by simp)
  have h13 : 13 ≤ S := by
    obtain ⟨x, hx⟩ := exists_class_ge_13 (eps τ)
    exact hx.trans (le_sup (f := fun x => (ecls τ x).card) (mem_univ x))
  have hne52 : S ≠ 52 := by
    intro e
    obtain ⟨c, hc⟩ := h
    have hall : ecls τ xs = univ := eq_univ_of_card _ (by rw [← hxs, e]; simp)
    have h1 : c ∈ ecls τ xs := by rw [hall]; exact mem_univ c
    have h2 : (0 : Fin 52) ∈ ecls τ xs := by rw [hall]; exact mem_univ _
    simp only [ecls, mem_filter, mem_univ, true_and] at h1 h2
    exact hc (h1.trans h2.symm)
  have hne51 : S ≠ 51 := by
    intro e
    have hsum := sum_toZ_eps τ
    rw [← sum_filter_add_sum_filter_not univ (fun c => eps τ c = xs)] at hsum
    have hA : ∑ c ∈ univ.filter (fun c => eps τ c = xs), toZ (eps τ c) = toZ xs := by
      rw [sum_congr rfl fun c hc => by rw [(mem_filter.1 hc).2], sum_const]
      have hc : (univ.filter fun c => eps τ c = xs).card = 51 := by
        rw [← e, hxs]; rfl
      rw [hc]; exact nsmul51 _
    have hcard : (univ.filter fun c => ¬ eps τ c = xs).card = 1 := by
      have := filter_card_add_filter_neg_card_eq_card (s := (univ : Finset (Fin 52)))
        (fun c => eps τ c = xs)
      have hc : (univ.filter fun c => eps τ c = xs).card = 51 := by
        rw [← e, hxs]; rfl
      rw [hc, card_univ, Fintype.card_fin] at this
      omega
    obtain ⟨c₀, hc₀⟩ := card_eq_one.1 hcard
    have hc₀' : ¬ eps τ c₀ = xs := by
      have : c₀ ∈ univ.filter fun c => ¬ eps τ c = xs := by rw [hc₀]; exact mem_singleton_self _
      exact (mem_filter.1 this).2
    rw [hA, hc₀, sum_singleton] at hsum
    exact hc₀' (toZ_inj _ _ (add_eq_zero_imp _ _ hsum).symm)
  have hle50 : S ≤ 50 := by omega
  unfold mStar
  rw [← hS]
  omega

/-- **Theorem B, Lean form** (PROOF.md §4): `Σ_π Π_j φ ≤ 52! · E_B(m')`
    (`lemma4_count_le` pointwise with `xs` a most common `ε`-value, then
    `hyper_cols` with `W` the off cards). -/
theorem caseB_sum (τ : Relabel) (h : ∃ c, eps τ c ≠ eps τ 0) :
    ∑ π : Equiv.Perm (Fin 52), ∏ j, phi τ (colOf π (prevCol j)) (colOf π j) ≤
      (Nat.factorial 52 : ℕ) * EB (mStar τ) := by
  classical
  set S := univ.sup fun x => (ecls τ x).card with hS
  obtain ⟨xs, -, hxs⟩ := Finset.exists_mem_eq_sup (univ : Finset (Fin 4)) univ_nonempty
    (fun x => (ecls τ x).card)
  rw [← hS] at hxs
  set W := univ.filter fun c => eps τ c ≠ xs
  have hW : ∀ c, eps τ c ≠ xs ↔ c ∈ W := fun c => by simp [W]
  have hWcard : W.card = mStar τ := by
    have := filter_card_add_filter_neg_card_eq_card (s := (univ : Finset (Fin 52)))
      (fun c => eps τ c = xs)
    have e1 : (univ.filter fun c => eps τ c = xs).card = S := by rw [hxs]; rfl
    rw [e1, card_univ, Fintype.card_fin] at this
    have e2 : W.card = (univ.filter fun c => ¬ eps τ c = xs).card := rfl
    have e3 : mStar τ = 52 - S := by unfold mStar; rw [← hS]
    rw [e2, e3]; omega
  have hoff : ∀ π j, offCount (fun r => eps τ (colOf π j r)) xs = yCol W π j := fun π j =>
    card_col_eq_yCol W π j _ hW
  have hpt : ∀ π, ∏ j, phi τ (colOf π (prevCol j)) (colOf π j) ≤
      ∏ j : Fin 13, fB (yCol W π (j - 1)) (yCol W π j) := by
    intro π
    apply prod_le_prod (fun j _ => phi_nonneg τ _ _)
    intro j _
    have h4 := lemma4_count_le (fun r => eps τ (colOf π (prevCol j) r)) xs
      (sLab fun r => eps τ (colOf π j r)) (offCount (fun r => eps τ (colOf π j r)) xs)
      (fun h0 => sLab_of_offCount_zero _ xs h0) (fun h1 => sLab_of_offCount_one _ xs h1)
    rw [hoff, hoff, prevCol_eq_sub_one] at h4
    rw [prevCol_eq_sub_one]
    exact h4
  refine (sum_le_sum fun π _ => hpt π).trans (le_of_eq ?_)
  rw [hyper_cols W (fun y => ∏ j : Fin 13, fB (y (j - 1)) (y j)), hWcard]
  have hn : mStar τ ≤ 52 := by rw [← hWcard]; exact (card_le_univ _).trans (by simp)
  unfold EB
  rw [← factorial_split _ hn, mul_sum]
  refine sum_congr rfl fun y _ => ?_
  rw [prod_mul_distrib]
  ring

/-- **Case B** (PROOF.md §4, Lean target `1/64`; the paper proves `1/425`):
    `ε` not constant ⇒ at most `52!/64` survivors. Uses only the column
    conditions, so it needs no hypothesis on `δ`. -/
theorem caseB_bound (τ : Relabel) (h : ∃ c, eps τ c ≠ eps τ 0) :
    64 * (survivors τ).card ≤ Nat.factorial 52 := by
  have h1 : (survivors τ).card ≤
      (univ.filter fun π : Equiv.Perm (Fin 52) =>
        ColCondsTraj τ (rowsDone rowTurnV10 (deckGrid π) 4)).card :=
    card_le_card fun π hπ => by
      simp only [survivors, mem_filter, mem_univ, true_and] at hπ ⊢
      exact (traj_of_survives τ _ (isDeck_deckGrid π) hπ).2
  rw [colConds_H_card] at h1
  have h2 := colChain_le τ
  have h3 := caseB_sum τ h
  obtain ⟨hm1, hm2⟩ := mStar_bounds τ h
  have h4 := EB_le (mStar τ) hm1 hm2
  have hf : (0 : ℚ) ≤ (Nat.factorial 52 : ℕ) := by positivity
  have h1q : ((survivors τ).card : ℚ) ≤
      ((univ.filter fun π : Equiv.Perm (Fin 52) => ColCondsTraj τ (deckGrid π)).card : ℚ) := by
    exact_mod_cast h1
  have : ((64 * (survivors τ).card : ℕ) : ℚ) ≤ (Nat.factorial 52 : ℕ) := by
    push_cast; nlinarith
  exact_mod_cast this

/-! ## §5 Main theorem -/

/-- **v10 SumRanks survival bound** (PROOF.md §5; paper constant `0.012768`,
    Lean target `1/64`): a relabelling outside `v10Sym` commutes with v10
    SumRanks on at most `52!/64` of the `52!` decks. -/
theorem sumRanksV10_survival_le (τ : Relabel) (h : ¬ ∃ a x, τ = v10Sym a x) :
    64 * (survivors τ).card ≤ Fintype.card (Equiv.Perm (Fin 52)) := by
  rw [Fintype.card_perm, Fintype.card_fin]
  rcases nonconst_of_not_sym τ h with hA | hB
  · exact caseA_bound τ hA
  · exact caseB_bound τ hB

/-- The same bound with the survival set written out. -/
theorem sumRanksV10_survival_le' (τ : Relabel) (h : ¬ ∃ a x, τ = v10Sym a x) :
    64 * (univ.filter fun π : Equiv.Perm (Fin 52) =>
        sumRanksV10 (relG τ (layColumnMajor (permDeck π))) =
          relG τ (sumRanksV10 (layColumnMajor (permDeck π)))).card ≤ Nat.factorial 52 := by
  have := sumRanksV10_survival_le τ h
  rwa [Fintype.card_perm, Fintype.card_fin] at this

end DoubleDeal.Security.SumRanksDP
