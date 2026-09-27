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
  sorry

/-! ## §1 Corollary 1: the row equations -/

/-- Row `r` of the deck `π`. -/
def rowOf (π : Equiv.Perm (Fin 52)) (r : Fin 4) : Fin 13 → Fin 52 := fun j => π (cmFlat r j)

/-- Column `j` of the deck `π`. -/
def colOf (π : Equiv.Perm (Fin 52)) (j : Fin 13) : Fin 4 → Fin 52 := fun r => π (cmFlat r j)

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
  sorry

/-- `θ_r` depends only on rows `0..r-1` (PROOF.md §1 Cor. 1, used in Lemma 3). -/
theorem thetaG_prefix (π π' : Equiv.Perm (Fin 52)) (r : Fin 4)
    (h : ∀ r' < r, rowOf π r' = rowOf π' r') : thetaG π r = thetaG π' r := by
  sorry

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

/-- **(A1)** (PROOF.md §3): `n* = 50` gives `Σ ≤ 52!/221` (the two off cards
    are `v* ± u`; same row: `ρ = 0` by `rho_eq_zero_of_cancel`; different rows:
    `1/13` each; probability of different rows `39/51`). -/
theorem caseA1 (τ : Relabel) (h : nStar τ = 50) : 221 * rhoSum τ ≤ (Nat.factorial 52 : ℕ) := by
  sorry

/-- **(A2)** (PROOF.md §3): `13 ≤ n* ≤ 49` gives `Σ ≤ 52! · E_A(n*)`
    (`rho_le_hA` with `v = v*` and `W = cls τ v*`, then `hyper_rows`, since the
    row-`r` count of `W` is `zRow W π r`). -/
theorem caseA2 (τ : Relabel) (h1 : 13 ≤ nStar τ) (h2 : nStar τ ≤ 49) :
    rhoSum τ ≤ (Nat.factorial 52 : ℕ) * EA (nStar τ) := by
  sorry

/-- **(A3)** (PROOF.md §3): `n* ≤ 12` gives `Σ ≤ 52! · (1/81 + 4·4¹³/C(52,13))`
    (no constant row; a row with a repeat has `ρ ≤ 1/3`; `distinct_row_count`
    for the rest). -/
theorem caseA3 (τ : Relabel) (h : nStar τ ≤ 12) :
    rhoSum τ ≤ (Nat.factorial 52 : ℕ) * ((1 / 81 : ℚ) + 4 * 4 ^ 13 / (Nat.choose 52 13 : ℕ)) := by
  sorry

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

/-- **`H` is uniform** (PROOF.md §4): `π ↦` (post-row grid) is a bijection of
    decks (`rowsUndo_rowsDone`, `rowsDone_rowsUndo`, `isDeckG_rowsUndo`), so
    counting the column conditions on `H` is counting them on `G`. -/
theorem colConds_H_card (τ : Relabel) :
    (univ.filter fun π : Equiv.Perm (Fin 52) =>
        ColCondsTraj τ (rowsDone rowTurnV10 (deckGrid π) 4)).card =
      (univ.filter fun π : Equiv.Perm (Fin 52) => ColCondsTraj τ (deckGrid π)).card := by
  sorry

/-- **Lemma 5 (column chain)** (PROOF.md §4): the decks satisfying the 13
    column conditions number at most `Σ_π Π_j φ(col j−1, col j)` (the paper
    proves equality). Same nesting as `rowChain_le`, over columns 0, 1, …, 12;
    the rotation of column `j−1` before it is read depends only on earlier
    columns, and a fixed rotation is a bijection on orders. -/
theorem colChain_le (τ : Relabel) :
    ((univ.filter fun π : Equiv.Perm (Fin 52) => ColCondsTraj τ (deckGrid π)).card : ℚ) ≤
      ∑ π : Equiv.Perm (Fin 52), ∏ j, phi τ (colOf π (prevCol j)) (colOf π j) := by
  sorry

/-- The `ε`-class of `x`. -/
def ecls (τ : Relabel) (x : Fin 4) : Finset (Fin 52) := univ.filter fun c => eps τ c = x

/-- `m'`: the number of cards off the most common `ε`-value (PROOF.md §4). -/
def mStar (τ : Relabel) : ℕ := 52 - univ.sup fun x => (ecls τ x).card

/-- `2 ≤ m' ≤ 39` when `ε` is not constant (PROOF.md §4: `m' ≠ 1` by
    `Σ ε = 0`, and the largest class has at least 13 cards). -/
theorem mStar_bounds (τ : Relabel) (h : ∃ c, eps τ c ≠ eps τ 0) : 2 ≤ mStar τ ∧ mStar τ ≤ 39 := by
  sorry

/-- **Theorem B, Lean form** (PROOF.md §4): `Σ_π Π_j φ ≤ 52! · E_B(m')`
    (`lemma4_count_le` pointwise with `xs` a most common `ε`-value, then
    `hyper_cols` with `W` the off cards). -/
theorem caseB_sum (τ : Relabel) (h : ∃ c, eps τ c ≠ eps τ 0) :
    ∑ π : Equiv.Perm (Fin 52), ∏ j, phi τ (colOf π (prevCol j)) (colOf π j) ≤
      (Nat.factorial 52 : ℕ) * EB (mStar τ) := by
  sorry

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
