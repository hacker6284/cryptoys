/-
  Step 4 toward `PrimeNonSwapCase`, and with steps 1-3 (`RankPartition`, `RankAffine`, `TauEq`)
  the single-cell statement `hcell` of `CovariantNarrow.roundBody_covariant_iff_id_of_cell0`:
  every σ with the seat-26 condition `Cell0Cov σ τ` (some τ) is a `v10Sym a x`, and τ = σ.

  Statements, GIVEN the finite checks `V10SymChecks` as a hypothesis (unconditional forms in
  the heavy library, `DoubleDealSecurityHeavy/V10Sym.lean`):
  * `cell0Cov_mem_v10Sym_of_checks`: `Cell0Cov σ τ → (∃ a x, σ = v10Sym a x) ∧ τ = σ`.
  * `roundBody_covariant_iff_id_of_checks`: `Covariant σ unkeyedWithMix ↔ σ = 1`, via
    `CovariantNarrow.roundBody_covariant_iff_id_of_cell0`. This is the statement of
    `Rounds.roundBody_covariant_iff_id` GIVEN `V10SymChecks`; that theorem itself is not
    changed here and keeps its `sorry`.

  A. Per-rank label translations `tr d` (label `l ⊕ d r` at rank index `r`; `tr` of a constant
     is `v10Sym 0 x`), in the card coordinates `ri`, `lbl`, `crd r l = v10Sym r l 0` of
     `SumRanksV10.lean`.
  B. Column chain (symbolic, `colAmt_congr_label`): if two grids differ, in labels, by a
     constant per column, the v10 column stage turns their columns by the same amounts
     (`colTurnV10` is unchanged: the column value has weights `1 ⊕ w ⊕ w² = 0`, and four
     equal labels cancel in the column suits).
  C. `tr_const_of_mem`: if `tr d` satisfies the seat-26 condition, `d` is constant. By `TauEq`
     τ = `tr d`; on the deck of `V10SymLists.lean` (after the row stage every column is a full
     rank class of a rank index ≠ 0 or holds only rank indices 0 and 1), `tr d` and
     `tr (eVec (d 0 ⊕ d 1))` differ by a constant per column, so B gives them the same source
     row of stem cell 0; `LabelChecks` says `tr (eVec e)` moves it for `e ≠ 0`; so
     `d 0 = d 1`, and conjugating by rank shifts `v10Sym k 0` gives `d r = d (r + 1)`.
  D. `rankPres_mem_v10Sym`: a rank-preserving σ with the seat-26 condition has label maps
     `g r` (one per rank index). Every permutation of `Fin 4` is affine (`DiagTable`,
     `decide`), so `σ · tr x · σ⁻¹ = tr (δ · x)`, and C makes `δ` independent of the rank:
     `g r (a ⊕ x) = g r a ⊕ z x`. So `g r = g 0 ∘ (· ⊕ c r)`; the commutator with the rank
     shift `v10Sym 1 0` is `tr (c (r + 1) ⊕ c r)`, so by C `c (r + 1) = c r ⊕ κ`, and 13 odd
     gives `κ = 0`: σ acts by one label map `h` on every rank, i.e. `σ = v10Sym 0 x * linSym 0
     g`; `CovariantAffine.not_cell0Cov_lin_of_check` forces `g = 0`.
  E. The rank map is a shift (`TauEq`); composing with `v10Sym a 0` makes σ rank-preserving.

  Write-up: `../analysis/v12-primenonswap/NOTES.md`; data: `v10sym_witness.py`.
-/
import DoubleDealSecurity.TauEq
import DoubleDealSecurity.CovariantAffine

namespace DoubleDeal.Security.LabelStep

open DoubleDeal Relabel
open DoubleDeal.Security (permDeck isDeck_permDeck rel_permDeck)
open DoubleDeal.Security.CovariantNarrow (Cell0Cov cell0Cov_v10Sym g0 g0_eq cell0Subgroup
  v10Sym_mem_cell0Subgroup roundBody_covariant_iff_id_of_cell0)
open DoubleDeal.Security.StemPosition (rowAmts colAmts c0Row rowSeat stemPos_zero)
open DoubleDeal.Security.RankPartition (swapsPerm RankChecks)
open DoubleDeal.Security.RankAffine (AffRankChecks)
open DoubleDeal.Security.TauEq (TauChecks rowAmts_congr tau_eq_of_rk exists_shift
  cell0Cov_tau_of_checks)
open DoubleDeal.Security.CovariantAffine (AffChecks glApp glApp_lt linSym linSym_zero_zero
  not_cell0Cov_lin_of_check)

/-! ## A. Per-rank label translations

  The card coordinates `ri`, `lbl`, `crd`, `xor4`, `ext_crd`, `v10Sym_crd` are in
  `SumRanksV10.lean`. -/

/-- The per-rank label translation: label `l ⊕ d r` at rank index `r`. -/
def trFn (d : Fin 13 → Fin 4) (c : Fin 52) : Fin 52 := crd (ri c) (xor4 (lbl c) (d (ri c)))

theorem trFn_crd (d : Fin 13 → Fin 4) (r : Fin 13) (l : Fin 4) :
    trFn d (crd r l) = crd r (xor4 l (d r)) := by
  simp only [trFn, ri_crd, lbl_crd]

theorem trFn_trFn (d : Fin 13 → Fin 4) (c : Fin 52) : trFn d (trFn d c) = c := by
  conv_lhs => rw [← crd_ri_lbl c]
  rw [trFn_crd, trFn_crd, xor4_cancel, crd_ri_lbl]

/-- `trFn d` as a relabelling (an involution). -/
def tr (d : Fin 13 → Fin 4) : Relabel where
  toFun := trFn d
  invFun := trFn d
  left_inv := trFn_trFn d
  right_inv := trFn_trFn d

theorem tr_crd (d : Fin 13 → Fin 4) (r : Fin 13) (l : Fin 4) :
    tr d (crd r l) = crd r (xor4 l (d r)) := trFn_crd d r l

theorem tr_ri (d : Fin 13 → Fin 4) (c : Fin 52) : ri (tr d c) = ri c := by
  show ri (crd _ _) = _; rw [ri_crd]

theorem tr_lbl (d : Fin 13 → Fin 4) (c : Fin 52) : lbl (tr d c) = xor4 (lbl c) (d (ri c)) := by
  show lbl (crd _ _) = _; rw [lbl_crd]

theorem tr_const (x : Fin 4) : tr (fun _ => x) = v10Sym 0 x :=
  ext_crd fun r l => by rw [tr_crd, v10Sym_crd, add_zero]

/-- (PROVED) Conjugating a per-rank translation by the rank shift `v10Sym k 0`. -/
theorem conj_tr (k : Fin 13) (d : Fin 13 → Fin 4) :
    v10Sym k 0 * tr d * (v10Sym k 0)⁻¹ = tr (fun r => d (r - k)) :=
  ext_crd fun r l => by
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, v10Sym_symm_crd, tr_crd, v10Sym_crd,
      xor4_zero, sub_add_cancel]

/-- A map on `Fin 13` with `f (r + 1) = f r ⊕ κ` has `κ = 0` (13 is odd) and is constant. -/
theorem chain_const (f : Fin 13 → Fin 4) (κ : Fin 4) (h : ∀ r, f (r + 1) = xor4 (f r) κ) :
    κ = 0 ∧ ∀ r, f r = f 0 := by
  have hn : ∀ n : ℕ, f (n : Fin 13) = xor4 (f 0) (if n % 2 = 0 then 0 else κ) := by
    intro n
    induction n with
    | zero => simp [xor4_zero]
    | succ n ih =>
      rw [Nat.cast_succ, h, ih, xor4_assoc]
      congr 1
      by_cases hn : n % 2 = 0
      · rw [if_pos hn, if_neg (by omega), zero_xor4]
      · rw [if_neg hn, if_pos (by omega), xor4_self]
  have h13 := hn 13
  simp only [show ((13 : ℕ) : Fin 13) = 0 from rfl, show 13 % 2 = 1 from rfl] at h13
  have hκ : κ = 0 := by
    have := h13
    rw [if_neg (by decide)] at this
    have e := congrArg (xor4 (f 0)) this
    rw [← xor4_assoc, xor4_self, zero_xor4] at e
    exact e.symm
  refine ⟨hκ, fun r => ?_⟩
  have := hn r.val
  rw [Fin.cast_val_eq_self, hκ] at this
  split at this <;> rw [this, xor4_zero]

/-! ## B. The column chain under per-column label shifts -/

theorem colValue_core : ∀ P1 P2 P3 a : Fin 4,
    gfAdd (gfAdd (gfAdd P1.val a.val) (gfTimesW (gfAdd P2.val a.val)))
        (gfTimesW (gfTimesW (gfAdd P3.val a.val))) =
      gfAdd (gfAdd P1.val (gfTimesW P2.val)) (gfTimesW (gfTimesW P3.val)) := by decide

theorem colSuits_core (y0 y1 y2 y3 b : Nat) :
    gfAdd (gfAdd (gfAdd (gfAdd y0 b) (gfAdd y1 b)) (gfAdd y2 b)) (gfAdd y3 b) =
      gfAdd (gfAdd (gfAdd y0 y1) y2) y3 := by
  unfold gfAdd; omega

/-- (PROVED) The v10 column turn is unchanged when every label of the previous column is
    shifted by `a` and every label of the own column by `b`. -/
theorem colTurnV10_congr {p y p' y' : Fin 4 → Nat} {a b : Nat} (ha : a < 4)
    (hp : ∀ r, suitLabel (p' r) = gfAdd (suitLabel (p r)) a)
    (hy : ∀ r, suitLabel (y' r) = gfAdd (suitLabel (y r)) b) :
    colTurnV10 p' y' = colTurnV10 p y := by
  unfold colTurnV10 colValue colSuits
  rw [hp 1, hp 2, hp 3, hy 0, hy 1, hy 2, hy 3, colSuits_core]
  congr 1
  exact colValue_core ⟨_, suitLabel_lt (p 1)⟩ ⟨_, suitLabel_lt (p 2)⟩ ⟨_, suitLabel_lt (p 3)⟩
    ⟨a, ha⟩

/-- `G'` is `G` with every label of column `c` shifted by `κ c`. -/
def LabelShift (G' G : Grid Nat) (κ : Fin 13 → Nat) : Prop :=
  (∀ c, κ c < 4) ∧ ∀ r c, suitLabel (G' r c) = gfAdd (suitLabel (G r c)) (κ c)

theorem LabelShift.colRotate {G' G : Grid Nat} {κ : Fin 13 → Nat} (h : LabelShift G' G κ)
    (s : Fin 13 → Nat) : LabelShift (DoubleDeal.colRotate G' s) (DoubleDeal.colRotate G s) κ :=
  ⟨h.1, fun r c => by rw [colRotate_apply, colRotate_apply]; exact h.2 _ c⟩

/-- (PROVED) Grids that differ in labels by a constant per column get the same v10 column
    amounts. -/
theorem colAmt_congr_label {G' G : Grid Nat} {κ : Fin 13 → Nat} (h : LabelShift G' G κ) :
    colAmt colTurnV10 G' = colAmt colTurnV10 G := by
  have key : ∀ n, n ≤ 13 → ∀ c, colStepOf c ≤ n → colAmt colTurnV10 G' c = colAmt colTurnV10 G c := by
    intro n
    induction n with
    | zero => intro _ c hc; exfalso; unfold colStepOf at hc; split at hc <;> omega
    | succ n ih =>
      intro hn c hc
      by_cases hle : colStepOf c ≤ n
      · exact ih (by omega) c hle
      have hs : colStepOf c - 1 = n := by omega
      unfold colAmt
      rw [hs, colsDone_eq_partial _ G' n (by omega), colsDone_eq_partial _ G n (by omega)]
      have he : (fun c => if colStepOf c ≤ n then colAmt colTurnV10 G' c else 0) =
          (fun c => if colStepOf c ≤ n then colAmt colTurnV10 G c else 0) := by
        funext c'
        split
        · exact ih (by omega) c' ‹_›
        · rfl
      rw [he]
      have hr := h.colRotate (fun c => if colStepOf c ≤ n then colAmt colTurnV10 G c else 0)
      exact colTurnV10_congr (h.1 _) (fun r => hr.2 r _) (fun r => hr.2 r _)
  funext c
  exact key 13 le_rfl c (by unfold colStepOf; have := c.isLt; split <;> omega)

/-! ## C. Per-rank translations with the seat-26 condition are constant -/

/-- σ preserves the rank (mod 13) of every card. -/
def RankPres (σ : Relabel) : Prop := ∀ c, rk (σ c) = rk c

theorem tr_rankPres (d : Fin 13 → Fin 4) : RankPres (tr d) :=
  fun c => (rk_eq_iff _ _).mpr (congrArg Fin.val (tr_ri d c))

theorem rowAmts_rankPres {σ : Relabel} (hp : RankPres σ) (π : Relabel) :
    rowAmts (permDeck (σ * π)) = rowAmts (permDeck π) :=
  rowAmts_congr fun s => hp (π s)

theorem lay_permDeck_mul (σ π : Relabel) :
    layColumnMajor (permDeck (σ * π)) = relG σ (layColumnMajor (permDeck π)) := by
  funext r c
  simp only [layColumnMajor, permDeck, relG, app_fin, Equiv.Perm.mul_apply]

/-- The grid after the v10 row stage. -/
def postGrid (m : Fin 52 → Nat) : Grid Nat := rowsDone rowTurnV10 (layColumnMajor m) 4

theorem postGrid_rankPres {σ : Relabel} (hp : RankPres σ) (π : Relabel) :
    postGrid (permDeck (σ * π)) = relG σ (postGrid (permDeck π)) := by
  have e := rowAmts_rankPres hp π
  unfold rowAmts at e
  unfold postGrid
  rw [rowsDone_eq, rowsDone_eq, e, lay_permDeck_mul, relG_rowRotate]

theorem postGrid_apply (π : Relabel) (r : Fin 4) (c : Fin 13) :
    postGrid (permDeck π) r c = (π (cmFlat r ⟨(c.val + rowAmts (permDeck π) r % 13) % 13,
      Nat.mod_lt _ (by decide)⟩)).val := by
  unfold postGrid
  rw [rowsDone_eq, rowRotate_apply]
  rfl

theorem c0Row_rankPres {σ : Relabel} (hp : RankPres σ) (π : Relabel) :
    c0Row (permDeck (σ * π)) =
      StemPosition.srcRow (colAmt colTurnV10 (relG σ (postGrid (permDeck π)))) 0 0 := by
  unfold c0Row colAmts
  rw [← postGrid_rankPres hp]
  rfl

/-- The deck of step 4, as a permutation (seat ↦ card). -/
def labPerm : Relabel := swapsPerm labSwaps

/-- The label translation by `e` at rank index 0 only. -/
def eVec (e : Fin 4) : Fin 13 → Fin 4 := fun r => if r = 0 then e else 0

/-- After the row stage, every column of the deck is a full rank class of a rank index
    `≠ 0`, or holds only rank indices 0 and 1. -/
abbrev LabStruct : Prop := ∀ c : Fin 13,
  (∀ r : Fin 4, postGrid (permDeck labPerm) r c % 13 = postGrid (permDeck labPerm) 0 c % 13 ∧
    postGrid (permDeck labPerm) 0 c % 13 ≠ 0) ∨
  (∀ r : Fin 4, postGrid (permDeck labPerm) r c % 13 = 0 ∨
    postGrid (permDeck labPerm) r c % 13 = 1)

/-- `tr (eVec e)` moves the source row of stem cell 0 of the deck. -/
abbrev LabKill (e : Fin 4) : Prop :=
  c0Row (permDeck (tr (eVec e) * labPerm)) ≠ c0Row (permDeck labPerm)

/-- The finite checks of step 4 (discharged by kernel `decide!` in the heavy library,
    `LabelStep.labelChecks_ok`). -/
abbrev LabelChecks : Prop := LabStruct ∧ ∀ e : Fin 4, e ≠ 0 → LabKill e

/-- (PROVED, GIVEN `LabStruct`) `tr d` and `tr (eVec (d 0 ⊕ d 1))` give the deck the same
    source row of stem cell 0. -/
theorem c0Row_tr_eq (hS : LabStruct) (d : Fin 13 → Fin 4) :
    c0Row (permDeck (tr d * labPerm)) = c0Row (permDeck (tr (eVec (xor4 (d 0) (d 1))) * labPerm)) := by
  rw [c0Row_rankPres (tr_rankPres d), c0Row_rankPres (tr_rankPres _)]
  congr 1
  set G := postGrid (permDeck labPerm) with hG
  set x : Fin 4 → Fin 13 → Fin 52 := fun r c => labPerm (cmFlat r ⟨(c.val +
    rowAmts (permDeck labPerm) r % 13) % 13, Nat.mod_lt _ (by decide)⟩) with hx
  have hGx : ∀ r c, G r c = (x r c).val := fun r c => postGrid_apply labPerm r c
  have hri : ∀ r c, G r c % 13 = (ri (x r c)).val := fun r c => by rw [hGx]; rfl
  let full : Fin 13 → Prop := fun c => ∀ r : Fin 4, G r c % 13 = G 0 c % 13 ∧ G 0 c % 13 ≠ 0
  classical
  let κ' : Fin 13 → Fin 4 := fun c => if full c then d (ri (x 0 c)) else d 1
  refine colAmt_congr_label (κ := fun c => (κ' c).val) ⟨fun c => (κ' c).isLt, fun r c => ?_⟩
  simp only [relG, hGx, app_fin]
  suffices hs : lbl (tr d (x r c)) = xor4 (lbl (tr (eVec (xor4 (d 0) (d 1))) (x r c))) (κ' c) from
    congrArg Fin.val hs
  rw [tr_lbl, tr_lbl]
  by_cases hf : full c
  · have hk : κ' c = d (ri (x 0 c)) := if_pos hf
    obtain ⟨h1, h2⟩ := hf r
    rw [hri, hri] at h1
    rw [hri] at h2
    have he : ri (x r c) = ri (x 0 c) := Fin.ext h1
    have hne : ri (x r c) ≠ 0 := fun e => h2 (by rw [← he, e]; rfl)
    rw [hk, he, show eVec _ (ri (x 0 c)) = 0 from if_neg (he ▸ hne), xor4_zero]
  · have hk : κ' c = d 1 := if_neg hf
    rw [hk]
    rcases hS c with hfull | h01
    · exact absurd hfull hf
    rcases h01 r with h0 | h1
    · rw [hri] at h0
      have : ri (x r c) = 0 := Fin.ext h0
      rw [this, show eVec _ 0 = xor4 (d 0) (d 1) from if_pos rfl]
      exact xor4_e0 _ _ _
    · rw [hri] at h1
      have : ri (x r c) = 1 := Fin.ext h1
      rw [this, show eVec (xor4 (d 0) (d 1)) 1 = 0 from if_neg (by decide), xor4_zero]

/-- (PROVED, GIVEN `TauChecks` and `LabelChecks`) If `tr d` satisfies the seat-26 condition,
    then `d 0 = d 1`. -/
theorem d01_of_cell0 (hT : TauChecks) (hL : LabelChecks) {d : Fin 13 → Fin 4} {τ : Relabel}
    (h : Cell0Cov (tr d) τ) : d 0 = d 1 := by
  have hτ : τ = tr d := tau_eq_of_rk hT h (tr_rankPres d)
  subst hτ
  have hc : c0Row (permDeck (tr d * labPerm)) = c0Row (permDeck labPerm) := by
    have h1 := h (permDeck labPerm) (isDeck_permDeck _)
    rw [rel_permDeck, stemPos_zero, stemPos_zero, rowAmts_rankPres (tr_rankPres d)] at h1
    simp only [permDeck, Equiv.Perm.mul_apply, app_fin] at h1
    have h2 := labPerm.injective ((tr d).injective (Fin.ext h1))
    have h3 := congrArg cmRow h2
    simp only [rowSeat, (cm_cmFlat _ _).1] at h3
    exact h3
  by_contra hne
  have he : xor4 (d 0) (d 1) ≠ 0 := fun e => hne (by
    have := congrArg (fun z => xor4 z (d 1)) e
    simpa only [xor4_cancel, zero_xor4] using this)
  exact hL.2 _ he ((c0Row_tr_eq hL.1 d).symm.trans hc)

/-- (PROVED, GIVEN `TauChecks` and `LabelChecks`) If `tr d` lies in `cell0Subgroup` (the
    seat-26 condition for some τ), `d` is constant. -/
theorem tr_const_of_mem (hT : TauChecks) (hL : LabelChecks) {d : Fin 13 → Fin 4}
    (h : tr d ∈ cell0Subgroup) : ∀ r, d r = d 0 := by
  have step : ∀ r, d (r + 1) = xor4 (d r) 0 := by
    intro r
    have hc : tr (fun r' => d (r' - -r)) ∈ cell0Subgroup := by
      rw [← conj_tr (-r) d]
      exact cell0Subgroup.mul_mem (cell0Subgroup.mul_mem (v10Sym_mem_cell0Subgroup _ 0) h)
        (cell0Subgroup.inv_mem (v10Sym_mem_cell0Subgroup _ 0))
    obtain ⟨_, hτ⟩ := hc
    have := d01_of_cell0 hT hL hτ
    simp only [zero_sub, neg_neg, sub_neg_eq_add] at this
    rw [zero_add, add_comm 1 r] at this
    rw [xor4_zero, this]
  exact (chain_const d 0 step).2

/-! ## D. A rank-preserving σ with the seat-26 condition is a `v10Sym 0 x` -/

/-- The label map `glApp g` of `linSym 0 g` (on every rank index), on `Fin 4`. -/
def gl4 (g : Fin 6) (l : Fin 4) : Fin 4 := ⟨glApp g l.val, glApp_lt g l⟩

theorem linSym_crd : ∀ (g : Fin 6) (r : Fin 13) (l : Fin 4),
    linSym 0 g (crd r l) = crd r (gl4 g l) := by decide!

/-- Every permutation of `Fin 4` (given by its four values) is `l ↦ gl4 g l ⊕ x`. -/
theorem diag_table : ∀ a b c e : Fin 4, a ≠ b → a ≠ c → a ≠ e → b ≠ c → b ≠ e → c ≠ e →
    ∃ x : Fin 4, ∃ g : Fin 6, a = xor4 (gl4 g 0) x ∧ b = xor4 (gl4 g 1) x ∧
      c = xor4 (gl4 g 2) x ∧ e = xor4 (gl4 g 3) x := by decide!

theorem perm4_affine (h : Fin 4 → Fin 4) (hi : Function.Injective h) :
    ∃ x : Fin 4, ∃ g : Fin 6, ∀ l, h l = xor4 (gl4 g l) x := by
  have ne : ∀ i j : Fin 4, i ≠ j → h i ≠ h j := fun i j hij e => hij (hi e)
  obtain ⟨x, g, h0, h1, h2, h3⟩ := diag_table (h 0) (h 1) (h 2) (h 3)
    (ne _ _ (by decide)) (ne _ _ (by decide)) (ne _ _ (by decide)) (ne _ _ (by decide))
    (ne _ _ (by decide)) (ne _ _ (by decide))
  exact ⟨x, g, fun l => by fin_cases l <;> assumption⟩

theorem affine_core : ∀ (g : Fin 6) (x0 a x : Fin 4),
    xor4 (gl4 g (xor4 a x)) x0 =
      xor4 (xor4 (gl4 g a) x0) (xor4 (xor4 (gl4 g x) x0) (xor4 (gl4 g 0) x0)) := by decide

/-- (PROVED) Every permutation of `Fin 4` is affine for XOR. -/
theorem perm4_xor (h : Fin 4 → Fin 4) (hi : Function.Injective h) (a x : Fin 4) :
    h (xor4 a x) = xor4 (h a) (xor4 (h x) (h 0)) := by
  obtain ⟨x0, g, hg⟩ := perm4_affine h hi
  rw [hg, hg, hg, hg]
  exact affine_core g x0 a x

/-- (PROVED, GIVEN `TauChecks`, `LabelChecks`, `AffChecks`) A rank-preserving σ in
    `cell0Subgroup` is a `v10Sym 0 x`. -/
theorem rankPres_mem_v10Sym (hT : TauChecks) (hL : LabelChecks) (hA : AffChecks) {σ : Relabel}
    (hσ : σ ∈ cell0Subgroup) (hp : RankPres σ) : ∃ x, σ = v10Sym 0 x := by
  -- the label maps
  set lab : Fin 13 → Fin 4 → Fin 4 := fun r l => lbl (σ (crd r l)) with hlab
  have hσc : ∀ r l, σ (crd r l) = crd r (lab r l) := by
    intro r l
    conv_lhs => rw [← crd_ri_lbl (σ (crd r l))]
    rw [ri_eq_of_rk (hp _), ri_crd]
  have linj : ∀ r, Function.Injective (lab r) := by
    intro r a b e
    have : σ (crd r a) = σ (crd r b) := by rw [hσc, hσc, e]
    exact (crd_inj (σ.injective this)).2
  have lsurj : ∀ r, Function.Surjective (lab r) := fun r =>
    Finite.injective_iff_surjective.mp (linj r)
  -- conjugating the diagonal translations: δ does not depend on the rank
  set δ : Fin 13 → Fin 4 → Fin 4 := fun r x => xor4 (lab r x) (lab r 0) with hδ
  have hconj : ∀ x, σ * tr (fun _ => x) * σ⁻¹ = tr (fun r => δ r x) := by
    intro x
    rw [mul_inv_eq_iff_eq_mul]
    refine ext_crd fun r l => ?_
    simp only [Equiv.Perm.mul_apply, tr_crd, hσc, hδ]
    rw [perm4_xor _ (linj r)]
  have hδc : ∀ r x, δ r x = δ 0 x := by
    intro r x
    have hm : tr (fun r => δ r x) ∈ cell0Subgroup := by
      rw [← hconj, tr_const]
      exact cell0Subgroup.mul_mem (cell0Subgroup.mul_mem hσ (v10Sym_mem_cell0Subgroup 0 x))
        (cell0Subgroup.inv_mem hσ)
    exact tr_const_of_mem hT hL hm r
  have haff : ∀ r a x, lab r (xor4 a x) = xor4 (lab r a) (δ 0 x) := by
    intro r a x
    rw [← hδc r x, perm4_xor _ (linj r)]
  -- every label map is the rank-0 one after a translation
  choose c hc using fun r => lsurj 0 (lab r 0)
  have hlabc : ∀ r l, lab r l = lab 0 (xor4 (c r) l) := by
    intro r l
    rw [haff 0, hc, ← haff r, zero_xor4]
  -- the rank-shift commutator: c (r + 1) = c r ⊕ κ
  set u := v10Sym 1 0 with hu
  set e : Fin 13 → Fin 4 := fun r => xor4 (c (r + 1)) (c r) with he
  have hcomm : u⁻¹ * σ * u = σ * tr e := by
    refine ext_crd fun r l => ?_
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, hu, v10Sym_crd, hσc, v10Sym_symm_crd,
      tr_crd, xor4_zero, add_sub_cancel_right]
    rw [hlabc (r + 1), hlabc r, he]
    simp only
    rw [xor4_shuffle]
  have hem : tr e ∈ cell0Subgroup := by
    have : tr e = σ⁻¹ * (u⁻¹ * σ * u) := by rw [hcomm, inv_mul_cancel_left]
    rw [this]
    exact cell0Subgroup.mul_mem (cell0Subgroup.inv_mem hσ)
      (cell0Subgroup.mul_mem (cell0Subgroup.mul_mem (cell0Subgroup.inv_mem (v10Sym_mem_cell0Subgroup 1 0)) hσ)
        (v10Sym_mem_cell0Subgroup 1 0))
  have hec := tr_const_of_mem hT hL hem
  have hcc := (chain_const c (e 0) fun r => xor4_eq_iff _ _ _ (hec r)).2
  -- σ acts by one label map on every rank
  set hfun : Fin 4 → Fin 4 := fun l => lab 0 (xor4 (c 0) l) with hhfun
  have hinj : Function.Injective hfun := fun a b h =>
    xor4_left_inj a b (c 0) (by rw [xor4_comm a, xor4_comm b]; exact linj 0 h)
  obtain ⟨x, g, hxg⟩ := perm4_affine hfun hinj
  have hσeq : σ = v10Sym 0 x * linSym 0 g := by
    refine ext_crd fun r l => ?_
    rw [Equiv.Perm.mul_apply, linSym_crd, v10Sym_crd, add_zero, hσc, hlabc, hcc r]
    exact congrArg (crd r) (hxg l)
  -- the linear part is trivial
  have hg : g = 0 := by
    by_contra hg
    have hm : linSym 0 g ∈ cell0Subgroup := by
      have : linSym 0 g = (v10Sym 0 x)⁻¹ * σ := by rw [hσeq, inv_mul_cancel_left]
      rw [this]
      exact cell0Subgroup.mul_mem (cell0Subgroup.inv_mem (v10Sym_mem_cell0Subgroup 0 x)) hσ
    obtain ⟨τ, hτ⟩ := hm
    exact not_cell0Cov_lin_of_check hA 0 g (fun e => hg (Prod.mk.inj e).2) τ hτ
  refine ⟨x, ?_⟩
  rw [hσeq, hg, linSym_zero_zero, mul_one]

/-! ## E. Every σ with the seat-26 condition is a `v10Sym`, and τ = σ -/

/-- All the finite checks of steps 1-4 (discharged by kernel `decide!` in the heavy library,
    `LabelStep.v10SymChecks_ok`). -/
abbrev V10SymChecks : Prop :=
  RankChecks ∧ AffChecks ∧ AffRankChecks ∧ TauChecks ∧ LabelChecks

/-- (PROVED, GIVEN the finite checks `V10SymChecks` as a hypothesis) If `Cell0Cov σ τ`, then
    σ is a `v10Sym a x` and τ = σ. Unconditional form: heavy library,
    `LabelStep.cell0Cov_mem_v10Sym`. -/
theorem cell0Cov_mem_v10Sym_of_checks (hchk : V10SymChecks) {σ τ : Relabel}
    (h : Cell0Cov σ τ) : (∃ (a : Fin 13) (x : Fin 4), σ = v10Sym a x) ∧ τ = σ := by
  obtain ⟨hR, hA, hAR, hT, hL⟩ := hchk
  obtain ⟨hτ, u, hu⟩ := cell0Cov_tau_of_checks hR hAR hT h
  obtain ⟨a, ha⟩ := exists_shift 1 u one_ne_zero
  have hm : σ * v10Sym a 0 ∈ cell0Subgroup :=
    cell0Subgroup.mul_mem ⟨τ, h⟩ (v10Sym_mem_cell0Subgroup a 0)
  have hp : RankPres (σ * v10Sym a 0) := fun c => by
    rw [Equiv.Perm.mul_apply, hu, rk_v10Sym]
    linear_combination ha
  obtain ⟨x, hx⟩ := rankPres_mem_v10Sym hT hL hA hm hp
  refine ⟨⟨neg13 a, x, ?_⟩, hτ⟩
  rw [eq_mul_inv_of_mul_eq hx]
  refine ext_crd fun r l => ?_
  rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, v10Sym_symm_crd, v10Sym_crd, v10Sym_crd,
    xor4_zero, add_zero, neg13_eq, sub_eq_add_neg]

/-- (PROVED, GIVEN `V10SymChecks`) The seat-26 condition holds exactly for the pairs
    `(v10Sym a x, v10Sym a x)`. -/
theorem cell0Cov_iff_of_checks (hchk : V10SymChecks) (σ τ : Relabel) :
    Cell0Cov σ τ ↔ (∃ (a : Fin 13) (x : Fin 4), σ = v10Sym a x) ∧ τ = σ := by
  refine ⟨cell0Cov_mem_v10Sym_of_checks hchk, ?_⟩
  rintro ⟨⟨a, x, rfl⟩, rfl⟩
  exact cell0Cov_v10Sym a x

/-- (PROVED, GIVEN `V10SymChecks`) The statement of the covariant round conjecture
    `Rounds.roundBody_covariant_iff_id`: σ is covariant for the unkeyed round body (for
    some output relabelling) iff σ = 1. Via `roundBody_covariant_iff_id_of_cell0`.
    `roundBody_covariant_iff_id` itself is unchanged and keeps its `sorry`. Unconditional
    form: heavy library, `LabelStep.roundBody_covariant_iff_id_heavy`. -/
theorem roundBody_covariant_iff_id_of_checks (hchk : V10SymChecks) (σ : Relabel) :
    Covariant σ unkeyedWithMix ↔ σ = 1 :=
  roundBody_covariant_iff_id_of_cell0 (fun _ _ h => (cell0Cov_mem_v10Sym_of_checks hchk h).1) σ

end DoubleDeal.Security.LabelStep
