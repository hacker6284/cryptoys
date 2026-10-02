/-
  The stem as a position map, and the support gap of its relabelling differences (first slice
  towards the off-diagonal stem column bound; security README, "Roadmap", the M7
  row). Structure only.

  NO BOUND ON `dpFCount` (OR ANY OTHER DIFFERENTIAL COUNT) IS PROVED HERE. Every statement is
  exact and deck-by-deck; nothing is counted over decks or keys.

  The stem `unkeyedNoMix = scoopColumnMajor ∘ shiftRows ∘ sumRanksV10 ∘ layColumnMajor` only
  moves cards. `SumRanksV10Iff.sumRanksChain_eq` writes v10 SumRanks as one row rotation by
  `rowAmt` followed by one column rotation by `colAmt`, the amounts depending on the cards.

  Definitions.
  * `seatMap t s`: the seat of the input grid that `colRotate (rowRotate g t) s` shows at a
    seat (`colRotate_rowRotate_apply`); `srcRow s r c` is its row (the source row; not
    `SumRanksDP.rowOf`, which is a row of a permutation).
  * `rowAmts m`, `colAmts m`: the amounts SumRanks uses on the packet `m` laid column-major.
  * `inSeat k`: the seat of the SumRanks output that the stem sends to output position `k`
    (ShiftRows, then scoop column-major). `stemPos m k = cmFlat (seatMap (rowAmts m)
    (colAmts m) (inSeat k))`, and `stemPerm m` is `stemPos m` as a permutation.
  * `zRows m m'`, `zCols m m'` (`z`: the number of agreeing rows / columns): the number of
    rows whose row amounts agree mod 13, and of columns whose column amounts agree mod 4,
    between the packets `m` and `m'`.

  Proved:
  * `unkeyedNoMix_eq_comp`: `unkeyedNoMix m = m ∘ stemPos m`, for every `m : Fin 52 → Nat`
    (no deck hypothesis); `stemPos_injective`. (`Rounds.unkeyedNoMix_cells`, the existential
    form, is proved from `unkeyedNoMix_eq_comp`.)
  * `conj_of_stem_rel`: if `unkeyedNoMix (β·x) = γ·unkeyedNoMix x` at the deck
    `x = permDeck π`, then `γ⁻¹ * β = π * q * π⁻¹` with
    `q = stemPerm x * (stemPerm (β·x))⁻¹`, the ratio of the two decks' position maps.
    The hypothesis is exactly the filter predicate of `FullCipher.dpFCount β γ`
    (`Differential.dpCount unkeyedNoMix β γ`) at the deck `permDeck π`, the count in the
    off-diagonal stem bound (`StemUnion.dpFCount_le_of_ne`), and it is the one-deck
    form of "the stem is exactly covariant from `β` to `γ`". In prose (not a separate
    theorem): since `stemPos m = cmFlat ∘ S_m ∘ inSeat` with `S_m` the seat map of `m`, the
    fixed layer `inSeat` cancels in the ratio, and `q = cmFlat ∘ (S_x ∘ S_(β·x)⁻¹) ∘ cmFlat⁻¹`:
    only `cmFlat` conjugates the ratio of the two seat maps.
  * `seatMap_eq_iff`: the two seat maps agree at `(r, c)` iff the column amounts of `c`
    agree mod 4 and the row amounts of row `srcRow s r c` agree mod 13. So the agreeing seats
    are, in each agreeing column, the agreeing rows moved by that column's rotation (a
    row-shifted copy of rows × columns, of the same size, not literally that product).
  * `card_fixed_eq`: under the same hypothesis, `γ⁻¹ * β` fixes exactly
    `zRows x (β·x) * zCols x (β·x)` cards; `card_moved_eq`: it moves `52 - zRows · zCols`.
  * `card_moved_cases`: so it moves `0` cards, exactly `4` cards with
    `(zRows, zCols) = (4, 12)`, or at least `8` cards (`zRows ≤ 4`, `zCols ≤ 13`, and the only
    such product in `45..51` is `48 = 4 · 12`). `card_moved_zero_or_ge_four` (`0` or at
    least `4`) is its corollary; never moving exactly 1 card holds for every permutation, so
    its content is "never exactly 2 or 3". The values `52 - a·b` also exclude the moved
    counts 9, 10, 11, 14, 15, 17, 18, 21, 23, 27, 29, 33 and 35, which is not stated here.

  NOT proved, and limits:
  * No count of decks: nothing here bounds `dpFCount β γ` or any differential probability.
    This proves no part of the off-diagonal stem bound. It would give `dpFCount β γ = 0` only when the support
    size of `γ⁻¹ * β` is not of the form `52 - a·b` (`a ≤ 4`, `b ≤ 13`), e.g. 2 or 3 (a
    transposition or a 3-cycle). For supports 1–3 and 5–7 that corollary is
    `StemSupportFour.dpFCount_eq_zero_of_support_lt_eight_ne_four`; for the other excluded
    values it is not stated. Nothing here says anything for any other `β`.
  * Which pairs `(zRows, zCols)` actually occur for a given `β` is not studied; the amounts
    of `x` and `β·x` are not related to `β` here.
  * About the stem (the final no-mix round) only, not GridCycle or a mix round.
-/
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.IntervalCases
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.GroupTheory.Perm.Support
import DoubleDealSecurity.SumRanksV10Iff

namespace DoubleDeal.Security.StemPosition

open DoubleDeal Relabel Finset

/-! ## One row stage, then one column stage, as a seat map -/

/-- The row of the input grid that the column stage shows at `(r, c)` (column `c` rotated
    top→bottom by `s c`). -/
def srcRow (s : Fin 13 → Nat) (r : Fin 4) (c : Fin 13) : Fin 4 :=
  ⟨(r.val + (4 - s c % 4)) % 4, Nat.mod_lt _ (by decide)⟩

/-- The seat of the input grid that `colRotate (rowRotate g t) s` shows at `p`. -/
def seatMap (t : Fin 4 → Nat) (s : Fin 13 → Nat) (p : Fin 4 × Fin 13) : Fin 4 × Fin 13 :=
  (srcRow s p.1 p.2, ⟨(p.2.val + t (srcRow s p.1 p.2) % 13) % 13, Nat.mod_lt _ (by decide)⟩)

/-- (PROVED) Rows by `t`, then columns by `s`, reads the seat `seatMap t s (r, c)`. -/
theorem colRotate_rowRotate_apply {α : Type} (g : Grid α) (t : Fin 4 → Nat)
    (s : Fin 13 → Nat) (r : Fin 4) (c : Fin 13) :
    colRotate (rowRotate g t) s r c = g (seatMap t s (r, c)).1 (seatMap t s (r, c)).2 := by
  rw [colRotate_apply, rowRotate_apply]
  rfl

/-- (PROVED) `seatMap t s` is injective, for all amounts. -/
theorem seatMap_injective (t : Fin 4 → Nat) (s : Fin 13 → Nat) :
    Function.Injective (seatMap t s) := by
  rintro ⟨r1, c1⟩ ⟨r2, c2⟩ h
  simp only [seatMap, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have h2' := congrArg Fin.val h2
  simp only at h2'
  rw [h1] at h2'
  have hc : c1 = c2 := by
    apply Fin.ext
    have := c1.isLt
    have := c2.isLt
    omega
  subst hc
  have h1' := congrArg Fin.val h1
  simp only [srcRow] at h1'
  have := r1.isLt
  have := r2.isLt
  have hr : r1 = r2 := Fin.ext (by omega)
  subst hr
  rfl

/-- (PROVED) Where two seat maps agree: the column amounts of `c` agree mod 4, and the row
    amounts of the row `srcRow s r c` read there agree mod 13. -/
theorem seatMap_eq_iff (t t' : Fin 4 → Nat) (s s' : Fin 13 → Nat) (r : Fin 4) (c : Fin 13) :
    seatMap t s (r, c) = seatMap t' s' (r, c) ↔
      s c % 4 = s' c % 4 ∧ t (srcRow s r c) % 13 = t' (srcRow s r c) % 13 := by
  have hrow : srcRow s r c = srcRow s' r c ↔ s c % 4 = s' c % 4 := by
    constructor
    · intro h
      have h' := congrArg Fin.val h
      simp only [srcRow] at h'
      have := r.isLt
      have := Nat.mod_lt (s c) (by decide : 0 < 4)
      have := Nat.mod_lt (s' c) (by decide : 0 < 4)
      omega
    · intro h
      apply Fin.ext
      simp only [srcRow, h]
  simp only [seatMap, Prod.mk.injEq]
  constructor
  · rintro ⟨h1, h2⟩
    have hs := hrow.1 h1
    refine ⟨hs, ?_⟩
    have h2' := congrArg Fin.val h2
    simp only at h2'
    rw [← h1] at h2'
    have := c.isLt
    have := Nat.mod_lt (t (srcRow s r c)) (by decide : 0 < 13)
    have := Nat.mod_lt (t' (srcRow s r c)) (by decide : 0 < 13)
    omega
  · rintro ⟨hs, ht⟩
    have h1 := hrow.2 hs
    refine ⟨h1, ?_⟩
    apply Fin.ext
    simp only
    rw [← h1, ht]

/-! ## The stem -/

/-- The row amounts v10 SumRanks uses on the packet `m` (laid column-major). -/
def rowAmts (m : Fin 52 → Nat) : Fin 4 → Nat := rowAmt rowTurnV10 (layColumnMajor m)

/-- The column amounts v10 SumRanks uses on the packet `m` (after its row stage). -/
def colAmts (m : Fin 52 → Nat) : Fin 13 → Nat :=
  colAmt colTurnV10 (rowsDone rowTurnV10 (layColumnMajor m) 4)

/-- The SumRanks output seat that the stem sends to output position `k` (ShiftRows turns
    row `r` left by `r`; then scoop column-major). -/
def inSeat (k : Fin 52) : Fin 4 × Fin 13 :=
  (cmRow k, ⟨((cmCol k).val + (cmRow k).val) % 13, Nat.mod_lt _ (by decide)⟩)

/-- The input position that the stem sends to output position `k`, for amounts `t`, `s`. -/
def stemPosOf (t : Fin 4 → Nat) (s : Fin 13 → Nat) (k : Fin 52) : Fin 52 :=
  cmFlat (seatMap t s (inSeat k)).1 (seatMap t s (inSeat k)).2

/-- The stem's position map on the packet `m`. -/
def stemPos (m : Fin 52 → Nat) : Fin 52 → Fin 52 := stemPosOf (rowAmts m) (colAmts m)

/-- (PROVED) The stem only moves cards: `unkeyedNoMix m = m ∘ stemPos m`, for every packet
    `m` (no deck hypothesis). -/
theorem unkeyedNoMix_eq_comp (m : Fin 52 → Nat) :
    unkeyedNoMix m = fun k => m (stemPos m k) := by
  funext k
  simp only [unkeyedNoMix, scoopColumnMajor, shiftRows, sumRanksV10, sumRanksChain_eq,
    colRotate_rowRotate_apply, layColumnMajor]
  rfl

/-- The row of column 0 that the last column step brings to the top (seat 0). -/
def c0Row (m : Fin 52 → Nat) : Fin 4 := srcRow (colAmts m) 0 0

/-- The seat `(ρ, t ρ % 13)` of row `ρ`. -/
def rowSeat (t : Fin 4 → Nat) (ρ : Fin 4) : Fin 52 :=
  cmFlat ρ ⟨t ρ % 13, Nat.mod_lt _ (by decide)⟩

/-- (PROVED) `unkeyedNoMix_eq_comp` at output position 0: stem cell 0 of any packet `m` is
    `m` at the seat `(ρ, rowAmts m ρ % 13)` of the row `ρ = c0Row m` (column 0 is turned
    only by the last column step; ShiftRows does not move row 0). -/
theorem stemPos_zero (m : Fin 52 → Nat) :
    unkeyedNoMix m 0 = m (rowSeat (rowAmts m) (c0Row m)) := by
  rw [unkeyedNoMix_eq_comp]
  show m (cmFlat (seatMap (rowAmts m) (colAmts m) (inSeat 0)).1
    (seatMap (rowAmts m) (colAmts m) (inSeat 0)).2) = _
  have h0 : inSeat 0 = (0, 0) := rfl
  rw [h0]
  unfold rowSeat c0Row seatMap
  congr 2
  apply Fin.ext
  simp only [Fin.val_zero, Nat.zero_add]
  exact Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide))

theorem inSeat_injective : Function.Injective inSeat := by
  intro k1 k2 h
  simp only [inSeat, Prod.mk.injEq, Fin.ext_iff, cmRow, cmCol] at h
  apply Fin.ext
  have := k1.isLt
  have := k2.isLt
  omega

theorem inSeat_bijective : Function.Bijective inSeat := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨inSeat_injective, by simp⟩

/-- `cmFlat` is injective on seats, as a function of the pair. (The same fact as
    `SumRanksDP.cmEquiv.symm.injective`, `SumRanksDP/Decomp.lean`; that module is not imported
    here. The long-term home for `cmEquiv` and this lemma is the core `Grid.lean`. Not the
    per-row `SumRanksDP.cmFlat_injective`.) -/
theorem cmFlat_inj2 {p q : Fin 4 × Fin 13} (h : cmFlat p.1 p.2 = cmFlat q.1 q.2) :
    p = q := by
  have e1 := congrArg cmRow h
  have e2 := congrArg cmCol h
  rw [(cm_cmFlat _ _).1, (cm_cmFlat _ _).1] at e1
  rw [(cm_cmFlat _ _).2, (cm_cmFlat _ _).2] at e2
  exact Prod.ext e1 e2

/-- (PROVED) `stemPosOf t s k = stemPosOf t' s' k` iff the seat maps agree at `inSeat k`. -/
theorem stemPosOf_eq_iff (t t' : Fin 4 → Nat) (s s' : Fin 13 → Nat) (k : Fin 52) :
    stemPosOf t s k = stemPosOf t' s' k ↔ seatMap t s (inSeat k) = seatMap t' s' (inSeat k) :=
  ⟨fun h => cmFlat_inj2 h, fun h => by unfold stemPosOf; rw [h]⟩

/-- (PROVED) The position map for row amounts `t` and column amounts `s` is injective. -/
theorem stemPosOf_injective (t : Fin 4 → Nat) (s : Fin 13 → Nat) :
    Function.Injective (stemPosOf t s) :=
  fun _ _ h => inSeat_injective (seatMap_injective _ _ (cmFlat_inj2 h))

/-- `stemPosOf t s` as a permutation of the positions. -/
noncomputable def seatPerm (t : Fin 4 → Nat) (s : Fin 13 → Nat) : Equiv.Perm (Fin 52) :=
  Equiv.ofBijective (stemPosOf t s) (Finite.injective_iff_bijective.mp (stemPosOf_injective t s))

theorem seatPerm_apply (t : Fin 4 → Nat) (s : Fin 13 → Nat) (k : Fin 52) :
    seatPerm t s k = stemPosOf t s k := rfl

/-- (PROVED) The stem's position map is injective, for every packet. -/
theorem stemPos_injective (m : Fin 52 → Nat) : Function.Injective (stemPos m) :=
  stemPosOf_injective _ _

/-- `stemPos m` as a permutation of the positions: the seat permutation of `m`'s amounts. -/
noncomputable def stemPerm (m : Fin 52 → Nat) : Equiv.Perm (Fin 52) :=
  seatPerm (rowAmts m) (colAmts m)

theorem stemPerm_apply (m : Fin 52 → Nat) (k : Fin 52) : stemPerm m k = stemPos m k := rfl

/-! ## A relabelling difference through the stem is a conjugated ratio of position maps -/

/-- (PROVED) If the stem sends the pair `(x, β·x)`, `x = permDeck π`, to a pair with
    difference `γ`, then `γ⁻¹ * β` is the ratio of the two position maps, conjugated by `π`:
    `γ⁻¹ * β = π * (stemPerm x * (stemPerm (β·x))⁻¹) * π⁻¹`. -/
theorem conj_of_stem_rel {β γ π : Equiv.Perm (Fin 52)}
    (h : unkeyedNoMix (rel β (permDeck π)) = rel γ (unkeyedNoMix (permDeck π))) :
    γ⁻¹ * β =
      π * (stemPerm (permDeck π) * (stemPerm (rel β (permDeck π)))⁻¹) * π⁻¹ := by
  have hk : ∀ k, β (π (stemPos (rel β (permDeck π)) k)) = γ (π (stemPos (permDeck π) k)) := by
    intro k
    have e := congrFun h k
    rw [unkeyedNoMix_eq_comp (rel β (permDeck π)), unkeyedNoMix_eq_comp (permDeck π)] at e
    apply Fin.ext
    simp only [rel, permDeck, app_fin] at e ⊢
    exact e
  refine Equiv.ext fun a => ?_
  obtain ⟨k, rfl⟩ : ∃ k, π (stemPerm (rel β (permDeck π)) k) = a :=
    ⟨(stemPerm (rel β (permDeck π)))⁻¹ (π⁻¹ a), by simp⟩
  simp only [Equiv.Perm.mul_apply, Equiv.Perm.inv_apply_self]
  rw [stemPerm_apply, stemPerm_apply, hk k, Equiv.Perm.inv_apply_self]

/-! ## The support gap -/

/-- `z` for rows: the number of agreeing rows, i.e. rows whose row amounts agree mod 13
    between the packets `m` and `m'`. -/
def zRows (m m' : Fin 52 → Nat) : ℕ :=
  (univ.filter fun r : Fin 4 => rowAmts m r % 13 = rowAmts m' r % 13).card

/-- `z` for columns: the number of agreeing columns, i.e. columns whose column amounts
    agree mod 4 between the packets `m` and `m'`. -/
def zCols (m m' : Fin 52 → Nat) : ℕ :=
  (univ.filter fun c : Fin 13 => colAmts m c % 4 = colAmts m' c % 4).card

theorem srcRow_eq_add (s : Fin 13 → Nat) (r : Fin 4) (c : Fin 13) :
    srcRow s r c = r + ⟨(4 - s c % 4) % 4, Nat.mod_lt _ (by decide)⟩ := by
  apply Fin.ext
  simp only [srcRow, Fin.val_add]
  omega

/-- (PROVED) The number of seats where two seat maps agree is (rows whose amounts agree
    mod 13) × (columns whose amounts agree mod 4). -/
theorem card_seatMap_eq (t t' : Fin 4 → Nat) (s s' : Fin 13 → Nat) :
    (univ.filter fun p : Fin 4 × Fin 13 => seatMap t s p = seatMap t' s' p).card =
      (univ.filter fun r : Fin 4 => t r % 13 = t' r % 13).card *
        (univ.filter fun c : Fin 13 => s c % 4 = s' c % 4).card := by
  have e : ∀ p : Fin 4 × Fin 13, seatMap t s p = seatMap t' s' p ↔
      s p.2 % 4 = s' p.2 % 4 ∧ t (srcRow s p.1 p.2) % 13 = t' (srcRow s p.1 p.2) % 13 :=
    fun p => seatMap_eq_iff t t' s s' p.1 p.2
  rw [filter_congr fun p _ => e p, card_filter, Fintype.sum_prod_type, sum_comm]
  have hc : ∀ c : Fin 13, (∑ r : Fin 4, if s c % 4 = s' c % 4 ∧
      t (srcRow s r c) % 13 = t' (srcRow s r c) % 13 then 1 else 0) =
      (if s c % 4 = s' c % 4 then 1 else 0) *
        (univ.filter fun r : Fin 4 => t r % 13 = t' r % 13).card := by
    intro c
    rw [card_filter]
    have hr : (∑ r : Fin 4, if t (srcRow s r c) % 13 = t' (srcRow s r c) % 13 then 1 else 0) =
        ∑ r : Fin 4, if t r % 13 = t' r % 13 then 1 else 0 := by
      simp only [srcRow_eq_add]
      exact Equiv.sum_comp (Equiv.addRight _) (fun r => if t r % 13 = t' r % 13 then 1 else 0)
    split_ifs with hs
    · simp only [hs, true_and, one_mul]
      exact hr
    · simp [hs]
  rw [sum_congr rfl fun c _ => hc c, ← sum_mul, ← card_filter, Nat.mul_comm]

/-- (PROVED) Under the hypothesis of `conj_of_stem_rel`, `γ⁻¹ * β` fixes exactly
    `zRows x (β·x) * zCols x (β·x)` cards (`x = permDeck π`). -/
theorem card_fixed_eq {β γ π : Equiv.Perm (Fin 52)}
    (h : unkeyedNoMix (rel β (permDeck π)) = rel γ (unkeyedNoMix (permDeck π))) :
    (univ.filter fun a : Fin 52 => (γ⁻¹ * β) a = a).card =
      zRows (permDeck π) (rel β (permDeck π)) * zCols (permDeck π) (rel β (permDeck π)) := by
  have hconj := conj_of_stem_rel h
  -- positions where the two position maps agree ↔ cards fixed by `γ⁻¹ * β`
  have e1 : (univ.filter fun k : Fin 52 =>
        stemPos (permDeck π) k = stemPos (rel β (permDeck π)) k).card =
      (univ.filter fun a : Fin 52 => (γ⁻¹ * β) a = a).card := by
    rw [← Fintype.card_subtype, ← Fintype.card_subtype]
    refine Fintype.card_congr
      (Equiv.subtypeEquiv ((stemPerm (rel β (permDeck π))).trans π) fun k => ?_)
    rw [Equiv.trans_apply, hconj]
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.inv_apply_self]
    rw [Equiv.apply_eq_iff_eq]
    rfl
  -- positions ↔ seats of the SumRanks output (`inSeat` is a bijection)
  have e2 : (univ.filter fun k : Fin 52 =>
        stemPos (permDeck π) k = stemPos (rel β (permDeck π)) k).card =
      (univ.filter fun p : Fin 4 × Fin 13 =>
        seatMap (rowAmts (permDeck π)) (colAmts (permDeck π)) p =
          seatMap (rowAmts (rel β (permDeck π))) (colAmts (rel β (permDeck π))) p).card := by
    rw [← Fintype.card_subtype, ← Fintype.card_subtype]
    exact Fintype.card_congr (Equiv.subtypeEquiv (Equiv.ofBijective inSeat inSeat_bijective)
      fun k => stemPosOf_eq_iff _ _ _ _ k)
  rw [← e1, e2, card_seatMap_eq]
  rfl

theorem zRows_le (m m' : Fin 52 → Nat) : zRows m m' ≤ 4 :=
  (card_filter_le _ _).trans (by simp)

theorem zCols_le (m m' : Fin 52 → Nat) : zCols m m' ≤ 13 :=
  (card_filter_le _ _).trans (by simp)

/-- (PROVED) Under the hypothesis of `conj_of_stem_rel`, `γ⁻¹ * β` moves exactly
    `52 - zRows x (β·x) * zCols x (β·x)` cards (`x = permDeck π`). -/
theorem card_moved_eq {β γ π : Equiv.Perm (Fin 52)}
    (h : unkeyedNoMix (rel β (permDeck π)) = rel γ (unkeyedNoMix (permDeck π))) :
    (γ⁻¹ * β).support.card =
      52 - zRows (permDeck π) (rel β (permDeck π)) * zCols (permDeck π) (rel β (permDeck π)) := by
  have e := filter_card_add_filter_neg_card_eq_card (s := (univ : Finset (Fin 52)))
    (fun a : Fin 52 => (γ⁻¹ * β) a = a)
  rw [card_fixed_eq h, card_univ, Fintype.card_fin] at e
  show (univ.filter fun a : Fin 52 => (γ⁻¹ * β) a ≠ a).card = _
  simp only [ne_eq]
  omega

/-- (PROVED) The support gap: under the hypothesis of `conj_of_stem_rel`, `γ⁻¹ * β` moves no
    card, exactly 4 cards with `(zRows, zCols) = (4, 12)`, or at least 8 cards. (`card_moved_eq`
    excludes more values, e.g. 9–11; not stated here.) -/
theorem card_moved_cases {β γ π : Equiv.Perm (Fin 52)}
    (h : unkeyedNoMix (rel β (permDeck π)) = rel γ (unkeyedNoMix (permDeck π))) :
    (γ⁻¹ * β).support.card = 0 ∨
      ((γ⁻¹ * β).support.card = 4 ∧ zRows (permDeck π) (rel β (permDeck π)) = 4 ∧
        zCols (permDeck π) (rel β (permDeck π)) = 12) ∨
      8 ≤ (γ⁻¹ * β).support.card := by
  have e : (γ⁻¹ * β).support.card =
      52 - zRows (permDeck π) (rel β (permDeck π)) * zCols (permDeck π) (rel β (permDeck π)) :=
    card_moved_eq h
  rw [e]
  have h1 := zRows_le (permDeck π) (rel β (permDeck π))
  have h2 := zCols_le (permDeck π) (rel β (permDeck π))
  generalize zRows (permDeck π) (rel β (permDeck π)) = a at h1 ⊢
  generalize zCols (permDeck π) (rel β (permDeck π)) = b at h2 ⊢
  interval_cases a <;> omega

/-- (PROVED) Corollary of `card_moved_cases`: `γ⁻¹ * β` moves no card or at least 4 cards.
    (Never exactly 1 holds for every permutation; the content is never exactly 2 or 3.) -/
theorem card_moved_zero_or_ge_four {β γ π : Equiv.Perm (Fin 52)}
    (h : unkeyedNoMix (rel β (permDeck π)) = rel γ (unkeyedNoMix (permDeck π))) :
    (γ⁻¹ * β).support.card = 0 ∨ 4 ≤ (γ⁻¹ * β).support.card := by
  rcases card_moved_cases h with e | ⟨e, -⟩ | e
  · exact Or.inl e
  · exact Or.inr e.ge
  · exact Or.inr (le_trans (by decide) e)

end DoubleDeal.Security.StemPosition
