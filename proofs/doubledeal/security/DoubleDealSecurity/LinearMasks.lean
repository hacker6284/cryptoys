/-
  First-order (single-card) masks and the sign mask for the M8a link (roadmap milestone
  M8b; security README, "Roadmap"). Note: `../analysis/v12-linear/NOTES.md`.

  NO NUMERIC BOUND IS PROVED HERE. Read this before citing anything below.

  Model. As in `Linear` (M8a): INDEPENDENT UNIFORM full-permutation keys (all `n + 2` keys
  of `encryptL n`, the whitening and the final key included), and every sum of squared
  correlations is key-summed and unnormalised. Nothing is proved for the real PassKey
  schedule. L5 involves no layer. L10 is proved for arbitrary layers that send decks to
  decks. L6, L7 and the row/column sums are stated for DoubleDeal's `encryptL`. L6 (through
  the column sums) uses injective layers; L5, L7, L10 and the row sums use only decks to
  decks. (The column sums `FullCipher.sum_fullDiffCount_left` use
  `FullCipher.outDiff_injective`, which uses `FullCipher.fullDiffCount_to_one`;
  `fullSumSqCorr_cardMask_seat` uses them through L6.)
  L9 is about the relabellings `v10Sym` and the mask only.
  Out of scope (not in this module): positivity of the L6 bracket (the proposal's L8), M8c,
  and the H1–H4 statements.

  Definitions.
  * `cardMask s c x = 52 · [x s = c] - 1`: the single-card mask "card `c` sits at seat `s`",
    centred (it sums to `0` over the `52!` decks).
  * `SameSeat c z z'`: card `c` sits at the same seat in `z` and `z'`.
  * `alignCount c c' n y = ∑_{α c = c} ∑_{β c' = c'} fullDiffCount α β n y`.
  * `signMask x`: the sign of the deck `x` as a permutation (`0` off decks).

  Proved:
  * L5 `autoCorr_cardMask`: `autoCorr (cardMask s c) α = 52! · (52 · [α c = c] - 1)`, for
    every seat `s` and relabelling `α`.
  * L6 `fullSumSqCorr_cardMask`: for any deck `y`,
    `fullSumSqCorr n (cardMask s c) (cardMask t c') =
      52! · (52^2 · alignCount c c' n y - (52!)^(n+3))`.
    `fullSumSqCorr_cardMask_seat`: the seats do not matter,
    `fullSumSqCorr n (cardMask s c) (cardMask t c') =
      fullSumSqCorr n (cardMask s' c) (cardMask t' c')`.
  * L7 `alignCount_eq` (the truncated-differential reading): for any deck `y`,
    `alignCount c c' n y` is the number of pairs (relabelling `α`, key tuple `L`) such that
    card `c` sits at the same seat in `y` and `α·y`, and card `c'` sits at the same seat in
    `encryptL n y L` and `encryptL n (α·y) L`.
  * L9 `autoCorr_cardMask_v10Sym` (a helper, not a headline): for `(a, x) ≠ (0, 0)`,
    `autoCorr (cardMask s c) (v10Sym a x) = -52!`. An immediate corollary of L5 and
    `GridCycleSurvival.v10Sym_fixfree`; its only content is the negative non-transfer: in L6
    the nontrivial `v10Sym` enter as input/output differences only through the constant,
    like every relabelling that moves `c`, never through `alignCount` (they fix no card, so
    they are in neither filter). They can still occur as intermediate differences inside
    the rounds, i.e. inside `fullDiffCount`.
  * L10 `corr_keyedLayer_sign`: ONE keyed layer `x ↦ U(x ∘ k₁) ∘ k₂`, `U` any deck map
    sending decks to decks: `corr (keyedLayer U k₁ k₂) signMask signMask =
      sign k₁ · sign k₂ · corr U signMask signMask`. The keys only flip the sign.
  * Supporting (here): `sameSeat_rel_iff`, `signMask_permDeck`, `signMask_compose`.
    Used from elsewhere: `PermCount.card_apply_eq_indep_card` (the number of decks putting
    card `c` at seat `s` does not depend on `c`), `PermCount.card_apply_eq` (`51!` decks put
    `c` at `s`), `FullCipher.sum_fullDiffCount` and `FullCipher.sum_fullDiffCount_left` (rows
    and columns of `fullDiffCount` sum to `(52!)^(n+2)`), `FullCipher.outDiff_injective`,
    `TrailBound.permDeck_apply_eq`, `TrailBound.rel_permDeck_apply_eq`.

  NOT proved, and limits; read before citing:
  * Any numeric bound. L6 moves the single-card question to `alignCount`, for which no bound
    is proved (not even positivity of the bracket, the proposal's L8, which is not here).
  * L10 is for one keyed layer only: nothing about several rounds, `encryptL` or
    `encryptN`, and nothing about the value of `corr U signMask signMask` for any DoubleDeal
    layer. The stem's exact sign correlation in the note is SCRIPT-COMPUTED and UNPROVED;
    the other first-order and sign values in the note are MEASURED (sampled), not proved.
  * Anything under the real PassKey schedule, anything per key, and any higher-order mask
    (two or more cards).
  Not a bit-security claim.
-/
import DoubleDealSecurity.Linear

namespace DoubleDeal.Security.LinearMasks

open DoubleDeal Relabel Finset
open DoubleDeal.Security (Key)
open DoubleDeal.Security.TrailBound (compose_permDeck permDeck_apply_eq rel_permDeck_apply_eq)
open DoubleDeal.Security.PermCount (card_apply_eq)
open DoubleDeal.Security.FullCipher (encryptL fullDiffCount isDeck_encryptL outDiff
  encryptL_rel_outDiff fullDiffCount_eq_card_outDiff sum_fullDiffCount sum_fullDiffCount_left)
open DoubleDeal.Security.Linear (corr autoCorr keyedLayer fullSumSqCorr fullSumSqCorr_eq)
open DoubleDeal.Security.GridCycleSurvival (v10Sym_fixfree)

/-! ## Definitions -/

/-- The first-order (single-card) mask: `52 · [card c sits at seat s] - 1` (sum `0` over the
    decks). -/
def cardMask (s c : Fin 52) (x : Fin 52 → Nat) : ℤ :=
  52 * (if x s = c.val then 1 else 0) - 1

/-- Card `c` sits at the same seat in `z` and `z'`. -/
def SameSeat (c : Fin 52) (z z' : Fin 52 → Nat) : Prop := ∀ i : Fin 52, z i = c.val ↔ z' i = c.val

instance (c : Fin 52) (z z' : Fin 52 → Nat) : Decidable (SameSeat c z z') :=
  inferInstanceAs (Decidable (∀ i : Fin 52, z i = c.val ↔ z' i = c.val))

/-- The alignment count: key tuples and input differences `α` fixing card `c`, with output
    difference `β` fixing card `c'`, summed: `∑_{α c = c} ∑_{β c' = c'} fullDiffCount α β n y`. -/
def alignCount (c c' : Fin 52) (n : ℕ) (y : Fin 52 → Nat) : ℕ :=
  ∑ α ∈ univ.filter (fun α : Relabel => α c = c),
    ∑ β ∈ univ.filter (fun β : Relabel => β c' = c'), fullDiffCount α β n y

open Classical in
/-- The sign of a deck (`0` off decks). -/
noncomputable def signMask (x : Fin 52 → Nat) : ℤ :=
  if h : IsDeck x then ((Equiv.Perm.sign (deckPerm x h) : ℤˣ) : ℤ) else 0

/-! ## L5: the autocorrelation of a single-card mask -/

/-- `(52 [P] - 1)(52 [Q] - 1)` expanded, with `[P ∧ Q]` written as `[R]`. -/
theorem mask_mul (P Q R : Prop) [Decidable P] [Decidable Q] [Decidable R] (hR : R ↔ P ∧ Q) :
    (52 * (if P then (1 : ℤ) else 0) - 1) * (52 * (if Q then 1 else 0) - 1) =
      52 * 52 * (if R then 1 else 0) - 52 * (if P then 1 else 0) - 52 * (if Q then 1 else 0)
        + 1 := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ, hR]

/-- (PROVED) L5. The autocorrelation of the single-card mask depends only on whether `α`
    fixes the card: `autoCorr (cardMask s c) α = 52! · (52 · [α c = c] - 1)`, for every
    seat `s`. -/
theorem autoCorr_cardMask (s c : Fin 52) (α : Relabel) :
    autoCorr (cardMask s c) α =
      (Nat.factorial 52 : ℤ) * (52 * (if α c = c then 1 else 0) - 1) := by
  unfold autoCorr cardMask
  simp only [permDeck_apply_eq, rel_permDeck_apply_eq]
  rw [sum_congr rfl fun π _ => mask_mul (π s = c) (α (π s) = c) (π s = c ∧ α c = c)
    (and_congr_right fun h => by rw [h])]
  rw [sum_add_distrib, sum_sub_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, ← mul_sum,
    sum_boole, sum_boole, sum_boole, sum_const, card_univ, Fintype.card_perm,
    Fintype.card_fin]
  have hQ : (univ.filter fun π : Equiv.Perm (Fin 52) => α (π s) = c).card =
      Nat.factorial 51 := by
    rw [filter_congr fun π _ => Equiv.apply_eq_iff_eq_symm_apply α, card_apply_eq s (α.symm c)]
  have hR : (univ.filter fun π : Equiv.Perm (Fin 52) => π s = c ∧ α c = c).card =
      if α c = c then Nat.factorial 51 else 0 := by
    by_cases hα : α c = c
    · simp only [hα, and_true, if_true, card_apply_eq]
    · simp [hα]
  have h52 : Nat.factorial 52 = 52 * Nat.factorial 51 := Nat.factorial_succ 51
  rw [hQ, hR, card_apply_eq, h52]
  split_ifs <;> push_cast <;> ring

/-! ## L7: the truncated-differential reading of `alignCount` -/

/-- (PROVED) For a deck `z`, card `c` sits at the same seat in `z` and `β·z` iff `β` fixes
    `c`. -/
theorem sameSeat_rel_iff (c : Fin 52) (β : Relabel) {z : Fin 52 → Nat} (hz : IsDeck z) :
    SameSeat c z (rel β z) ↔ β c = c := by
  have hz' : ∀ i, z i = (deckPerm z hz i).val := fun i => (deckPerm_val z hz i).symm
  have hrel : ∀ i, rel β z i = (β (deckPerm z hz i)).val := fun i => by
    show β.app (z i) = _
    rw [hz' i, app_fin]
  constructor
  · intro h
    have hi := (h ((deckPerm z hz).symm c)).1 (by rw [hz', Equiv.apply_symm_apply])
    rw [hrel, Equiv.apply_symm_apply] at hi
    exact Fin.ext hi
  · intro hβ i
    rw [hz' i, hrel i, Fin.val_inj, Fin.val_inj]
    constructor
    · intro h
      rw [h, hβ]
    · intro h
      exact β.injective (h.trans hβ.symm)

/-- (PROVED) L7. `alignCount c c' n y` counts the pairs (input difference `α`, key tuple `L`)
    for which the plaintext pair `(y, α·y)` has card `c` at the same seat and the
    ciphertext pair has card `c'` at the same seat (a truncated differential on one card's
    seat). -/
theorem alignCount_eq (c c' : Fin 52) (n : ℕ) {y : Fin 52 → Nat} (hy : IsDeck y) :
    alignCount c c' n y = (univ.filter fun p : Relabel × (Fin (n + 2) → Key) =>
      SameSeat c y (rel p.1 y) ∧
        SameSeat c' (encryptL n y p.2) (encryptL n (rel p.1 y) p.2)).card := by
  rw [card_filter, Fintype.sum_prod_type]
  simp only [sameSeat_rel_iff c _ hy]
  unfold alignCount
  rw [sum_filter]
  refine sum_congr rfl fun α _ => ?_
  by_cases hα : α c = c
  · simp only [hα, true_and, if_true]
    rw [← card_filter]
    simp only [encryptL_rel_outDiff α n hy, sameSeat_rel_iff c' _ (isDeck_encryptL n _ hy)]
    rw [card_eq_sum_card_fiberwise (f := fun L => outDiff α n y L)
      (t := univ.filter fun β : Relabel => β c' = c') (fun L hL => by simpa using hL)]
    refine sum_congr rfl fun β hβ => ?_
    rw [fullDiffCount_eq_card_outDiff α β n hy, filter_filter]
    congr 1
    apply filter_congr
    intro L _
    exact ⟨fun h => ⟨h ▸ (mem_filter.1 hβ).2, h⟩, fun h => h.2⟩
  · simp [hα]

/-! ## L6: squared correlations of single-card masks -/

/-- `∑∑ (52 a - 1) D (52 b - 1)` expanded into the four sums. -/
theorem sum_mask_expand (a b : Relabel → ℤ) (D : Relabel → Relabel → ℤ) :
    ∑ α, ∑ β, (52 * a α - 1) * D α β * (52 * b β - 1) =
      52 ^ 2 * (∑ α, ∑ β, a α * D α β * b β) - 52 * (∑ α, a α * ∑ β, D α β) -
        52 * (∑ β, b β * ∑ α, D α β) + ∑ α, ∑ β, D α β := by
  have e : ∀ α β, (52 * a α - 1) * D α β * (52 * b β - 1) =
      52 ^ 2 * (a α * D α β * b β) - 52 * (a α * D α β) - 52 * (b β * D α β) + D α β :=
    fun α β => by ring
  simp only [e, sum_add_distrib, sum_sub_distrib, ← mul_sum]
  rw [sum_comm (f := fun α β => b β * D α β)]
  simp only [← mul_sum]

/-- (PROVED) L6. The squared correlation of two single-card masks through `encryptL n`,
    summed over all `(52!)^(n+2)` independent key tuples, for any deck `y`:
    `fullSumSqCorr n (cardMask s c) (cardMask t c') = 52! · (52^2 · alignCount c c' n y -
    (52!)^(n+3))`. The seats `s`, `t` do not appear on the right. An identity only; no
    numeric bound on `alignCount` is proved. -/
theorem fullSumSqCorr_cardMask (s c t c' : Fin 52) (n : ℕ) {y : Fin 52 → Nat} (hy : IsDeck y) :
    fullSumSqCorr n (cardMask s c) (cardMask t c') =
      (Nat.factorial 52 : ℤ) *
        (52 ^ 2 * (alignCount c c' n y : ℤ) - (Nat.factorial 52 : ℤ) ^ (n + 3)) := by
  have h := fullSumSqCorr_eq n (cardMask s c) (cardMask t c') hy
  simp only [autoCorr_cardMask] at h
  have hF : (Nat.factorial 52 : ℤ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero 52)
  have hfix : ∀ d : Fin 52, (∑ α : Relabel, (if α d = d then (1 : ℤ) else 0)) =
      Nat.factorial 51 := fun d => by rw [sum_boole, card_apply_eq]
  have hR : ∀ α, (∑ β, (fullDiffCount α β n y : ℤ)) = (Nat.factorial 52 : ℤ) ^ (n + 2) :=
    fun α => by rw [← Nat.cast_sum, sum_fullDiffCount α n hy, Nat.cast_pow]
  have hC : ∀ β, (∑ α, (fullDiffCount α β n y : ℤ)) = (Nat.factorial 52 : ℤ) ^ (n + 2) :=
    fun β => by rw [← Nat.cast_sum, sum_fullDiffCount_left β n hy, Nat.cast_pow]
  have hA : (alignCount c c' n y : ℤ) = ∑ α, ∑ β, (if α c = c then (1 : ℤ) else 0) *
      (fullDiffCount α β n y : ℤ) * (if β c' = c' then 1 else 0) := by
    unfold alignCount
    push_cast
    rw [sum_filter]
    refine sum_congr rfl fun α _ => ?_
    rw [sum_filter]
    by_cases hα : α c = c
    · simp only [hα, if_true, one_mul]
      exact sum_congr rfl fun β _ => by split_ifs <;> simp
    · simp [hα]
  have e : ∀ α β, (Nat.factorial 52 : ℤ) * (52 * (if α c = c then 1 else 0) - 1) *
      (fullDiffCount α β n y : ℤ) *
        ((Nat.factorial 52 : ℤ) * (52 * (if β c' = c' then 1 else 0) - 1)) =
      (Nat.factorial 52 : ℤ) ^ 2 * ((52 * (if α c = c then 1 else 0) - 1) *
        (fullDiffCount α β n y : ℤ) * (52 * (if β c' = c' then 1 else 0) - 1)) :=
    fun α β => by ring
  simp only [e, ← mul_sum] at h
  rw [sum_mask_expand, ← hA] at h
  simp only [hR, hC, ← sum_mul, mul_comm _ ((Nat.factorial 52 : ℤ) ^ (n + 2)), ← mul_sum,
    hfix, sum_const, card_univ, Fintype.card_perm, Fintype.card_fin, smul_eq_mul,
    nsmul_eq_mul] at h
  refine mul_left_cancel₀ hF (h.trans ?_)
  have h52 : (Nat.factorial 52 : ℤ) = 52 * (Nat.factorial 51 : ℤ) := by
    rw [Nat.factorial_succ 51]; push_cast; ring
  rw [h52]
  ring

/-- (PROVED) The seats do not matter: for any seats `s, s', t, t'`,
    `fullSumSqCorr n (cardMask s c) (cardMask t c') =
      fullSumSqCorr n (cardMask s' c) (cardMask t' c')`. -/
theorem fullSumSqCorr_cardMask_seat (s s' c t t' c' : Fin 52) (n : ℕ) :
    fullSumSqCorr n (cardMask s c) (cardMask t c') =
      fullSumSqCorr n (cardMask s' c) (cardMask t' c') := by
  rw [fullSumSqCorr_cardMask s c t c' n isDeck_idDeck,
    fullSumSqCorr_cardMask s' c t' c' n isDeck_idDeck]

/-! ## L9: the `v10Sym` symmetries do not show up in single-card masks -/

/-- (PROVED) L9 (a helper). An immediate corollary of L5 (`autoCorr_cardMask`) and
    `v10Sym_fixfree`: for `(a, x) ≠ (0, 0)`, `autoCorr (cardMask s c) (v10Sym a x) = -52!`.
    Its only content is the negative non-transfer: the SumRanks symmetries `v10Sym` (which
    pass the proof's finalRound step on every deck, `FullCipher.dpFCount_v10Sym`) enter L6
    as input/output differences only through the same constant as every relabelling that
    moves `c`, never through `alignCount`; they can still occur as intermediate differences
    inside the rounds. Nothing about the cipher's layers. -/
theorem autoCorr_cardMask_v10Sym (a : Fin 13) (x : Fin 4) (hne : ¬ (a = 0 ∧ x = 0))
    (s c : Fin 52) : autoCorr (cardMask s c) (v10Sym a x) = -(Nat.factorial 52 : ℤ) := by
  rw [autoCorr_cardMask, if_neg (v10Sym_fixfree a x hne c)]
  ring

/-! ## L10: the sign mask through one keyed layer -/

theorem signMask_permDeck (ρ : Equiv.Perm (Fin 52)) :
    signMask (permDeck ρ) = ((Equiv.Perm.sign ρ : ℤˣ) : ℤ) := by
  unfold signMask
  rw [dif_pos (isDeck_permDeck ρ)]
  congr 3
  exact Equiv.ext fun i => Fin.ext (deckPerm_val _ _ i)

theorem signMask_compose {z : Fin 52 → Nat} (hz : IsDeck z) (k : Key) :
    signMask (composeVec 52 Nat z k) = signMask z * ((Equiv.Perm.sign k : ℤˣ) : ℤ) := by
  have hzρ : z = permDeck (deckPerm z hz) := funext fun i => (deckPerm_val z hz i).symm
  rw [hzρ, compose_permDeck, signMask_permDeck, signMask_permDeck, Equiv.Perm.sign_mul,
    Units.val_mul]

/-- (PROVED) L10. The sign mask through ONE keyed layer `x ↦ U(x ∘ k₁) ∘ k₂` (`U` any deck
    map sending decks to decks): the keys only flip the sign of the correlation,
    `corr (keyedLayer U k₁ k₂) signMask signMask = sign k₁ · sign k₂ · corr U signMask signMask`.
    One layer only; no statement about several rounds or about the value of
    `corr U signMask signMask`. -/
theorem corr_keyedLayer_sign (U : (Fin 52 → Nat) → Fin 52 → Nat)
    (hU : ∀ {x : Fin 52 → Nat}, IsDeck x → IsDeck (U x)) (k₁ k₂ : Key) :
    corr (keyedLayer U k₁ k₂) signMask signMask =
      ((Equiv.Perm.sign k₁ : ℤˣ) : ℤ) * ((Equiv.Perm.sign k₂ : ℤˣ) : ℤ) *
        corr U signMask signMask := by
  unfold corr keyedLayer
  have hc : ∀ π : Equiv.Perm (Fin 52), signMask (composeVec 52 Nat (U (permDeck π)) k₂) =
      signMask (U (permDeck π)) * ((Equiv.Perm.sign k₂ : ℤˣ) : ℤ) :=
    fun π => signMask_compose (hU (isDeck_permDeck π)) k₂
  simp only [compose_permDeck, hc, signMask_permDeck]
  -- reindex the left sum by `π ↦ π * k₁⁻¹`; `sign k₁⁻¹ = sign k₁`
  conv_lhs => rw [← Equiv.sum_comp (Equiv.mulRight k₁⁻¹)]
  simp only [Equiv.coe_mulRight, inv_mul_cancel_right, Equiv.Perm.sign_mul,
    Equiv.Perm.sign_inv, Units.val_mul, mul_sum]
  exact sum_congr rfl fun σ _ => by ring

end DoubleDeal.Security.LinearMasks
