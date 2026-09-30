/-
  T1: rounds and encrypt versus relabellings. Layer-wise lifting, the stem
  maps decks onto decks, v8 consequences, the covariant round conjecture
  `roundBody_covariant_iff_id` (the only DRAFT-SORRY), and a side lemma with
  degenerate constant keys. Permutation round keys: `PermKeys.lean`.
-/
import DoubleDealSecurity.GridCycle
import DoubleDealSecurity.SumRanksV10
import DoubleDealSecurity.StemPosition

namespace DoubleDeal.Security

open DoubleDeal Relabel

/-! ## 4. Rounds and encrypt -/

theorem cards_rel (σ : Relabel) {m : Fin 52 → Nat} (hm : Cards m) : Cards (rel σ m) :=
  fun i => σ.app_lt (hm i)

theorem cardsG_lay {m : Fin 52 → Nat} (hm : Cards m) : CardsG (layColumnMajor m) :=
  fun _ _ => hm _

theorem cards_unkeyedNoMix {m : Fin 52 → Nat} (hm : Cards m) : Cards (unkeyedNoMix m) := by
  intro i
  exact sumRanksV10_bound (· < 52) _ (cardsG_lay hm) _ _

theorem placeN_cards (hand : Fin 52 → Nat) (hb : Cards hand) :
    ∀ n, ∀ r c, (placeN hand n).1 r c < 52
  | 0, r, c => by simp [placeN]
  | n + 1, r, c => by
      have ih := placeN_cards hand hb n r c
      by_cases hlt : n < 52
      · simp only [placeN, hlt, ↓reduceDIte, setGrid]
        by_cases hcell : r = (chooseSeat! (placeN hand n).2).1.1 ∧
            c = (chooseSeat! (placeN hand n).2).1.2
        · simp [hcell, hb _]
        · simpa [hcell] using ih
      · simp only [placeN, hlt, ↓reduceDIte]; exact ih

theorem cards_mixColumns {m : Fin 52 → Nat} (hm : Cards m) : Cards (mixColumns m) :=
  fun _ => placeN_cards m hm 52 _ _

theorem cards_compose {m : Fin 52 → Nat} (hm : Cards m) (pos : Fin 52 → Fin 52) :
    Cards (composeVec 52 Nat m pos) := fun _ => hm _

/-- (PROVED) The unkeyed stem commutes with σ whenever SumRanks does. -/
theorem unkeyedNoMix_commutes (σ : Relabel) (hs : CommutesG σ sumRanksV10) :
    Commutes σ unkeyedNoMix := by
  intro m hm
  simp only [unkeyedNoMix]
  rw [layColumnMajor_rel, hs _ (cardsG_lay hm)]
  rfl

/-- (PROVED) Layer-wise commutation lifts to the full round, for every key. -/
theorem fullRound_commutes (σ : Relabel) (hs : CommutesG σ sumRanksV10)
    (hmix : Commutes σ mixColumns) (pos : Fin 52 → Fin 52) :
    Commutes σ (fun m => fullRound m pos) := by
  intro m hm
  simp only [fullRound, unkeyedWithMix]
  rw [unkeyedNoMix_commutes σ hs m hm, hmix _ (cards_unkeyedNoMix hm)]
  rfl

theorem fullRoundNoMix_commutes (σ : Relabel) (hs : CommutesG σ sumRanksV10)
    (pos : Fin 52 → Fin 52) : Commutes σ (fun m => fullRoundNoMix m pos) := by
  intro m hm
  simp only [fullRoundNoMix]
  rw [unkeyedNoMix_commutes σ hs m hm]
  rfl

theorem cards_fullRound {m : Fin 52 → Nat} (hm : Cards m) (pos : Fin 52 → Fin 52) :
    Cards (fullRound m pos) :=
  cards_compose (cards_mixColumns (cards_unkeyedNoMix hm)) pos

theorem cards_applyFullRounds (pos : Nat → Fin 52 → Fin 52) :
    ∀ n {m : Fin 52 → Nat}, Cards m → Cards (applyFullRounds n m pos)
  | 0, _, hm => hm
  | n + 1, _, hm => cards_fullRound (cards_applyFullRounds pos n hm) _

/-- (PROVED) Layer-wise commutation lifts to encrypt with arbitrary round keys:
    `E_K(σM) = σ E_K(M)` (key not relabelled). -/
theorem encryptN_commutes (σ : Relabel) (hs : CommutesG σ sumRanksV10)
    (hmix : Commutes σ mixColumns) (nMix : Nat) (pos0 : Fin 52 → Fin 52)
    (posMix : Nat → Fin 52 → Fin 52) (posFinal : Fin 52 → Fin 52) :
    Commutes σ (fun m => encryptN nMix m pos0 posMix posFinal) := by
  intro m hm
  have hrounds : ∀ n {x : Fin 52 → Nat}, Cards x →
      applyFullRounds n (rel σ x) posMix = rel σ (applyFullRounds n x posMix) := by
    intro n
    induction n with
    | zero => intro _ _; rfl
    | succ n ih =>
      intro x hx
      simp only [applyFullRounds]
      rw [ih hx]
      exact fullRound_commutes σ hs hmix _ _ (cards_applyFullRounds posMix n hx)
  simp only [encryptN]
  rw [compose_rel, hrounds nMix (cards_compose hm pos0)]
  exact fullRoundNoMix_commutes σ hs posFinal _
    (cards_applyFullRounds posMix nMix (cards_compose hm pos0))

/-- (PROVED) The stem only moves cells: every output cell is an input cell. -/
theorem unkeyedNoMix_cells (m : Fin 52 → Nat) (k : Fin 52) : ∃ i, unkeyedNoMix m k = m i :=
  -- the weak form of `StemPosition.unkeyedNoMix_eq_comp`, which names the cell
  ⟨StemPosition.stemPos m k, congrFun (StemPosition.unkeyedNoMix_eq_comp m) k⟩

-- `unkeyedNoMix_invUnkeyedNoMix` (same statement) now lives in the core
-- package, `DoubleDeal.Round` (next to `encrypt6_decrypt6`).

/-- (PROVED) `invUnkeyedNoMix` maps decks to decks (`unkeyedNoMix` only moves cells). -/
theorem isDeck_invUnkeyedNoMix {v : Fin 52 → Nat} (hv : IsDeck v) : IsDeck (invUnkeyedNoMix v) :=
  isDeck_of_cells hv fun k => by
    obtain ⟨i, hi⟩ := unkeyedNoMix_cells (invUnkeyedNoMix v) k
    rw [unkeyedNoMix_invUnkeyedNoMix] at hi
    exact ⟨i, hi⟩

/-- (PROVED) Compose with a permutation key is injective. -/
theorem composeVec_inj (k : Equiv.Perm (Fin 52)) {x x' : Fin 52 → Nat} :
    composeVec 52 Nat x k = composeVec 52 Nat x' k ↔ x = x' := by
  refine ⟨fun h => funext fun i => ?_, fun h => h ▸ rfl⟩
  have := congrFun h (k.symm i)
  simpa [composeVec] using this

/-- (PROVED) The stem maps well-formed decks onto well-formed decks. The
    preimage is `invUnkeyedNoMix x`; since `x = unkeyedNoMix m` only moves cells
    of `m` and `x` has 52 distinct cells, the cell map is a bijection of
    positions, so `m` is a deck too. -/
theorem unkeyedNoMix_onto_decks (x : Fin 52 → Nat) (hx : IsDeck x) :
    ∃ m, IsDeck m ∧ unkeyedNoMix m = x :=
  ⟨invUnkeyedNoMix x, isDeck_invUnkeyedNoMix hx, unkeyedNoMix_invUnkeyedNoMix x⟩

/-- (PROVED from the lemmas above) If σ ≠ id commutes with v10 SumRanks
    (e.g. one of the 51 nontrivial `v10Sym a x`), then no full round
    commutes with σ: the stem is onto decks, so the round commuting would make
    GridCycle commute, forcing σ = id. -/
theorem fullRound_not_commutes_of_stem (σ : Relabel) (hid : σ ≠ 1)
    (hs : CommutesG σ sumRanksV10) (pos invPos : Fin 52 → Fin 52)
    (hR : ∀ i, pos (invPos i) = i) :
    ¬ CommutesOnDecks σ (fun m => fullRound m pos) := by
  intro hround
  apply hid
  apply (mixColumns_commutes_iff_id σ).1
  intro x hx
  obtain ⟨m, hm, rfl⟩ := unkeyedNoMix_onto_decks x hx
  have h1 := hround m hm
  simp only [fullRound, unkeyedWithMix] at h1
  rw [unkeyedNoMix_commutes σ hs m hm.1] at h1
  funext i
  have := congrFun h1 (invPos i)
  simpa [composeVec, rel, hR] using this

/-! ### 4a. v8 consequences -/

/-- (PROVED) v8: every rank-preserving σ (e.g. every same-rank swap) commutes
    with Compose (every key), the column-major lay/scoop, ShiftRows and v8
    SumRanks. -/
theorem v8_rank_preserving_commutes_except_gridCycle (σ : Relabel)
    (h : ∀ c : Fin 52, rank (σ c).val = rank c.val) :
    (∀ pos, Commutes σ (fun m => composeVec 52 Nat m pos)) ∧
    CommutesG σ shiftRows ∧ CommutesG σ sumRanksV8 ∧
    Commutes σ V8.unkeyedNoMix := by
  refine ⟨compose_commutes σ, shiftRows_commutes σ,
    v8_sumRanks_commutes_of_rank_preserving σ h, ?_⟩
  intro m hm
  simp only [V8.unkeyedNoMix]
  rw [layColumnMajor_rel, v8_sumRanks_commutes_of_rank_preserving σ h _ (cardsG_lay hm)]
  rfl

theorem v8_same_rank_swap_commutes_except_gridCycle (a b : Fin 52)
    (hab : rank a.val = rank b.val) :
    (∀ pos, Commutes (swap a b) (fun m => composeVec 52 Nat m pos)) ∧
    CommutesG (swap a b) shiftRows ∧ CommutesG (swap a b) sumRanksV8 ∧
    Commutes (swap a b) V8.unkeyedNoMix :=
  v8_rank_preserving_commutes_except_gridCycle _ (rank_swap_same a b hab)

/-! ### 4b. Covariance: the output relabelling may differ from σ

With permutation round keys, encrypt only pins down that the round body maps
σ-relabelled decks to τ-relabelled decks for *some* τ (see `PermKeys.lean`).
So the conjecture is stated in that (stronger) covariant form; the commuting
form is the case τ = σ. -/

/-- `F` maps σ-relabelled decks to τ-relabelled outputs for one fixed τ. -/
def Covariant (σ : Relabel) (F : (Fin 52 → Nat) → (Fin 52 → Nat)) : Prop :=
  ∃ τ : Relabel, ∀ m, IsDeck m → F (rel σ m) = rel τ (F m)

/-- GridCycle writes the first card at `AS` = (2,0), row-major index 26. -/
theorem mixColumns_at_AS (h : Fin 52 → Nat) :
    mixColumns h ⟨26, by decide⟩ = h ⟨0, by decide⟩ :=
  placed_at_seat h 0 (by decide)

/-- (PROVED) If σ ≠ id commutes with v10 SumRanks (e.g. a nontrivial `v10Sym`),
    the round body is not σ-covariant for any τ: the first card sits at `AS`,
    which forces τ = σ, and then GridCycle would commute with σ. -/
theorem roundBody_not_covariant_of_stem (σ : Relabel) (hid : σ ≠ 1)
    (hs : CommutesG σ sumRanksV10) : ¬ Covariant σ unkeyedWithMix := by
  rintro ⟨τ, hτ⟩
  apply hid
  have hmix : ∀ x, IsDeck x → mixColumns (rel σ x) = rel τ (mixColumns x) := by
    intro x hx
    obtain ⟨m, hm, rfl⟩ := unkeyedNoMix_onto_decks x hx
    have := hτ m hm
    simp only [unkeyedWithMix] at this
    rwa [unkeyedNoMix_commutes σ hs m hm.1] at this
  have hστ : τ = σ := by
    apply Equiv.ext; intro c
    have := congrFun (hmix _ (firstDeck_isDeck c)) ⟨26, by decide⟩
    simp only [rel, mixColumns_at_AS, firstDeck_zero, app_fin] at this
    exact (Fin.ext this).symm
  subst hστ
  exact (mixColumns_commutes_iff_id τ).1 hmix

/-- (DRAFT-SORRY, CONJECTURE — checked, not proved) v11: no nontrivial σ makes
    the unkeyed round body covariant, i.e. there is no pair (σ, τ) with σ ≠ id
    and `F(σ·m) = τ·F(m)` on every deck, `F = GridCycle ∘ stem`.
    Checked (`checks/check_covariant.py`, log committed): all 1,326
    transpositions, all 51 nontrivial `v10Sym` (and `v9Sym`) and 200 random σ
    are non-covariant, for v8, v9, v10 and v11 (v11 keeps v10 SumRanks and
    changes only GridCycle). The `v10Sym` cases are proved
    (`roundBody_not_covariant_of_stem` with `sumRanksV10_commutes_v10Sym`).
    The assessment below was written for v9; v10 rows and columns are
    chained, which makes the single-cell argument harder, not easier.

    Assessment: the other σ already fail at SumRanks, but a failing layer
    inside a composite does not by itself make the composite fail. Covariance
    is equivalent to `gridW (stem (σ·m)) = τ · gridW (stem m)` on all decks
    (`walkW_rel_iff` machinery). Its AS cell gives `stem(σ·m)₀ = τ(stem(m)₀)`,
    a single-cell condition on the SumRanks rotation amounts (row sum mod 13 of
    one row, column-0 sum mod 4 after the row rotation). Turning that into
    "σ ∈ v9Sym" needs a swap-pair argument like `sumRanks_shift_of_commutes`,
    but with one cell and the column sum depending on the row rotations; the
    remaining cells interleave two different walks. Effort: uncertain,
    ~1–2 weeks. Not attempted further.

    Narrowed in v12 (separate theorems; this statement is unchanged and still
    open), `CovariantNarrow.lean`: it holds for every transposition
    (`CovariantNarrow.roundBody_not_covariant_swap`, heavy library). It is
    equivalent to its prime-order case (`CovariantNarrow.prime_case_iff`), and to
    its case of prime-order σ that are neither a transposition nor a `v10Sym`
    (`CovariantNarrow.prime_nonswap_case_iff`, heavy library).
    It also follows from single-cell SumRanks statements
    (`CovariantNarrow.roundBody_covariant_iff_id_of_cell0`, `…_of_cell0_prime`) that
    are sufficient conditions, not known to be true or necessary. The reduced cases
    are hypotheses there, not proved. Write-up: `../analysis/v12-covariant/NOTES.md`. -/
theorem roundBody_covariant_iff_id (σ : Relabel) :
    Covariant σ unkeyedWithMix ↔ σ = 1 := by
  constructor
  · intro h
    sorry -- DRAFT-SORRY (conjecture)
  · rintro rfl
    exact ⟨1, fun m _ => by rw [rel_one, rel_one]⟩

/-- (PROVED from the covariant conjecture) No nontrivial σ commutes with the
    full round for all keys (the case τ = σ, key = id). -/
theorem fullRound_commutes_iff_id (σ : Relabel) :
    (∀ pos, CommutesOnDecks σ (fun m => fullRound m pos)) ↔ σ = 1 := by
  constructor
  · intro h
    exact (roundBody_covariant_iff_id σ).1 ⟨σ, fun m hm => h id m hm⟩
  · rintro rfl _; exact commutesOnDecks_one _

/-! ### 4c. Degenerate model keys (constant, non-permutation)

Clearly labelled side lemma, not the headline: the Lean model allows any key
map `Fin 52 → Fin 52`. With constant round keys every mixing round outputs a
constant vector, so `encrypt6` exposes one cell of the round body per key.
Real keys are permutations; the permutation-key statement is
`encrypt6_commutes_iff_id` in `PermKeys.lean`. -/

def constDeck (c : Nat) : Fin 52 → Nat := fun _ => c

theorem unkeyedNoMix_const (c : Nat) : unkeyedNoMix (constDeck c) = constDeck c := by
  funext k
  exact sumRanksV10_bound (· = c) (layColumnMajor (constDeck c))
    (fun _ _ => rfl) _ _

theorem mixColumns_const (c : Nat) : mixColumns (constDeck c) = constDeck c := by
  rw [mixColumns_eq]; funext k
  obtain ⟨j, hj⟩ := seatW_surj _ freeChooser (constDeck c) (rmRow k, rmCol k)
  have := gridW_at_seat _ freeChooser (constDeck c) j
  rw [hj] at this
  exact this

theorem applyFullRounds_constKey (m : Fin 52 → Nat) (k : Fin 52) :
    ∀ n, applyFullRounds (n + 1) m (fun _ _ => k) = constDeck (unkeyedWithMix m k)
  | 0 => rfl
  | n + 1 => by
      rw [applyFullRounds, applyFullRounds_constKey m k n]
      simp only [fullRound, unkeyedWithMix, unkeyedNoMix_const, mixColumns_const]
      rfl

/-- (PROVED, degenerate keys) With `pos0 = posFinal = id` and every round key
    the constant map to `k`, `encrypt6` outputs the constant deck
    `unkeyedWithMix m k`. -/
theorem encrypt6_constKey (m : Fin 52 → Nat) (k : Fin 52) :
    encrypt6 m id (fun _ _ => k) id = constDeck (unkeyedWithMix m k) := by
  simp only [encrypt6, encryptN]
  rw [show composeVec 52 Nat m id = m from rfl, applyFullRounds_constKey m k 4]
  simp only [fullRoundNoMix, unkeyedNoMix_const]
  rfl

/-- (PROVED, degenerate keys — NOT permutation keys) If σ commutes with
    `encrypt6` for all key *maps* (including constant, non-bijective ones), it
    commutes with the full round for all keys. -/
theorem round_of_encrypt6_constKey (σ : Relabel)
    (h : ∀ pos0 posMix posFinal,
      CommutesOnDecks σ (fun m => encrypt6 m pos0 posMix posFinal)) :
    ∀ pos, CommutesOnDecks σ (fun m => fullRound m pos) := by
  intro pos m hm
  have hF : unkeyedWithMix (rel σ m) = rel σ (unkeyedWithMix m) := by
    funext k
    have := congrFun (h id (fun _ _ => k) id m hm) k
    simp only [encrypt6_constKey] at this
    simpa [constDeck, rel] using this
  simp only [fullRound]; rw [hF]; rfl

end DoubleDeal.Security
