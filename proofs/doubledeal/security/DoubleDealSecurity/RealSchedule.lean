/-
  The REAL PassKey key schedule and the constant-σ characteristic (roadmap milestone M5;
  security README, "Roadmap"). Analysis notes: `../analysis/v12-keysched/NOTES.md`.

  Model. A master key is a deck, given as a permutation `π` (seat `i` holds card `π i`;
  `masterList π` is the list form). Round key `i` is `realKey i π`, the position map
  `keyPos (F^i K0)` of the `i`-th PassKey iterate `F^i K0 = passKeyIter i (masterList π)`.
  These are exactly the keys `encryptDeckFn` uses (`encryptDeckFn_masterList`). Counting is
  over all `52!` master keys, i.e. a UNIFORM MASTER KEY; nothing else is random.

  Proved:
  * `card_realKey`: each single round key `realKey i π` is uniform (it is a bijective
    function of `π`). This says nothing about two keys together.
  * `card_image_realKey_pair`, `card_image_realKey_pair_lt`: for any rounds `r`, `s`, the
    pair `(realKey r π, realKey s π)` takes exactly `52!` of the `(52!)^2` values, so the
    round keys are NOT independent (they are not even pairwise independent).
  * `passKey_head_ne`, `card_realKey_top_eq`: the top card of `F K` is never the top card
    of `K` (for a 52-card deck), so no master key gives `K_{r+1}[0] = K_r[0]`. For
    independent uniform keys that event would have probability 1/52 (not proved here).
  * `realTrail_card_le_of_round` and its instances `realTrail_card_le_26` (unconditional),
    `realTrail_card_le_64_of_not_v10Sym` (unconditional), `realTrail_card_le_64_of_check`
    (given the two finite GridCycle checks; unconditional in the heavy library:
    `DoubleDealSecurityHeavy/RealSchedule.lean`, `realTrail_card_le_64`): for every
    `R ≥ 1`, every `σ ≠ 1` and every starting deck `y`, at most `52!/64` of the master keys
    make `(y, σ·y)` follow the constant-σ characteristic through `R` rounds of the real
    schedule.

  What this does NOT give, read before citing it:
  * NO GAIN BEYOND ROUND 1. The bound is one round's: probability at most 1/64 for EVERY
    `R ≥ 1`, against `(1/64)^R` for independent uniform round keys (`TrailBound`). Only
    round 0 uses a key that is uniform given the state it meets; from round 1 on the state
    and the key are both functions of the master key, and the M2 product argument does not
    apply. Nothing better than one round is proved for the real schedule.
  * ONE CHARACTERISTIC, NOT A DIFFERENTIAL. Same event `Trail` as `TrailBound` (the
    difference stays σ after every round). Pairs whose difference changes and comes back,
    and `σ → β` for `β ≠ σ`, are not bounded.
  * NOT THE FINAL NO-MIX ROUND, and `rounds` is not linked to `encryptN`/`encryptDeckFn`
    (only the KEYS are linked, by `encryptDeckFn_masterList`).
  * The two-round values and the key-statistics in the analysis notes are EMPIRICAL
    (sampled), not proved, and no theorem uses them.
  Not a bit-security claim.
-/
import DoubleDealSecurity.TrailBound
import DoubleDealSecurity.RealKey

namespace DoubleDeal.Security.RealSchedule

open DoubleDeal Relabel Finset
open DoubleDeal.Security (Key)
open DoubleDeal.Security.TrailBound (Trail RoundChar roundCharCount card_keys_roundChar)
open DoubleDeal.Security.GridCycleSurvival (Check3 LKC LKS)

/-! ## Definitions and the link to `encryptDeckFn` -/

/-- A master key deck as a list: seat `i` holds card `π i`. -/
def masterList (π : Equiv.Perm (Fin 52)) : List Nat := toDeck (permDeck π)

theorem perm52_masterList (π : Equiv.Perm (Fin 52)) : Perm52 (masterList π) :=
  perm52_toDeck (isDeck_permDeck π)

/-- The position map of a 52-card key deck, as a `Key` (inverse `keyInvPos`). -/
def keyPerm (key : List Nat) (hk : Perm52 key) : Key where
  toFun := keyPos key
  invFun := keyInvPos key
  left_inv := keyInvPos_keyPos key hk
  right_inv := keyPos_keyInvPos key hk

/-- Round key `i` of the real schedule: `keyPos (F^i K0)` with `K0 = masterList π`. -/
def realKey (i : ℕ) (π : Equiv.Perm (Fin 52)) : Key :=
  keyPerm (passKeyIter i (masterList π)) (passKeyIter_perm52 _ (perm52_masterList π) i)

/-- The first `R` round keys `K_0, …, K_{R-1}` of the real schedule. -/
def realKeys (R : ℕ) (π : Equiv.Perm (Fin 52)) : Fin R → Key := fun i => realKey i π

theorem coe_realKey (i : ℕ) (π : Equiv.Perm (Fin 52)) :
    ⇑(realKey i π) = keyPos (passKeyIter i (masterList π)) := rfl

/-- (PROVED) The real round keys are the keys `encryptDeckFn` uses: whitening `K_0`, mix
    rounds `K_1 … K_5`, final round `K_6`. -/
theorem encryptDeckFn_masterList (m : Fin 52 → Nat) (π : Equiv.Perm (Fin 52)) :
    encryptDeckFn m (masterList π) =
      encrypt6 m (realKey 0 π) (fun r => realKey (r + 1) π) (realKey 6 π) := by
  simp only [encryptDeckFn, coe_realKey, passKeyIter]

/-! ## (a) Each single round key is uniform -/

theorem masterList_injective : Function.Injective masterList := by
  intro π₁ π₂ h
  have h' : List.ofFn (permDeck π₁) = List.ofFn (permDeck π₂) := by
    simpa only [masterList, toDeck, Array.toList_ofFn] using h
  have hf := List.ofFn_injective h'
  exact Equiv.ext fun i => Fin.ext (congrFun hf i)

theorem passKey_injective : Function.Injective passToKeyCutFallback := by
  intro a b h
  rw [← passKey_leftInverse a, ← passKey_leftInverse b, h]

theorem passKeyIter_injective : ∀ i : ℕ, Function.Injective (passKeyIter i)
  | 0 => fun _ _ h => h
  | i + 1 => fun _ _ h => passKeyIter_injective i (passKey_injective h)

/-- Two 52-card key decks with the same position map are equal. -/
theorem keyPerm_injective {k₁ k₂ : List Nat} (h₁ : Perm52 k₁) (h₂ : Perm52 k₂)
    (h : keyPerm k₁ h₁ = keyPerm k₂ h₂) : k₁ = k₂ := by
  have hinv : ∀ i, keyInvPos k₁ i = keyInvPos k₂ i := fun i =>
    congrArg (fun e : Key => e.symm i) h
  apply List.ext_getElem (h₁.length.trans h₂.length.symm)
  intro n hn₁ hn₂
  have hn : n < 52 := h₁.length ▸ hn₁
  have hi := hinv ⟨n, hn⟩
  have b₁ : k₁[n] < 52 := h₁.bounded _ (List.getElem_mem hn₁)
  have b₂ : k₂[n] < 52 := h₂.bounded _ (List.getElem_mem hn₂)
  simp only [keyInvPos, hn₁, hn₂, dite_true, clampFin_of_lt _ b₁, clampFin_of_lt _ b₂] at hi
  exact congrArg Fin.val hi

theorem realKey_injective (i : ℕ) : Function.Injective (realKey i) := fun _ _ h =>
  masterList_injective (passKeyIter_injective i (keyPerm_injective _ _ h))

theorem realKey_bijective (i : ℕ) : Function.Bijective (realKey i) :=
  Finite.injective_iff_bijective.1 (realKey_injective i)

/-- (PROVED) Each single round key of the real schedule is uniform: for every round `i`
    and every property `P` of keys, as many master keys give a round key `i` with `P` as
    there are keys with `P`. About ONE key at a time; nothing about two keys jointly
    (see `card_image_realKey_pair`). -/
theorem card_realKey (i : ℕ) (P : Key → Prop) [DecidablePred P] :
    (univ.filter fun π : Equiv.Perm (Fin 52) => P (realKey i π)).card =
      (univ.filter P).card := by
  let e := Equiv.ofBijective (realKey i) (realKey_bijective i)
  apply card_nbij' (fun π => e π) (fun k => e.symm k)
  · intro π hπ
    simpa only [coe_filter, Set.mem_setOf_eq, mem_filter, mem_univ, true_and] using hπ
  · intro k hk
    simp only [coe_filter, Set.mem_setOf_eq, mem_filter, mem_univ, true_and] at hk ⊢
    have : realKey i (e.symm k) = k := e.apply_symm_apply k
    rwa [this]
  · intro π _; exact e.symm_apply_apply π
  · intro k _; exact e.apply_symm_apply k

/-! ## (a′) The round keys are not independent -/

/-- (PROVED) For any rounds `r` and `s`, the pair `(K_r, K_s)` of real round keys takes
    exactly `52!` values over the `52!` master keys (`K_r` alone determines the master
    key). Independent uniform keys would take all `(52!)^2` pairs, each equally often. -/
theorem card_image_realKey_pair (r s : ℕ) :
    (univ.image fun π : Equiv.Perm (Fin 52) => (realKey r π, realKey s π)).card =
      Nat.factorial 52 := by
  rw [card_image_of_injective _ (fun _ _ h => realKey_injective r (congrArg Prod.fst h)),
    card_univ, Fintype.card_perm, Fintype.card_fin]

/-- (PROVED) Hence the pair `(K_r, K_s)` is not uniform on `Key × Key`: its support is a
    proper subset (so the two keys are not independent uniform keys). -/
theorem card_image_realKey_pair_lt (r s : ℕ) :
    (univ.image fun π : Equiv.Perm (Fin 52) => (realKey r π, realKey s π)).card <
      Fintype.card (Key × Key) := by
  rw [card_image_realKey_pair, Fintype.card_prod, Fintype.card_perm, Fintype.card_fin]
  have h : 1 < Nat.factorial 52 := by decide
  calc Nat.factorial 52 = Nat.factorial 52 * 1 := (Nat.mul_one _).symm
    _ < Nat.factorial 52 * Nat.factorial 52 := Nat.mul_lt_mul_of_pos_left h (Nat.factorial_pos 52)

/-! ## The top card of the next round key -/

theorem onPile_fst_perm {α : Type} (fits : ℕ → Prop) [DecidablePred fits]
    (f : List α → List α) (hf : ∀ xs, List.Perm (f xs) xs) (hand key : List α) :
    List.Perm (onPile fits f hand key).1 hand := by
  unfold onPile
  split
  · exact hf hand
  · split <;> exact List.Perm.refl _

/-- One PassKey step leaves the hand a permutation of itself (it only reorders piles). -/
theorem passKeyStep_fst_perm (hand key : List Nat) (c : Nat) :
    List.Perm (passKeyStep hand key c).1 hand := by
  simp only [passKeyStep, maybeCut, maybeDeal]
  exact (onPile_fst_perm _ _ (cutProper_perm · _) _ _).trans
    (onPile_fst_perm _ _ (dealUnder_perm · _) _ _)

/-- The top of the final key pile is a card of the hand the recursion starts from: the
    last controller. -/
theorem passKeyGoN_head_mem : ∀ (n : ℕ) (hand key : List Nat), hand ≠ [] →
    hand.length ≤ n → ∃ x ∈ hand, (passKeyGoN n hand key).head? = some x
  | 0, hand, _, hne, hlen => absurd (List.length_eq_zero.1 (Nat.le_zero.1 hlen)) hne
  | _ + 1, [], _, hne, _ => absurd rfl hne
  | n + 1, c :: rest, key, _, hlen => by
      simp only [passKeyGoN]
      by_cases hr : rest = []
      · subst hr
        have h0 : (passKeyStep [] key c).1 = [] :=
          List.length_eq_zero.1 (by rw [length_passKeyStep_fst]; rfl)
        refine ⟨c, List.mem_cons_self _ _, ?_⟩
        rw [h0]
        cases n <;> simp [passKeyGoN, passKeyStep]
      · have hp := passKeyStep_fst_perm rest key c
        have hne : (passKeyStep rest key c).1 ≠ [] := fun h =>
          hr (List.length_eq_zero.1 (by rw [← hp.length_eq, h]; rfl))
        have hl : (passKeyStep rest key c).1.length ≤ n := by
          rw [length_passKeyStep_fst]; simp at hlen; omega
        obtain ⟨x, hx, hh⟩ := passKeyGoN_head_mem n _ _ hne hl
        exact ⟨x, List.mem_cons_of_mem _ (hp.subset hx), hh⟩

/-- (PROVED) For a deck with at least two cards and no repeats, the top card of `F deck`
    is not the top card of `deck`: the top of `F deck` is the last controller, and the top
    of `deck` is the first. -/
theorem passKey_head_ne (deck : List Nat) (hnd : deck.Nodup) (hlen : 2 ≤ deck.length) :
    (passToKeyCutFallback deck).head? ≠ deck.head? := by
  match deck, hnd, hlen with
  | c :: rest, hnd, hlen =>
    have hr : rest ≠ [] := by rintro rfl; simp at hlen
    have hc : c ∉ rest := (List.nodup_cons.1 hnd).1
    have hp := passKeyStep_fst_perm rest [] c
    have hne : (passKeyStep rest [] c).1 ≠ [] := fun h =>
      hr (List.length_eq_zero.1 (by rw [← hp.length_eq, h]; rfl))
    obtain ⟨x, hx, hh⟩ := passKeyGoN_head_mem rest.length _ _ hne
      (by rw [length_passKeyStep_fst])
    have e : passToKeyCutFallback (c :: rest) =
        passKeyGoN rest.length (passKeyStep rest [] c).1 (passKeyStep rest [] c).2 := by
      simp only [passToKeyCutFallback, List.length_cons, passKeyGoN]
    rw [e, hh, List.head?_cons]
    intro hxc
    exact hc (Option.some_inj.1 hxc ▸ hp.subset hx)

/-- The card on top of the key deck behind a key (`keyInvPos key 0` is the card at seat 0). -/
theorem realKey_symm_zero (i : ℕ) (π : Equiv.Perm (Fin 52)) :
    ((realKey i π).symm 0 : Fin 52).val = (passKeyIter i (masterList π)).head?.getD 0 := by
  have hk := passKeyIter_perm52 _ (perm52_masterList π) i
  obtain ⟨c, rest, hL⟩ : ∃ c rest, passKeyIter i (masterList π) = c :: rest := by
    cases h : passKeyIter i (masterList π) with
    | nil => have := hk.length; rw [h] at this; simp at this
    | cons c rest => exact ⟨c, rest, rfl⟩
  have hc : c < 52 := hk.bounded c (by rw [hL]; exact List.mem_cons_self _ _)
  show (keyInvPos (passKeyIter i (masterList π)) 0).val = _
  rw [hL]
  simp [keyInvPos, clampFin_of_lt c hc]

/-- (PROVED) Under the real schedule no master key gives round keys `K_r`, `K_{r+1}`
    with the same top card (`K_{r+1}[0] = K_r[0]`): the count is `0`. (For two independent
    uniform keys the same event would have probability `1/52`; that comparison is not a
    theorem here.) About the top card only. -/
theorem card_realKey_top_eq (r : ℕ) :
    (univ.filter fun π : Equiv.Perm (Fin 52) =>
      (realKey (r + 1) π).symm 0 = (realKey r π).symm 0).card = 0 := by
  rw [card_eq_zero, filter_eq_empty_iff]
  intro π _ h
  have hk := passKeyIter_perm52 _ (perm52_masterList π) r
  have hF := passKeyIter_perm52 _ (perm52_masterList π) (r + 1)
  have hv := congrArg Fin.val h
  rw [realKey_symm_zero, realKey_symm_zero] at hv
  have hne := passKey_head_ne (passKeyIter r (masterList π)) hk.nodup
    (by rw [hk.length]; decide)
  have hL1 : passKeyIter (r + 1) (masterList π) =
      passToKeyCutFallback (passKeyIter r (masterList π)) := rfl
  rw [hL1] at hv hF
  obtain ⟨a, as, ha⟩ : ∃ a as, passToKeyCutFallback (passKeyIter r (masterList π)) = a :: as := by
    cases h' : passToKeyCutFallback (passKeyIter r (masterList π)) with
    | nil => have := hF.length; rw [h'] at this; simp at this
    | cons a as => exact ⟨a, as, rfl⟩
  obtain ⟨b, bs, hb⟩ : ∃ b bs, passKeyIter r (masterList π) = b :: bs := by
    cases h' : passKeyIter r (masterList π) with
    | nil => have := hk.length; rw [h'] at this; simp at this
    | cons b bs => exact ⟨b, bs, rfl⟩
  rw [ha, hb] at hv hne
  simp only [List.head?_cons, Option.getD_some] at hv hne
  exact hne (congrArg some hv)

/-! ## The characteristic under the real schedule: one round's bound -/

/-- (PROVED) If one round's characteristic set has at most `52!/p` decks, then for every
    `R ≥ 1` and every starting deck `y`, at most `52!/p` master keys make `(y, σ·y)`
    follow the constant-σ characteristic through `R` rounds of the REAL schedule. The
    proof uses round 0 only (`K_0` is uniform and `y` is fixed); there is no factor for
    later rounds. -/
theorem realTrail_card_le_of_round (σ : Relabel) (p : ℕ)
    (hround : p * roundCharCount σ ≤ Nat.factorial 52) (R : ℕ) (hR : 0 < R)
    (y : Fin 52 → Nat) (hy : IsDeck y) :
    p * (univ.filter fun π : Equiv.Perm (Fin 52) => Trail σ R y (realKeys R π)).card ≤
      Nat.factorial 52 := by
  obtain ⟨R', rfl⟩ : ∃ R', R = R' + 1 := ⟨R - 1, by omega⟩
  have hsub : (univ.filter fun π : Equiv.Perm (Fin 52) => Trail σ (R' + 1) y (realKeys (R' + 1) π)) ⊆
      univ.filter fun π => RoundChar σ (composeVec 52 Nat y (realKey 0 π)) := by
    intro π hπ
    simp only [mem_filter, mem_univ, true_and] at hπ ⊢
    exact hπ.1
  have hcount : (univ.filter fun π : Equiv.Perm (Fin 52) =>
      RoundChar σ (composeVec 52 Nat y (realKey 0 π))).card = roundCharCount σ := by
    rw [card_realKey 0 (fun k => RoundChar σ (composeVec 52 Nat y k)), card_keys_roundChar σ hy]
  calc p * _ ≤ p * roundCharCount σ := Nat.mul_le_mul_left p (hcount ▸ card_le_card hsub)
    _ ≤ Nat.factorial 52 := hround

/-- (PROVED, unconditional) Every `σ ≠ 1`, real schedule, every `R ≥ 1`, every deck `y`:
    at most `52!/26` master keys follow the constant-σ characteristic through `R` rounds.
    ONE round's bound, not `(1/26)^R`. -/
theorem realTrail_card_le_26 (σ : Relabel) (h1 : σ ≠ 1) (R : ℕ) (hR : 0 < R)
    (y : Fin 52 → Nat) (hy : IsDeck y) :
    26 * (univ.filter fun π : Equiv.Perm (Fin 52) => Trail σ R y (realKeys R π)).card ≤
      Nat.factorial 52 :=
  realTrail_card_le_of_round σ 26
    (TrailBound.round_le_of_v10Sym 26 (by norm_num) TrailBound.round_le_26_v10Sym σ h1) R hR y hy

/-- (PROVED, unconditional) `σ ∉ v10Sym`: at most `52!/64` master keys. One round's bound. -/
theorem realTrail_card_le_64_of_not_v10Sym (σ : Relabel) (h : ¬ ∃ a x, σ = v10Sym a x)
    (R : ℕ) (hR : 0 < R) (y : Fin 52 → Nat) (hy : IsDeck y) :
    64 * (univ.filter fun π : Equiv.Perm (Fin 52) => Trail σ R y (realKeys R π)).card ≤
      Nat.factorial 52 :=
  realTrail_card_le_of_round σ 64 (TrailBound.round_le_64_of_not_v10Sym σ h) R hR y hy

/-- (PROVED, given the two finite GridCycle checks as hypotheses) Every `σ ≠ 1`: at most
    `52!/64` master keys. One round's bound. Unconditional in the heavy library
    (`realTrail_card_le_64`). -/
theorem realTrail_card_le_64_of_check (hKC : Check3 KC LKC) (hKS : Check3 KS LKS)
    (σ : Relabel) (h1 : σ ≠ 1) (R : ℕ) (hR : 0 < R) (y : Fin 52 → Nat) (hy : IsDeck y) :
    64 * (univ.filter fun π : Equiv.Perm (Fin 52) => Trail σ R y (realKeys R π)).card ≤
      Nat.factorial 52 :=
  realTrail_card_le_of_round σ 64
    (TrailBound.round_le_of_v10Sym 64 le_rfl (fun a x hne =>
      (Nat.mul_le_mul_right _ (by norm_num : (64 : ℕ) ≤ 4420)).trans
        (TrailBound.round_le_4420_v10Sym_of_check hKC hKS a x hne)) σ h1) R hR y hy

end DoubleDeal.Security.RealSchedule
