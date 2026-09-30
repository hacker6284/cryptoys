/-
  The REAL PassKey key schedule and the constant-σ characteristic (roadmap milestone M5;
  security README, "Roadmap"). Analysis notes: `../analysis/v12-keysched/NOTES.md`.

  Model. The master key is a uniform `π : Equiv.Perm (Fin 52)`, injected into key decks
  by `masterList` (seat `i` holds card `π i`; `masterList_injective`). Its image is
  exactly the 52-card key decks (`exists_masterList_eq`), so counting over `π` is
  counting over key decks. Round key `i` is `roundKey i π`, the position map
  `keyPos (F^i K0)` of the `i`-th PassKey iterate `F^i K0 = passKeyIter i (masterList π)`.
  These are exactly the keys `encryptDeckFn` uses (`encryptDeckFn_masterList`): `K_0`
  (whitening), `K_1 … K_5` (the five full rounds, each Compose after that round's mix)
  and `K_6` (the final no-mix round).
  Counting is over all `52!` master keys, i.e. a UNIFORM MASTER KEY; nothing else is
  random.

  Proved:
  * `card_roundKey`: each single round key `roundKey i π` is uniform (it is a bijective
    function of `π`). This says nothing about two keys together.
  * `card_image_roundKey_pair`, `card_image_roundKey_pair_lt`: for any two rounds
    `r ≠ s`, the pair `(roundKey r π, roundKey s π)` takes exactly `52!` of the `(52!)^2`
    values, so the round keys are NOT independent (not even pairwise). (The theorems are
    stated for all `r`, `s`; for `r = s` they are trivially true and say nothing.)
  * `passKey_head_ne`, `card_roundKey_top_eq`: the top card of `F K` is never the top
    card of `K` (for a 52-card deck), so no master key gives `K_{r+1}[0] = K_r[0]`. For
    independent uniform keys that event would have probability 1/52 (not proved here).
  * `realTrail_card_le_of_round` and its instances `realTrail_card_le_26` (unconditional),
    `realTrail_card_le_64_of_not_v10Sym` (unconditional), `realTrail_card_le_64_of_check`
    (given the two finite GridCycle checks; unconditional in the heavy library:
    `DoubleDealSecurityHeavy/RealSchedule.lean`, `realTrail_card_le_64`): for every
    `R ≥ 1`, every `σ ≠ 1` and every starting deck `y`, at most `52!/64` of the master keys
    make `(y, σ·y)` follow the constant-σ characteristic through `R` rounds of the real
    schedule.

  What this does NOT give, read before citing it:
  * THE PROVED BOUND GAINS NOTHING BEYOND THE FIRST MIX ROUND (round 0, key `K_0`). It is
    1/64 for every `R ≥ 1`, weaker than M2's `(1/64)^R` for independent uniform round keys
    (`TrailBound`), because from
    round 1 on the round key is not uniform given the state (both are functions of the
    master key), so the M2 product argument does not apply. This is a limit of the proof,
    not a measured weakness. For `R ≥ 2` nothing proved here rules out the real schedule
    following the characteristic with probability above `(1/64)^R`.
  * ONE CHARACTERISTIC, NOT A DIFFERENTIAL. Same event `Trail` as `TrailBound` (the
    difference stays σ after every round). Pairs whose difference changes and comes back,
    and `σ → β` for `β ≠ σ`, are not bounded.
  * NOT THE FINAL NO-MIX ROUND here, and `rounds` is not linked to `encryptN`/`encryptDeckFn`
    in this file (only the KEYS are linked, by `encryptDeckFn_masterList`). Both are in
    `FullCipher` (roadmap M7), where the whole cipher under the real schedule gets the same
    bound, from the first mix round (round 0, key `K_0`) alone (`realFullTrail_card_le_26`,
    …), and nothing more.
  * `R ≤ 5` is the cipher's range. `Trail σ R y (roundKeys R π)` is `R` steps "Compose
    with `K_i`, then the unkeyed round with mix", `i = 0 … R-1`. The cipher runs exactly
    five such steps (`K_0 … K_4`, each followed by the next full round's mix), then
    Compose `K_5`, the unkeyed round WITHOUT mix, and Compose `K_6`. For `R ≥ 6` the model
    uses `K_5, K_6, …` as keys before a mix, which the cipher never does; the theorems
    stay true there (harmless) but describe no part of the cipher.
  * The two-round values and the key statistics in the analysis notes are EMPIRICAL
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
def roundKey (i : ℕ) (π : Equiv.Perm (Fin 52)) : Key :=
  keyPerm (passKeyIter i (masterList π)) (passKeyIter_perm52 _ (perm52_masterList π) i)

/-- The first `R` round keys `K_0, …, K_{R-1}` of the real schedule. -/
def roundKeys (R : ℕ) (π : Equiv.Perm (Fin 52)) : Fin R → Key := fun i => roundKey i π

theorem coe_roundKey (i : ℕ) (π : Equiv.Perm (Fin 52)) :
    ⇑(roundKey i π) = keyPos (passKeyIter i (masterList π)) := rfl

/-- (PROVED) The real round keys are the keys `encryptDeckFn` uses: whitening `K_0`, mix
    rounds `K_1 … K_5`, final round `K_6`. -/
theorem encryptDeckFn_masterList (m : Fin 52 → Nat) (π : Equiv.Perm (Fin 52)) :
    encryptDeckFn m (masterList π) =
      encrypt6 m (roundKey 0 π) (fun r => roundKey (r + 1) π) (roundKey 6 π) := by
  simp only [encryptDeckFn, coe_roundKey, passKeyIter]

/-! ## (a) Each single round key is uniform -/

/-- `masterList` is injective (`toDeck_inj`). -/
theorem masterList_injective : Function.Injective masterList := fun _ _ h =>
  Equiv.ext fun i => Fin.ext (congrFun (toDeck_inj h) i)

/-- `masterList` is onto the 52-card key decks: every `Perm52` list is `masterList π`
    for some `π`. With `masterList_injective`, a uniform `π` is a uniform key deck. -/
theorem exists_masterList_eq {L : List Nat} (hL : Perm52 L) : ∃ π, masterList π = L := by
  have hd : IsDeck (ofDeck L hL.length) := by
    refine ⟨fun i => hL.bounded _ (List.getElem_mem _), fun i j h => ?_⟩
    exact Fin.ext ((List.Nodup.getElem_inj_iff hL.nodup).1 h)
  refine ⟨deckPerm _ hd, ?_⟩
  have e : permDeck (deckPerm _ hd) = ofDeck L hL.length := funext fun i => deckPerm_val _ hd i
  rw [masterList, e, Link2.toDeck_ofDeck]

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

theorem roundKey_injective (i : ℕ) : Function.Injective (roundKey i) := fun _ _ h =>
  masterList_injective (passKeyIter_injective i (keyPerm_injective _ _ h))

theorem roundKey_bijective (i : ℕ) : Function.Bijective (roundKey i) :=
  Finite.injective_iff_bijective.1 (roundKey_injective i)

/-- (PROVED) Each single round key of the real schedule is uniform: for every round `i`
    and every property `P` of keys, as many master keys give a round key `i` with `P` as
    there are keys with `P`. About ONE key at a time; nothing about two keys jointly
    (see `card_image_roundKey_pair`). -/
theorem card_roundKey (i : ℕ) (P : Key → Prop) [DecidablePred P] :
    (univ.filter fun π : Equiv.Perm (Fin 52) => P (roundKey i π)).card =
      (univ.filter P).card :=
  card_bijective (roundKey i) (roundKey_bijective i) (by simp)

/-! ## (a′) The round keys are not independent -/

/-- (PROVED) For any two rounds `r ≠ s`, the pair `(K_r, K_s)` of real round keys takes
    exactly `52!` values over the `52!` master keys (`K_r` alone determines the master
    key). Independent uniform keys would take all `(52!)^2` pairs, each equally often.
    Stated for all `r`, `s`; for `r = s` it is trivially true and says nothing. -/
theorem card_image_roundKey_pair (r s : ℕ) :
    (univ.image fun π : Equiv.Perm (Fin 52) => (roundKey r π, roundKey s π)).card =
      Nat.factorial 52 := by
  rw [card_image_of_injective _ (fun _ _ h => roundKey_injective r (congrArg Prod.fst h)),
    card_univ, Fintype.card_perm, Fintype.card_fin]

/-- (PROVED) Hence for any two rounds `r ≠ s` the pair `(K_r, K_s)` is not uniform on
    `Key × Key`: its support is a proper subset (so the two keys are not independent
    uniform keys). Stated for all `r`, `s` (for `r = s` it is trivial). -/
theorem card_image_roundKey_pair_lt (r s : ℕ) :
    (univ.image fun π : Equiv.Perm (Fin 52) => (roundKey r π, roundKey s π)).card <
      Fintype.card (Key × Key) := by
  rw [card_image_roundKey_pair, Fintype.card_prod, Fintype.card_perm, Fintype.card_fin]
  exact Nat.lt_mul_self_iff.2 (Nat.one_lt_factorial.2 (by norm_num))

/-! ## The top card of the next round key -/

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

/-- The card on top of the key deck behind round key `i`: `(roundKey i π).symm 0` is the
    card at seat 0 of `F^i K0`, i.e. its head. -/
theorem roundKey_symm_zero (i : ℕ) (π : Equiv.Perm (Fin 52)) :
    some ((roundKey i π).symm 0).val = (passKeyIter i (masterList π)).head? := by
  have hk := passKeyIter_perm52 _ (perm52_masterList π) i
  show some (keyInvPos (passKeyIter i (masterList π)) 0).val = _
  match passKeyIter i (masterList π), hk with
  | [], hk => exact absurd hk.length (by simp)
  | c :: _, hk =>
    have hc : c < 52 := hk.bounded c (List.mem_cons_self _ _)
    simp [keyInvPos, clampFin_of_lt c hc]

/-- (PROVED) Under the real schedule no master key gives round keys `K_r`, `K_{r+1}`
    with the same top card (`K_{r+1}[0] = K_r[0]`): the count is `0`. (For two independent
    uniform keys the same event would have probability `1/52`; that comparison is not a
    theorem here.) About the top card only. -/
theorem card_roundKey_top_eq (r : ℕ) :
    (univ.filter fun π : Equiv.Perm (Fin 52) =>
      (roundKey (r + 1) π).symm 0 = (roundKey r π).symm 0).card = 0 := by
  rw [card_eq_zero, filter_eq_empty_iff]
  intro π _ h
  have hk := passKeyIter_perm52 _ (perm52_masterList π) r
  have hv := congrArg (fun k : Fin 52 => some k.val) h
  simp only [roundKey_symm_zero] at hv
  exact passKey_head_ne _ hk.nodup (by rw [hk.length]; decide) hv

/-! ## The characteristic under the real schedule: one round's bound -/

/-- (PROVED) If one round's characteristic set has at most `52!/p` decks, then for every
    `R ≥ 1` and every starting deck `y`, at most `52!/p` master keys make `(y, σ·y)`
    follow the constant-σ characteristic through `R` rounds of the REAL schedule. The
    proof uses round 0 only (`K_0` is uniform and `y` is fixed); there is no factor for
    later rounds. -/
theorem realTrail_card_le_of_round (σ : Relabel) (p : ℕ)
    (hround : p * roundCharCount σ ≤ Nat.factorial 52) (R : ℕ) (hR : 0 < R)
    (y : Fin 52 → Nat) (hy : IsDeck y) :
    p * (univ.filter fun π : Equiv.Perm (Fin 52) => Trail σ R y (roundKeys R π)).card ≤
      Nat.factorial 52 := by
  obtain ⟨R', rfl⟩ : ∃ R', R = R' + 1 := ⟨R - 1, by omega⟩
  have hsub : (univ.filter fun π : Equiv.Perm (Fin 52) => Trail σ (R' + 1) y (roundKeys (R' + 1) π)) ⊆
      univ.filter fun π => RoundChar σ (composeVec 52 Nat y (roundKey 0 π)) := by
    intro π hπ
    simp only [mem_filter, mem_univ, true_and] at hπ ⊢
    exact hπ.1
  have hcount : (univ.filter fun π : Equiv.Perm (Fin 52) =>
      RoundChar σ (composeVec 52 Nat y (roundKey 0 π))).card = roundCharCount σ := by
    rw [card_roundKey 0 (fun k => RoundChar σ (composeVec 52 Nat y k)), card_keys_roundChar σ hy]
  calc p * _ ≤ p * roundCharCount σ := Nat.mul_le_mul_left p (hcount ▸ card_le_card hsub)
    _ ≤ Nat.factorial 52 := hround

/-- (PROVED, unconditional) Every `σ ≠ 1`, real schedule, every `R ≥ 1`, every deck `y`:
    at most `52!/26` master keys follow the constant-σ characteristic through `R` rounds.
    The first mix round's bound (round 0, key `K_0`), not `(1/26)^R`. -/
theorem realTrail_card_le_26 (σ : Relabel) (h1 : σ ≠ 1) (R : ℕ) (hR : 0 < R)
    (y : Fin 52 → Nat) (hy : IsDeck y) :
    26 * (univ.filter fun π : Equiv.Perm (Fin 52) => Trail σ R y (roundKeys R π)).card ≤
      Nat.factorial 52 :=
  realTrail_card_le_of_round σ 26 (TrailBound.round_le_26 σ h1) R hR y hy

/-- (PROVED, unconditional) `σ ∉ v10Sym`: at most `52!/64` master keys. One round's bound. -/
theorem realTrail_card_le_64_of_not_v10Sym (σ : Relabel) (h : ¬ ∃ a x, σ = v10Sym a x)
    (R : ℕ) (hR : 0 < R) (y : Fin 52 → Nat) (hy : IsDeck y) :
    64 * (univ.filter fun π : Equiv.Perm (Fin 52) => Trail σ R y (roundKeys R π)).card ≤
      Nat.factorial 52 :=
  realTrail_card_le_of_round σ 64 (TrailBound.round_le_64_of_not_v10Sym σ h) R hR y hy

/-- (PROVED, given the two finite GridCycle checks as hypotheses) Every `σ ≠ 1`: at most
    `52!/64` master keys. One round's bound. Unconditional in the heavy library
    (`realTrail_card_le_64`). -/
theorem realTrail_card_le_64_of_check (hKC : Check3 KC LKC) (hKS : Check3 KS LKS)
    (σ : Relabel) (h1 : σ ≠ 1) (R : ℕ) (hR : 0 < R) (y : Fin 52 → Nat) (hy : IsDeck y) :
    64 * (univ.filter fun π : Equiv.Perm (Fin 52) => Trail σ R y (roundKeys R π)).card ≤
      Nat.factorial 52 :=
  realTrail_card_le_of_round σ 64 (TrailBound.round_le_64_of_check hKC hKS σ h1) R hR y hy

end DoubleDeal.Security.RealSchedule
