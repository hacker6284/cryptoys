/-
  The WHOLE cipher `encryptN` (and the model and emitted cipher under the real schedule),
  including the final no-mix round (roadmap milestone M7; security README, "Roadmap").
  Measurement notes: `../analysis/v12-fullcipher/NOTES.md`.

  NO NUMERIC BOUND ON THE FULL-CIPHER DIFFERENTIAL IS PROVED HERE. Read this before citing
  anything below.

  Model. `encryptN n m pos0 posMix posFinal` is: Compose `pos0`; `n` times (unkeyed round
  with GridCycle, Compose `posMix r`); the stem WITHOUT GridCycle; Compose `posFinal`.
  `encryptL n m L` is `encryptN n m` with its own `n + 2` Compose keys as one tuple
  `L : Fin (n + 2) → Key` (`L 0 = pos0`, `L (r+1) = posMix r`, `L (n+1) = posFinal`;
  `encryptN_eq_encryptL`: every `encryptN` call with permutation keys is one). Counting over
  all `(52!)^(n+2)` tuples `L` is INDEPENDENT UNIFORM keys, whitening and final key included.
  Grouping (`encryptL_eq`): `n` rounds of `TrailBound.rounds` (the proof's mix round `i`:
  Compose `L i`, then the unkeyed round with GridCycle), then `finalRound` (Compose `L n`,
  the stem, Compose `L (n+1)`). The cipher is `n = 5` with `L = realKeys π = (K_0, …, K_6)`
  (`encryptDeckFn_masterList_eq`).

  Mapping to SPEC's rounds (this header is its one home). SPEC (§4.7) numbers the cipher as
  whitening (Compose `K_0`), full rounds `r = 1..5` (the unkeyed layers with GridCycle, then
  Compose `K_r`) and a final round (the stem without GridCycle, then Compose `K_6`). The
  proof regroups the same steps. The proof's mix round `i` (`i = 0..4`) is Compose `K_i`
  (the whitening for `i = 0`, the end of SPEC full round `i` otherwise) followed by the
  unkeyed layers of SPEC full round `i+1`. The proof's `finalRound` step is SPEC full round
  5's closing Compose `K_5` followed by SPEC's final round (stem, Compose `K_6`). "The
  proof's mix rounds" and "the proof's finalRound step (`K_5`, `K_6`)", here and in the other
  docs, mean this grouping; they do not renumber SPEC's rounds.

  The relabelling difference passes Compose (any key), lay,
  ShiftRows and scoop unchanged; only SumRanks depends on the deck. The final Compose key
  (`K_6` of the cipher) never changes a relabelling difference.

  Proved:
  * A (link). `encryptN_eq_rounds`, `encryptL_eq`: `encryptN` is `TrailBound.rounds n` then
    `finalRound`. `encryptDeckFn_masterList_eq`: the model cipher under master key `π` is
    `encryptL 5` on `realKeys π`. `generated_encrypt_rel_iff` (`Link.lean`): the emitted
    `Doubledeal.encrypt` maps `α·M` to `γ·C` exactly when `encryptDeckFn` does.
  * B (final round, one step). `dpFCount β γ = Differential.dpCount unkeyedNoMix β γ` counts
    decks with `U(β·w) = γ·U(w)` (`U = unkeyedNoMix`). `dpFCount_self_eq_survivors`:
    `dpFCount σ σ` is the SumRanks survivor count; `dpFCount_self_le_64`: `≤ 52!/64` for `σ`
    outside `v10Sym`. `dpFCount_v10Sym`, `dpFCount_to_v10Sym`: `v10Sym a x` goes to itself on
    every deck and nothing else enters it. `sum_dpFCount`, `sum_dpFCount_left`: rows and
    columns sum to `52!`.
  * C (characteristic, independent keys). `FullTrail σ n y L`: the `TrailBound`
    characteristic through the `n` mix rounds and `TrailBound.SumRanksChar` (SumRanks
    commutes with `σ`) in the final round; it gives `encryptL n (σ·y) L = σ · encryptL n y L`
    (`fullTrail_encryptL`). `card_fullTrail`: `# = 52! · #Trail · #survivors` (exact).
    `card_fullTrail_le`: `# ≤ (52!)^2 · #Trail`, i.e. the final round never increases the
    characteristic's probability. `card_fullTrail_v10Sym`: for `v10Sym`,
    `# = (52!)^2 · #Trail`, NO extra factor. Bounds `p · # ≤ (52!)^(n+2)`:
    - `fullTrail_card_le_26`: `p = 26^n`, every `σ ≠ 1`;
    - `fullTrail_card_le_64_of_not_v10Sym`: `p = 64^(n+1)`, `σ` outside `v10Sym`, no
      hypothesis;
    - `fullTrail_card_le_4420_v10Sym_of_check`: `p = 4420^n`, `v10Sym a x` with
      `(a, x) ≠ (0, 0)`;
    - `fullTrail_card_le_64_of_check`: `p = 64^(n+1)`, every `σ ≠ 1`, `n ≥ 1`.
    The `_of_check` forms are given the two finite GridCycle checks and hold without them in
    the heavy library (`fullTrail_card_le_4420_v10Sym`, `fullTrail_card_le_64`).
  * D (differential, independent keys; STRUCTURE ONLY). `fullDiffCount α γ n y` counts the
    tuples `L` with `encryptL n (α·y) L = γ · encryptL n y L`. `fullDiffCount_eq`: the exact
    Markov step `fullDiffCount α γ n y = 52! · ∑ β, diffCount α β n y · dpFCount β γ`.
    `fullDiffCount_le_sup` (max monotonicity): `≤ (52!)^2 · max_β diffCount α β n y`. This
    gives NO number (no numeric bound on `diffCount` is proved). Single entries can rise
    (at `n = 0`): `exists_fullDiffCount_zero_gt` gives, for `α` outside `v10Sym`, some
    `γ ≠ α` with `(52!)^2 · diffCount α γ 0 y < fullDiffCount α γ 0 y`. For `n ≥ 1` nothing is
    proved or measured about single entries. `fullDiffCount_v10Sym`: into `v10Sym a x` the
    count is exactly `(52!)^2 · diffCount` (transparent column; no extra factor).
    `FullStaysInV10` (difference some `v10Sym` after every mix round and after the final
    round) is `StaysInV10` (`fullStaysInV10_iff`), with `card_fullStaysInV10`
    (`= (52!)^2 · #StaysInV10`), `fullStaysInV10_card_le_26` and
    `fullStaysInV10_card_le_4420_of_check` (heavy: `fullStaysInV10_card_le_4420`), for
    `(a, x) ≠ (0, 0)`: the same `26^n`, `4420^n` as for `n` rounds.
  * E (real PassKey schedule, uniform master key, the whole cipher `n = 5`). Bounds
    `p · # ≤ 52!` on the master keys:
    - `realFullTrail_card_le_26`: `p = 26`, every `σ ≠ 1`;
    - `realFullTrail_card_le_64_of_not_v10Sym`: `p = 64`, `σ` outside `v10Sym`, no
      hypothesis;
    - `realFullTrail_card_le_64_of_check` (heavy: `realFullTrail_card_le_64`): `p = 64`,
      every `σ ≠ 1`;
    - `realFullStaysInV10_card_le_26`, `realFullStaysInV10_card_le_4420_of_check` (heavy:
      `realFullStaysInV10_card_le_4420`): the `v10Sym` cluster, `p = 26`, `p = 4420`, for
      `(a, x) ≠ (0, 0)`.
    These are M5/M6's bounds for the proof's first mix round (key `K_0`) alone. The proof
    gains NOTHING beyond it: the proof's later mix rounds (keys `K_1 … K_4`) and the proof's
    finalRound step (`K_5`, `K_6`) add no factor. This is a limit of the proof, not a
    measured weakness: from the proof's second mix round on, the round key is not uniform
    given the state, so the independent-key counting does not apply.
    `generated_encrypt_of_realFullTrail`, `generated_encrypt_of_realFullStaysInV10`: under
    these events the emitted
    `Doubledeal.encrypt` maps the relabelled message to the relabelled ciphertext.

  NOT proved, and limits; read before citing:
  * Any numeric bound on the full-cipher differential (independent or real keys). The
    real-schedule differential `P[E(α·M) = γ·E(M)]` gets NO bound at all.
  * Anything under the real schedule beyond the proof's first mix round (key `K_0`).
  * For `v10Sym` the final round gives NO extra factor, and `K_6` never changes a relabelling
    difference. Every `v10Sym` bound needs `(a, x) ≠ (0, 0)` (`v10Sym 0 0 = 1`).
  * The measured values in the notes are EMPIRICAL (sampled), not proved; no theorem uses them.
  Not a bit-security claim.
-/
import DoubleDealSecurity.Differential

namespace DoubleDeal.Security.FullCipher

open DoubleDeal Relabel Finset
open DoubleDeal.Security (Key isDeck_compose isDeck_rel isDeck_unkeyedNoMix rel_left_inj
  cardsG_lay composeVec_inj isDeck_invUnkeyedNoMix generated_encrypt_rel_iff)
open DoubleDeal.Security.TrailBound (rounds Trail SumRanksChar unkeyedNoMix_rel_iff
  trail_rounds_rel isDeck_rounds card_keys_compose card_filter_snoc ne_zero_of_ne_one)
open DoubleDeal.Security.Differential (Diff diffCount relDiff rel_relDiff relDiff_eq_iff
  dpCount sum_dpCount sum_dpCount_left StaysInV10 staysInV10_iff_trail unkeyedNoMix_rel_v10Sym)
open DoubleDeal.Security.GridCycleSurvival (Check3 LKC LKS)
open DoubleDeal.Security.RealSchedule (roundKey roundKeys masterList perm52_masterList
  encryptDeckFn_masterList)

/-! ## A. `encryptN` in terms of `TrailBound.rounds` -/

/-- The final round in this decomposition: Compose with `k` (the Compose that ends the last
    mix round of `encryptN`), the unkeyed stem WITHOUT GridCycle, then Compose with `kF`
    (`posFinal`). -/
def finalRound (k kF : Key) (z : Fin 52 → Nat) : Fin 52 → Nat :=
  composeVec 52 Nat (unkeyedNoMix (composeVec 52 Nat z k)) kF

/-- (PROVED) `rounds` peeled from the LAST round. -/
theorem rounds_succ_last : ∀ (R : ℕ) (y : Fin 52 → Nat) (K : Fin (R + 1) → Key),
    rounds (R + 1) y K =
      unkeyedWithMix (composeVec 52 Nat (rounds R y (Fin.init K)) (K (Fin.last R)))
  | 0, _, _ => rfl
  | R + 1, y, K => by
    rw [rounds, rounds_succ_last R _ (Fin.tail K), rounds]
    rfl

/-- The first `n + 1` Compose keys of `encryptN n _ k0 kMix _` as a tuple:
    `k0, kMix 0, …, kMix (n-1)`. -/
def mixKeys (n : ℕ) (k0 : Key) (kMix : ℕ → Key) : Fin (n + 1) → Key :=
  Fin.cons k0 (fun i : Fin n => kMix i)

theorem init_mixKeys (n : ℕ) (k0 : Key) (kMix : ℕ → Key) :
    Fin.init (mixKeys (n + 1) k0 kMix) = mixKeys n k0 kMix := by
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  simp only [mixKeys, Fin.init]
  rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ]
  rfl

theorem mixKeys_last (n : ℕ) (k0 : Key) (kMix : ℕ → Key) :
    mixKeys (n + 1) k0 kMix (Fin.last (n + 1)) = kMix n := by
  simp only [mixKeys, ← Fin.succ_last, Fin.cons_succ, Fin.val_last]

theorem applyFullRounds_eq_rounds (k0 : Key) (kMix : ℕ → Key) (m : Fin 52 → Nat) :
    ∀ n, applyFullRounds n (composeVec 52 Nat m k0) (fun r => kMix r) =
      composeVec 52 Nat (rounds n m (Fin.init (mixKeys n k0 kMix))) (mixKeys n k0 kMix (Fin.last n))
  | 0 => rfl
  | n + 1 => by
    rw [applyFullRounds, applyFullRounds_eq_rounds k0 kMix m n, init_mixKeys, rounds_succ_last,
      mixKeys_last]
    rfl

/-- (PROVED) `encryptN` with permutation keys is `n` rounds of `TrailBound.rounds` (keys
    `k0, kMix 0, …, kMix (n-2)`), then `finalRound` with `kMix (n-1)` (for `n = 0`: `k0`)
    and `kF`. -/
theorem encryptN_eq_rounds (n : ℕ) (m : Fin 52 → Nat) (k0 : Key) (kMix : ℕ → Key) (kF : Key) :
    encryptN n m k0 (fun r => kMix r) kF =
      finalRound (mixKeys n k0 kMix (Fin.last n)) kF
        (rounds n m (Fin.init (mixKeys n k0 kMix))) := by
  simp only [encryptN]
  rw [applyFullRounds_eq_rounds]
  rfl

/-! ### `encryptN` with its own `n + 2` Compose keys as one tuple -/

/-- `encryptN n m` with its `n + 2` Compose keys as one tuple `L`: `L 0 = pos0`,
    `L (r + 1) = posMix r` for `r < n`, `L (n + 1) = posFinal`. The entries `posMix r` for
    `r ≥ n` are set to `1`; they are never read: the right-hand side of `encryptN_eq_rounds`
    uses `kMix i` only for `i < n`. -/
def encryptL (n : ℕ) (m : Fin 52 → Nat) (L : Fin (n + 2) → Key) : Fin 52 → Nat :=
  encryptN n m (L 0) (fun r => ⇑(if h : r < n then L ⟨r + 1, by omega⟩ else (1 : Key)))
    (L (Fin.last (n + 1)))

/-- The `n` mix-round keys `L 0, …, L (n-1)` of the tuple. -/
def roundKeysOf {n : ℕ} (L : Fin (n + 2) → Key) : Fin n → Key := fun i => L i.castSucc.castSucc

/-- The Compose key `L n` that ends the last mix round (for `n = 0`: the whitening key). -/
def lastKeyOf {n : ℕ} (L : Fin (n + 2) → Key) : Key := L (Fin.last n).castSucc

/-- The final Compose key `L (n + 1)` (`posFinal`; `K_6` of the cipher). -/
def finalKeyOf {n : ℕ} (L : Fin (n + 2) → Key) : Key := L (Fin.last (n + 1))

/-- (PROVED) `encryptL` is `rounds` followed by `finalRound`. -/
theorem encryptL_eq (n : ℕ) (m : Fin 52 → Nat) (L : Fin (n + 2) → Key) :
    encryptL n m L = finalRound (lastKeyOf L) (finalKeyOf L) (rounds n m (roundKeysOf L)) := by
  have h := encryptN_eq_rounds n m (L 0) (fun r => if h : r < n then L ⟨r + 1, by omega⟩ else 1)
    (L (Fin.last (n + 1)))
  have hk : mixKeys n (L 0) (fun r => if h : r < n then L ⟨r + 1, by omega⟩ else 1) =
      Fin.init L := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    simp only [mixKeys, Fin.cons_succ, Fin.init, dif_pos j.isLt]
    rfl
  rwa [hk] at h

/-- The key tuple of an `encryptN` call: `k0, kMix 0, …, kMix (n-1), kF`. -/
def keyTuple (n : ℕ) (k0 : Key) (kMix : ℕ → Key) (kF : Key) : Fin (n + 2) → Key :=
  Fin.snoc (mixKeys n k0 kMix) kF

/-- (PROVED) Every `encryptN` call with permutation keys is an `encryptL` call (on its own key
    tuple), so counting over all `L` is counting over all `(pos0, posMix 0, …, posMix (n-1),
    posFinal)`. -/
theorem encryptN_eq_encryptL (n : ℕ) (m : Fin 52 → Nat) (k0 : Key) (kMix : ℕ → Key) (kF : Key) :
    encryptN n m k0 (fun r => kMix r) kF = encryptL n m (keyTuple n k0 kMix kF) := by
  have h1 : roundKeysOf (keyTuple n k0 kMix kF) = Fin.init (mixKeys n k0 kMix) := by
    funext i
    simp only [roundKeysOf, keyTuple, Fin.snoc_castSucc, Fin.init]
  have h2 : lastKeyOf (keyTuple n k0 kMix kF) = mixKeys n k0 kMix (Fin.last n) := by
    simp only [lastKeyOf, keyTuple, Fin.snoc_castSucc]
  have h3 : finalKeyOf (keyTuple n k0 kMix kF) = kF := by
    simp only [finalKeyOf, keyTuple, Fin.snoc_last]
  rw [encryptN_eq_rounds, encryptL_eq, h1, h2, h3]

/-- (PROVED) Counting the `n + 2` keys of `encryptL` as (mix-round keys, `lastKeyOf`,
    `finalKeyOf`). -/
theorem card_filter_keys {n : ℕ} (P : (Fin n → Key) → Key → Key → Prop)
    [∀ K k kF, Decidable (P K k kF)] :
    (univ.filter fun L : Fin (n + 2) → Key => P (roundKeysOf L) (lastKeyOf L) (finalKeyOf L)).card =
      ∑ kF : Key, ∑ k : Key, (univ.filter fun K : Fin n → Key => P K k kF).card := by
  rw [card_filter_snoc]
  refine sum_congr rfl fun kF _ => ?_
  rw [card_filter_snoc]
  refine sum_congr rfl fun k _ => ?_
  congr 1
  apply filter_congr
  intro K _
  have hK : roundKeysOf (Fin.snoc (Fin.snoc K k) kF : Fin (n + 2) → Key) = K := by
    funext i
    simp only [roundKeysOf, Fin.snoc_castSucc]
  rw [hK]
  simp only [lastKeyOf, finalKeyOf, Fin.snoc_castSucc, Fin.snoc_last]

/-! ### The real PassKey schedule and the emitted program -/

/-- The seven real round keys `K_0, …, K_6` (`RealSchedule.roundKey`) as an `encryptL` tuple. -/
def realKeys (π : Equiv.Perm (Fin 52)) : Fin 7 → Key := fun i => roundKey i π

theorem roundKeysOf_realKeys (π : Equiv.Perm (Fin 52)) :
    roundKeysOf (realKeys π) = roundKeys 5 π := rfl

/-- (PROVED) The model cipher under master key `π` is `encryptL 5` on the real round keys. -/
theorem encryptDeckFn_masterList_eq (m : Fin 52 → Nat) (π : Equiv.Perm (Fin 52)) :
    encryptDeckFn m (masterList π) = encryptL 5 m (realKeys π) := by
  rw [encryptDeckFn_masterList, encrypt6, encryptN_eq_encryptL 5 m (roundKey 0 π)
    (fun r => roundKey (r + 1) π) (roundKey 6 π)]
  congr 1

/-! ## B. The final round, one step -/

/-- (PROVED) Through the final round, the output difference is `γ` exactly when it is `γ`
    after the stem: the final Compose (key `kF`) never changes it. -/
theorem finalRound_rel_iff (γ : Relabel) (k kF : Key) (z z' : Fin 52 → Nat) :
    finalRound k kF z' = rel γ (finalRound k kF z) ↔
      unkeyedNoMix (composeVec 52 Nat z' k) = rel γ (unkeyedNoMix (composeVec 52 Nat z k)) := by
  simp only [finalRound]
  rw [← compose_rel, composeVec_inj]

/-- (PROVED) The final round keeps the difference `σ` exactly under `SumRanksChar`. -/
theorem finalRound_rel_self_iff (σ : Relabel) (k kF : Key) (z : Fin 52 → Nat) :
    finalRound k kF (rel σ z) = rel σ (finalRound k kF z) ↔
      SumRanksChar σ (composeVec 52 Nat z k) := by
  rw [finalRound_rel_iff, compose_rel, unkeyedNoMix_rel_iff]

/-- The final round's one-step count (`Differential.dpCount` of the stem): decks `w` (as
    permutations) with `U(β·w) = γ·U(w)`, `U = unkeyedNoMix`. -/
def dpFCount (β γ : Relabel) : ℕ := dpCount unkeyedNoMix β γ

/-- (PROVED) `dpFCount σ σ` is the SumRanks survivor count (`SumRanksDP.survivors`). -/
theorem dpFCount_self_eq_survivors (σ : Relabel) :
    dpFCount σ σ = (SumRanksDP.survivors σ).card := by
  unfold dpFCount dpCount SumRanksDP.survivors
  congr 1
  exact filter_congr fun π _ => unkeyedNoMix_rel_iff σ (permDeck π)

/-- (PROVED, unconditional) For `σ` outside `v10Sym`, the final round keeps the difference `σ`
    on at most `52!/64` decks (`sumRanksV10_survival_le`). -/
theorem dpFCount_self_le_64 (σ : Relabel) (h : ¬ ∃ a x, σ = v10Sym a x) :
    64 * dpFCount σ σ ≤ Nat.factorial 52 := by
  have := SumRanksDP.sumRanksV10_survival_le σ h
  rw [Fintype.card_perm, Fintype.card_fin] at this
  rw [dpFCount_self_eq_survivors]
  exact this

/-- (PROVED) `SumRanksChar` always holds for `v10Sym` (an exact SumRanks symmetry). -/
theorem sumRanksChar_v10Sym (a : Fin 13) (x : Fin 4) {w : Fin 52 → Nat} (hw : Cards w) :
    SumRanksChar (v10Sym a x) w :=
  sumRanksV10_commutes_v10Sym a x _ (cardsG_lay hw)

/-- (PROVED) The final round is transparent to `v10Sym` differences: `v10Sym a x` goes to
    itself on every deck, and to nothing else. -/
theorem dpFCount_v10Sym (a : Fin 13) (x : Fin 4) (γ : Relabel) :
    dpFCount (v10Sym a x) γ = if γ = v10Sym a x then Nat.factorial 52 else 0 := by
  unfold dpFCount dpCount
  have e : ∀ π : Equiv.Perm (Fin 52),
      (unkeyedNoMix (rel (v10Sym a x) (permDeck π)) = rel γ (unkeyedNoMix (permDeck π))) ↔
        γ = v10Sym a x := fun π => by
    rw [unkeyedNoMix_rel_v10Sym a x (isDeck_permDeck π).1, eq_comm,
      rel_left_inj (isDeck_unkeyedNoMix (isDeck_permDeck π))]
  rw [filter_congr (fun π _ => e π)]
  split_ifs with h
  · simp [h, Fintype.card_perm]
  · simp [h]

/-- (PROVED) Nothing enters `v10Sym a x` in the final round from a different difference. -/
theorem dpFCount_to_v10Sym (a : Fin 13) (x : Fin 4) {β : Relabel} (hβ : β ≠ v10Sym a x) :
    dpFCount β (v10Sym a x) = 0 := by
  unfold dpFCount dpCount
  rw [card_eq_zero, filter_eq_empty_iff]
  intro π _ h
  have hd := isDeck_permDeck π
  rw [← unkeyedNoMix_rel_v10Sym a x hd.1] at h
  have h2 := congrArg invUnkeyedNoMix h
  rw [invUnkeyedNoMix_unkeyedNoMix, invUnkeyedNoMix_unkeyedNoMix] at h2
  exact hβ ((rel_left_inj hd).1 h2)

/-- (PROVED) Row sums: from each `β`, the final-round counts add up to `52!`. -/
theorem sum_dpFCount (β : Relabel) : ∑ γ, dpFCount β γ = Nat.factorial 52 :=
  sum_dpCount unkeyedNoMix isDeck_unkeyedNoMix β

/-- (PROVED) Column sums: into each `γ`, the final-round counts add up to `52!` (so the
    one-step matrix `dpFCount / 52!` is doubly stochastic). -/
theorem sum_dpFCount_left (γ : Relabel) : ∑ β, dpFCount β γ = Nat.factorial 52 :=
  sum_dpCount_left unkeyedNoMix invUnkeyedNoMix isDeck_unkeyedNoMix isDeck_invUnkeyedNoMix
    invUnkeyedNoMix_unkeyedNoMix unkeyedNoMix_invUnkeyedNoMix γ

/-! ## Counting helpers -/

/-- (PROVED) `∑ k, #{K | A K ∧ B K k} = ∑_{K ∈ A} #{k | B K k}`. -/
theorem sum_card_filter_and {ι : Type} [Fintype ι] (A : ι → Prop) [DecidablePred A]
    (B : ι → Key → Prop) [∀ i k, Decidable (B i k)] :
    ∑ k : Key, (univ.filter fun i => A i ∧ B i k).card =
      ∑ i ∈ univ.filter A, (univ.filter fun k => B i k).card := by
  simp only [card_filter]
  rw [sum_comm, sum_filter]
  refine sum_congr rfl fun i _ => ?_
  by_cases hA : A i <;> simp [hA]

/-- (PROVED) `∑ k, #{i | B i k} = ∑ i, #{k | B i k}`. -/
theorem sum_card_filter_comm {ι : Type} [Fintype ι] (B : ι → Key → Prop)
    [∀ i k, Decidable (B i k)] :
    ∑ k : Key, (univ.filter fun i => B i k).card =
      ∑ i, (univ.filter fun k => B i k).card := by
  simp only [card_filter]
  exact sum_comm

/-- (PROVED) Arithmetic for the whole-cipher bounds: if `c ≤ (52!)^2 · d` and
    `p^n · d ≤ (52!)^n`, then `p^n · c ≤ (52!)^(n+2)`. -/
theorem pow_mul_le_of_le_sq_mul {p n c d : ℕ} (hc : c ≤ Nat.factorial 52 ^ 2 * d)
    (hd : p ^ n * d ≤ Nat.factorial 52 ^ n) : p ^ n * c ≤ Nat.factorial 52 ^ (n + 2) :=
  calc p ^ n * c ≤ p ^ n * (Nat.factorial 52 ^ 2 * d) := Nat.mul_le_mul_left _ hc
    _ = Nat.factorial 52 ^ 2 * (p ^ n * d) := by ring
    _ ≤ Nat.factorial 52 ^ 2 * Nat.factorial 52 ^ n := Nat.mul_le_mul_left _ hd
    _ = Nat.factorial 52 ^ (n + 2) := by ring

/-- (PROVED) Summing a function of `g K` over all `K` by the fibres of `g`. -/
theorem sum_comp_fiber {ι : Type} [Fintype ι] (g : ι → Relabel) (f : Relabel → ℕ) :
    ∑ i, f (g i) = ∑ β, (univ.filter fun i => g i = β).card * f β := by
  rw [← sum_fiberwise univ g (fun i => f (g i))]
  refine sum_congr rfl fun β _ => ?_
  rw [sum_congr rfl (fun i hi => by rw [(mem_filter.1 hi).2]), sum_const, smul_eq_mul]

/-! ## C. The constant-σ characteristic through the whole cipher (independent keys) -/

/-- The constant-σ characteristic through ALL of `encryptL n`: the `TrailBound`
    characteristic through the `n` mix rounds, and SumRanks commuting with `σ` in the final
    round. -/
def FullTrail (σ : Relabel) (n : ℕ) (y : Fin 52 → Nat) (L : Fin (n + 2) → Key) : Prop :=
  Trail σ n y (roundKeysOf L) ∧
    SumRanksChar σ (composeVec 52 Nat (rounds n y (roundKeysOf L)) (lastKeyOf L))

instance (σ : Relabel) (n : ℕ) (y : Fin 52 → Nat) : DecidablePred (FullTrail σ n y) :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _))

/-- (PROVED) Following the characteristic through the whole cipher, the ciphertext pair has
    difference `σ`: `encryptL n (σ·y) L = σ · encryptL n y L`. -/
theorem fullTrail_encryptL {σ : Relabel} {n : ℕ} {y : Fin 52 → Nat} {L : Fin (n + 2) → Key}
    (h : FullTrail σ n y L) : encryptL n (rel σ y) L = rel σ (encryptL n y L) := by
  rw [encryptL_eq, encryptL_eq, trail_rounds_rel σ n y _ h.1]
  exact (finalRound_rel_self_iff σ _ _ _).2 h.2

/-- (PROVED) Exact count, independent uniform keys (all `(52!)^(n+2)` tuples `L`): the final
    Compose key is free, and the final round multiplies the `Trail` count by the SumRanks
    survivor count. -/
theorem card_fullTrail (σ : Relabel) (n : ℕ) {y : Fin 52 → Nat} (hy : IsDeck y) :
    (univ.filter fun L : Fin (n + 2) → Key => FullTrail σ n y L).card =
      Nat.factorial 52 * ((univ.filter fun K : Fin n → Key => Trail σ n y K).card *
        (SumRanksDP.survivors σ).card) := by
  have h := card_filter_keys (n := n) (fun K k _ => Trail σ n y K ∧
    SumRanksChar σ (composeVec 52 Nat (rounds n y K) k))
  simp only at h
  rw [show (univ.filter fun L : Fin (n + 2) → Key => FullTrail σ n y L) =
    univ.filter fun L : Fin (n + 2) → Key => Trail σ n y (roundKeysOf L) ∧
      SumRanksChar σ (composeVec 52 Nat (rounds n y (roundKeysOf L)) (lastKeyOf L)) from rfl, h,
    sum_const, card_univ, Fintype.card_perm, Fintype.card_fin, smul_eq_mul,
    sum_card_filter_and]
  congr 1
  rw [sum_congr rfl (fun K _ => (card_keys_compose (SumRanksChar σ) (isDeck_rounds n y K hy)).trans
    (congrArg card (filter_congr fun π _ => Iff.rfl))), sum_const, smul_eq_mul]
  rfl

/-- (PROVED) The sub-event remark of `TrailBound`: extending the characteristic through the
    final round (and the free final Compose key) never increases its probability. -/
theorem card_fullTrail_le (σ : Relabel) (n : ℕ) {y : Fin 52 → Nat} (hy : IsDeck y) :
    (univ.filter fun L : Fin (n + 2) → Key => FullTrail σ n y L).card ≤
      Nat.factorial 52 ^ 2 * (univ.filter fun K : Fin n → Key => Trail σ n y K).card := by
  rw [card_fullTrail σ n hy, pow_two, mul_assoc]
  refine Nat.mul_le_mul_left _ ?_
  rw [mul_comm]
  refine Nat.mul_le_mul_right _ ?_
  have := card_le_univ (SumRanksDP.survivors σ)
  rwa [Fintype.card_perm, Fintype.card_fin] at this

/-- (PROVED) For `v10Sym a x` the final round gives NO extra factor: the count is exactly
    `(52!)^2` times the `Trail` count (SumRanks always commutes with `v10Sym`). -/
theorem card_fullTrail_v10Sym (a : Fin 13) (x : Fin 4) (n : ℕ) {y : Fin 52 → Nat}
    (hy : IsDeck y) :
    (univ.filter fun L : Fin (n + 2) → Key => FullTrail (v10Sym a x) n y L).card =
      Nat.factorial 52 ^ 2 *
        (univ.filter fun K : Fin n → Key => Trail (v10Sym a x) n y K).card := by
  rw [card_fullTrail _ n hy]
  have hs : (SumRanksDP.survivors (v10Sym a x)).card = Nat.factorial 52 := by
    have : SumRanksDP.survivors (v10Sym a x) = univ :=
      filter_true_of_mem fun π _ => sumRanksChar_v10Sym a x (isDeck_permDeck π).1
    rw [this, card_univ, Fintype.card_perm, Fintype.card_fin]
  rw [hs]
  ring

/-- (PROVED) Generic: a bound `p^n` on the `n`-round characteristic carries to the whole cipher. -/
theorem fullTrail_card_le_of_trail (σ : Relabel) (p n : ℕ) {y : Fin 52 → Nat} (hy : IsDeck y)
    (hT : p ^ n * (univ.filter fun K : Fin n → Key => Trail σ n y K).card ≤ Nat.factorial 52 ^ n) :
    p ^ n * (univ.filter fun L : Fin (n + 2) → Key => FullTrail σ n y L).card ≤
      Nat.factorial 52 ^ (n + 2) :=
  pow_mul_le_of_le_sq_mul (card_fullTrail_le σ n hy) hT

/-- (PROVED, unconditional) Whole cipher, every `σ ≠ 1`: `26^n · # ≤ (52!)^(n+2)`. The final
    round adds no factor here (it adds none for `v10Sym`). -/
theorem fullTrail_card_le_26 (σ : Relabel) (h1 : σ ≠ 1) (n : ℕ) {y : Fin 52 → Nat}
    (hy : IsDeck y) :
    26 ^ n * (univ.filter fun L : Fin (n + 2) → Key => FullTrail σ n y L).card ≤
      Nat.factorial 52 ^ (n + 2) :=
  fullTrail_card_le_of_trail σ 26 n hy (TrailBound.trail_card_le_26 σ h1 n y hy)

/-- (PROVED, unconditional) Whole cipher, `σ` outside `v10Sym`: `64^(n+1) · # ≤ (52!)^(n+2)`
    (one factor `64` per mix round and one from the final round's SumRanks). -/
theorem fullTrail_card_le_64_of_not_v10Sym (σ : Relabel) (h : ¬ ∃ a x, σ = v10Sym a x)
    (n : ℕ) {y : Fin 52 → Nat} (hy : IsDeck y) :
    64 ^ (n + 1) * (univ.filter fun L : Fin (n + 2) → Key => FullTrail σ n y L).card ≤
      Nat.factorial 52 ^ (n + 2) := by
  have hT := TrailBound.trail_card_le_64_of_not_v10Sym σ h n y hy
  have hS := dpFCount_self_le_64 σ h
  rw [dpFCount_self_eq_survivors] at hS
  rw [card_fullTrail σ n hy]
  calc 64 ^ (n + 1) * (Nat.factorial 52 * ((univ.filter fun K : Fin n → Key => Trail σ n y K).card *
        (SumRanksDP.survivors σ).card))
      = Nat.factorial 52 * ((64 ^ n * (univ.filter fun K : Fin n → Key => Trail σ n y K).card) *
          (64 * (SumRanksDP.survivors σ).card)) := by ring
    _ ≤ Nat.factorial 52 * (Nat.factorial 52 ^ n * Nat.factorial 52) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul hT hS)
    _ = Nat.factorial 52 ^ (n + 2) := by ring

/-- (PROVED, given the two finite GridCycle checks as hypotheses) Whole cipher, nontrivial
    `v10Sym a x` (`(a, x) ≠ (0, 0)`): `4420^n · # ≤ (52!)^(n+2)`; the final round adds NO
    factor. -/
theorem fullTrail_card_le_4420_v10Sym_of_check (hKC : Check3 KC LKC) (hKS : Check3 KS LKS)
    (a : Fin 13) (x : Fin 4) (hne : ¬ (a = 0 ∧ x = 0)) (n : ℕ) {y : Fin 52 → Nat}
    (hy : IsDeck y) :
    4420 ^ n * (univ.filter fun L : Fin (n + 2) → Key => FullTrail (v10Sym a x) n y L).card ≤
      Nat.factorial 52 ^ (n + 2) :=
  fullTrail_card_le_of_trail _ 4420 n hy
    (TrailBound.trail_card_le_4420_v10Sym_of_check hKC hKS a x hne n y hy)

/-- (PROVED, given the two finite GridCycle checks as hypotheses) Whole cipher with at least
    one mix round, every `σ ≠ 1`: `64^(n+1) · # ≤ (52!)^(n+2)`. Why `n ≥ 1`: for `v10Sym` the
    final round adds no factor, so at `n = 0` `card_fullTrail_v10Sym` gives `# = (52!)^2` and
    `64 · # > (52!)^2`; for `n ≥ 1` the `v10Sym` case follows from `4420^n`, since
    `64^(n+1) ≤ 4420^n` (from `64^2 ≤ 4420`). -/
theorem fullTrail_card_le_64_of_check (hKC : Check3 KC LKC) (hKS : Check3 KS LKS)
    (σ : Relabel) (h1 : σ ≠ 1) (n : ℕ) (hn : 0 < n) {y : Fin 52 → Nat} (hy : IsDeck y) :
    64 ^ (n + 1) * (univ.filter fun L : Fin (n + 2) → Key => FullTrail σ n y L).card ≤
      Nat.factorial 52 ^ (n + 2) := by
  by_cases hs : ∃ a x, σ = v10Sym a x
  · obtain ⟨a, x, rfl⟩ := hs
    have h := fullTrail_card_le_4420_v10Sym_of_check hKC hKS a x (ne_zero_of_ne_one h1 rfl) n hy
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    refine le_trans (Nat.mul_le_mul_right _ ?_) h
    rw [show m + 1 + 1 = m + 2 from rfl, pow_add, pow_succ]
    calc 64 ^ m * 64 ^ 2 = 4096 * 64 ^ m := by ring
      _ ≤ 4420 * 4420 ^ m := Nat.mul_le_mul (by norm_num) (Nat.pow_le_pow_left (by norm_num) m)
      _ = 4420 ^ m * 4420 := by ring
  · exact fullTrail_card_le_64_of_not_v10Sym σ hs n hy

/-! ## D. The full-cipher relabelling differential (independent keys): structure only -/

/-- The ciphertext pair of `(y, α·y)` under `encryptL n _ L` has difference `γ`. -/
def FullDiff (α γ : Relabel) (n : ℕ) (y : Fin 52 → Nat) (L : Fin (n + 2) → Key) : Prop :=
  encryptL n (rel α y) L = rel γ (encryptL n y L)

instance (α γ : Relabel) (n : ℕ) (y : Fin 52 → Nat) : DecidablePred (FullDiff α γ n y) :=
  fun _ => inferInstanceAs (Decidable (_ = _))

/-- Key tuples `L` (all `(52!)^(n+2)` of them: independent uniform keys, including the
    whitening and the final key) for which the full-cipher differential `α → γ` holds. -/
def fullDiffCount (α γ : Relabel) (n : ℕ) (y : Fin 52 → Nat) : ℕ :=
  (univ.filter fun L : Fin (n + 2) → Key => FullDiff α γ n y L).card

/-- (PROVED) The Markov step through the final round:
    `fullDiffCount α γ n y = 52! · ∑ β, diffCount α β n y · dpFCount β γ`. The factor `52!` is
    the final Compose key, which never changes the difference. -/
theorem fullDiffCount_eq (α γ : Relabel) (n : ℕ) {y : Fin 52 → Nat} (hy : IsDeck y) :
    fullDiffCount α γ n y =
      Nat.factorial 52 * ∑ β, diffCount α β n y * dpFCount β γ := by
  have h := card_filter_keys (n := n) (fun K k _ =>
    unkeyedNoMix (composeVec 52 Nat (rounds n (rel α y) K) k) =
      rel γ (unkeyedNoMix (composeVec 52 Nat (rounds n y K) k)))
  simp only at h
  unfold fullDiffCount FullDiff
  rw [filter_congr (fun L _ => by rw [encryptL_eq, encryptL_eq, finalRound_rel_iff]), h,
    sum_const, card_univ, Fintype.card_perm, Fintype.card_fin, smul_eq_mul]
  refine congrArg (Nat.factorial 52 * ·) ?_
  -- each `K`: the pair after the mix rounds is `(z, β_K·z)`
  set z := fun K : Fin n → Key => rounds n y K
  set g := fun K : Fin n → Key => relDiff (z K) (rounds n (rel α y) K)
  have hz : ∀ K, IsDeck (z K) := fun K => isDeck_rounds n y K hy
  have hz' : ∀ K, IsDeck (rounds n (rel α y) K) := fun K => isDeck_rounds n _ K (isDeck_rel α hy)
  have hg : ∀ K, rounds n (rel α y) K = rel (g K) (z K) :=
    fun K => (rel_relDiff (hz K) (hz' K)).symm
  rw [sum_card_filter_comm (ι := Fin n → Key) (fun K k =>
    unkeyedNoMix (composeVec 52 Nat (rounds n (rel α y) K) k) =
      rel γ (unkeyedNoMix (composeVec 52 Nat (rounds n y K) k)))]
  have hK : ∀ K, (univ.filter fun k : Key =>
      unkeyedNoMix (composeVec 52 Nat (rounds n (rel α y) K) k) =
        rel γ (unkeyedNoMix (composeVec 52 Nat (rounds n y K) k))).card = dpFCount (g K) γ := by
    intro K
    rw [show (univ.filter fun k : Key =>
        unkeyedNoMix (composeVec 52 Nat (rounds n (rel α y) K) k) =
          rel γ (unkeyedNoMix (composeVec 52 Nat (rounds n y K) k))) =
        univ.filter fun k : Key =>
          unkeyedNoMix (rel (g K) (composeVec 52 Nat (z K) k)) =
            rel γ (unkeyedNoMix (composeVec 52 Nat (z K) k)) from
      filter_congr fun k _ => by rw [hg K, compose_rel]]
    exact card_keys_compose (fun w => unkeyedNoMix (rel (g K) w) = rel γ (unkeyedNoMix w)) (hz K)
  rw [sum_congr rfl (fun K _ => hK K), sum_comp_fiber g (fun β => dpFCount β γ)]
  refine sum_congr rfl fun β _ => ?_
  have e : (univ.filter fun K : Fin n → Key => g K = β) =
      univ.filter fun K : Fin n → Key => Diff α β n y K :=
    filter_congr fun K _ => by
      rw [relDiff_eq_iff (hz K) (hz' K), eq_comm]
      rfl
  rw [e]
  rfl

/-- (PROVED) Zero mix rounds (whitening, final round):
    `fullDiffCount α γ 0 y = 52! · dpFCount α γ`. -/
theorem fullDiffCount_zero (α γ : Relabel) {y : Fin 52 → Nat} (hy : IsDeck y) :
    fullDiffCount α γ 0 y = Nat.factorial 52 * dpFCount α γ := by
  rw [fullDiffCount_eq α γ 0 hy]
  refine congrArg (Nat.factorial 52 * ·) ?_
  simp only [Differential.diffCount_zero _ _ hy, ite_mul, one_mul, zero_mul, sum_ite_eq,
    mem_univ, if_true]

/-- (PROVED) Single entries CAN rise through the final round (at `n = 0`; nothing is proved
    or measured for `n ≥ 1`): for `α` outside `v10Sym` some `γ ≠ α` has a larger full-cipher
    count than `(52!)^2` times its `0`-round count (which is `0`). Proof: the row of
    `dpFCount α` sums to `52!` but its diagonal is at most `52!/64`. -/
theorem exists_fullDiffCount_zero_gt (α : Relabel) (h : ¬ ∃ a x, α = v10Sym a x)
    {y : Fin 52 → Nat} (hy : IsDeck y) :
    ∃ γ, γ ≠ α ∧ Nat.factorial 52 ^ 2 * diffCount α γ 0 y < fullDiffCount α γ 0 y := by
  by_contra hne
  push_neg at hne
  have h0 : ∀ γ ∈ univ, γ ≠ α → dpFCount α γ = 0 := fun γ _ hγ => by
    have hle := hne γ hγ
    rw [fullDiffCount_zero α γ hy, Differential.diffCount_zero α γ hy, if_neg (Ne.symm hγ),
      mul_zero, Nat.le_zero, Nat.mul_eq_zero] at hle
    exact hle.resolve_left (Nat.factorial_ne_zero 52)
  have hs := sum_dpFCount α
  rw [sum_eq_single α h0 (fun h => absurd (mem_univ α) h)] at hs
  have h64 := dpFCount_self_le_64 α h
  have hpos := Nat.factorial_pos 52
  omega

/-- (PROVED) Max monotonicity: the final round never raises the LARGEST differential count,
    `fullDiffCount α γ n y ≤ (52!)^2 · max_β diffCount α β n y` (the one-step matrix is doubly
    stochastic, `sum_dpFCount_left`). This gives NO number (no numeric bound on
    `diffCount` is proved), and it does NOT say `fullDiffCount α γ ≤ (52!)^2 · diffCount α γ`:
    single entries can rise (at `n = 0`, `exists_fullDiffCount_zero_gt`). -/
theorem fullDiffCount_le_sup (α γ : Relabel) (n : ℕ) {y : Fin 52 → Nat} (hy : IsDeck y) :
    fullDiffCount α γ n y ≤
      Nat.factorial 52 ^ 2 * univ.sup (fun β => diffCount α β n y) := by
  rw [fullDiffCount_eq α γ n hy]
  calc Nat.factorial 52 * ∑ β, diffCount α β n y * dpFCount β γ
      ≤ Nat.factorial 52 * ∑ β, univ.sup (fun β => diffCount α β n y) * dpFCount β γ :=
        Nat.mul_le_mul_left _ (sum_le_sum fun β _ =>
          Nat.mul_le_mul_right _ (le_sup (f := fun β => diffCount α β n y) (mem_univ β)))
    _ = Nat.factorial 52 ^ 2 * univ.sup (fun β => diffCount α β n y) := by
        rw [← mul_sum, sum_dpFCount_left]
        ring

/-- (PROVED) The `v10Sym a x` output column is transparent: the full-cipher count into
    `v10Sym a x` is exactly `(52!)^2` times the `n`-round count (the final round gives no
    extra factor, and `K_6` never changes a relabelling difference). -/
theorem fullDiffCount_v10Sym (α : Relabel) (a : Fin 13) (x : Fin 4) (n : ℕ) {y : Fin 52 → Nat}
    (hy : IsDeck y) :
    fullDiffCount α (v10Sym a x) n y = Nat.factorial 52 ^ 2 * diffCount α (v10Sym a x) n y := by
  rw [fullDiffCount_eq _ _ n hy, sum_eq_single (v10Sym a x)
    (fun β _ hβ => by rw [dpFCount_to_v10Sym a x hβ, mul_zero])
    (fun h => absurd (mem_univ _) h), dpFCount_v10Sym, if_pos rfl]
  ring

/-- The `v10Sym` cluster through the whole cipher: the difference is some `v10Sym` after every
    mix round (`StaysInV10`) AND after the final round. -/
def FullStaysInV10 (a : Fin 13) (x : Fin 4) (n : ℕ) (y : Fin 52 → Nat)
    (L : Fin (n + 2) → Key) : Prop :=
  StaysInV10 n (v10Sym a x) y (roundKeysOf L) ∧ ∃ (a' : Fin 13) (x' : Fin 4),
    FullDiff (v10Sym a x) (v10Sym a' x') n y L

/-- (PROVED) The final-round condition is automatic: `FullStaysInV10` is `StaysInV10` on the
    mix-round keys. -/
theorem fullStaysInV10_iff (a : Fin 13) (x : Fin 4) (n : ℕ) {y : Fin 52 → Nat} (hy : IsDeck y)
    (L : Fin (n + 2) → Key) :
    FullStaysInV10 a x n y L ↔ StaysInV10 n (v10Sym a x) y (roundKeysOf L) := by
  refine ⟨fun h => h.1, fun h => ⟨h, a, x, ?_⟩⟩
  have ht := (staysInV10_iff_trail a x n y (roundKeysOf L) hy).1 h
  unfold FullDiff
  rw [encryptL_eq, encryptL_eq, trail_rounds_rel _ n y _ ht]
  exact (finalRound_rel_self_iff _ _ _ _).2
    (sumRanksChar_v10Sym a x (isDeck_compose (isDeck_rounds n y _ hy) _).1)

open Classical in
/-- (PROVED) The full-cipher cluster count is exactly `(52!)^2` times the `n`-round one: the
    final round gives no extra factor. -/
theorem card_fullStaysInV10 (a : Fin 13) (x : Fin 4) (n : ℕ) {y : Fin 52 → Nat} (hy : IsDeck y) :
    (univ.filter fun L : Fin (n + 2) → Key => FullStaysInV10 a x n y L).card =
      Nat.factorial 52 ^ 2 *
        (univ.filter fun K : Fin n → Key => StaysInV10 n (v10Sym a x) y K).card := by
  rw [filter_congr (fun L _ => fullStaysInV10_iff a x n hy L)]
  rw [card_filter_keys (n := n) (fun K _ _ => StaysInV10 n (v10Sym a x) y K)]
  simp only [sum_const, card_univ, Fintype.card_perm, Fintype.card_fin, smul_eq_mul]
  ring

open Classical in
/-- (PROVED; no hypothesis beyond `(a, x) ≠ (0, 0)`) Whole cipher, independent uniform keys:
    `26^n · # ≤ (52!)^(n+2)` for the `v10Sym` cluster. Only paths inside `v10Sym`; NOT a bound
    on the differential. -/
theorem fullStaysInV10_card_le_26 (a : Fin 13) (x : Fin 4) (hne : ¬ (a = 0 ∧ x = 0)) (n : ℕ)
    {y : Fin 52 → Nat} (hy : IsDeck y) :
    26 ^ n * (univ.filter fun L : Fin (n + 2) → Key => FullStaysInV10 a x n y L).card ≤
      Nat.factorial 52 ^ (n + 2) :=
  pow_mul_le_of_le_sq_mul (card_fullStaysInV10 a x n hy).le
    (Differential.staysInV10_card_le_26 a x hne n hy)

open Classical in
/-- (PROVED, given the two finite GridCycle checks as hypotheses) As
    `fullStaysInV10_card_le_26` with `4420^n` (`(a, x) ≠ (0, 0)`). -/
theorem fullStaysInV10_card_le_4420_of_check (hKC : Check3 KC LKC) (hKS : Check3 KS LKS)
    (a : Fin 13) (x : Fin 4) (hne : ¬ (a = 0 ∧ x = 0)) (n : ℕ) {y : Fin 52 → Nat}
    (hy : IsDeck y) :
    4420 ^ n * (univ.filter fun L : Fin (n + 2) → Key => FullStaysInV10 a x n y L).card ≤
      Nat.factorial 52 ^ (n + 2) :=
  pow_mul_le_of_le_sq_mul (card_fullStaysInV10 a x n hy).le
    (Differential.staysInV10_card_le_4420_of_check hKC hKS a x hne n hy)

/-! ## E. The real PassKey schedule: the proof's first mix round (key `K_0`) only -/

/-- (PROVED) Real schedule: following the characteristic through the whole cipher is a
    sub-event of following it through the 5 mix rounds (`RealSchedule`'s event). -/
theorem card_realFullTrail_le (σ : Relabel) (y : Fin 52 → Nat) :
    (univ.filter fun π : Equiv.Perm (Fin 52) => FullTrail σ 5 y (realKeys π)).card ≤
      (univ.filter fun π : Equiv.Perm (Fin 52) => Trail σ 5 y (roundKeys 5 π)).card :=
  card_le_card (monotone_filter_right _ fun _ h => h.1)

/-- (PROVED, unconditional) Real schedule, uniform master key, every `σ ≠ 1`, every deck `y`:
    at most `52!/26` master keys make `(y, σ·y)` follow the characteristic through the WHOLE
    cipher. This is M5's bound for the proof's first mix round (key `K_0`) alone; the proof's
    later mix rounds and its finalRound step add no factor (a limit of the proof, not a
    measured weakness). -/
theorem realFullTrail_card_le_26 (σ : Relabel) (h1 : σ ≠ 1) {y : Fin 52 → Nat} (hy : IsDeck y) :
    26 * (univ.filter fun π : Equiv.Perm (Fin 52) => FullTrail σ 5 y (realKeys π)).card ≤
      Nat.factorial 52 :=
  (Nat.mul_le_mul_left _ (card_realFullTrail_le σ y)).trans
    (RealSchedule.realTrail_card_le_26 σ h1 5 (by norm_num) y hy)

/-- (PROVED, unconditional) As `realFullTrail_card_le_26` with `52!/64`, for `σ` outside
    `v10Sym`. The bound of the proof's first mix round. -/
theorem realFullTrail_card_le_64_of_not_v10Sym (σ : Relabel) (h : ¬ ∃ a x, σ = v10Sym a x)
    {y : Fin 52 → Nat} (hy : IsDeck y) :
    64 * (univ.filter fun π : Equiv.Perm (Fin 52) => FullTrail σ 5 y (realKeys π)).card ≤
      Nat.factorial 52 :=
  (Nat.mul_le_mul_left _ (card_realFullTrail_le σ y)).trans
    (RealSchedule.realTrail_card_le_64_of_not_v10Sym σ h 5 (by norm_num) y hy)

/-- (PROVED, given the two finite GridCycle checks as hypotheses) As
    `realFullTrail_card_le_26` with `52!/64`, for every `σ ≠ 1`. The bound of the proof's
    first mix round. -/
theorem realFullTrail_card_le_64_of_check (hKC : Check3 KC LKC) (hKS : Check3 KS LKS)
    (σ : Relabel) (h1 : σ ≠ 1) {y : Fin 52 → Nat} (hy : IsDeck y) :
    64 * (univ.filter fun π : Equiv.Perm (Fin 52) => FullTrail σ 5 y (realKeys π)).card ≤
      Nat.factorial 52 :=
  (Nat.mul_le_mul_left _ (card_realFullTrail_le σ y)).trans
    (RealSchedule.realTrail_card_le_64_of_check hKC hKS σ h1 5 (by norm_num) y hy)

open Classical in
/-- (PROVED; no hypothesis beyond `(a, x) ≠ (0, 0)`) Real schedule, whole cipher, `v10Sym`
    cluster: at most `52!/26` master keys. The bound of the proof's first mix round; only
    paths inside `v10Sym`. -/
theorem realFullStaysInV10_card_le_26 (a : Fin 13) (x : Fin 4) (hne : ¬ (a = 0 ∧ x = 0))
    {y : Fin 52 → Nat} (hy : IsDeck y) :
    26 * (univ.filter fun π : Equiv.Perm (Fin 52) => FullStaysInV10 a x 5 y (realKeys π)).card ≤
      Nat.factorial 52 := by
  rw [filter_congr (fun π _ => fullStaysInV10_iff a x 5 hy (realKeys π))]
  exact Differential.realStaysInV10_card_le_26 a x hne 5 (by norm_num) hy

open Classical in
/-- (PROVED, given the two finite GridCycle checks as hypotheses) As
    `realFullStaysInV10_card_le_26` with `52!/4420` (`(a, x) ≠ (0, 0)`). The first mix
    round's bound. -/
theorem realFullStaysInV10_card_le_4420_of_check (hKC : Check3 KC LKC) (hKS : Check3 KS LKS)
    (a : Fin 13) (x : Fin 4) (hne : ¬ (a = 0 ∧ x = 0)) {y : Fin 52 → Nat} (hy : IsDeck y) :
    4420 * (univ.filter fun π : Equiv.Perm (Fin 52) => FullStaysInV10 a x 5 y (realKeys π)).card ≤
      Nat.factorial 52 := by
  rw [filter_congr (fun π _ => fullStaysInV10_iff a x 5 hy (realKeys π))]
  exact Differential.realStaysInV10_card_le_4420_of_check hKC hKS a x hne 5 (by norm_num) hy

/-- (PROVED) The emitted program follows: if `(ofDeck message, σ·ofDeck message)` follows the
    characteristic through the whole cipher under master key `π`, then the emitted
    `Doubledeal.encrypt` maps the `σ`-relabelled message to the `σ`-relabelled ciphertext. -/
theorem generated_encrypt_of_realFullTrail (σ : Relabel) (message : List Nat)
    (hm : message.length = 52) (hc : ∀ x ∈ message, x < 52) (π : Equiv.Perm (Fin 52))
    (h : FullTrail σ 5 (ofDeck message hm) (realKeys π)) :
    Doubledeal.encrypt (Link2.embed (message.map σ.app)) (Link2.embed (masterList π)) =
      .ok (Link2.embed ((encryptDeck message (masterList π)).map σ.app)) := by
  rw [generated_encrypt_rel_iff σ σ message _ hm (perm52_masterList π) hc,
    encryptDeckFn_masterList_eq, encryptDeckFn_masterList_eq]
  exact fullTrail_encryptL h

/-- (PROVED) The emitted program, `v10Sym` cluster: under `FullStaysInV10`, the emitted
    `Doubledeal.encrypt` maps the `v10Sym a x`-relabelled message to the ciphertext relabelled
    by some `v10Sym a' x'`. -/
theorem generated_encrypt_of_realFullStaysInV10 (a : Fin 13) (x : Fin 4) (message : List Nat)
    (hm : message.length = 52) (hc : ∀ c ∈ message, c < 52) (π : Equiv.Perm (Fin 52))
    (h : FullStaysInV10 a x 5 (ofDeck message hm) (realKeys π)) :
    ∃ (a' : Fin 13) (x' : Fin 4),
      Doubledeal.encrypt (Link2.embed (message.map (v10Sym a x).app)) (Link2.embed (masterList π)) =
        .ok (Link2.embed ((encryptDeck message (masterList π)).map (v10Sym a' x').app)) := by
  obtain ⟨a', x', hd⟩ := h.2
  refine ⟨a', x', ?_⟩
  rw [generated_encrypt_rel_iff _ _ message _ hm (perm52_masterList π) hc,
    encryptDeckFn_masterList_eq, encryptDeckFn_masterList_eq]
  exact hd

end DoubleDeal.Security.FullCipher
