/-
  A linear analogue of the differential structure, for key-alternating ciphers on decks with
  INDEPENDENT UNIFORM full-permutation keys (roadmap milestone M8a; security README,
  "Roadmap"). Note and toy check: `../analysis/v12-linear/NOTES.md`.

  NO NUMERIC BOUND IS PROVED HERE. Read this before citing anything below.

  Generality. L1 and the final-key step are proved for arbitrary layers that send decks to
  decks. L2–L4 are proved for DoubleDeal's encryptL; their proofs use only independent
  uniform keys, layers sending decks to decks and, for L4, injective layers. Formally: L1
  (`sumSqCorrLayer_eq`) and the final-key step (`sum_sq_corr_finalKey`) take the layer
  (family) as an argument, with only the hypothesis that it maps decks to decks. L2–L4 are
  stated for `FullCipher.encryptL` only; the facts about its layers that they use are the
  generic `Differential.dpCount_one_left` (decks to decks) and `Differential.dpCount_to_one`
  (hypothesis `Function.Injective U`; L4 only), applied to DoubleDeal's layers, together
  with `FullCipher.fullDiffCount_eq_of_isDeck` and
  `FullCipher.fullDiffCount_eq_card_beforeFinal`. L2–L4 are not stated for other ciphers
  here; for non-injective layers the same-shape L4 (and `fullDiffCount_to_one`) can fail. The
  cipher enters only through the differential counts (`Differential.dpCount`,
  `FullCipher.fullDiffCount`, `Differential.diffCount`, `FullCipher.dpFCount`), which are
  themselves not bounded here.
  Key schedule. The statements are stated only for independent uniform keys; nothing is
  proved for the real PassKey schedule (`RealSchedule`), and a dependent toy schedule shows
  the same-shape equation can fail (the note's 4-card toy check; a toy, not the PassKey
  schedule).

  Definitions (generic before specific, as in `Differential`). A deck function
  `f : (Fin 52 → Nat) → ℤ` (only its values on the `52!` decks `permDeck π` are used). For a
  deck map `E`, the unnormalised correlation is `corr E f g = ∑_x f(x) · g(E x)` over all
  decks `x`, and the autocorrelation of `f` at a relabelling `α` is
  `autoCorr f α = ∑_x f(x) · f(α·x)`. `sumSqCorrLayer U f g` sums `corr ^ 2` of the keyed
  layer `x ↦ U(x ∘ k₁) ∘ k₂` over all key pairs `(k₁, k₂)`; `fullCorr n f g L` is `corr` of
  `encryptL n _ L`, and `fullSumSqCorr n f g` sums `fullCorr ^ 2` over all `(52!)^(n+2)` key
  tuples. These are key-SUMMED and UNNORMALISED; the normalised quantity is not defined in
  Lean (all statements are integer identities).
  Remark (not a theorem): the key-averaged normalised squared correlation would be
  `E_L[ĉ²] = fullSumSqCorr n f g / ((52!)^(n+2) · autoCorr f 1 · autoCorr g 1)`
  (f, g not identically zero on decks); under it, L4 reads as `1/52!` plus the `α, β ≠ 1`
  remainder over `(52!)^(n+3) · A_f(1) · A_g(1)`.

  Proved (headlines L1–L4):
  * L1 `sumSqCorrLayer_eq`: one keyed layer, any deck map `U` sending decks to decks,
    `sumSqCorrLayer U f g = ∑_α ∑_β autoCorr f α · dpCount U α β · autoCorr g β`.
  * L2 `fullSumSqCorr_eq`: the whole of `encryptL n`, for any deck `y`,
    `52! · fullSumSqCorr n f g = ∑_α ∑_β autoCorr f α · fullDiffCount α β n y · autoCorr g β`
    (uses `FullCipher.fullDiffCount_eq_of_isDeck`).
  * L3 `fullSumSqCorr_eq_final`: the proof's finalRound step acts on the output side through
    `dpFCount`: `fullSumSqCorr n f g = ∑_α ∑_β autoCorr f α · diffCount α β n y ·
    ∑_γ dpFCount β γ · autoCorr g γ`.
  * L4 `fullSumSqCorr_split`: the trivial difference separates off:
    `52! · fullSumSqCorr n f g = (52!)^(n+2) · autoCorr f 1 · autoCorr g 1 +
    ∑_{α ≠ 1} ∑_{β ≠ 1} autoCorr f α · fullDiffCount α β n y · autoCorr g β`
    (uses `FullCipher.fullDiffCount_one_left`, `FullCipher.fullDiffCount_to_one`; the latter
    needs injective layers). `autoCorr f 1 = ∑ f²` (`autoCorr_one`). The first term does not
    depend on the layers; every layer-dependent part is in the second, through
    `fullDiffCount` with `α ≠ 1`, `β ≠ 1`. The split is an identity only.
  Helper used by L1 and L2: `sum_sq_corr_finalKey` (the final-key step, for any family of
  deck maps sending decks to decks, followed by an independent uniform final Compose key).

  NOT proved, and limits; read before citing:
  * Any numeric bound on any correlation, squared-correlation sum or potential. L1–L4 are
    identities; they move the question to the differential counts, for which no numeric
    bound is proved (M6/M7).
  * Anything under the real PassKey schedule, and anything per key: every statement sums
    over ALL keys with independent uniform full-permutation keys.
  * L2–L4 for any cipher other than DoubleDeal's `encryptL` (see "Generality").
  Not a bit-security claim.
-/
import DoubleDealSecurity.FullCipher

namespace DoubleDeal.Security.Linear

open DoubleDeal Relabel Finset
open DoubleDeal.Security (Key isDeck_compose isDeck_rel isDeck_unkeyedNoMix composeVec_inj)
open DoubleDeal.Security.TrailBound (rounds isDeck_rounds card_keys_compose compose_permDeck
  card_filter_snoc rel_permDeck sum_keys_compose)
open DoubleDeal.Security.Differential (diffCount relDiff rel_relDiff relDiff_eq_iff dpCount)
open DoubleDeal.Security.FullCipher (encryptL FullDiff fullDiffCount dpFCount fullDiffCount_eq
  fullDiffCount_eq_of_isDeck fullDiffCount_one_left fullDiffCount_to_one sum_comp_fiber
  beforeFinal encryptL_snoc isDeck_beforeFinal fullDiffCount_eq_card_beforeFinal)

/-! ## Definitions -/

/-- The unnormalised correlation of an input function `f` and an output function `g`
    through a deck map `E`: `∑_x f(x) · g(E x)` over all `52!` decks `x`. -/
def corr (E : (Fin 52 → Nat) → Fin 52 → Nat) (f g : (Fin 52 → Nat) → ℤ) : ℤ :=
  ∑ π : Equiv.Perm (Fin 52), f (permDeck π) * g (E (permDeck π))

/-- The autocorrelation of `f` at the relabelling `α`: `∑_x f(x) · f(α·x)` over all decks. -/
def autoCorr (f : (Fin 52 → Nat) → ℤ) (α : Relabel) : ℤ :=
  ∑ π : Equiv.Perm (Fin 52), f (permDeck π) * f (rel α (permDeck π))

/-- One keyed layer: Compose with `k₁`, the deck map `U`, Compose with `k₂`. -/
def keyedLayer (U : (Fin 52 → Nat) → Fin 52 → Nat) (k₁ k₂ : Key) (x : Fin 52 → Nat) :
    Fin 52 → Nat :=
  composeVec 52 Nat (U (composeVec 52 Nat x k₁)) k₂

/-- The squared correlation of `f` and `g` through one keyed layer, summed over all `(52!)^2`
    independent key pairs `(k₁, k₂)`. -/
def sumSqCorrLayer (U : (Fin 52 → Nat) → Fin 52 → Nat) (f g : (Fin 52 → Nat) → ℤ) : ℤ :=
  ∑ k₁ : Key, ∑ k₂ : Key, corr (keyedLayer U k₁ k₂) f g ^ 2

/-- The correlation of `f` and `g` through `encryptL n _ L` (one key tuple `L`). -/
def fullCorr (n : ℕ) (f g : (Fin 52 → Nat) → ℤ) (L : Fin (n + 2) → Key) : ℤ :=
  corr (fun x => encryptL n x L) f g

/-- The squared correlation through `encryptL n`, summed over all `(52!)^(n+2)` key tuples
    (independent uniform keys, the whitening and the final key included). -/
def fullSumSqCorr (n : ℕ) (f g : (Fin 52 → Nat) → ℤ) : ℤ :=
  ∑ L : Fin (n + 2) → Key, fullCorr n f g L ^ 2

/-! ## Summation helpers -/

/-- (PROVED) The final Compose key averages a pair with difference `β` into `autoCorr g β`. -/
theorem sum_keys_final (g : (Fin 52 → Nat) → ℤ) (β : Relabel) {z : Fin 52 → Nat}
    (hz : IsDeck z) :
    ∑ k : Key, g (composeVec 52 Nat z k) * g (composeVec 52 Nat (rel β z) k) = autoCorr g β :=
  sum_keys_compose (fun w => g w * g (rel β w)) hz

/-- (PROVED) `autoCorr f 1 = ∑_x f(x)^2`. -/
theorem autoCorr_one (f : (Fin 52 → Nat) → ℤ) :
    autoCorr f 1 = ∑ π : Equiv.Perm (Fin 52), f (permDeck π) ^ 2 := by
  simp only [autoCorr, rel_one, sq]

/-- (PROVED) A squared correlation as a double sum over (deck, difference):
    `corr E f g ^ 2 = ∑_x ∑_α f(x) f(α·x) · g(E x) g(E (α·x))`. -/
theorem corr_sq (E : (Fin 52 → Nat) → Fin 52 → Nat) (f g : (Fin 52 → Nat) → ℤ) :
    corr E f g ^ 2 = ∑ π : Equiv.Perm (Fin 52), ∑ α : Relabel,
      f (permDeck π) * f (rel α (permDeck π)) *
        (g (E (permDeck π)) * g (E (rel α (permDeck π)))) := by
  rw [sq, corr, sum_mul_sum]
  refine sum_congr rfl fun π _ => ?_
  rw [← Fintype.sum_equiv (Equiv.mulRight π) (fun α => f (permDeck π) * g (E (permDeck π)) *
    (f (permDeck (α * π)) * g (E (permDeck (α * π))))) _ fun _ => rfl]
  refine sum_congr rfl fun α _ => ?_
  rw [rel_permDeck]
  ring

/-- (PROVED) If the inner count `C α β` does not depend on the deck, the double sum over
    (deck, difference) collapses to autocorrelations. -/
theorem sum_autoCorr_left (f : (Fin 52 → Nat) → ℤ) (G : Relabel → ℤ) :
    ∑ π : Equiv.Perm (Fin 52), ∑ α : Relabel, f (permDeck π) * f (rel α (permDeck π)) * G α =
      ∑ α, autoCorr f α * G α := by
  rw [sum_comm]
  exact sum_congr rfl fun α _ => by rw [autoCorr, sum_mul]

/-- (PROVED) Reordering four finite sums. -/
theorem sum_comm4 {A B C D M : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [AddCommMonoid M] (T : A → B → C → D → M) :
    ∑ a, ∑ b, ∑ c, ∑ d, T a b c d = ∑ c, ∑ d, ∑ a, ∑ b, T a b c d :=
  (sum_congr rfl fun _ _ => sum_comm.trans (sum_congr rfl fun _ _ => sum_comm)).trans
    (sum_comm.trans (sum_congr rfl fun _ _ => sum_comm))

/-! ## The final-key step (arbitrary layers sending decks to decks): a uniform final key -/

/-- (PROVED) For any family `H i` (`i` in a finite type) of deck maps sending decks to decks,
    followed by an independent uniform final Compose key `kF`:
    `∑_i ∑_kF corr² = ∑_x ∑_α f(x) f(α·x) ∑_β #{i | H i (α·x) = β · H i x} · autoCorr g β`.
    Proved for arbitrary layer families (only `hH`: decks to decks). -/
theorem sum_sq_corr_finalKey {ι : Type} [Fintype ι]
    (H : ι → (Fin 52 → Nat) → Fin 52 → Nat)
    (hH : ∀ i {x : Fin 52 → Nat}, IsDeck x → IsDeck (H i x)) (f g : (Fin 52 → Nat) → ℤ) :
    ∑ i, ∑ kF : Key, corr (fun x => composeVec 52 Nat (H i x) kF) f g ^ 2 =
      ∑ π : Equiv.Perm (Fin 52), ∑ α : Relabel, f (permDeck π) * f (rel α (permDeck π)) *
        ∑ β : Relabel, ((univ.filter fun i =>
          H i (rel α (permDeck π)) = rel β (H i (permDeck π))).card : ℤ) * autoCorr g β := by
  simp only [corr_sq]
  -- bring the (deck, difference) sums outside
  refine (sum_comm4 _).trans ?_
  refine sum_congr rfl fun π _ => sum_congr rfl fun α _ => ?_
  simp only [← mul_sum]
  congr 1
  set x := permDeck π
  have hx : IsDeck x := isDeck_permDeck π
  -- the difference after `H i`
  set b := fun i => relDiff (H i x) (H i (rel α x))
  have hb : ∀ i, H i (rel α x) = rel (b i) (H i x) :=
    fun i => (rel_relDiff (hH i hx) (hH i (isDeck_rel α hx))).symm
  rw [sum_congr rfl fun i _ => by rw [hb i, sum_keys_final g (b i) (hH i hx)],
    sum_comp_fiber b (autoCorr g)]
  refine sum_congr rfl fun β _ => ?_
  congr 3
  exact filter_congr fun i _ => by
    rw [relDiff_eq_iff (hH i hx) (hH i (isDeck_rel α hx)), eq_comm]

/-! ## L1: one keyed layer -/

/-- (PROVED) L1. One keyed layer `x ↦ U(x ∘ k₁) ∘ k₂` with independent uniform keys, for any
    deck map `U` sending decks to decks:
    `sumSqCorrLayer U f g = ∑_α ∑_β autoCorr f α · dpCount U α β · autoCorr g β`.
    An identity only; no numeric bound. -/
theorem sumSqCorrLayer_eq (U : (Fin 52 → Nat) → Fin 52 → Nat)
    (hU : ∀ {x : Fin 52 → Nat}, IsDeck x → IsDeck (U x)) (f g : (Fin 52 → Nat) → ℤ) :
    sumSqCorrLayer U f g = ∑ α, ∑ β, autoCorr f α * (dpCount U α β : ℤ) * autoCorr g β := by
  unfold sumSqCorrLayer keyedLayer
  rw [sum_sq_corr_finalKey (fun (k₁ : Key) x => U (composeVec 52 Nat x k₁))
    (fun k₁ _ hx => hU (isDeck_compose hx k₁)) f g]
  have hc : ∀ (π : Equiv.Perm (Fin 52)) (α β : Relabel),
      (univ.filter fun k₁ : Key => U (composeVec 52 Nat (rel α (permDeck π)) k₁) =
        rel β (U (composeVec 52 Nat (permDeck π) k₁))).card = dpCount U α β :=
    fun π α β => card_keys_compose (fun w => U (rel α w) = rel β (U w)) (isDeck_permDeck π)
  simp only [hc]
  rw [sum_autoCorr_left f (fun α => ∑ β, (dpCount U α β : ℤ) * autoCorr g β)]
  refine sum_congr rfl fun α _ => ?_
  rw [mul_sum]
  exact sum_congr rfl fun β _ => by ring

/-! ## L2: the whole of `encryptL n` -/

/-- (PROVED) L2. The whole of `encryptL n` with independent uniform keys (all `n + 2`,
    whitening and final key included), for any deck `y`:
    `52! · fullSumSqCorr n f g = ∑_α ∑_β autoCorr f α · fullDiffCount α β n y · autoCorr g β`.
    An identity only; no numeric bound. Stated only for independent uniform keys; nothing is
    proved for the real PassKey schedule. -/
theorem fullSumSqCorr_eq (n : ℕ) (f g : (Fin 52 → Nat) → ℤ) {y : Fin 52 → Nat} (hy : IsDeck y) :
    (Nat.factorial 52 : ℤ) * fullSumSqCorr n f g =
      ∑ α, ∑ β, autoCorr f α * (fullDiffCount α β n y : ℤ) * autoCorr g β := by
  unfold fullSumSqCorr fullCorr
  rw [← Fintype.sum_equiv (Fin.snocEquiv fun _ => Key) (fun p => corr
    (fun x => encryptL n x (Fin.snoc p.2 p.1)) f g ^ 2) _ fun _ => rfl,
    Fintype.sum_prod_type, sum_comm]
  simp only [encryptL_snoc]
  rw [sum_sq_corr_finalKey beforeFinal (fun K _ hx => isDeck_beforeFinal K hx) f g]
  -- the count of the keys before the final one does not depend on the deck
  have hc : ∀ (π : Equiv.Perm (Fin 52)) (α β : Relabel),
      (univ.filter fun K : Fin (n + 1) → Key =>
        beforeFinal K (rel α (permDeck π)) = rel β (beforeFinal K (permDeck π))).card =
      (univ.filter fun K : Fin (n + 1) → Key =>
        beforeFinal K (rel α y) = rel β (beforeFinal K y)).card := fun π α β =>
    Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos 52) (by
      rw [← fullDiffCount_eq_card_beforeFinal, ← fullDiffCount_eq_card_beforeFinal,
        fullDiffCount_eq_of_isDeck α β n (isDeck_permDeck π) hy])
  simp only [hc, fullDiffCount_eq_card_beforeFinal _ _ n y]
  rw [sum_autoCorr_left f, mul_sum]
  refine sum_congr rfl fun α _ => ?_
  simp only [mul_sum]
  exact sum_congr rfl fun β _ => by push_cast; ring

/-! ## L3: the proof's finalRound step on the output side -/

/-- (PROVED) L3. The proof's finalRound step (Compose `lastKeyOf L`, the stem, Compose
    `finalKeyOf L`) acts on the output autocorrelations through `dpFCount`, for any deck `y`:
    `fullSumSqCorr n f g = ∑_α ∑_β autoCorr f α · diffCount α β n y ·
      ∑_γ dpFCount β γ · autoCorr g γ`.
    An identity only; no numeric bound. -/
theorem fullSumSqCorr_eq_final (n : ℕ) (f g : (Fin 52 → Nat) → ℤ) {y : Fin 52 → Nat}
    (hy : IsDeck y) :
    fullSumSqCorr n f g = ∑ α, ∑ β, autoCorr f α * (diffCount α β n y : ℤ) *
      ∑ γ, (dpFCount β γ : ℤ) * autoCorr g γ := by
  have h := fullSumSqCorr_eq n f g hy
  simp only [fullDiffCount_eq _ _ n hy] at h
  have h0 : (Nat.factorial 52 : ℤ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero 52)
  refine mul_left_cancel₀ h0 (h.trans ?_)
  rw [mul_sum]
  refine sum_congr rfl fun α _ => ?_
  push_cast
  simp only [mul_sum, sum_mul]
  rw [sum_comm]
  exact sum_congr rfl fun β _ => sum_congr rfl fun γ _ => by ring

/-! ## L4: the trivial difference separates off -/

/-- (PROVED) L4. For any deck `y`, the trivial difference `1` contributes exactly
    `(52!)^(n+2) · autoCorr f 1 · autoCorr g 1`, and the rest involves only `α ≠ 1`, `β ≠ 1`:
    `52! · fullSumSqCorr n f g = (52!)^(n+2) · autoCorr f 1 · autoCorr g 1 +
      ∑_{α ≠ 1} ∑_{β ≠ 1} autoCorr f α · fullDiffCount α β n y · autoCorr g β`.
    An identity only; no numeric bound. -/
theorem fullSumSqCorr_split (n : ℕ) (f g : (Fin 52 → Nat) → ℤ) {y : Fin 52 → Nat}
    (hy : IsDeck y) :
    (Nat.factorial 52 : ℤ) * fullSumSqCorr n f g =
      (Nat.factorial 52 : ℤ) ^ (n + 2) * autoCorr f 1 * autoCorr g 1 +
        ∑ α ∈ univ.erase 1, ∑ β ∈ univ.erase 1,
          autoCorr f α * (fullDiffCount α β n y : ℤ) * autoCorr g β := by
  rw [fullSumSqCorr_eq n f g hy, ← add_sum_erase _ _ (mem_univ (1 : Relabel))]
  refine congrArg₂ (· + ·) ?_ ?_
  · rw [sum_eq_single (1 : Relabel) (fun β _ hβ => by
        rw [fullDiffCount_one_left β n hy, if_neg hβ]
        simp only [Nat.cast_zero, mul_zero, zero_mul])
      (fun h => absurd (mem_univ _) h),
      fullDiffCount_one_left 1 n hy, if_pos rfl]
    push_cast
    ring
  · refine sum_congr rfl fun α hα => ?_
    rw [← add_sum_erase _ _ (mem_univ (1 : Relabel)),
      fullDiffCount_to_one (ne_of_mem_erase hα) n hy]
    simp only [Nat.cast_zero, mul_zero, zero_mul, zero_add]

end DoubleDeal.Security.Linear
