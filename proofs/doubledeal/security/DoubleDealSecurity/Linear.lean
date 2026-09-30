/-
  A linear analogue of the differential structure, for key-alternating ciphers on decks with
  INDEPENDENT UNIFORM full-permutation keys (roadmap milestone M8a; security README,
  "Roadmap"). Note and toy check: `../analysis/v12-linear/NOTES.md`.

  NO NUMERIC BOUND IS PROVED HERE. Read this before citing anything below.

  What this is. The link below is GENERIC: it holds for ANY key-alternating cipher on the
  `52!` decks whose Compose keys are independent uniform permutations, the whitening key and
  the final key included, and whose unkeyed layers map decks to decks. Nothing in it uses
  SumRanks, GridCycle or any other DoubleDeal layer; the cipher enters only through the
  differential counts (`Differential.dpCount`, `FullCipher.fullDiffCount`,
  `Differential.diffCount`, `FullCipher.dpFCount`), which are themselves not bounded here.
  It does NOT apply to the real PassKey schedule (`RealSchedule`): there all keys are
  functions of one master key, and the proofs below need every key uniform and independent
  of the others. (The note's 4-card toy check has a dependent toy schedule for which the
  equation of the same shape as L2 fails; that is a toy, not the PassKey schedule.)

  Definitions. A deck function `f : (Fin 52 → Nat) → ℤ` (only its values on the `52!` decks
  `permDeck π` are used). For a deck map `E`, the unnormalised correlation is
  `corrOf E f g = ∑_x f(x) · g(E x)` over all decks `x`, and the autocorrelation of `f` at a
  relabelling `α` is `autoCorr f α = ∑_x f(x) · f(α·x)`. `sumSqCorrU U f g` sums
  `corrOf ^ 2` of the keyed layer `x ↦ U(x ∘ k₁) ∘ k₂` over all key pairs `(k₁, k₂)`;
  `sumSqCorr n f g` sums `corr ^ 2` of `encryptL n` over all `(52!)^(n+2)` key tuples.
  Dividing by the number of keys and by `(∑ f²)(∑ g²)` would give the usual key-averaged
  squared correlation; that normalised quantity is not defined in Lean (all statements are
  integer identities).

  Proved:
  * `sum_sq_corrOf_finalKey` (the generic step): for any family `H i` of deck maps that send
    decks to decks, each followed by a final Compose key `kF`, the squared correlation
    summed over all `i` and all `kF` is
    `∑_x ∑_α f(x) f(α·x) ∑_β #{i | H i (α·x) = β·H i x} · autoCorr g β`.
  * L1 `sumSqCorrU_eq`: one keyed layer,
    `sumSqCorrU U f g = ∑_α ∑_β autoCorr f α · dpCount U α β · autoCorr g β`.
  * L2 `sumSqCorr_eq`: the whole of `encryptL n`, for any deck `y`,
    `52! · sumSqCorr n f g = ∑_α ∑_β autoCorr f α · fullDiffCount α β n y · autoCorr g β`
    (uses `FullCipher.fullDiffCount_eq_of_isDeck`).
  * L3 `sumSqCorr_eq_final`: the proof's finalRound step acts on the output side through
    `dpFCount`: `sumSqCorr n f g = ∑_α ∑_β autoCorr f α · diffCount α β n y ·
    ∑_γ dpFCount β γ · autoCorr g γ`.
  * L4 `sumSqCorr_split`: the trivial difference separates off:
    `52! · sumSqCorr n f g = (52!)^(n+2) · autoCorr f 1 · autoCorr g 1 +
    ∑_{α ≠ 1} ∑_{β ≠ 1} autoCorr f α · fullDiffCount α β n y · autoCorr g β`
    (uses `FullCipher.fullDiffCount_one_left`, `FullCipher.fullDiffCount_to_one`).
    `autoCorr f 1 = ∑ f²` (`autoCorr_one`). The first term is the same for every cipher of
    this shape (it does not depend on the layers); every layer-dependent part is in the
    second, through `fullDiffCount` with `α ≠ 1`, `β ≠ 1`. The split is an identity only.

  NOT proved, and limits; read before citing:
  * Any numeric bound on any correlation, squared-correlation sum or potential. L1–L4 are
    identities; they move the question to the differential counts, for which no numeric
    bound is proved (M6/M7).
  * Anything under the real PassKey schedule, and anything per key: every statement sums
    over ALL keys with independent uniform full-permutation keys.
  * Any statement specific to DoubleDeal's layers: L1–L4 hold for every choice of unkeyed
    layers that map decks to decks.
  Not a bit-security claim.
-/
import DoubleDealSecurity.FullCipher

namespace DoubleDeal.Security.Linear

open DoubleDeal Relabel Finset
open DoubleDeal.Security (Key isDeck_compose isDeck_rel isDeck_unkeyedNoMix composeVec_inj)
open DoubleDeal.Security.TrailBound (rounds isDeck_rounds card_keys_compose compose_permDeck
  card_filter_snoc)
open DoubleDeal.Security.Differential (diffCount relDiff rel_relDiff relDiff_eq_iff dpCount)
open DoubleDeal.Security.FullCipher (encryptL encryptL_eq finalRound roundKeysOf lastKeyOf
  finalKeyOf FullDiff fullDiffCount dpFCount fullDiffCount_eq fullDiffCount_eq_of_isDeck
  fullDiffCount_one_left fullDiffCount_to_one)

/-! ## Definitions -/

/-- The unnormalised correlation of an input function `f` and an output function `g`
    through a deck map `E`: `∑_x f(x) · g(E x)` over all `52!` decks `x`. -/
def corrOf (E : (Fin 52 → Nat) → Fin 52 → Nat) (f g : (Fin 52 → Nat) → ℤ) : ℤ :=
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
def sumSqCorrU (U : (Fin 52 → Nat) → Fin 52 → Nat) (f g : (Fin 52 → Nat) → ℤ) : ℤ :=
  ∑ k₁ : Key, ∑ k₂ : Key, corrOf (keyedLayer U k₁ k₂) f g ^ 2

/-- The correlation of `f` and `g` through `encryptL n _ L` (one key tuple `L`). -/
def corr (n : ℕ) (f g : (Fin 52 → Nat) → ℤ) (L : Fin (n + 2) → Key) : ℤ :=
  corrOf (fun x => encryptL n x L) f g

/-- The squared correlation through `encryptL n`, summed over all `(52!)^(n+2)` key tuples
    (independent uniform keys, the whitening and the final key included). -/
def sumSqCorr (n : ℕ) (f g : (Fin 52 → Nat) → ℤ) : ℤ :=
  ∑ L : Fin (n + 2) → Key, corr n f g L ^ 2

/-! ## Summation helpers -/

theorem rel_permDeck (α π : Equiv.Perm (Fin 52)) : rel α (permDeck π) = permDeck (α * π) :=
  funext fun i => app_fin α (π i)

/-- (PROVED) Summing over `z ∘ k` for all keys `k` (`z` a deck) is summing over all decks. -/
theorem sum_keys_compose (F : (Fin 52 → Nat) → ℤ) {z : Fin 52 → Nat} (hz : IsDeck z) :
    ∑ k : Key, F (composeVec 52 Nat z k) = ∑ π : Equiv.Perm (Fin 52), F (permDeck π) := by
  set ρ := deckPerm z hz
  have hzρ : z = permDeck ρ := funext fun i => (deckPerm_val z hz i).symm
  rw [hzρ]
  exact Fintype.sum_equiv (Equiv.mulLeft ρ) _ _ fun _ => rfl

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
    `corrOf E f g ^ 2 = ∑_x ∑_α f(x) f(α·x) · g(E x) g(E (α·x))`. -/
theorem corrOf_sq (E : (Fin 52 → Nat) → Fin 52 → Nat) (f g : (Fin 52 → Nat) → ℤ) :
    corrOf E f g ^ 2 = ∑ π : Equiv.Perm (Fin 52), ∑ α : Relabel,
      f (permDeck π) * f (rel α (permDeck π)) *
        (g (E (permDeck π)) * g (E (rel α (permDeck π)))) := by
  rw [sq, corrOf, sum_mul_sum]
  refine sum_congr rfl fun π _ => ?_
  rw [← Fintype.sum_equiv (Equiv.mulRight π) (fun α => f (permDeck π) * g (E (permDeck π)) *
    (f (permDeck (α * π)) * g (E (permDeck (α * π))))) _ fun _ => rfl]
  refine sum_congr rfl fun α _ => ?_
  rw [rel_permDeck]
  ring

/-- (PROVED) Summing a function of `h i` over `i` by the fibres of `h` (integer values). -/
theorem sum_comp_fiber_int {ι : Type} [Fintype ι] (h : ι → Relabel) (F : Relabel → ℤ) :
    ∑ i, F (h i) = ∑ β, ((univ.filter fun i => h i = β).card : ℤ) * F β := by
  rw [← sum_fiberwise univ h (fun i => F (h i))]
  refine sum_congr rfl fun β _ => ?_
  rw [sum_congr rfl (fun i hi => by rw [(mem_filter.1 hi).2]), sum_const, nsmul_eq_mul]

/-- (PROVED) If the inner count `C α β` does not depend on the deck, the double sum over
    (deck, difference) collapses to autocorrelations. -/
theorem sum_autoCorr_left (f : (Fin 52 → Nat) → ℤ) (G : Relabel → ℤ) :
    ∑ π : Equiv.Perm (Fin 52), ∑ α : Relabel, f (permDeck π) * f (rel α (permDeck π)) * G α =
      ∑ α, autoCorr f α * G α := by
  rw [sum_comm]
  exact sum_congr rfl fun α _ => by rw [autoCorr, sum_mul]

/-- (PROVED) Reordering four finite sums. -/
theorem sum_comm4 {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (T : A → B → C → D → ℤ) :
    ∑ a, ∑ b, ∑ c, ∑ d, T a b c d = ∑ c, ∑ d, ∑ a, ∑ b, T a b c d :=
  (sum_congr rfl fun _ _ => sum_comm.trans (sum_congr rfl fun _ _ => sum_comm)).trans
    (sum_comm.trans (sum_congr rfl fun _ _ => sum_comm))

/-! ## The generic step: a uniform final Compose key -/

/-- (PROVED) For any family `H i` (`i` in a finite type) of deck maps sending decks to decks,
    followed by an independent uniform final Compose key `kF`:
    `∑_i ∑_kF corr² = ∑_x ∑_α f(x) f(α·x) ∑_β #{i | H i (α·x) = β · H i x} · autoCorr g β`.
    Generic: no DoubleDeal layer is used. -/
theorem sum_sq_corrOf_finalKey {ι : Type} [Fintype ι]
    (H : ι → (Fin 52 → Nat) → Fin 52 → Nat)
    (hH : ∀ i {x : Fin 52 → Nat}, IsDeck x → IsDeck (H i x)) (f g : (Fin 52 → Nat) → ℤ) :
    ∑ i, ∑ kF : Key, corrOf (fun x => composeVec 52 Nat (H i x) kF) f g ^ 2 =
      ∑ π : Equiv.Perm (Fin 52), ∑ α : Relabel, f (permDeck π) * f (rel α (permDeck π)) *
        ∑ β : Relabel, ((univ.filter fun i =>
          H i (rel α (permDeck π)) = rel β (H i (permDeck π))).card : ℤ) * autoCorr g β := by
  simp only [corrOf_sq]
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
    sum_comp_fiber_int b (autoCorr g)]
  refine sum_congr rfl fun β _ => ?_
  congr 3
  exact filter_congr fun i _ => by
    rw [relDiff_eq_iff (hH i hx) (hH i (isDeck_rel α hx)), eq_comm]

/-! ## L1: one keyed layer -/

/-- (PROVED) L1. One keyed layer `x ↦ U(x ∘ k₁) ∘ k₂` with independent uniform keys, for any
    deck map `U` sending decks to decks:
    `sumSqCorrU U f g = ∑_α ∑_β autoCorr f α · dpCount U α β · autoCorr g β`.
    An identity only; no numeric bound. -/
theorem sumSqCorrU_eq (U : (Fin 52 → Nat) → Fin 52 → Nat)
    (hU : ∀ {x : Fin 52 → Nat}, IsDeck x → IsDeck (U x)) (f g : (Fin 52 → Nat) → ℤ) :
    sumSqCorrU U f g = ∑ α, ∑ β, autoCorr f α * (dpCount U α β : ℤ) * autoCorr g β := by
  unfold sumSqCorrU keyedLayer
  rw [sum_sq_corrOf_finalKey (fun (k₁ : Key) x => U (composeVec 52 Nat x k₁))
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

/-- The part of `encryptL n _ (Fin.snoc K kF)` before the final Compose `kF`. -/
def beforeFinal {n : ℕ} (K : Fin (n + 1) → Key) (x : Fin 52 → Nat) : Fin 52 → Nat :=
  unkeyedNoMix (composeVec 52 Nat (rounds n x (Fin.init K)) (K (Fin.last n)))

theorem encryptL_snoc {n : ℕ} (K : Fin (n + 1) → Key) (kF : Key) (x : Fin 52 → Nat) :
    encryptL n x (Fin.snoc K kF) = composeVec 52 Nat (beforeFinal K x) kF := by
  rw [encryptL_eq]
  have h1 : roundKeysOf (Fin.snoc K kF : Fin (n + 2) → Key) = Fin.init K := by
    funext i
    simp only [roundKeysOf, Fin.snoc_castSucc, Fin.init]
  simp only [finalRound, h1, lastKeyOf, finalKeyOf, Fin.snoc_castSucc, Fin.snoc_last,
    beforeFinal]

theorem isDeck_beforeFinal {n : ℕ} (K : Fin (n + 1) → Key) {x : Fin 52 → Nat}
    (hx : IsDeck x) : IsDeck (beforeFinal K x) :=
  isDeck_unkeyedNoMix (isDeck_compose (isDeck_rounds n x _ hx) _)

/-- (PROVED) `fullDiffCount` counted by the final key: it is `52!` times the count of the
    remaining `n + 1` keys. -/
theorem fullDiffCount_eq_card_beforeFinal (α β : Relabel) (n : ℕ) (x : Fin 52 → Nat) :
    fullDiffCount α β n x = Nat.factorial 52 *
      (univ.filter fun K : Fin (n + 1) → Key =>
        beforeFinal K (rel α x) = rel β (beforeFinal K x)).card := by
  unfold fullDiffCount FullDiff
  rw [card_filter_snoc]
  simp only [encryptL_snoc, ← compose_rel, composeVec_inj]
  rw [sum_const, card_univ, Fintype.card_perm, Fintype.card_fin, smul_eq_mul]

/-- (PROVED) L2. The whole of `encryptL n` with independent uniform keys (all `n + 2`,
    whitening and final key included), for any deck `y`:
    `52! · sumSqCorr n f g = ∑_α ∑_β autoCorr f α · fullDiffCount α β n y · autoCorr g β`.
    An identity only; no numeric bound. Not the real PassKey schedule. -/
theorem sumSqCorr_eq (n : ℕ) (f g : (Fin 52 → Nat) → ℤ) {y : Fin 52 → Nat} (hy : IsDeck y) :
    (Nat.factorial 52 : ℤ) * sumSqCorr n f g =
      ∑ α, ∑ β, autoCorr f α * (fullDiffCount α β n y : ℤ) * autoCorr g β := by
  unfold sumSqCorr corr
  rw [← Fintype.sum_equiv (Fin.snocEquiv fun _ => Key) (fun p => corrOf
    (fun x => encryptL n x (Fin.snoc p.2 p.1)) f g ^ 2) _ fun _ => rfl,
    Fintype.sum_prod_type, sum_comm]
  simp only [encryptL_snoc]
  rw [sum_sq_corrOf_finalKey beforeFinal (fun K _ hx => isDeck_beforeFinal K hx) f g,
    mul_sum]
  have hc : ∀ (π : Equiv.Perm (Fin 52)) (α β : Relabel),
      (Nat.factorial 52 : ℤ) * ((univ.filter fun K : Fin (n + 1) → Key =>
        beforeFinal K (rel α (permDeck π)) = rel β (beforeFinal K (permDeck π))).card : ℤ) =
      (fullDiffCount α β n y : ℤ) := fun π α β => by
    rw [fullDiffCount_eq_of_isDeck α β n hy (isDeck_permDeck π),
      fullDiffCount_eq_card_beforeFinal]
    push_cast
    rfl
  calc ∑ π : Equiv.Perm (Fin 52), (Nat.factorial 52 : ℤ) * ∑ α : Relabel,
        f (permDeck π) * f (rel α (permDeck π)) * ∑ β : Relabel,
          ((univ.filter fun K : Fin (n + 1) → Key =>
            beforeFinal K (rel α (permDeck π)) = rel β (beforeFinal K (permDeck π))).card : ℤ) *
            autoCorr g β
      = ∑ π : Equiv.Perm (Fin 52), ∑ α : Relabel, f (permDeck π) * f (rel α (permDeck π)) *
          ∑ β, (fullDiffCount α β n y : ℤ) * autoCorr g β := by
        refine sum_congr rfl fun π _ => ?_
        rw [mul_sum]
        refine sum_congr rfl fun α _ => ?_
        simp only [← hc π α, mul_sum]
        exact sum_congr rfl fun β _ => by ring
    _ = ∑ α, autoCorr f α * ∑ β, (fullDiffCount α β n y : ℤ) * autoCorr g β :=
        sum_autoCorr_left f _
    _ = _ := sum_congr rfl fun α _ => by
        rw [mul_sum]
        exact sum_congr rfl fun β _ => by ring

/-! ## L3: the proof's finalRound step on the output side -/

/-- (PROVED) L3. The proof's finalRound step (Compose `lastKeyOf L`, the stem, Compose
    `finalKeyOf L`) acts on the output autocorrelations through `dpFCount`, for any deck `y`:
    `sumSqCorr n f g = ∑_α ∑_β autoCorr f α · diffCount α β n y ·
      ∑_γ dpFCount β γ · autoCorr g γ`.
    An identity only; no numeric bound. -/
theorem sumSqCorr_eq_final (n : ℕ) (f g : (Fin 52 → Nat) → ℤ) {y : Fin 52 → Nat}
    (hy : IsDeck y) :
    sumSqCorr n f g = ∑ α, ∑ β, autoCorr f α * (diffCount α β n y : ℤ) *
      ∑ γ, (dpFCount β γ : ℤ) * autoCorr g γ := by
  have h := sumSqCorr_eq n f g hy
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
    `52! · sumSqCorr n f g = (52!)^(n+2) · autoCorr f 1 · autoCorr g 1 +
      ∑_{α ≠ 1} ∑_{β ≠ 1} autoCorr f α · fullDiffCount α β n y · autoCorr g β`.
    An identity only; no numeric bound. -/
theorem sumSqCorr_split (n : ℕ) (f g : (Fin 52 → Nat) → ℤ) {y : Fin 52 → Nat}
    (hy : IsDeck y) :
    (Nat.factorial 52 : ℤ) * sumSqCorr n f g =
      (Nat.factorial 52 : ℤ) ^ (n + 2) * autoCorr f 1 * autoCorr g 1 +
        ∑ α ∈ univ.erase 1, ∑ β ∈ univ.erase 1,
          autoCorr f α * (fullDiffCount α β n y : ℤ) * autoCorr g β := by
  rw [sumSqCorr_eq n f g hy, ← add_sum_erase _ _ (mem_univ (1 : Relabel))]
  refine congrArg₂ (· + ·) ?_ ?_
  · rw [sum_eq_single (1 : Relabel) (fun β _ hβ => by
      rw [fullDiffCount_one_left β n hy, if_neg hβ]; simp) (fun h => absurd (mem_univ _) h),
      fullDiffCount_one_left 1 n hy, if_pos rfl]
    push_cast
    ring
  · refine sum_congr rfl fun α hα => ?_
    rw [← add_sum_erase _ _ (mem_univ (1 : Relabel)),
      fullDiffCount_to_one (ne_of_mem_erase hα) n hy]
    simp

end DoubleDeal.Security.Linear
