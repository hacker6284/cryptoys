/-
  T1 DRAFT — card relabellings versus the DoubleDeal layers (Mathlib side).

  STATUS: draft statements for review, local branch `doubledeal-t1` only.
  Every `sorry` is marked `DRAFT-SORRY` with its reason and proof plan; each
  such statement is checked numerically (`checks/check_relabel.py`, log in
  `checks/check_relabel.log`). `Axioms.lean` / `check_axioms.py` list which
  theorems are already sorry-free.

  A relabelling `σ : Equiv.Perm (Fin 52)` permutes card values and acts on every
  card of a deck (value-wise, not positional) through the bridge `Relabel.app`
  on the model's `Nat` cells. All statements are about the proof-only algebraic
  model (`Round.lean`, `GridCycle.lean`, `SumRanks.lean` in ../lean). The
  transfer to the emitted `Doubledeal.encrypt` (Link 2, `encrypt_refines`) is in
  `Link.lean`. Link 1 (sudo = Generated) stays open.
  Structural facts, not a security proof.
-/
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Logic.Equiv.Fin
import DoubleDeal.Round
import DoubleDealSecurity.Decks

namespace DoubleDeal.Security

open DoubleDeal

/-! ## Relabellings -/

/-- A relabelling: a permutation of the card values `0..51` (Mathlib `Equiv.Perm`). -/
abbrev Relabel := Equiv.Perm (Fin 52)

namespace Relabel

/-- Bridge to the model's `Nat` cells: cards `< 52` are relabelled, anything
    else is fixed. -/
def app (σ : Relabel) (n : Nat) : Nat :=
  if h : n < 52 then (σ ⟨n, h⟩).val else n

def IsId (σ : Relabel) : Prop := σ = 1

theorem isId_iff (σ : Relabel) : σ.IsId ↔ ∀ c, σ c = c := by
  unfold IsId; constructor
  · rintro rfl c; rfl
  · intro h; ext c; simp [h c]

/-- The transposition of two card values (Mathlib `Equiv.swap`). -/
abbrev swap (a b : Fin 52) : Relabel := Equiv.swap a b

theorem app_fin (σ : Relabel) (c : Fin 52) : σ.app c.val = (σ c).val := by
  simp [app, c.isLt]

theorem app_lt (σ : Relabel) {n : Nat} (h : n < 52) : σ.app n < 52 := by
  simp [app, h]

theorem app_inj (σ : Relabel) {a b : Nat} (h : σ.app a = σ.app b) : a = b := by
  unfold app at h
  by_cases ha : a < 52 <;> by_cases hb : b < 52 <;> simp only [ha, hb, ↓reduceDIte] at h
  · exact congrArg Fin.val (σ.injective (Fin.ext h))
  · have := (σ ⟨a, ha⟩).isLt; omega
  · have := (σ ⟨b, hb⟩).isLt; omega
  · exact h

theorem app_one (n : Nat) : app 1 n = n := by
  unfold app; split <;> rfl

end Relabel

open Relabel

/-- Relabel every card of a deck. -/
def rel (σ : Relabel) (m : Fin 52 → Nat) : Fin 52 → Nat := fun i => σ.app (m i)

/-- Relabel every card of a grid. -/
def relG (σ : Relabel) (g : Grid Nat) : Grid Nat := fun r c => σ.app (g r c)

/-- Every cell is a card value. -/
def Cards (m : Fin 52 → Nat) : Prop := ∀ i, m i < 52
def CardsG (g : Grid Nat) : Prop := ∀ r c, g r c < 52

/-- A well-formed deck: 52 distinct card values. -/
def IsDeck (m : Fin 52 → Nat) : Prop := Cards m ∧ ∀ i j, m i = m j → i = j

/-- `σ` commutes with a deck map on every card-valued deck. -/
def Commutes (σ : Relabel) (F : (Fin 52 → Nat) → (Fin 52 → Nat)) : Prop :=
  ∀ m, Cards m → F (rel σ m) = rel σ (F m)

/-- `σ` commutes with a deck map on every well-formed deck (weaker hypothesis). -/
def CommutesOnDecks (σ : Relabel) (F : (Fin 52 → Nat) → (Fin 52 → Nat)) : Prop :=
  ∀ m, IsDeck m → F (rel σ m) = rel σ (F m)

def CommutesG (σ : Relabel) (F : Grid Nat → Grid Nat) : Prop :=
  ∀ g, CardsG g → F (relG σ g) = relG σ (F g)

/-- Grid version on well-formed decks (read column-major). -/
def CommutesOnDecksG (σ : Relabel) (F : Grid Nat → Grid Nat) : Prop :=
  ∀ g, IsDeck (scoopColumnMajor g) → F (relG σ g) = relG σ (F g)

theorem Commutes.onDecks {σ F} (h : Commutes σ F) : CommutesOnDecks σ F :=
  fun m hm => h m hm.1

theorem CommutesG.onDecks {σ F} (h : CommutesG σ F) : CommutesOnDecksG σ F := by
  intro g hg
  apply h
  intro r c
  have := hg.1 (cmFlat r c)
  simpa [scoopColumnMajor, (cm_cmFlat r c).1, (cm_cmFlat r c).2] using this

/-! ## Bridge to the cell-map lemmas of `Link.lean` -/

/-- `σ.app` is a card map in the sense of the Link-side transfer theorems. -/
theorem app_cardMap (σ : Relabel) : CardMap σ.app := ⟨fun _ h => σ.app_lt h⟩

/-- `swap K♣ K♦` acts on cells as the Link-side `swapNat 12 51`. -/
theorem swap_KC_KD_app : (swap KC KD).app = swapNat 12 51 := by
  funext n
  unfold Relabel.app swapNat
  by_cases h : n < 52
  · simp only [h, ↓reduceDIte]
    have : ∀ c : Fin 52, ((swap KC KD) c).val =
        (if c.val = 12 then 51 else if c.val = 51 then 12 else c.val) := by decide
    rw [this ⟨n, h⟩]
  · have h12 : n ≠ 12 := by omega
    have h51 : n ≠ 51 := by omega
    simp [h, h12, h51]

theorem cards_firstDeck : Cards (firstDeck 51) := firstDeck_lt

/-! ## 1. Positional layers commute with every relabelling

Compose/AddRoundKey is `C[j] = M[keyPos K j]`: the key only supplies
positions. So the right form is `E_K(σM) = σ E_K(M)` with the key NOT
relabelled. Relabelling the key instead permutes the output positions
(`keyPos_relabel_key` in `Link.lean`), and PassKey is value-dependent, so neither
`E_{σK}(M)` nor `E_{σK}(σM)` is related to `σ E_K(M)` in general. -/

theorem compose_rel (σ : Relabel) (m : Fin 52 → Nat) (pos : Fin 52 → Fin 52) :
    composeVec 52 Nat (rel σ m) pos = rel σ (composeVec 52 Nat m pos) := rfl

theorem compose_commutes (σ : Relabel) (pos : Fin 52 → Fin 52) :
    Commutes σ (fun m => composeVec 52 Nat m pos) := fun _ _ => rfl

theorem layColumnMajor_rel (σ : Relabel) (m : Fin 52 → Nat) :
    layColumnMajor (rel σ m) = relG σ (layColumnMajor m) := rfl

theorem scoopColumnMajor_rel (σ : Relabel) (g : Grid Nat) :
    scoopColumnMajor (relG σ g) = rel σ (scoopColumnMajor g) := rfl

theorem layRowMajor_rel (σ : Relabel) (m : Fin 52 → Nat) :
    layRowMajor (rel σ m) = relG σ (layRowMajor m) := rfl

theorem scoopRowMajor_rel (σ : Relabel) (g : Grid Nat) :
    scoopRowMajor (relG σ g) = rel σ (scoopRowMajor g) := rfl

theorem shiftRows_rel (σ : Relabel) (g : Grid Nat) :
    shiftRows (relG σ g) = relG σ (shiftRows g) := rfl

theorem shiftRows_commutes (σ : Relabel) : CommutesG σ shiftRows := fun _ _ => rfl

/-! ## 2. SumRanks commutes with σ iff σ shifts both weights by a constant

The cipher rotates row `r` left by (Σ row weights) mod 13 and column `c`
down by (Σ column weights) mod 4. A 13-card row has 13 cells, so a constant
shift `k` of every row weight changes the row sum by `13k ≡ 0 (mod 13)`;
likewise a constant column-weight shift changes a 4-card column sum by
`4k ≡ 0 (mod 4)`. So the exact condition is a constant *shift*, not
preservation. -/

/-- `w ∘ σ ≡ w + k (mod M)` on every card, for one constant `k`. -/
def WeightShift (σ : Relabel) (w : Nat → Nat) (M : Nat) : Prop :=
  ∃ k, ∀ c : Fin 52, w (σ c).val % M = (w c.val + k) % M

theorem weightSum_map_app_mod (σ : Relabel) (w : Nat → Nat) (M k : Nat)
    (hk : ∀ c : Fin 52, w (σ c).val % M = (w c.val + k) % M) :
    ∀ xs : List Nat, (∀ x ∈ xs, x < 52) →
      weightSum w (xs.map σ.app) % M = (weightSum w xs + xs.length * k) % M
  | [], _ => by simp [weightSum, sumNats]
  | x :: xs, hx => by
    have hx0 : x < 52 := hx x (List.mem_cons_self _ _)
    have ih := weightSum_map_app_mod σ w M k hk xs (fun y hy => hx y (List.mem_cons_of_mem _ hy))
    have h1 : w (σ.app x) % M = (w x + k) % M := by
      have := hk ⟨x, hx0⟩
      rwa [← σ.app_fin ⟨x, hx0⟩] at this
    simp only [weightSum, List.map, sumNats] at ih ⊢
    rw [Nat.add_mod, h1, ih, ← Nat.add_mod]
    congr 1
    simp only [List.length_cons, Nat.succ_mul]
    omega

theorem mem_toList13 {f : Fin 13 → α} {x : α} (h : x ∈ toList13 f) : ∃ c, f c = x := by
  obtain ⟨i, hi, hx⟩ := List.getElem_of_mem h
  have hi' : i < 13 := by simpa [length_toList13] using hi
  exact ⟨⟨i, hi'⟩, by rw [← getElem_toList13 f ⟨i, hi'⟩]; exact hx⟩

theorem mem_toList4 {f : Fin 4 → α} {x : α} (h : x ∈ toList4 f) : ∃ c, f c = x := by
  obtain ⟨i, hi, hx⟩ := List.getElem_of_mem h
  have hi' : i < 4 := by simpa [length_toList4] using hi
  exact ⟨⟨i, hi'⟩, by rw [← getElem_toList4 f ⟨i, hi'⟩]; exact hx⟩

theorem rotL_congr_mod (xs : List α) {n n' : Nat} (h : n % xs.length = n' % xs.length) :
    rotL xs n = rotL xs n' := by
  unfold rotL; rw [h]

theorem rotR_congr_mod (xs : List α) {n n' : Nat} (h : n % xs.length = n' % xs.length) :
    rotR xs n = rotR xs n' := by
  unfold rotR; rw [h]

theorem ofList13_map (f : α → β) (xs : List α) (h : xs.length = 13)
    (h' : (xs.map f).length = 13) (i : Fin 13) :
    ofList13 (xs.map f) h' i = f (ofList13 xs h i) := by
  simp [ofList13]

theorem ofList4_map (f : α → β) (xs : List α) (h : xs.length = 4)
    (h' : (xs.map f).length = 4) (i : Fin 4) :
    ofList4 (xs.map f) h' i = f (ofList4 xs h i) := by
  simp [ofList4]

theorem rowRotate_rel (σ : Relabel) (g : Grid Nat) (t t' : Fin 4 → Nat)
    (h : ∀ r, t' r % 13 = t r % 13) :
    rowRotate (relG σ g) t' = relG σ (rowRotate g t) := by
  funext r c
  have hl : toList13 (relG σ g r) = (toList13 (g r)).map σ.app := rfl
  have hrot : rotL (toList13 (relG σ g r)) (t' r) = (rotL (toList13 (g r)) (t r)).map σ.app := by
    rw [hl, map_rotL]
    apply rotL_congr_mod
    simp only [List.length_map, length_toList13]
    exact h r
  simp only [rowRotate, relG]
  rw [congrFun (ofList13_eq _ (by simp [length_rotL, length_toList13]) hrot) c]
  exact ofList13_map σ.app _ (by rw [length_rotL, length_toList13]) _ c

theorem colRotate_rel (σ : Relabel) (g : Grid Nat) (s s' : Fin 13 → Nat)
    (h : ∀ c, s' c % 4 = s c % 4) :
    colRotate (relG σ g) s' = relG σ (colRotate g s) := by
  funext r c
  have hl : toList4 (fun r' => relG σ g r' c) = (toList4 (fun r' => g r' c)).map σ.app := rfl
  have hrot : rotR (toList4 (fun r' => relG σ g r' c)) (s' c) =
      (rotR (toList4 (fun r' => g r' c)) (s c)).map σ.app := by
    rw [hl, map_rotR]
    apply rotR_congr_mod
    simp only [List.length_map, length_toList4]
    exact h c
  show colRotate (relG σ g) s' r c = σ.app (colRotate g s r c)
  unfold colRotate
  rw [congrFun (ofList4_eq _ (by simp [length_rotR, length_toList4]) hrot) r]
  exact ofList4_map σ.app _ (by rw [length_rotR, length_toList4]) _ r

theorem applyRowRotates_rel (σ : Relabel) (w : Nat → Nat) (hs : WeightShift σ w 13)
    (g : Grid Nat) (hg : CardsG g) :
    applyRowRotates w (relG σ g) = relG σ (applyRowRotates w g) := by
  obtain ⟨k, hk⟩ := hs
  apply rowRotate_rel
  intro r
  have hl : toList13 (relG σ g r) = (toList13 (g r)).map σ.app := rfl
  simp only [rowWeightSum]
  rw [hl, weightSum_map_app_mod σ w 13 k hk _ (fun x hx => by
    obtain ⟨c, rfl⟩ := mem_toList13 hx; exact hg r c)]
  rw [length_toList13, Nat.add_mul_mod_self_left]

theorem applyColRotates_rel (σ : Relabel) (w : Nat → Nat) (hs : WeightShift σ w 4)
    (g : Grid Nat) (hg : CardsG g) :
    applyColRotates w (relG σ g) = relG σ (applyColRotates w g) := by
  obtain ⟨k, hk⟩ := hs
  apply colRotate_rel
  intro c
  have hl : toList4 (fun r => relG σ g r c) = (toList4 (fun r => g r c)).map σ.app := rfl
  simp only [colWeightSum]
  rw [hl, weightSum_map_app_mod σ w 4 k hk _ (fun x hx => by
    obtain ⟨r, rfl⟩ := mem_toList4 hx; exact hg r c)]
  rw [length_toList4, Nat.add_mul_mod_self_left]

/-- **SumRanks, "if"** (PROVED): constant weight shifts ⇒ SumRanks commutes with σ
    on every card-valued grid. Any weights; the cipher uses rank / rank + suit. -/
theorem sumRanks_commutes_of_shift (σ : Relabel) (rowW colW : Nat → Nat)
    (hr : WeightShift σ rowW 13) (hc : WeightShift σ colW 4) :
    CommutesG σ (sumRanks rowW colW) := by
  intro g hg
  unfold sumRanks
  rw [applyRowRotates_rel σ rowW hr g hg,
    applyColRotates_rel σ colW hc _ (applyRowRotates_bound (· < 52) rowW g hg)]

/-- **SumRanks, "only if"** (DRAFT-SORRY): if SumRanks commutes with σ on all
    well-formed decks, both weights shift by a constant. Any weights.

    Plan (single pair-swap witnesses + reduction, no search over σ):
    * Rows. If the row shift fails there are cards `a ≠ b` with
      `rowW(σa) − rowW a ≢ rowW(σb) − rowW b (mod 13)`. Take a deck with `a` in
      row 0 and `b` in row 1, and the same deck with `a`,`b` exchanged. If both
      row-0 rotations agreed under σ, subtracting gives the congruence above, a
      contradiction. So on one of the two decks row 0 of `σg` rotates by a
      different amount (mod 13) than row 0 of `g`; 13 distinct cards then land in
      different columns, the column stage preserves column contents, so the
      outputs differ.
    * Columns. With the row shift in hand, the row stage commutes with σ
      (`applyRowRotates_rel`) and is onto decks (`applyRowRotatesInv`), so pick
      the post-row grid freely and repeat the pair swap inside column 0: 4
      distinct cards rotated by different amounts (mod 4) differ.
    Effort: ~300–500 lines (deck construction + "column contents" invariant). -/
theorem sumRanks_shift_of_commutes (σ : Relabel) (rowW colW : Nat → Nat)
    (h : CommutesOnDecksG σ (sumRanks rowW colW)) :
    WeightShift σ rowW 13 ∧ WeightShift σ colW 4 := by
  sorry -- DRAFT-SORRY: see plan above

/-- SumRanks characterisation (iff), any weights. -/
theorem sumRanks_commutes_iff (σ : Relabel) (rowW colW : Nat → Nat) :
    CommutesOnDecksG σ (sumRanks rowW colW) ↔
      WeightShift σ rowW 13 ∧ WeightShift σ colW 4 :=
  ⟨sumRanks_shift_of_commutes σ rowW colW,
   fun ⟨hr, hc⟩ => (sumRanks_commutes_of_shift σ rowW colW hr hc).onDecks⟩

/-! ### 2a. v8 weights (rows rank, columns rank): exactly the rank-preserving σ -/

/-- v8 (frozen) SumRanks: column weight is rank, as in the deprecated cipher. -/
def sumRanksV8 : Grid Nat → Grid Nat := sumRanks cardRank cardRank

/-- v9 SumRanks: column weight rank + suit (A2). -/
def sumRanksV9 : Grid Nat → Grid Nat := sumRanks cardRank cardColumnWeight

/-- (PROVED) For the v8 weights, the two shift conditions hold iff σ preserves
    every card's rank. (A nonzero rank shift mod 13 wraps K→A somewhere, which
    changes the rank difference by 13 ≡ 1 (mod 4) and breaks the column shift.) -/
theorem v8_shift_iff_rank_preserving (σ : Relabel) :
    (WeightShift σ cardRank 13 ∧ WeightShift σ cardRank 4) ↔
      ∀ c : Fin 52, rank (σ c).val = rank c.val := by
  constructor
  · rintro ⟨⟨k1, h1⟩, ⟨k2, h2⟩⟩
    have a1 := h1 ⟨0, by decide⟩
    have a2 := h2 ⟨0, by decide⟩
    have b1 := h1 ⟨12, by decide⟩
    have b2 := h2 ⟨12, by decide⟩
    have hx := (σ ⟨0, by decide⟩).isLt
    have hy := (σ ⟨12, by decide⟩).isLt
    simp only [cardRank, rank] at a1 a2 b1 b2
    have hk : k1 % 13 = 0 := by omega
    intro c
    have := h1 c
    have hc := (σ c).isLt
    simp only [cardRank, rank] at this ⊢
    omega
  · intro h
    refine ⟨⟨0, fun c => ?_⟩, ⟨0, fun c => ?_⟩⟩ <;> simp [cardRank, h c]

/-- Corollary (PROVED): every rank-preserving σ — in particular every same-rank
    swap such as K♣↔K♦ — commutes with v8 SumRanks. -/
theorem v8_sumRanks_commutes_of_rank_preserving (σ : Relabel)
    (h : ∀ c : Fin 52, rank (σ c).val = rank c.val) : CommutesG σ sumRanksV8 := by
  obtain ⟨hr, hc⟩ := (v8_shift_iff_rank_preserving σ).2 h
  exact sumRanks_commutes_of_shift σ _ _ hr hc

theorem rank_swap_same (a b : Fin 52) (hab : rank a.val = rank b.val) (c : Fin 52) :
    rank ((swap a b) c).val = rank c.val := by
  rw [Equiv.swap_apply_def]
  split_ifs with ha hb
  · subst ha; exact hab.symm
  · subst hb; exact hab
  · rfl

/-! ### 2b. v9 weights (rows rank, columns rank + suit): a 52-element group

SURPRISE vs the expected shape: v9 SumRanks does NOT force σ = id. The σ with
`rank ∘ σ ≡ rank + a (mod 13)` and `(rank+suit) ∘ σ ≡ (rank+suit) + b (mod 4)`
form a group of exactly 52 relabellings `v9Sym a b` (≅ ℤ/13 × ℤ/4 ≅ ℤ/52), e.g.
`v9Sym 0 1` is the suit rotation ♣→♥→♠→♦→♣ within each rank. -/

/-- `v9Sym a b`: rank index `+a (mod 13)`; suit chosen so that
    `(rank + suit) mod 4` moves by exactly `b`. -/
def v9SymFn (a : Fin 13) (b : Fin 4) (c : Fin 52) : Fin 52 :=
  let r0 := c.val % 13
  let su := c.val / 13
  let wrap := if r0 + a.val < 13 then 0 else 13
  ⟨13 * ((su + b.val + 16 - a.val + wrap) % 4) + (r0 + a.val) % 13, by omega⟩

def neg13 (a : Fin 13) : Fin 13 := ⟨(13 - a.val) % 13, Nat.mod_lt _ (by decide)⟩
def neg4 (b : Fin 4) : Fin 4 := ⟨(4 - b.val) % 4, Nat.mod_lt _ (by decide)⟩

theorem v9SymFn_left : ∀ (a : Fin 13) (b : Fin 4) (c : Fin 52),
    v9SymFn (neg13 a) (neg4 b) (v9SymFn a b c) = c := by decide!

theorem v9SymFn_right : ∀ (a : Fin 13) (b : Fin 4) (c : Fin 52),
    v9SymFn a b (v9SymFn (neg13 a) (neg4 b) c) = c := by decide!

def v9Sym (a : Fin 13) (b : Fin 4) : Relabel where
  toFun := v9SymFn a b
  invFun := v9SymFn (neg13 a) (neg4 b)
  left_inv := v9SymFn_left a b
  right_inv := v9SymFn_right a b

theorem v9SymFn_weights : ∀ (a : Fin 13) (b : Fin 4) (c : Fin 52),
    cardRank (v9SymFn a b c).val % 13 = (cardRank c.val + a.val) % 13 ∧
    cardColumnWeight (v9SymFn a b c).val % 4 = (cardColumnWeight c.val + b.val) % 4 := by
  decide!

/-- A card is determined by (rank mod 13, (rank + suit) mod 4). -/
theorem card_eq_of_weights : ∀ x y : Fin 52,
    cardRank x.val % 13 = cardRank y.val % 13 →
    cardColumnWeight x.val % 4 = cardColumnWeight y.val % 4 → x = y := by
  decide!

/-- (PROVED) The v9 shift conditions hold iff σ is one of the 52 `v9Sym a b`. -/
theorem v9_shift_iff (σ : Relabel) :
    (WeightShift σ cardRank 13 ∧ WeightShift σ cardColumnWeight 4) ↔
      ∃ a b, ∀ c, σ c = v9SymFn a b c := by
  constructor
  · rintro ⟨⟨k1, h1⟩, ⟨k2, h2⟩⟩
    refine ⟨⟨k1 % 13, Nat.mod_lt _ (by decide)⟩, ⟨k2 % 4, Nat.mod_lt _ (by decide)⟩, fun c => ?_⟩
    have ⟨w1, w2⟩ := v9SymFn_weights ⟨k1 % 13, Nat.mod_lt _ (by decide)⟩
      ⟨k2 % 4, Nat.mod_lt _ (by decide)⟩ c
    apply card_eq_of_weights
    · rw [h1 c, w1]; simp only; omega
    · rw [h2 c, w2]; simp only; omega
  · rintro ⟨a, b, h⟩
    exact ⟨⟨a.val, fun c => by rw [h]; exact (v9SymFn_weights a b c).1⟩,
           ⟨b.val, fun c => by rw [h]; exact (v9SymFn_weights a b c).2⟩⟩

theorem v9SymFn_fixed : ∀ (a : Fin 13) (b : Fin 4) (c : Fin 52),
    v9SymFn a b c = c → a = 0 ∧ b = 0 := by decide!

theorem v9SymFn_zero (c : Fin 52) : v9SymFn 0 0 c = c := by
  revert c; decide!

/-- v9 SumRanks commutes with σ on all decks iff σ is one of the 52 `v9Sym a b`.
    ("if" PROVED; "only if" rests on `sumRanks_shift_of_commutes`.) -/
theorem v9_sumRanks_commutes_iff (σ : Relabel) :
    CommutesOnDecksG σ sumRanksV9 ↔ ∃ a b, ∀ c, σ c = v9SymFn a b c :=
  (sumRanks_commutes_iff σ _ _).trans (v9_shift_iff σ)

/-- No transposition commutes with v9 SumRanks (PROVED modulo the "only if"):
    a transposition fixes 50 cards, so it would be `v9Sym 0 0 = id`. -/
theorem v9_no_swap_commutes_sumRanks (a b : Fin 52) (hab : a ≠ b) :
    ¬ CommutesOnDecksG (swap a b) sumRanksV9 := by
  intro h
  obtain ⟨x, y, hxy⟩ := (v9_sumRanks_commutes_iff _).1 h
  -- two fixed cards pin (x, y) = (0, 0), then σ = id contradicts σ a = b
  have key : ∀ (x : Fin 13) (y : Fin 4) (a b : Fin 52), a ≠ b →
      (∀ c, (swap a b) c = v9SymFn x y c) → False := by
    intro x y a b hab hxy
    -- some card among 0, 1, 2 is fixed by the swap; a fixed card forces (x, y) = (0, 0)
    have hfix : ∃ c : Fin 52, c ≠ a ∧ c ≠ b := by
      by_cases h0 : (⟨0, by decide⟩ : Fin 52) ≠ a ∧ (⟨0, by decide⟩ : Fin 52) ≠ b
      · exact ⟨_, h0⟩
      by_cases h1 : (⟨1, by decide⟩ : Fin 52) ≠ a ∧ (⟨1, by decide⟩ : Fin 52) ≠ b
      · exact ⟨_, h1⟩
      refine ⟨⟨2, by decide⟩, ?_, ?_⟩ <;> intro e <;> subst e <;>
        simp_all [Fin.ext_iff] <;> omega
    obtain ⟨c, hca, hcb⟩ := hfix
    have hc : v9SymFn x y c = c := by
      rw [← hxy c]; exact Equiv.swap_apply_of_ne_of_ne hca hcb
    obtain ⟨rfl, rfl⟩ := v9SymFn_fixed x y c hc
    have := hxy a
    rw [v9SymFn_zero] at this
    rw [Equiv.swap_apply_left] at this
    exact hab this.symm
  exact key x y a b hab hxy

/-! ## 3. GridCycle (MixColumns) commutes with no nontrivial σ

GridCycle is value-dependent in a different way: card `n` is placed at a seat
computed from card `n−1`'s (suit, rank) step, the current occupancy, and the
overflow marker `t` (v9 also uses the blocked target's column as the scan
start). So on one deck, GridCycle commutes with σ exactly when the seat walk of
`σ·m` equals the walk of `m` (`mixColumns_rel_iff_walk`). Over all decks this
forces σ = id: the second card's seat is an injective function of the first
card, except that K♣ (step (0,0), always overflows to (0,0)) and K♠ (step
(2,0) from (2,0), lands on (0,0)) collide. -/

/-- Seat of card `n` in the GridCycle walk of `hand`. -/
def walkSeat (hand : Fin 52 → Nat) (n : Nat) : Fin 4 × Fin 13 :=
  (chooseSeat! (placeN hand n).2).1

/-- Seat of the second card as a function of the first card. -/
def seat2 (c : Nat) : Fin 4 × Fin 13 := (chooseSeat! (advance initWalk c asStart 0)).1

theorem walkSeat_zero (hand : Fin 52 → Nat) : walkSeat hand 0 = asStart := rfl

theorem walkSeat_one (hand : Fin 52 → Nat) : walkSeat hand 1 = seat2 (hand ⟨0, by decide⟩) := rfl

/-- (PROVED, kernel `decide!`) The second seat is injective in the first card,
    except for the single collision K♣/K♠. -/
theorem seat2_inj : ∀ a b : Fin 52, seat2 a.val = seat2 b.val →
    a = b ∨ (a = KC ∧ b = KS) ∨ (a = KS ∧ b = KC) := by
  decide!

/-- (DRAFT-SORRY) On a well-formed deck, GridCycle commutes with σ iff the seat
    walk is unchanged. Plan: placement writes card `n` at `walkSeat n` and the
    scoop is a bijection (existing `placed_at_seat`, `inv_place_agree`); cards
    are distinct, so equal outputs force equal seats and conversely.
    Effort: ~150 lines. -/
theorem mixColumns_rel_iff_walk (σ : Relabel) (m : Fin 52 → Nat) (hm : IsDeck m) :
    mixColumns (rel σ m) = rel σ (mixColumns m) ↔
      ∀ n < 52, walkSeat (rel σ m) n = walkSeat m n := by
  sorry -- DRAFT-SORRY

/-- (PROVED, kernel `decide!`) K♣↔K♦ does not commute with v9 GridCycle:
    on the deck `K♦, A♣, 2♣, …` the second card goes to (1,0) but, after the
    swap, K♣ leads and the second card overflows to (0,0). -/
theorem mixColumns_KC_KD_fails :
    mixColumns (rel (swap KC KD) (firstDeck 51)) ≠ rel (swap KC KD) (mixColumns (firstDeck 51)) := by
  intro h
  have := congrFun h ⟨0, by decide⟩
  revert this
  decide!

/-- (PROVED, kernel `decide!`) The K♣/K♠ collision is broken on the third card. -/
theorem mixColumns_KC_KS_fails :
    mixColumns (rel (swap KC KS) (firstDeck 12)) ≠ rel (swap KC KS) (mixColumns (firstDeck 12)) := by
  intro h
  have := congrFun h ⟨4, by decide⟩
  revert this
  decide!

/-- (DRAFT-SORRY) GridCycle commutes with σ on all decks iff σ = id.
    Plan: "if" by `rel id = id` on card decks. "Only if": pick `c` with
    `σ c ≠ c`. Unless `{c, σ c} = {K♣, K♠}`, the deck `firstDeck c` has
    `walkSeat 1` changed (`walkSeat_one`, `seat2_inj`), so the outputs differ
    (`mixColumns_rel_iff_walk`). Otherwise σ swaps K♣,K♠; if σ moves any other
    card use that card, else σ = (K♣ K♠) and `mixColumns_KC_KS_fails` applies.
    Needs `firstDeck c` well-formed (finite, decide). Effort: ~100 lines on top
    of `mixColumns_rel_iff_walk`. -/
theorem mixColumns_commutes_iff_id (σ : Relabel) :
    CommutesOnDecks σ mixColumns ↔ σ.IsId := by
  sorry -- DRAFT-SORRY

/-! ### 3a. Frozen v8 GridCycle model (overflow scan starts at column 0)

Proof-only copy of the v9 walk with the v8 scan start, for the v8 statements.
Checked against the frozen v8 known-answer vectors in `RelabelCheck.lean`. -/

namespace V8

def chooseSeat? (st : WalkState) : Option ((Fin 4 × Fin 13) × Nat) :=
  match st.prev with
  | none => some (asStart, st.t)
  | some (card, pos) =>
      let target := gridStep card pos
      if occAt st.occ target then overflowSeat st.occ st.t 0
      else some (target, st.t)

def chooseSeat! (st : WalkState) : (Fin 4 × Fin 13) × Nat :=
  match chooseSeat? st with
  | some x => x
  | none => ((⟨0, by decide⟩, ⟨0, by decide⟩), st.t)

def placeN (hand : Fin 52 → Nat) : Nat → NatGrid × WalkState
  | 0 => ((fun _ _ => (0 : Nat)), initWalk)
  | n + 1 =>
      let (g, st) := placeN hand n
      if h : n < 52 then
        let (pos, t') := chooseSeat! st
        let card := hand ⟨n, h⟩
        (setGrid g pos card, advance st card pos t')
      else (g, st)

def mixColumns (hand : Fin 52 → Nat) : Fin 52 → Nat := scoopRowMajor (placeN hand 52).1

def unkeyedNoMix (m : Fin 52 → Nat) : Fin 52 → Nat :=
  scoopColumnMajor (shiftRows (sumRanksV8 (layColumnMajor m)))

def fullRound (m : Fin 52 → Nat) (pos : Fin 52 → Fin 52) : Fin 52 → Nat :=
  composeVec 52 Nat (mixColumns (unkeyedNoMix m)) pos

end V8

/-- (PROVED, kernel `decide!`) K♣↔K♦ does not commute with v8 GridCycle either
    (same deck, same second-seat split (1,0) vs (0,0)). -/
theorem v8_mixColumns_KC_KD_fails :
    V8.mixColumns (rel (swap KC KD) (firstDeck 51)) ≠
      rel (swap KC KD) (V8.mixColumns (firstDeck 51)) := by
  intro h
  have := congrFun h ⟨0, by decide⟩
  revert this
  decide!

/-- (DRAFT-SORRY) v8 GridCycle commutes with σ on all decks iff σ = id.
    Same proof as `mixColumns_commutes_iff_id` (the first two seats never scan
    past column 0, so v8 and v9 agree on `seat2`). -/
theorem v8_mixColumns_commutes_iff_id (σ : Relabel) :
    CommutesOnDecks σ V8.mixColumns ↔ σ.IsId := by
  sorry -- DRAFT-SORRY

/-! ## 4. Rounds and encrypt -/

theorem cards_rel (σ : Relabel) {m : Fin 52 → Nat} (hm : Cards m) : Cards (rel σ m) :=
  fun i => σ.app_lt (hm i)

theorem cardsG_lay {m : Fin 52 → Nat} (hm : Cards m) : CardsG (layColumnMajor m) :=
  fun _ _ => hm _

theorem cards_unkeyedNoMix {m : Fin 52 → Nat} (hm : Cards m) : Cards (unkeyedNoMix m) := by
  intro i
  exact sumRanks_bound (· < 52) cardRank cardColumnWeight _ (cardsG_lay hm) _ _

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
theorem unkeyedNoMix_commutes (σ : Relabel) (hs : CommutesG σ sumRanksV9) :
    Commutes σ unkeyedNoMix := by
  intro m hm
  simp only [unkeyedNoMix]
  rw [layColumnMajor_rel, show sumRanks cardRank cardColumnWeight = sumRanksV9 from rfl,
    hs _ (cardsG_lay hm)]
  rfl

/-- (PROVED) Layer-wise commutation lifts to the full round, for every key. -/
theorem fullRound_commutes (σ : Relabel) (hs : CommutesG σ sumRanksV9)
    (hmix : Commutes σ mixColumns) (pos : Fin 52 → Fin 52) :
    Commutes σ (fun m => fullRound m pos) := by
  intro m hm
  simp only [fullRound, unkeyedWithMix]
  rw [unkeyedNoMix_commutes σ hs m hm, hmix _ (cards_unkeyedNoMix hm)]
  rfl

theorem fullRoundNoMix_commutes (σ : Relabel) (hs : CommutesG σ sumRanksV9)
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
theorem encryptN_commutes (σ : Relabel) (hs : CommutesG σ sumRanksV9)
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

/-- (DRAFT-SORRY, plumbing) The stem maps well-formed decks onto well-formed
    decks: it only moves cells, and `invUnkeyedNoMix` is a two-sided inverse.
    Needs "a position permutation of an injective deck is injective" for the
    input-dependent rotations. Effort: ~100 lines. -/
theorem unkeyedNoMix_onto_decks (x : Fin 52 → Nat) (hx : IsDeck x) :
    ∃ m, IsDeck m ∧ unkeyedNoMix m = x := by
  sorry -- DRAFT-SORRY

/-- (PROVED from the lemmas above) If σ ≠ id commutes with the v9 stem
    (i.e. σ is one of the 51 nontrivial `v9Sym a b`), then no full round
    commutes with σ: the stem is onto decks, so the round commuting would make
    GridCycle commute, forcing σ = id. -/
theorem fullRound_not_commutes_of_stem (σ : Relabel) (hid : ¬ σ.IsId)
    (hs : CommutesG σ sumRanksV9) (pos invPos : Fin 52 → Fin 52)
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

/-- (DRAFT-SORRY, CONJECTURE — checked, not proved) v9: no nontrivial σ commutes
    with a full round for any key. Checked on all 1,326 transpositions, all 51
    nontrivial `v9Sym`, and 200 random σ (3 random decks/keys each: every one
    fails). The 51 `v9Sym` cases follow from `fullRound_not_commutes_of_stem`;
    the remaining σ fail at SumRanks, but a failing layer inside a composite
    does not by itself make the composite fail, so this needs its own argument
    (e.g. track the first two cards the walk places, which are the stem's first
    output cell and its seat-2 successor). Effort: uncertain, ~1–2 weeks. -/
theorem fullRound_commutes_iff_id (σ : Relabel) :
    (∀ pos, CommutesOnDecks σ (fun m => fullRound m pos)) ↔ σ.IsId := by
  sorry -- DRAFT-SORRY (conjecture)

/-- (DRAFT-SORRY, CONJECTURE) Same for encrypt: no nontrivial σ gives
    `E_K(σM) = σ E_K(M)` for all keys and decks. -/
theorem encrypt6_commutes_iff_id (σ : Relabel) :
    (∀ pos0 posMix posFinal, CommutesOnDecks σ (fun m => encrypt6 m pos0 posMix posFinal)) ↔
      σ.IsId := by
  sorry -- DRAFT-SORRY (conjecture)

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

end DoubleDeal.Security
