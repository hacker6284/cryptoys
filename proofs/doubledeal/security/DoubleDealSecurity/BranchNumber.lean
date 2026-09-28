/-
  Branch-number floor for DoubleDeal decks, and tightness for GridCycle.

  Distinct decks differ in at least two seats (`two_le_hammingDist`). Any map
  that sends decks to decks and separates them therefore has branch number at
  least 4 (`four_le_branch`): two seats in, two seats out. That floor is
  attained by GridCycle. Swapping walk cards 50 and 51 leaves the seat walk
  unchanged — seats `0..50` depend only on cards below them, and seat 51 is
  the one seat left — so the output differs in exactly those two cards
  (`mixColumns_swap_tail`). The same argument applies to every `FreeChooser`,
  including the frozen v8 model.

  Walk card 0 is always placed at `(2,0)` and scooped to output seat 26
  (`mixColumns_seat26`).

  This is not a wide-trail bound, and not a bit-security claim. It does not
  classify the other weight-2 GridCycle swaps, and it says nothing about
  SumRanks or keyed rounds.
-/
import Mathlib.Data.Finset.Card
import Mathlib.InformationTheory.Hamming
import Mathlib.Logic.Function.Basic
import DoubleDealSecurity.GridCycle

namespace DoubleDeal.Security

open DoubleDeal

/-- Exchange the cards at seats `i` and `j`. -/
def swapAt (m : Fin 52 → Nat) (i j : Fin 52) : Fin 52 → Nat :=
  m ∘ Equiv.swap i j

theorem swapAt_left (m : Fin 52 → Nat) (i j : Fin 52) : swapAt m i j i = m j := by
  simp [swapAt, Equiv.swap_apply_left]

theorem swapAt_right (m : Fin 52 → Nat) (i j : Fin 52) : swapAt m i j j = m i := by
  simp [swapAt, Equiv.swap_apply_right]

theorem swapAt_of_ne (m : Fin 52 → Nat) {i j k : Fin 52} (hi : k ≠ i) (hj : k ≠ j) :
    swapAt m i j k = m k := by
  simp [swapAt, Equiv.swap_apply_of_ne_of_ne hi hj]

theorem swapAt_ne_iff {m : Fin 52 → Nat} (hm : Function.Injective m) {i j : Fin 52}
    (hij : i ≠ j) (k : Fin 52) : m k ≠ swapAt m i j k ↔ k = i ∨ k = j := by
  constructor
  · intro hne
    by_cases hi : k = i
    · exact Or.inl hi
    · by_cases hj : k = j
      · exact Or.inr hj
      · exact False.elim (hne (swapAt_of_ne m hi hj).symm)
  · intro hk
    rcases hk with rfl | rfl
    · rw [swapAt_left]
      exact fun h => hij (hm h)
    · rw [swapAt_right]
      exact fun h => hij (hm h.symm)

/-- A deck uses every card value. -/
theorem isDeck_surj {m : Fin 52 → Nat} (hm : IsDeck m) {c : Nat} (hc : c < 52) :
    ∃ i, m i = c :=
  let ⟨i, hi⟩ := (deckPerm m hm).surjective ⟨c, hc⟩
  ⟨i, congrArg Fin.val hi⟩

/-- (T0, PROVED) Distinct decks differ in at least two seats. One differing
    seat would leave the other 51 cards fixed, so the missing value at that
    seat could not occur anywhere else. -/
theorem two_le_hammingDist {a b : Fin 52 → Nat} (ha : IsDeck a) (hb : IsDeck b) (h : a ≠ b) :
    2 ≤ hammingDist a b := by
  have hpos := hammingDist_pos.2 h
  by_contra hlt
  obtain ⟨k, hk⟩ := Finset.card_eq_one.mp (show hammingDist a b = 1 by omega)
  have mem : ∀ j, a j ≠ b j ↔ j = k := fun j => by
    simpa using congrArg (j ∈ ·) hk
  obtain ⟨j, hj⟩ := isDeck_surj ha (hb.1 k)
  have hjk : j ≠ k := fun e => (mem k).2 rfl (e ▸ hj)
  exact hjk (hb.2 (hj ▸ (not_not.1 (mt (mem j).1 hjk)).symm))

/-- Swapping two distinct seats of an injective packet changes exactly those
    two seats. -/
theorem hammingDist_swapAt {m : Fin 52 → Nat} (hm : Function.Injective m) {i j : Fin 52}
    (hij : i ≠ j) : hammingDist m (swapAt m i j) = 2 := by
  classical
  have hset :
      (Finset.univ.filter fun k => m k ≠ swapAt m i j k) = {i, j} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    exact swapAt_ne_iff hm hij k
  rw [hammingDist, hset]
  exact Finset.card_pair hij

/-- (PROVED) Trivial branch-number floor: a map that preserves decks and
    separates them moves at least two seats on the way in and at least two on
    the way out. -/
theorem four_le_branch {F : (Fin 52 → Nat) → (Fin 52 → Nat)}
    (hdeck : ∀ m, IsDeck m → IsDeck (F m))
    (hsep : ∀ {a b : Fin 52 → Nat}, IsDeck a → IsDeck b → a ≠ b → F a ≠ F b)
    {a b : Fin 52 → Nat} (ha : IsDeck a) (hb : IsDeck b) (h : a ≠ b) :
    4 ≤ hammingDist a b + hammingDist (F a) (F b) := by
  have h1 := two_le_hammingDist ha hb h
  have h2 := two_le_hammingDist (hdeck a ha) (hdeck b hb) (hsep ha hb h)
  omega

/-! ## GridCycle tail

`placeW ch hand n` reads `hand` only at indices `< n`. Seats `0..50` are
therefore fixed by a swap of walk cards 50 and 51, and seat 51 is whatever
grid seat those 51 seats did not use. -/

theorem placeW_depends_on_prefix (ch : Chooser) (hand hand' : Fin 52 → Nat) :
    ∀ n, (∀ k : Fin 52, k.val < n → hand k = hand' k) →
      placeW ch hand n = placeW ch hand' n
  | 0, _ => rfl
  | n + 1, h => by
      have hp := placeW_depends_on_prefix ch hand hand' n
        (fun k hk => h k (Nat.lt_succ_of_lt hk))
      simp only [placeW, hp]
      by_cases hn : n < 52
      · simp only [hn, ↓reduceDIte]
        have hc : hand ⟨n, hn⟩ = hand' ⟨n, hn⟩ := h ⟨n, hn⟩ (Nat.lt_succ_self n)
        simp [hc]
      · simp only [hn, ↓reduceDIte]

theorem seatW_depends_on_prefix (ch : Chooser) (hand hand' : Fin 52 → Nat) {n : Nat}
    (h : ∀ k : Fin 52, k.val < n → hand k = hand' k) :
    seatW ch hand n = seatW ch hand' n := by
  simp only [seatW, placeW_depends_on_prefix ch hand hand' n h]

/-- A swap of seats `i` and `j` does not change walk seats at indices
    `≤ min(i, j)`. Those seats are chosen from the strict prefix. -/
theorem seatW_swapAt_of_le (ch : Chooser) (m : Fin 52 → Nat) {i j : Fin 52} {n : Nat}
    (hi : n ≤ i.val) (hj : n ≤ j.val) :
    seatW ch (swapAt m i j) n = seatW ch m n := by
  refine seatW_depends_on_prefix ch (swapAt m i j) m ?_
  intro k hk
  have hki : k ≠ i := by
    intro heq
    exact Nat.lt_irrefl k.val (by
      have : k.val = i.val := congrArg Fin.val heq
      omega)
  have hkj : k ≠ j := by
    intro heq
    exact Nat.lt_irrefl k.val (by
      have : k.val = j.val := congrArg Fin.val heq
      omega)
  exact swapAt_of_ne m hki hkj

/-- Seat 51 is the unique grid seat not used by seats `0..50`. -/
theorem seatW_last (ch : Chooser) (hch : FreeChooser ch) (hand : Fin 52 → Nat)
    (p : Fin 4 × Fin 13)
    (hp : ∀ k : Fin 52, k.val < 51 → seatW ch hand k.val ≠ p) :
    seatW ch hand 51 = p := by
  obtain ⟨k, hk⟩ := seatW_surj ch hch hand p
  have hlt : ¬ k.val < 51 := fun h => hp k h hk
  have h51 : k.val = 51 := by have := k.isLt; omega
  have hk51 : k = 51 := Fin.ext h51
  subst hk51
  exact hk

theorem seatW_swap_tail (ch : Chooser) (hch : FreeChooser ch)
    (m : Fin 52 → Nat) (n : Nat) (hn : n < 52) :
    seatW ch (swapAt m 50 51) n = seatW ch m n := by
  by_cases hlt : n < 51
  · exact seatW_swapAt_of_le ch m (i := 50) (j := 51) (n := n) (by omega) (by omega)
  · have hn51 : n = 51 := by omega
    subst hn51
    refine seatW_last ch hch (swapAt m 50 51) (seatW ch m 51) ?_
    intro k hk
    rw [seatW_swapAt_of_le ch m (i := 50) (j := 51) (n := k.val) (by omega) (by omega)]
    exact (seatW_ne ch hch m hk (by decide)).symm

theorem hammingDist_gridW_swap_tail (ch : Chooser) (hch : FreeChooser ch)
    {m : Fin 52 → Nat} (hm : IsDeck m) :
    hammingDist (scoopRowMajor (gridW ch m))
      (scoopRowMajor (gridW ch (swapAt m 50 51))) = 2 := by
  classical
  let m' := swapAt m (50 : Fin 52) (51 : Fin 52)
  have hij : (50 : Fin 52) ≠ 51 := by decide
  have hval : m 50 ≠ m 51 := fun h => hij (hm.2 h)
  have htne : rmFlat (seatW ch m 50).1 (seatW ch m 50).2 ≠
      rmFlat (seatW ch m 51).1 (seatW ch m 51).2 := by
    intro h
    have h1 := rm_rmFlat (seatW ch m 50).1 (seatW ch m 50).2
    have h2 := rm_rmFlat (seatW ch m 51).1 (seatW ch m 51).2
    have hr : (seatW ch m 50).1 = (seatW ch m 51).1 := by rw [← h1.1, h, h2.1]
    have hc : (seatW ch m 50).2 = (seatW ch m 51).2 := by rw [← h1.2, h, h2.2]
    exact (seatW_ne ch hch m (by decide : (50 : Nat) < 51) (by decide)).symm
      (Prod.ext hr hc)
  have hchar : ∀ t : Fin 52,
      scoopRowMajor (gridW ch m) t ≠ scoopRowMajor (gridW ch m') t ↔
        t = rmFlat (seatW ch m 50).1 (seatW ch m 50).2 ∨
          t = rmFlat (seatW ch m 51).1 (seatW ch m 51).2 := by
    intro t
    obtain ⟨n, hn⟩ := seatW_surj ch hch m (rmRow t, rmCol t)
    have hn' : seatW ch m' n.val = (rmRow t, rmCol t) := by
      rw [seatW_swap_tail ch hch m n.val n.isLt, hn]
    have hg := scoop_eq_hand_at ch hch m t n hn
    have hg' := scoop_eq_hand_at ch hch m' t n hn'
    constructor
    · intro hne
      have hmk : m n ≠ m' n := by
        intro heq
        exact hne (by rw [hg, hg', heq])
      rcases (swapAt_ne_iff hm.2 hij n).mp hmk with rfl | rfl
      · left
        rw [(rmFlat_rm t).symm]
        congr 1
        · exact (congrArg Prod.fst hn).symm
        · exact (congrArg Prod.snd hn).symm
      · right
        rw [(rmFlat_rm t).symm]
        congr 1
        · exact (congrArg Prod.fst hn).symm
        · exact (congrArg Prod.snd hn).symm
    · intro ht
      rcases ht with ht | ht
      · have hseat : seatW ch m n.val = seatW ch m 50 := by
          apply Prod.ext
          · rw [congrArg Prod.fst hn, ht]
            exact (rm_rmFlat _ _).1
          · rw [congrArg Prod.snd hn, ht]
            exact (rm_rmFlat _ _).2
        have hn50 : n = 50 := seatW_injective ch hch m hseat
        have hm' : m' 50 = m 51 := by simp [m', swapAt_left]
        rw [hg, hg', hn50, hm']
        exact hval
      · have hseat : seatW ch m n.val = seatW ch m 51 := by
          apply Prod.ext
          · rw [congrArg Prod.fst hn, ht]
            exact (rm_rmFlat _ _).1
          · rw [congrArg Prod.snd hn, ht]
            exact (rm_rmFlat _ _).2
        have hn51 : n = 51 := seatW_injective ch hch m hseat
        have hm' : m' 51 = m 50 := by simp [m', swapAt_right]
        rw [hg, hg', hn51, hm']
        exact hval.symm
  have hset :
      (Finset.univ.filter fun t =>
        scoopRowMajor (gridW ch m) t ≠ scoopRowMajor (gridW ch m') t) =
      {rmFlat (seatW ch m 50).1 (seatW ch m 50).2,
       rmFlat (seatW ch m 51).1 (seatW ch m 51).2} := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    exact hchar t
  rw [hammingDist, hset]
  exact Finset.card_pair htne

/-- The placed grid determines the hand: card `n` is what the final grid
    stores at seat `n`, and seat `n` is fixed by the prefix. -/
theorem hand_eq_of_gridW_eq (ch : Chooser) (hch : FreeChooser ch) {a b : Fin 52 → Nat}
    (h : gridW ch a = gridW ch b) : a = b := by
  suffices H : ∀ n, n ≤ 52 →
      placeW ch a n = placeW ch b n ∧ ∀ k : Fin 52, k.val < n → a k = b k by
    funext k
    exact (H 52 (le_refl _)).2 k k.isLt
  intro n hn
  induction n with
  | zero =>
      exact ⟨rfl, fun k hk => (Nat.not_lt_zero _ hk).elim⟩
  | succ n ih =>
      have hlt : n < 52 := by omega
      obtain ⟨hp, hc⟩ := ih (by omega)
      have hcard : a ⟨n, hlt⟩ = b ⟨n, hlt⟩ := by
        have ha := gridW_at_seat ch hch a ⟨n, hlt⟩
        have hb := gridW_at_seat ch hch b ⟨n, hlt⟩
        have hseat : seatW ch a n = seatW ch b n := by simp [seatW, hp]
        rw [← ha, h, hseat, hb]
      refine ⟨?_, ?_⟩
      · simp only [placeW, hlt, ↓reduceDIte, hp, hcard]
      · intro k hk
        rcases lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hk' | hk'
        · exact hc k hk'
        · have : k = ⟨n, hlt⟩ := Fin.ext hk'
          simpa [this] using hcard

theorem scoop_gridW_inj (ch : Chooser) (hch : FreeChooser ch) {a b : Fin 52 → Nat}
    (h : scoopRowMajor (gridW ch a) = scoopRowMajor (gridW ch b)) : a = b := by
  apply hand_eq_of_gridW_eq ch hch
  have := congrArg layRowMajor h
  rwa [lay_scoop_rowMajor, lay_scoop_rowMajor] at this

/-! ## Live (v11) GridCycle (`mixColumns`) -/

/-- (T1, PROVED) For every deck, swapping walk cards 50 and 51 changes
    exactly two output seats of GridCycle. -/
theorem mixColumns_swap_tail (m : Fin 52 → Nat) (hm : IsDeck m) :
    hammingDist (mixColumns m) (mixColumns (swapAt m 50 51)) = 2 := by
  simpa only [mixColumns_eq] using
    hammingDist_gridW_swap_tail chooseSeat! freeChooser_v9 hm

/-- (PROVED) Generic seat 26: if the walk places card 0 at `(2, 0)`, the
    row-major scoop returns it at output seat 26. -/
theorem scoop_gridW_seat26 (ch : Chooser) (hch : FreeChooser ch) (m : Fin 52 → Nat)
    (h0 : seatW ch m 0 = asStart) : scoopRowMajor (gridW ch m) 26 = m 0 := by
  have hidx : rmRow (26 : Fin 52) = asStart.1 ∧ rmCol (26 : Fin 52) = asStart.2 := by
    decide
  rw [scoopRowMajor, hidx.1, hidx.2, ← h0]
  exact gridW_at_seat ch hch m (0 : Fin 52)

/-- (PROVED) Walk card 0 is placed at `(2, 0)` and scooped to output seat 26. -/
theorem mixColumns_seat26 (m : Fin 52 → Nat) : mixColumns m 26 = m 0 := by
  rw [mixColumns_eq]
  exact scoop_gridW_seat26 chooseSeat! freeChooser_v9 m (by simpa [walkSeat_eq] using walkSeat_zero m)

/-- (PROVED) `invMixColumns ∘ mixColumns = id`, so GridCycle separates decks. -/
theorem mixColumns_separates {a b : Fin 52 → Nat} (h : mixColumns a = mixColumns b) : a = b :=
  Function.LeftInverse.injective invMixColumns_mixColumns h

/-- (PROVED) Branch number of the live (v11) GridCycle, on decks, is at least 4. -/
theorem four_le_mixColumns_branch {a b : Fin 52 → Nat} (ha : IsDeck a) (hb : IsDeck b)
    (h : a ≠ b) :
    4 ≤ hammingDist a b + hammingDist (mixColumns a) (mixColumns b) := by
  exact four_le_branch (F := mixColumns)
    (fun m hm => by simpa only [mixColumns_eq] using isDeck_scoop_gridW chooseSeat! freeChooser_v9 hm)
    (fun _ _ hab heq => hab (mixColumns_separates heq)) ha hb h

/-- (PROVED) The walk-card tail swap attains the floor: input weight 2 and
    output weight 2. -/
theorem mixColumns_tail_branch (m : Fin 52 → Nat) (hm : IsDeck m) :
    hammingDist m (swapAt m 50 51) +
      hammingDist (mixColumns m) (mixColumns (swapAt m 50 51)) = 4 := by
  have hne : (50 : Fin 52) ≠ 51 := by decide
  rw [hammingDist_swapAt hm.2 hne, mixColumns_swap_tail m hm]

/-! ## Frozen v8 GridCycle

The tail argument never uses the overflow rule, only `FreeChooser`. -/

theorem V8.seatW_zero (hand : Fin 52 → Nat) : seatW V8.chooseSeat! hand 0 = asStart := by
  simp [seatW, placeW, initWalk, V8.chooseSeat!, V8.chooseSeat?]

/-- (PROVED) v8 GridCycle, same tail swap: output weight exactly 2. -/
theorem v8_mixColumns_swap_tail (m : Fin 52 → Nat) (hm : IsDeck m) :
    hammingDist (V8.mixColumns m) (V8.mixColumns (swapAt m 50 51)) = 2 := by
  simpa only [V8.mixColumns_eq] using
    hammingDist_gridW_swap_tail V8.chooseSeat! V8.freeChooser hm

/-- (PROVED) v8 walk card 0 is also scooped to output seat 26. -/
theorem v8_mixColumns_seat26 (m : Fin 52 → Nat) : V8.mixColumns m 26 = m 0 := by
  rw [V8.mixColumns_eq]
  exact scoop_gridW_seat26 V8.chooseSeat! V8.freeChooser m (V8.seatW_zero m)

theorem isDeck_v8_mixColumns {m : Fin 52 → Nat} (hm : IsDeck m) :
    IsDeck (V8.mixColumns m) := by
  simpa only [V8.mixColumns_eq] using isDeck_scoop_gridW V8.chooseSeat! V8.freeChooser hm

theorem v8_mixColumns_separates {a b : Fin 52 → Nat}
    (h : V8.mixColumns a = V8.mixColumns b) : a = b := by
  apply scoop_gridW_inj V8.chooseSeat! V8.freeChooser
  simpa only [V8.mixColumns_eq] using h

/-- (PROVED) Branch number of the frozen v8 GridCycle, on decks, is at least 4. -/
theorem four_le_v8_mixColumns_branch {a b : Fin 52 → Nat} (ha : IsDeck a) (hb : IsDeck b)
    (h : a ≠ b) :
    4 ≤ hammingDist a b + hammingDist (V8.mixColumns a) (V8.mixColumns b) := by
  exact four_le_branch (F := V8.mixColumns) (fun m hm => isDeck_v8_mixColumns hm)
    (fun _ _ hab heq => hab (v8_mixColumns_separates heq)) ha hb h

/-- (PROVED) The same tail swap attains the floor for v8 GridCycle. -/
theorem v8_mixColumns_tail_branch (m : Fin 52 → Nat) (hm : IsDeck m) :
    hammingDist m (swapAt m 50 51) +
      hammingDist (V8.mixColumns m) (V8.mixColumns (swapAt m 50 51)) = 4 := by
  have hne : (50 : Fin 52) ≠ 51 := by decide
  rw [hammingDist_swapAt hm.2 hne, v8_mixColumns_swap_tail m hm]

end DoubleDeal.Security
