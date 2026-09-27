/-
  The GridCycle seat walk, generic in the seat chooser (v9 `chooseSeat!` or the
  frozen v8 chooser). Proof-only: the placement lemmas of `GridCycle.lean`
  restated for an arbitrary chooser that always returns a free seat, plus
  "the 52 seats are distinct, hence cover the grid".
-/
import Mathlib.Data.Fintype.Prod
import DoubleDeal.Round

namespace DoubleDeal.Security

open DoubleDeal

/-- A seat chooser. -/
abbrev Chooser := WalkState → (Fin 4 × Fin 13) × Nat

/-- The walk of `GridCycle.placeN`, with the seat chooser as a parameter. -/
def placeW (ch : Chooser) (hand : Fin 52 → Nat) : Nat → NatGrid × WalkState
  | 0 => ((fun _ _ => (0 : Nat)), initWalk)
  | n + 1 =>
      let (g, st) := placeW ch hand n
      if h : n < 52 then
        let (pos, t') := ch st
        let card := hand ⟨n, h⟩
        (setGrid g pos card, advance st card pos t')
      else (g, st)

/-- The chooser returns a free seat while one exists (and, at the start, `AS`
    is free). -/
def FreeChooser (ch : Chooser) : Prop :=
  ∀ st : WalkState, occCount st.occ < 52 →
    (st.prev.isSome ∨ occAt st.occ asStart = false) → occAt st.occ (ch st).1 = false

theorem freeChooser_v9 : FreeChooser chooseSeat! := fun st h1 h2 => chooseSeat!_free st h1 h2

theorem placeN_eq_placeW (hand : Fin 52 → Nat) :
    ∀ n, placeN hand n = placeW chooseSeat! hand n
  | 0 => rfl
  | n + 1 => by
      simp only [placeN, placeW, placeN_eq_placeW hand n]

section
variable (ch : Chooser) (hch : FreeChooser ch)

/-- Seat of card `n`. -/
def seatW (hand : Fin 52 → Nat) (n : Nat) : Fin 4 × Fin 13 := (ch (placeW ch hand n).2).1

/-- The placed grid. -/
def gridW (hand : Fin 52 → Nat) : NatGrid := (placeW ch hand 52).1

theorem placeW_occ_size (hand : Fin 52 → Nat) :
    ∀ n, (placeW ch hand n).2.occ.size = 52
  | 0 => by simp [placeW, initWalk, size_emptyOcc]
  | n + 1 => by
      simp only [placeW]
      split
      · rw [advance, size_setOcc]; exact placeW_occ_size hand n
      · exact placeW_occ_size hand n

include hch in
theorem placeW_free_count (hand : Fin 52 → Nat) :
    ∀ n : Nat, n ≤ 52 → occCount (placeW ch hand n).2.occ = n ∧
      (n < 52 → occAt (placeW ch hand n).2.occ (seatW ch hand n) = false)
  | 0, _ => by
      refine ⟨by simp [placeW, initWalk, occCount_empty], fun _ => ?_⟩
      exact hch _ (by simp [placeW, initWalk, occCount_empty])
        (Or.inr (by simp [placeW, initWalk, occAt_empty]))
  | n + 1, hn => by
      have hlt : n < 52 := by omega
      obtain ⟨hc, hf⟩ := placeW_free_count hand n (by omega)
      have hf := hf hlt
      have hcount : occCount (placeW ch hand (n + 1)).2.occ = n + 1 := by
        simp only [placeW, hlt, ↓reduceDIte]
        change occCount (setOcc (placeW ch hand n).2.occ (seatW ch hand n)) = n + 1
        have := occCount_set_free (placeW ch hand n).2.occ (seatW ch hand n)
          (placeW_occ_size ch hand n) hf
        omega
      refine ⟨hcount, fun h => ?_⟩
      refine hch _ (by omega) (Or.inl ?_)
      simp [placeW, hlt, advance]

theorem occW_mono (hand : Fin 52 → Nat) :
    ∀ (m n : Nat), n ≤ m → m ≤ 52 → ∀ (p : Fin 4 × Fin 13),
      occAt (placeW ch hand n).2.occ p = true →
      occAt (placeW ch hand m).2.occ p = true
  | 0, n, hnm, _, p, hp => by
      have : n = 0 := by omega
      subst this; exact hp
  | m + 1, n, hnm, hm, p, hp => by
      by_cases hnm' : n ≤ m
      · have hprev := occW_mono hand m n hnm' (by omega) p hp
        have hlt : m < 52 := by omega
        simp only [placeW, hlt, ↓reduceDIte, advance]
        by_cases he : p = (ch (placeW ch hand m).2).1
        · cases he; exact setOcc_at_self _ _ (placeW_occ_size ch hand m)
        · rw [setOcc_at_ne (placeW ch hand m).2.occ (Ne.symm he) (placeW_occ_size ch hand m)]
          exact hprev
      · have : n = m + 1 := by omega
        cases this; exact hp

theorem seatW_occupied_after (hand : Fin 52 → Nat) (n : Nat) (hn : n < 52) :
    occAt (placeW ch hand (n + 1)).2.occ (seatW ch hand n) = true := by
  simp only [placeW, seatW, hn, ↓reduceDIte, advance]
  exact setOcc_at_self _ _ (placeW_occ_size ch hand n)

include hch in
/-- Distinct cards get distinct seats. -/
theorem seatW_ne (hand : Fin 52 → Nat) {k n : Nat} (hkn : k < n) (hn : n < 52) :
    seatW ch hand n ≠ seatW ch hand k := by
  intro he
  have hocc := occW_mono ch hand n (k + 1) (by omega) (by omega) _
    (seatW_occupied_after ch hand k (by omega))
  have hfree := (placeW_free_count ch hch hand n (by omega)).2 hn
  rw [he, hocc] at hfree
  exact Bool.noConfusion hfree

include hch in
theorem seatW_injective (hand : Fin 52 → Nat) :
    Function.Injective (fun k : Fin 52 => seatW ch hand k.val) := by
  intro a b h
  simp only at h
  rcases Nat.lt_trichotomy a.val b.val with hl | he | hg
  · exact absurd h.symm (seatW_ne ch hch hand hl b.isLt)
  · exact Fin.ext he
  · exact absurd h (seatW_ne ch hch hand hg a.isLt)

include hch in
/-- The 52 seats cover the 4×13 grid. -/
theorem seatW_surj (hand : Fin 52 → Nat) (p : Fin 4 × Fin 13) :
    ∃ k : Fin 52, seatW ch hand k.val = p := by
  have hb := (Fintype.bijective_iff_injective_and_card
    (fun k : Fin 52 => seatW ch hand k.val)).2 ⟨seatW_injective ch hch hand, by simp⟩
  exact hb.2 p

include hch in
theorem placeW_write_stable (hand : Fin 52 → Nat) (n : Nat) (hn : n < 52)
    (m : Nat) (hnm : n < m) (hm : m ≤ 52) :
    (placeW ch hand m).1 (seatW ch hand n).1 (seatW ch hand n).2 = hand ⟨n, hn⟩ := by
  induction m with
  | zero => omega
  | succ m ih =>
      have hlt : m < 52 := by omega
      simp only [placeW, hlt, ↓reduceDIte]
      by_cases hmn : m = n
      · cases hmn
        exact get_setGrid_self _ _ _
      · have hne : (ch (placeW ch hand m).2).1 ≠ seatW ch hand n := by
          rcases Nat.lt_or_gt_of_ne hmn with h | h
          · omega
          · exact seatW_ne ch hch hand h hlt
        rw [get_setGrid_ne (placeW ch hand m).1 (hand ⟨m, hlt⟩) hne]
        exact ih (by omega) (by omega)

include hch in
/-- Card `n` sits at its seat in the placed grid. -/
theorem gridW_at_seat (hand : Fin 52 → Nat) (n : Fin 52) :
    gridW ch hand (seatW ch hand n.val).1 (seatW ch hand n.val).2 = hand n :=
  placeW_write_stable ch hch hand n.val n.isLt 52 n.isLt (le_refl _)

end

end DoubleDeal.Security
