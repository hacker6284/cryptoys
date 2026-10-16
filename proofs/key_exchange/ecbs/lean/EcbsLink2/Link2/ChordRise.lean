/-
  The rise of `chord_add_demo`: copy the base up into the spare (mirrored when
  the cell is red) and take the accumulator up away. The spare is `fieldSub`.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.Add
import EcbsLink2.Link2.CopyMirror
import EcbsLink2.Link2.TailStay
import EcbsLink2.SpecBase

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- A trit list flipped coefficient-wise is still trits. -/
theorem mirrorTrits_allTrit {xs : List Nat} (h : allTritList xs) : allTritList (mirrorTrits xs) := by
  rw [mirrorTrits_flip]
  intro z hz
  rcases List.mem_map.mp hz with ⟨c, hc, rfl⟩
  have hc2 : c ≤ 2 := h c hc
  unfold flipTrit
  by_cases hz0 : c = 0
  · simp [hz0]
  · simp [hz0]
    omega

theorem mirror_length (xs : List Nat) : (mirrorTrits xs).length = xs.length := by
  rw [mirrorTrits_flip, List.length_map]

private theorem idx_eq {α : Type} {a b : Array α} (h : a = b) (i : Nat)
    (ha : i < a.size) : a[i] = b[i]'(h ▸ ha) := by
  cases h
  rfl

private theorem place_flag (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat) :
    (placeBoard b home hH hD xs moves peak).sudo_5Board_9marker_on =
      b.sudo_5Board_9marker_on := by
  unfold placeBoard
  dsimp only
  split <;> rfl

private theorem place_same (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat) :
    (placeBoard b home hH hD xs moves peak).sudo_5Board_1t = b.sudo_5Board_1t ∧
      (placeBoard b home hH hD xs moves peak).sudo_5Board_6marker = b.sudo_5Board_6marker ∧
      (placeBoard b home hH hD xs moves peak).sudo_5Board_4cost.sudo_5Costs_4ctrl =
        b.sudo_5Board_4cost.sudo_5Costs_4ctrl ∧
      (placeBoard b home hH hD xs moves peak).sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
        b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max ∧
      (placeBoard b home hH hD xs moves peak).sudo_5Board_4cost.sudo_5Costs_6slides =
        b.sudo_5Board_4cost.sudo_5Costs_6slides ∧
      (placeBoard b home hH hD xs moves peak).sudo_5Board_4cost.sudo_5Costs_3ops =
        b.sudo_5Board_4cost.sudo_5Costs_3ops ∧
      (placeBoard b home hH hD xs moves peak).sudo_5Board_8bench_on = b.sudo_5Board_8bench_on ∧
      (placeBoard b home hH hD xs moves peak).sudo_5Board_5bench = b.sudo_5Board_5bench ∧
      (placeBoard b home hH hD xs moves peak).sudo_5Board_8bench_to = b.sudo_5Board_8bench_to ∧
      (placeBoard b home hH hD xs moves peak).sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
        b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole ∧
      (placeBoard b home hH hD xs moves peak).sudo_5Board_4cost.sudo_5Costs_11peak_strict =
        b.sudo_5Board_4cost.sudo_5Costs_11peak_strict := by
  unfold placeBoard
  dsimp only
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem place_row (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat) :
    (placeBoard b home hH hD xs moves peak).sudo_5Board_3row = b.sudo_5Board_3row := by
  unfold placeBoard
  dsimp only
  split <;> rfl

private theorem place_stay (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat) (h3 : home ≠ 3) (h4 : home ≠ 4) :
    TailStay b (placeBoard b home hH hD xs moves peak) := by
  unfold placeBoard
  dsimp only
  split
  · exact TailStay.trans
      (TailStay.set_cell b home hH hD (embed xs) true (Int.ofNat (moves + pegCount xs)) h3 h4)
      (TailStay.of_eq rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)
  · exact TailStay.set_cell b home hH hD (embed xs) true (Int.ofNat (moves + pegCount xs)) h3 h4

private theorem add_stay (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (arr : Array Int) (mv : Nat)
    (h3 : home ≠ 3) (h4 : home ≠ 4) :
    TailStay b (addBoard b home hH arr mv) := by
  unfold addBoard withMoves
  refine TailStay.of_eq rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl ?_ rfl ?_ rfl
  · unfold homeD
    rw [Array.getElem?_set_ne _ _ _ (by simpa using h3)]
  · unfold homeD
    rw [Array.getElem?_set_ne _ _ _ (by simpa using h4)]

private theorem place_high (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat) :
    (placeBoard b home hH hD xs moves peak).sudo_5Board_4cost.sudo_5Costs_15control_highest =
      b.sudo_5Board_4cost.sudo_5Costs_15control_highest := by
  unfold placeBoard
  dsimp only
  split <;> rfl

private theorem place_home_at (b : Ecbs.Board)
    (hH : 6 < b.sudo_5Board_4home.size) (hD : 6 < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak i : Nat) (hne : (6 : Nat) ≠ i)
    (hi : i < b.sudo_5Board_4home.size) :
    (placeBoard b 6 hH hD xs moves peak).sudo_5Board_4home[i]'(by
      rw [place_home_eq, Array.size_set]; exact hi) = b.sudo_5Board_4home[i] := by
  have hset := place_home_eq b 6 hH hD xs moves peak
  have hget := idx_eq hset i (by rw [hset, Array.size_set]; exact hi)
  simp only [Array.getElem_set, hne, if_false] at hget
  exact hget

private theorem place_held_at (b : Ecbs.Board)
    (hH : 6 < b.sudo_5Board_4home.size) (hD : 6 < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak i : Nat) (hne : (6 : Nat) ≠ i)
    (hi : i < b.sudo_5Board_4held.size) :
    (placeBoard b 6 hH hD xs moves peak).sudo_5Board_4held[i]'(by
      rw [place_held_eq, Array.size_set]; exact hi) = b.sudo_5Board_4held[i] := by
  have hset := place_held_eq b 6 hH hD xs moves peak
  have hget := idx_eq hset i (by rw [hset, Array.size_set]; exact hi)
  simp only [Array.getElem_set, hne, if_false] at hget
  exact hget

/-- `add` of the spare by the up, mirror on. The spare becomes `fieldSub`.
    Up and base up stay. The marker flag stays. -/
theorem rise_add (b : Ecbs.Board) (ySrc accY baseY : List Nat) (n moves : Nat)
    (hszH : b.sudo_5Board_4home.size = 8) (hszD : b.sudo_5Board_4held.size = 8)
    (hyS : ySrc.length = n) (hyA : accY.length = n) (hpos : 0 < n)
    (htriS : allTritList ySrc) (htriA : allTritList accY)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hfit : FitsLen (moves + n))
    (h6t : ∀ h : 6 < b.sudo_5Board_4held.size, b.sudo_5Board_4held[6] = true)
    (h6a : ∀ h : 6 < b.sudo_5Board_4home.size, b.sudo_5Board_4home[6] = embed ySrc)
    (h1t : ∀ h : 1 < b.sudo_5Board_4held.size, b.sudo_5Board_4held[1] = true)
    (h1a : ∀ h : 1 < b.sudo_5Board_4home.size, b.sudo_5Board_4home[1] = embed accY)
    (h4t : ∀ h : 4 < b.sudo_5Board_4held.size, b.sudo_5Board_4held[4] = true)
    (h4a : ∀ h : 4 < b.sudo_5Board_4home.size, b.sudo_5Board_4home[4] = embed baseY) :
    ∃ bR,
      Ecbs.add b Ecbs.spare Ecbs.up true = .ok bR ∧
      (∀ h : 6 < bR.sudo_5Board_4home.size,
        bR.sudo_5Board_4home[6] = embed (fieldSub n ySrc accY)) ∧
      (∀ h : 6 < bR.sudo_5Board_4held.size, bR.sudo_5Board_4held[6] = true) ∧
      (∀ h : 1 < bR.sudo_5Board_4home.size, bR.sudo_5Board_4home[1] = embed accY) ∧
      (∀ h : 1 < bR.sudo_5Board_4held.size, bR.sudo_5Board_4held[1] = true) ∧
      (∀ h : 4 < bR.sudo_5Board_4home.size, bR.sudo_5Board_4home[4] = embed baseY) ∧
      (∀ h : 4 < bR.sudo_5Board_4held.size, bR.sudo_5Board_4held[4] = true) ∧
      bR.sudo_5Board_4held.size = 8 ∧
      bR.sudo_5Board_4home.size = 8 ∧
      bR.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) ∧
      bR.sudo_5Board_4cost.sudo_5Costs_5moves =
        ((moves + pegCount accY : Nat) : Int) ∧
      bR.sudo_5Board_9marker_on = b.sudo_5Board_9marker_on ∧
      (∀ h : 0 < bR.sudo_5Board_4home.size,
        bR.sudo_5Board_4home[0] = b.sudo_5Board_4home[0]'(by rw [hszH]; decide)) ∧
      (∀ h : 0 < bR.sudo_5Board_4held.size,
        bR.sudo_5Board_4held[0] = b.sudo_5Board_4held[0]'(by rw [hszD]; decide)) ∧
      (∀ h : 2 < bR.sudo_5Board_4home.size,
        bR.sudo_5Board_4home[2] = b.sudo_5Board_4home[2]'(by rw [hszH]; decide)) ∧
      (∀ h : 2 < bR.sudo_5Board_4held.size,
        bR.sudo_5Board_4held[2] = b.sudo_5Board_4held[2]'(by rw [hszD]; decide)) ∧
      (∀ h : 5 < bR.sudo_5Board_4home.size,
        bR.sudo_5Board_4home[5] = b.sudo_5Board_4home[5]'(by rw [hszH]; decide)) ∧
      (∀ h : 5 < bR.sudo_5Board_4held.size,
        bR.sudo_5Board_4held[5] = b.sudo_5Board_4held[5]'(by rw [hszD]; decide)) ∧
      bR.sudo_5Board_1t = b.sudo_5Board_1t ∧
      bR.sudo_5Board_6marker = b.sudo_5Board_6marker ∧
      bR.sudo_5Board_4cost.sudo_5Costs_4ctrl = b.sudo_5Board_4cost.sudo_5Costs_4ctrl ∧
      bR.sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
        b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max ∧
      bR.sudo_5Board_4cost.sudo_5Costs_6slides = b.sudo_5Board_4cost.sudo_5Costs_6slides ∧
      bR.sudo_5Board_4cost.sudo_5Costs_3ops = b.sudo_5Board_4cost.sudo_5Costs_3ops ∧
      bR.sudo_5Board_8bench_on = b.sudo_5Board_8bench_on ∧
      bR.sudo_5Board_5bench = b.sudo_5Board_5bench ∧
      bR.sudo_5Board_8bench_to = b.sudo_5Board_8bench_to ∧
      bR.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
        b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole ∧
      bR.sudo_5Board_4cost.sudo_5Costs_11peak_strict =
        b.sudo_5Board_4cost.sudo_5Costs_11peak_strict ∧
      bR.sudo_5Board_4cost.sudo_5Costs_4peak = b.sudo_5Board_4cost.sudo_5Costs_4peak ∧
      bR.sudo_5Board_4cost.sudo_5Costs_15control_highest =
        b.sudo_5Board_4cost.sudo_5Costs_15control_highest ∧
      TailStay b bR ∧
      bR.sudo_5Board_3row = b.sudo_5Board_3row := by
  have h6H : 6 < b.sudo_5Board_4home.size := by rw [hszH]; decide
  have h6D : 6 < b.sudo_5Board_4held.size := by rw [hszD]; decide
  have h1H : 1 < b.sudo_5Board_4home.size := by rw [hszH]; decide
  have h1D : 1 < b.sudo_5Board_4held.size := by rw [hszD]; decide
  have h4H : 4 < b.sudo_5Board_4home.size := by rw [hszH]; decide
  have h4D : 4 < b.sudo_5Board_4held.size := by rw [hszD]; decide
  have hadd := add_refines b 6 1 ySrc accY n moves h6H h6D h1H h1D
    (h6t h6D) (h6a h6H) (h1t h1D) (h1a h1H) hn hyA hyS hpos htriS htriA hmoves hfit
  let bR := addBoard b 6 h6H (embed (fieldAdd n ySrc (mirrorTrits accY)))
    (moves + pegCount accY)
  have hsub : fieldAdd n ySrc (mirrorTrits accY) = fieldSub n ySrc accY := rfl
  refine ⟨bR, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show Ecbs.spare = ((6 : Nat) : Int) from rfl,
        show Ecbs.up = ((1 : Nat) : Int) from rfl]
    simpa [bR, hsub] using hadd
  · intro h
    have hset : bR.sudo_5Board_4home =
        b.sudo_5Board_4home.set ⟨6, h6H⟩ (embed (fieldAdd n ySrc (mirrorTrits accY))) := by
      simp [bR, addBoard, withMoves]
    have hget := idx_eq hset 6 h
    simp only [Array.getElem_set, if_true] at hget
    simpa [hsub] using hget
  · intro h
    have hheld : bR.sudo_5Board_4held = b.sudo_5Board_4held := by
      simp [bR, addBoard, withMoves]
    simpa [hheld] using h6t h6D
  · intro h
    have hset : bR.sudo_5Board_4home =
        b.sudo_5Board_4home.set ⟨6, h6H⟩ (embed (fieldAdd n ySrc (mirrorTrits accY))) := by
      simp [bR, addBoard, withMoves]
    have hget := idx_eq hset 1 h
    have hne : (6 : Nat) ≠ 1 := by decide
    simp only [Array.getElem_set, hne, if_false] at hget
    exact hget.trans (h1a h1H)
  · intro h
    have hheld : bR.sudo_5Board_4held = b.sudo_5Board_4held := by
      simp [bR, addBoard, withMoves]
    simpa [hheld] using h1t h1D
  · intro h
    have hset : bR.sudo_5Board_4home =
        b.sudo_5Board_4home.set ⟨6, h6H⟩ (embed (fieldAdd n ySrc (mirrorTrits accY))) := by
      simp [bR, addBoard, withMoves]
    have hget := idx_eq hset 4 h
    have hne : (6 : Nat) ≠ 4 := by decide
    simp only [Array.getElem_set, hne, if_false] at hget
    exact hget.trans (h4a h4H)
  · intro h
    have hheld : bR.sudo_5Board_4held = b.sudo_5Board_4held := by
      simp [bR, addBoard, withMoves]
    simpa [hheld] using h4t h4D
  · have hheld : bR.sudo_5Board_4held = b.sudo_5Board_4held := by
      simp [bR, addBoard, withMoves]
    rw [hheld, hszD]
  · have hhome : bR.sudo_5Board_4home =
        b.sudo_5Board_4home.set ⟨6, h6H⟩ (embed (fieldAdd n ySrc (mirrorTrits accY))) := by
      simp [bR, addBoard, withMoves]
    rw [hhome, Array.size_set, hszH]
  · have ht : bR.sudo_5Board_1t = b.sudo_5Board_1t := by
      simp [bR, addBoard, withMoves]
    rw [ht, hn]
  · simp [bR, addBoard, withMoves, ofNat_eq_natCast]
  · simp [bR, addBoard, withMoves]
  · intro h
    have hset : bR.sudo_5Board_4home =
        b.sudo_5Board_4home.set ⟨6, h6H⟩ (embed (fieldAdd n ySrc (mirrorTrits accY))) := by
      simp [bR, addBoard, withMoves]
    have h0 : 0 < b.sudo_5Board_4home.size := by rw [hszH]; decide
    have hget := idx_eq hset 0 (by rw [hset, Array.size_set]; exact h0)
    have hne : (6 : Nat) ≠ 0 := by decide
    simp only [Array.getElem_set, hne, if_false] at hget
    exact hget
  · intro h
    have hheld : bR.sudo_5Board_4held = b.sudo_5Board_4held := by
      simp [bR, addBoard, withMoves]
    have h0 : 0 < b.sudo_5Board_4held.size := by rw [hszD]; decide
    exact idx_eq hheld 0 (by rw [hheld]; exact h0)
  · intro h
    have hset : bR.sudo_5Board_4home =
        b.sudo_5Board_4home.set ⟨6, h6H⟩ (embed (fieldAdd n ySrc (mirrorTrits accY))) := by
      simp [bR, addBoard, withMoves]
    have h2 : 2 < b.sudo_5Board_4home.size := by rw [hszH]; decide
    have hget := idx_eq hset 2 (by rw [hset, Array.size_set]; exact h2)
    have hne : (6 : Nat) ≠ 2 := by decide
    simp only [Array.getElem_set, hne, if_false] at hget
    exact hget
  · intro h
    have hheld : bR.sudo_5Board_4held = b.sudo_5Board_4held := by
      simp [bR, addBoard, withMoves]
    have h2 : 2 < b.sudo_5Board_4held.size := by rw [hszD]; decide
    exact idx_eq hheld 2 (by rw [hheld]; exact h2)
  · intro h
    have hset : bR.sudo_5Board_4home =
        b.sudo_5Board_4home.set ⟨6, h6H⟩ (embed (fieldAdd n ySrc (mirrorTrits accY))) := by
      simp [bR, addBoard, withMoves]
    have h5 : 5 < b.sudo_5Board_4home.size := by rw [hszH]; decide
    have hget := idx_eq hset 5 (by rw [hset, Array.size_set]; exact h5)
    have hne : (6 : Nat) ≠ 5 := by decide
    simp only [Array.getElem_set, hne, if_false] at hget
    exact hget
  · intro h
    have hheld : bR.sudo_5Board_4held = b.sudo_5Board_4held := by
      simp [bR, addBoard, withMoves]
    have h5 : 5 < b.sudo_5Board_4held.size := by rw [hszD]; decide
    exact idx_eq hheld 5 (by rw [hheld]; exact h5)
  · simp [bR, addBoard, withMoves]
  · simp [bR, addBoard, withMoves]
  · simp [bR, addBoard, withMoves]
  · simp [bR, addBoard, withMoves]
  · simp [bR, addBoard, withMoves]
  · simp [bR, addBoard, withMoves]
  · simp [bR, addBoard, withMoves]
  · simp [bR, addBoard, withMoves]
  · simp [bR, addBoard, withMoves]
  · simp [bR, addBoard, withMoves]
  · simp [bR, addBoard, withMoves]
  · simp [bR, addBoard, withMoves]
  · simp [bR, addBoard, withMoves]
  · exact add_stay b 6 h6H (embed (fieldAdd n ySrc (mirrorTrits accY)))
      (moves + pegCount accY) (by decide) (by decide)
  · exact addBoard_row b 6 h6H (embed (fieldAdd n ySrc (mirrorTrits accY)))
      (moves + pegCount accY)

/-- What `place` of the spare leaves: that home holds `ys`, and up and base up stay. -/
theorem place_spare (b : Ecbs.Board) (ys accY baseY : List Nat) (moves peak : Nat)
    (h6H : 6 < b.sudo_5Board_4home.size) (h6D : 6 < b.sudo_5Board_4held.size)
    (hszH : b.sudo_5Board_4home.size = 8) (hszD : b.sudo_5Board_4held.size = 8)
    (h1t : b.sudo_5Board_4held[1]'(by rw [hszD]; decide) = true)
    (h1a : b.sudo_5Board_4home[1]'(by rw [hszH]; decide) = embed accY)
    (h4t : b.sudo_5Board_4held[4]'(by rw [hszD]; decide) = true)
    (h4a : b.sudo_5Board_4home[4]'(by rw [hszH]; decide) = embed baseY) :
    (placeBoard b 6 h6H h6D ys moves peak).sudo_5Board_4home.size = 8 ∧
      (placeBoard b 6 h6H h6D ys moves peak).sudo_5Board_4held.size = 8 ∧
      (placeBoard b 6 h6H h6D ys moves peak).sudo_5Board_1t.sudo_4Tier_1n =
        b.sudo_5Board_1t.sudo_4Tier_1n ∧
      (placeBoard b 6 h6H h6D ys moves peak).sudo_5Board_4cost.sudo_5Costs_5moves =
        Int.ofNat (moves + pegCount ys) ∧
      (placeBoard b 6 h6H h6D ys moves peak).sudo_5Board_9marker_on =
        b.sudo_5Board_9marker_on ∧
      (∀ h : 6 < (placeBoard b 6 h6H h6D ys moves peak).sudo_5Board_4home.size,
        (placeBoard b 6 h6H h6D ys moves peak).sudo_5Board_4home[6] = embed ys) ∧
      (∀ h : 6 < (placeBoard b 6 h6H h6D ys moves peak).sudo_5Board_4held.size,
        (placeBoard b 6 h6H h6D ys moves peak).sudo_5Board_4held[6] = true) ∧
      (∀ h : 1 < (placeBoard b 6 h6H h6D ys moves peak).sudo_5Board_4home.size,
        (placeBoard b 6 h6H h6D ys moves peak).sudo_5Board_4home[1] = embed accY) ∧
      (∀ h : 1 < (placeBoard b 6 h6H h6D ys moves peak).sudo_5Board_4held.size,
        (placeBoard b 6 h6H h6D ys moves peak).sudo_5Board_4held[1] = true) ∧
      (∀ h : 4 < (placeBoard b 6 h6H h6D ys moves peak).sudo_5Board_4home.size,
        (placeBoard b 6 h6H h6D ys moves peak).sudo_5Board_4home[4] = embed baseY) ∧
      (∀ h : 4 < (placeBoard b 6 h6H h6D ys moves peak).sudo_5Board_4held.size,
        (placeBoard b 6 h6H h6D ys moves peak).sudo_5Board_4held[4] = true) := by
  let b1 := placeBoard b 6 h6H h6D ys moves peak
  change
    b1.sudo_5Board_4home.size = 8 ∧
      b1.sudo_5Board_4held.size = 8 ∧
      b1.sudo_5Board_1t.sudo_4Tier_1n = b.sudo_5Board_1t.sudo_4Tier_1n ∧
      b1.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat (moves + pegCount ys) ∧
      b1.sudo_5Board_9marker_on = b.sudo_5Board_9marker_on ∧
      (∀ h : 6 < b1.sudo_5Board_4home.size, b1.sudo_5Board_4home[6] = embed ys) ∧
      (∀ h : 6 < b1.sudo_5Board_4held.size, b1.sudo_5Board_4held[6] = true) ∧
      (∀ h : 1 < b1.sudo_5Board_4home.size, b1.sudo_5Board_4home[1] = embed accY) ∧
      (∀ h : 1 < b1.sudo_5Board_4held.size, b1.sudo_5Board_4held[1] = true) ∧
      (∀ h : 4 < b1.sudo_5Board_4home.size, b1.sudo_5Board_4home[4] = embed baseY) ∧
      (∀ h : 4 < b1.sudo_5Board_4held.size, b1.sudo_5Board_4held[4] = true)
  have hszH1 : b1.sudo_5Board_4home.size = 8 := by
    rw [place_home_eq, Array.size_set, hszH]
  have hszD1 : b1.sudo_5Board_4held.size = 8 := by
    rw [place_held_eq, Array.size_set, hszD]
  have h1B : 1 < b.sudo_5Board_4held.size := by rw [hszD]; decide
  have h1HB : 1 < b.sudo_5Board_4home.size := by rw [hszH]; decide
  have h4B : 4 < b.sudo_5Board_4held.size := by rw [hszD]; decide
  have h4HB : 4 < b.sudo_5Board_4home.size := by rw [hszH]; decide
  refine ⟨hszH1, hszD1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [place_tier_eq]
  · exact place_moves_eq b 6 h6H h6D ys moves peak
  · exact place_flag b 6 h6H h6D ys moves peak
  · intro h
    have hset := place_home_eq b 6 h6H h6D ys moves peak
    have hget := idx_eq hset 6 h
    simp only [Array.getElem_set, if_true] at hget
    exact hget
  · intro h
    have hset := place_held_eq b 6 h6H h6D ys moves peak
    have hget := idx_eq hset 6 h
    simp only [Array.getElem_set, if_true] at hget
    exact hget
  · intro h
    have hset := place_home_eq b 6 h6H h6D ys moves peak
    have hget := idx_eq hset 1 (by rw [hset, Array.size_set]; exact h1HB)
    have hne : (6 : Nat) ≠ 1 := by decide
    simp only [Array.getElem_set, hne, if_false] at hget
    exact hget.trans h1a
  · intro h
    have hset := place_held_eq b 6 h6H h6D ys moves peak
    have hget := idx_eq hset 1 (by rw [hset, Array.size_set]; exact h1B)
    have hne : (6 : Nat) ≠ 1 := by decide
    simp only [Array.getElem_set, hne, if_false] at hget
    exact hget.trans h1t
  · intro h
    have hset := place_home_eq b 6 h6H h6D ys moves peak
    have hget := idx_eq hset 4 (by rw [hset, Array.size_set]; exact h4HB)
    have hne : (6 : Nat) ≠ 4 := by decide
    simp only [Array.getElem_set, hne, if_false] at hget
    exact hget.trans h4a
  · intro h
    have hset := place_held_eq b 6 h6H h6D ys moves peak
    have hget := idx_eq hset 4 (by rw [hset, Array.size_set]; exact h4B)
    have hne : (6 : Nat) ≠ 4 := by decide
    simp only [Array.getElem_set, hne, if_false] at hget
    exact hget.trans h4t

/-- White rise. The spare becomes the base up minus the accumulator up. -/
theorem chord_rise_white (b : Ecbs.Board) (baseY accY : List Nat)
    (n moves peak : Nat)
    (hszH : b.sudo_5Board_4home.size = 8) (hszD : b.sudo_5Board_4held.size = 8)
    (hyB : baseY.length = n) (hyA : accY.length = n) (hpos : 0 < n)
    (htriB : allTritList baseY) (htriA : allTritList accY)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hfit : FitsLen (moves + 2 * n))
    (h6e : b.sudo_5Board_4held[6]'(by rw [hszD]; decide) = false)
    (h4t : b.sudo_5Board_4held[4]'(by rw [hszD]; decide) = true)
    (h4a : b.sudo_5Board_4home[4]'(by rw [hszH]; decide) = embed baseY)
    (h1t : b.sudo_5Board_4held[1]'(by rw [hszD]; decide) = true)
    (h1a : b.sudo_5Board_4home[1]'(by rw [hszH]; decide) = embed accY) :
    ∃ bR,
      (do
          let b ← Ecbs.copy_band b Ecbs.spare Ecbs.base_up false
          Ecbs.add b Ecbs.spare Ecbs.up true) = .ok bR ∧
      (∀ h : 6 < bR.sudo_5Board_4home.size,
        bR.sudo_5Board_4home[6] = embed (fieldSub n baseY accY)) ∧
      (∀ h : 6 < bR.sudo_5Board_4held.size, bR.sudo_5Board_4held[6] = true) ∧
      (∀ h : 1 < bR.sudo_5Board_4home.size, bR.sudo_5Board_4home[1] = embed accY) ∧
      (∀ h : 1 < bR.sudo_5Board_4held.size, bR.sudo_5Board_4held[1] = true) ∧
      (∀ h : 4 < bR.sudo_5Board_4home.size, bR.sudo_5Board_4home[4] = embed baseY) ∧
      (∀ h : 4 < bR.sudo_5Board_4held.size, bR.sudo_5Board_4held[4] = true) ∧
      bR.sudo_5Board_4held.size = 8 ∧
      bR.sudo_5Board_4home.size = 8 ∧
      bR.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) ∧
      bR.sudo_5Board_4cost.sudo_5Costs_5moves =
        ((moves + pegCount baseY + pegCount accY : Nat) : Int) ∧
      bR.sudo_5Board_9marker_on = b.sudo_5Board_9marker_on ∧
      (∀ h : 0 < bR.sudo_5Board_4home.size,
        bR.sudo_5Board_4home[0] = b.sudo_5Board_4home[0]'(by rw [hszH]; decide)) ∧
      (∀ h : 0 < bR.sudo_5Board_4held.size,
        bR.sudo_5Board_4held[0] = b.sudo_5Board_4held[0]'(by rw [hszD]; decide)) ∧
      (∀ h : 2 < bR.sudo_5Board_4home.size,
        bR.sudo_5Board_4home[2] = b.sudo_5Board_4home[2]'(by rw [hszH]; decide)) ∧
      (∀ h : 2 < bR.sudo_5Board_4held.size,
        bR.sudo_5Board_4held[2] = b.sudo_5Board_4held[2]'(by rw [hszD]; decide)) ∧
      (∀ h : 5 < bR.sudo_5Board_4home.size,
        bR.sudo_5Board_4home[5] = b.sudo_5Board_4home[5]'(by rw [hszH]; decide)) ∧
      (∀ h : 5 < bR.sudo_5Board_4held.size,
        bR.sudo_5Board_4held[5] = b.sudo_5Board_4held[5]'(by rw [hszD]; decide)) ∧
      bR.sudo_5Board_1t = b.sudo_5Board_1t ∧
      bR.sudo_5Board_6marker = b.sudo_5Board_6marker ∧
      bR.sudo_5Board_4cost.sudo_5Costs_4ctrl = b.sudo_5Board_4cost.sudo_5Costs_4ctrl ∧
      bR.sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
        b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max ∧
      bR.sudo_5Board_4cost.sudo_5Costs_6slides = b.sudo_5Board_4cost.sudo_5Costs_6slides ∧
      bR.sudo_5Board_4cost.sudo_5Costs_3ops = b.sudo_5Board_4cost.sudo_5Costs_3ops ∧
      bR.sudo_5Board_8bench_on = b.sudo_5Board_8bench_on ∧
      bR.sudo_5Board_5bench = b.sudo_5Board_5bench ∧
      bR.sudo_5Board_8bench_to = b.sudo_5Board_8bench_to ∧
      bR.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
        b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole ∧
      bR.sudo_5Board_4cost.sudo_5Costs_11peak_strict =
        b.sudo_5Board_4cost.sudo_5Costs_11peak_strict ∧
      (∃ pk, bR.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk) ∧
      bR.sudo_5Board_4cost.sudo_5Costs_15control_highest =
        b.sudo_5Board_4cost.sudo_5Costs_15control_highest ∧
      TailStay b bR ∧
      bR.sudo_5Board_3row = b.sudo_5Board_3row := by
  have hpeg : pegCount baseY ≤ n := by rw [← hyB]; exact pegCount_le baseY
  have hfitn : FitsLen n := FitsLen.of_le hfit (by omega)
  have hfitC : FitsLen (moves + pegCount baseY) := FitsLen.of_le hfit (by omega)
  have hfitA : FitsLen (moves + pegCount baseY + n) := FitsLen.of_le hfit (by omega)
  have h6H : 6 < b.sudo_5Board_4home.size := by rw [hszH]; decide
  have h6D : 6 < b.sudo_5Board_4held.size := by rw [hszD]; decide
  have h4H : 4 < b.sudo_5Board_4home.size := by rw [hszH]; decide
  have h4D : 4 < b.sudo_5Board_4held.size := by rw [hszD]; decide
  have h7 : 7 ≤ b.sudo_5Board_4held.size := by rw [hszD]; decide
  have hflen : FitsLen baseY.length := by rw [hyB]; exact hfitn
  have hnlen : b.sudo_5Board_1t.sudo_4Tier_1n = (baseY.length : Int) := by rw [hn, hyB]
  have hcopy := copy_band_refines b 6 4 baseY moves peak h6H h6D h4H h4D h7
    h4t h4a h6e hnlen hflen hmoves hpeak hfitC
  have hplace := place_spare b baseY accY baseY moves peak h6H h6D hszH hszD h1t h1a h4t h4a
  let b1 := placeBoard b 6 h6H h6D baseY moves peak
  have hszH1 : b1.sudo_5Board_4home.size = 8 := hplace.1
  have hszD1 : b1.sudo_5Board_4held.size = 8 := hplace.2.1
  have hn1 : b1.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by
    rw [hplace.2.2.1, hn]
  have hmoves1 : b1.sudo_5Board_4cost.sudo_5Costs_5moves =
      ((moves + pegCount baseY : Nat) : Int) := by
    rw [hplace.2.2.2.1, ofNat_eq_natCast]
  have hflag1 : b1.sudo_5Board_9marker_on = b.sudo_5Board_9marker_on := hplace.2.2.2.2.1
  obtain ⟨bR, hadd, h6a, h6t, h1aR, h1tR, h4aR, h4tR, hszDR, hszHR, hnR, hmv, hflag,
      h0aR, h0tR, h2aR, h2tR, h5aR, h5tR, htR, hmR, hcR, hxR, hslR, hopR, honR, hbR, htoR,
      hhoR, hstR, hpkR, hhiR, hstayR, hrowA⟩ :=
    rise_add b1 baseY accY baseY n (moves + pegCount baseY) hszH1 hszD1 hyB hyA hpos
      htriB htriA hn1 hmoves1 hfitA hplace.2.2.2.2.2.2.1 hplace.2.2.2.2.2.1
      hplace.2.2.2.2.2.2.2.2.1 hplace.2.2.2.2.2.2.2.1
      hplace.2.2.2.2.2.2.2.2.2.2 hplace.2.2.2.2.2.2.2.2.2.1
  refine ⟨bR, ?_, h6a, h6t, h1aR, h1tR, h4aR, h4tR, hszDR, hszHR, hnR, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show Ecbs.spare = ((6 : Nat) : Int) from rfl,
        show Ecbs.base_up = ((4 : Nat) : Int) from rfl, hcopy, ok_bind]
    simpa [b1] using hadd
  · simpa [Nat.add_assoc] using hmv
  · rw [hflag, hflag1]
  · intro h
    exact (h0aR h).trans (place_home_at b h6H h6D baseY moves peak 0 (by decide)
      (by rw [hszH]; decide))
  · intro h
    exact (h0tR h).trans (place_held_at b h6H h6D baseY moves peak 0 (by decide)
      (by rw [hszD]; decide))
  · intro h
    exact (h2aR h).trans (place_home_at b h6H h6D baseY moves peak 2 (by decide)
      (by rw [hszH]; decide))
  · intro h
    exact (h2tR h).trans (place_held_at b h6H h6D baseY moves peak 2 (by decide)
      (by rw [hszD]; decide))
  · intro h
    exact (h5aR h).trans (place_home_at b h6H h6D baseY moves peak 5 (by decide)
      (by rw [hszH]; decide))
  · intro h
    exact (h5tR h).trans (place_held_at b h6H h6D baseY moves peak 5 (by decide)
      (by rw [hszD]; decide))
  · exact htR.trans (place_same b 6 h6H h6D baseY moves peak).1
  · exact hmR.trans (place_same b 6 h6H h6D baseY moves peak).2.1
  · exact hcR.trans (place_same b 6 h6H h6D baseY moves peak).2.2.1
  · exact hxR.trans (place_same b 6 h6H h6D baseY moves peak).2.2.2.1
  · exact hslR.trans (place_same b 6 h6H h6D baseY moves peak).2.2.2.2.1
  · exact hopR.trans (place_same b 6 h6H h6D baseY moves peak).2.2.2.2.2.1
  · exact honR.trans (place_same b 6 h6H h6D baseY moves peak).2.2.2.2.2.2.1
  · exact hbR.trans (place_same b 6 h6H h6D baseY moves peak).2.2.2.2.2.2.2.1
  · exact htoR.trans (place_same b 6 h6H h6D baseY moves peak).2.2.2.2.2.2.2.2.1
  · exact hhoR.trans (place_same b 6 h6H h6D baseY moves peak).2.2.2.2.2.2.2.2.2.1
  · exact hstR.trans (place_same b 6 h6H h6D baseY moves peak).2.2.2.2.2.2.2.2.2.2
  · have hpk := place_peak_nat b 6 h6H h6D baseY moves peak hpeak
    exact ⟨_, hpkR.trans hpk⟩
  · exact hhiR.trans (place_high b 6 h6H h6D baseY moves peak)
  · exact TailStay.trans (place_stay b 6 h6H h6D baseY moves peak (by decide) (by decide)) hstayR
  · exact hrowA.trans (place_row b 6 h6H h6D baseY moves peak)

/-- Red rise. The spare becomes the negated base up minus the accumulator up. -/
theorem chord_rise_red (b : Ecbs.Board) (baseY accY : List Nat)
    (n moves peak : Nat)
    (hszH : b.sudo_5Board_4home.size = 8) (hszD : b.sudo_5Board_4held.size = 8)
    (hyB : baseY.length = n) (hyA : accY.length = n) (hpos : 0 < n)
    (htriB : allTritList baseY) (htriA : allTritList accY)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hfit : FitsLen (moves + 2 * n))
    (h6e : b.sudo_5Board_4held[6]'(by rw [hszD]; decide) = false)
    (h4t : b.sudo_5Board_4held[4]'(by rw [hszD]; decide) = true)
    (h4a : b.sudo_5Board_4home[4]'(by rw [hszH]; decide) = embed baseY)
    (h1t : b.sudo_5Board_4held[1]'(by rw [hszD]; decide) = true)
    (h1a : b.sudo_5Board_4home[1]'(by rw [hszH]; decide) = embed accY) :
    ∃ bR,
      (do
          let b ← Ecbs.copy_band b Ecbs.spare Ecbs.base_up true
          Ecbs.add b Ecbs.spare Ecbs.up true) = .ok bR ∧
      (∀ h : 6 < bR.sudo_5Board_4home.size,
        bR.sudo_5Board_4home[6] = embed (fieldSub n (mirrorTrits baseY) accY)) ∧
      (∀ h : 6 < bR.sudo_5Board_4held.size, bR.sudo_5Board_4held[6] = true) ∧
      (∀ h : 1 < bR.sudo_5Board_4home.size, bR.sudo_5Board_4home[1] = embed accY) ∧
      (∀ h : 1 < bR.sudo_5Board_4held.size, bR.sudo_5Board_4held[1] = true) ∧
      (∀ h : 4 < bR.sudo_5Board_4home.size, bR.sudo_5Board_4home[4] = embed baseY) ∧
      (∀ h : 4 < bR.sudo_5Board_4held.size, bR.sudo_5Board_4held[4] = true) ∧
      bR.sudo_5Board_4held.size = 8 ∧
      bR.sudo_5Board_4home.size = 8 ∧
      bR.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) ∧
      bR.sudo_5Board_4cost.sudo_5Costs_5moves =
        ((moves + pegCount baseY + pegCount accY : Nat) : Int) ∧
      bR.sudo_5Board_9marker_on = b.sudo_5Board_9marker_on ∧
      (∀ h : 0 < bR.sudo_5Board_4home.size,
        bR.sudo_5Board_4home[0] = b.sudo_5Board_4home[0]'(by rw [hszH]; decide)) ∧
      (∀ h : 0 < bR.sudo_5Board_4held.size,
        bR.sudo_5Board_4held[0] = b.sudo_5Board_4held[0]'(by rw [hszD]; decide)) ∧
      (∀ h : 2 < bR.sudo_5Board_4home.size,
        bR.sudo_5Board_4home[2] = b.sudo_5Board_4home[2]'(by rw [hszH]; decide)) ∧
      (∀ h : 2 < bR.sudo_5Board_4held.size,
        bR.sudo_5Board_4held[2] = b.sudo_5Board_4held[2]'(by rw [hszD]; decide)) ∧
      (∀ h : 5 < bR.sudo_5Board_4home.size,
        bR.sudo_5Board_4home[5] = b.sudo_5Board_4home[5]'(by rw [hszH]; decide)) ∧
      (∀ h : 5 < bR.sudo_5Board_4held.size,
        bR.sudo_5Board_4held[5] = b.sudo_5Board_4held[5]'(by rw [hszD]; decide)) ∧
      bR.sudo_5Board_1t = b.sudo_5Board_1t ∧
      bR.sudo_5Board_6marker = b.sudo_5Board_6marker ∧
      bR.sudo_5Board_4cost.sudo_5Costs_4ctrl = b.sudo_5Board_4cost.sudo_5Costs_4ctrl ∧
      bR.sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
        b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max ∧
      bR.sudo_5Board_4cost.sudo_5Costs_6slides = b.sudo_5Board_4cost.sudo_5Costs_6slides ∧
      bR.sudo_5Board_4cost.sudo_5Costs_3ops = b.sudo_5Board_4cost.sudo_5Costs_3ops ∧
      bR.sudo_5Board_8bench_on = b.sudo_5Board_8bench_on ∧
      bR.sudo_5Board_5bench = b.sudo_5Board_5bench ∧
      bR.sudo_5Board_8bench_to = b.sudo_5Board_8bench_to ∧
      bR.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
        b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole ∧
      bR.sudo_5Board_4cost.sudo_5Costs_11peak_strict =
        b.sudo_5Board_4cost.sudo_5Costs_11peak_strict ∧
      (∃ pk, bR.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk) ∧
      bR.sudo_5Board_4cost.sudo_5Costs_15control_highest =
        b.sudo_5Board_4cost.sudo_5Costs_15control_highest ∧
      TailStay b bR ∧
      bR.sudo_5Board_3row = b.sudo_5Board_3row := by
  have hpeg : pegCount baseY ≤ n := by rw [← hyB]; exact pegCount_le baseY
  have hpegM : pegCount (mirrorTrits baseY) = pegCount baseY := pegCount_mirror baseY htriB
  have hlenM : (mirrorTrits baseY).length = n := by rw [mirror_length, hyB]
  have htriM : allTritList (mirrorTrits baseY) := mirrorTrits_allTrit htriB
  have hfitn : FitsLen n := FitsLen.of_le hfit (by omega)
  have hfitC : FitsLen (moves + pegCount baseY) := FitsLen.of_le hfit (by omega)
  have hfitA : FitsLen (moves + pegCount baseY + n) := FitsLen.of_le hfit (by omega)
  have h6H : 6 < b.sudo_5Board_4home.size := by rw [hszH]; decide
  have h6D : 6 < b.sudo_5Board_4held.size := by rw [hszD]; decide
  have h4H : 4 < b.sudo_5Board_4home.size := by rw [hszH]; decide
  have h4D : 4 < b.sudo_5Board_4held.size := by rw [hszD]; decide
  have h7 : 7 ≤ b.sudo_5Board_4held.size := by rw [hszD]; decide
  have hflen : FitsLen baseY.length := by rw [hyB]; exact hfitn
  have hnlen : b.sudo_5Board_1t.sudo_4Tier_1n = (baseY.length : Int) := by rw [hn, hyB]
  have hcopy := copy_band_mirror_refines b 6 4 baseY moves peak h6H h6D h4H h4D h7
    h4t h4a h6e hnlen (by rw [hyB]; exact hpos) htriB hflen hmoves hpeak hfitC
  have hplace := place_spare b (mirrorTrits baseY) accY baseY moves peak h6H h6D hszH hszD
    h1t h1a h4t h4a
  let b1 := placeBoard b 6 h6H h6D (mirrorTrits baseY) moves peak
  have hszH1 : b1.sudo_5Board_4home.size = 8 := hplace.1
  have hszD1 : b1.sudo_5Board_4held.size = 8 := hplace.2.1
  have hn1 : b1.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by
    rw [hplace.2.2.1, hn]
  have hmoves1 : b1.sudo_5Board_4cost.sudo_5Costs_5moves =
      ((moves + pegCount baseY : Nat) : Int) := by
    rw [hplace.2.2.2.1, hpegM, ofNat_eq_natCast]
  have hflag1 : b1.sudo_5Board_9marker_on = b.sudo_5Board_9marker_on := hplace.2.2.2.2.1
  obtain ⟨bR, hadd, h6a, h6t, h1aR, h1tR, h4aR, h4tR, hszDR, hszHR, hnR, hmv, hflag,
      h0aR, h0tR, h2aR, h2tR, h5aR, h5tR, htR, hmR, hcR, hxR, hslR, hopR, honR, hbR, htoR,
      hhoR, hstR, hpkR, hhiR, hstayR, hrowA⟩ :=
    rise_add b1 (mirrorTrits baseY) accY baseY n (moves + pegCount baseY) hszH1 hszD1
      hlenM hyA hpos htriM htriA hn1 hmoves1 hfitA
      hplace.2.2.2.2.2.2.1 hplace.2.2.2.2.2.1
      hplace.2.2.2.2.2.2.2.2.1 hplace.2.2.2.2.2.2.2.1
      hplace.2.2.2.2.2.2.2.2.2.2 hplace.2.2.2.2.2.2.2.2.2.1
  refine ⟨bR, ?_, h6a, h6t, h1aR, h1tR, h4aR, h4tR, hszDR, hszHR, hnR, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show Ecbs.spare = ((6 : Nat) : Int) from rfl,
        show Ecbs.base_up = ((4 : Nat) : Int) from rfl, hcopy, ok_bind]
    simpa [b1] using hadd
  · simpa [Nat.add_assoc] using hmv
  · rw [hflag, hflag1]
  · intro h
    exact (h0aR h).trans (place_home_at b h6H h6D (mirrorTrits baseY) moves peak 0 (by decide)
      (by rw [hszH]; decide))
  · intro h
    exact (h0tR h).trans (place_held_at b h6H h6D (mirrorTrits baseY) moves peak 0 (by decide)
      (by rw [hszD]; decide))
  · intro h
    exact (h2aR h).trans (place_home_at b h6H h6D (mirrorTrits baseY) moves peak 2 (by decide)
      (by rw [hszH]; decide))
  · intro h
    exact (h2tR h).trans (place_held_at b h6H h6D (mirrorTrits baseY) moves peak 2 (by decide)
      (by rw [hszD]; decide))
  · intro h
    exact (h5aR h).trans (place_home_at b h6H h6D (mirrorTrits baseY) moves peak 5 (by decide)
      (by rw [hszH]; decide))
  · intro h
    exact (h5tR h).trans (place_held_at b h6H h6D (mirrorTrits baseY) moves peak 5 (by decide)
      (by rw [hszD]; decide))
  · exact htR.trans (place_same b 6 h6H h6D (mirrorTrits baseY) moves peak).1
  · exact hmR.trans (place_same b 6 h6H h6D (mirrorTrits baseY) moves peak).2.1
  · exact hcR.trans (place_same b 6 h6H h6D (mirrorTrits baseY) moves peak).2.2.1
  · exact hxR.trans (place_same b 6 h6H h6D (mirrorTrits baseY) moves peak).2.2.2.1
  · exact hslR.trans (place_same b 6 h6H h6D (mirrorTrits baseY) moves peak).2.2.2.2.1
  · exact hopR.trans (place_same b 6 h6H h6D (mirrorTrits baseY) moves peak).2.2.2.2.2.1
  · exact honR.trans (place_same b 6 h6H h6D (mirrorTrits baseY) moves peak).2.2.2.2.2.2.1
  · exact hbR.trans (place_same b 6 h6H h6D (mirrorTrits baseY) moves peak).2.2.2.2.2.2.2.1
  · exact htoR.trans (place_same b 6 h6H h6D (mirrorTrits baseY) moves peak).2.2.2.2.2.2.2.2.1
  · exact hhoR.trans (place_same b 6 h6H h6D (mirrorTrits baseY) moves peak).2.2.2.2.2.2.2.2.2.1
  · exact hstR.trans (place_same b 6 h6H h6D (mirrorTrits baseY) moves peak).2.2.2.2.2.2.2.2.2.2
  · have hpk := place_peak_nat b 6 h6H h6D (mirrorTrits baseY) moves peak hpeak
    exact ⟨_, hpkR.trans hpk⟩
  · exact hhiR.trans (place_high b 6 h6H h6D (mirrorTrits baseY) moves peak)
  · exact TailStay.trans
      (place_stay b 6 h6H h6D (mirrorTrits baseY) moves peak (by decide) (by decide)) hstayR
  · exact hrowA.trans (place_row b 6 h6H h6D (mirrorTrits baseY) moves peak)

/-- The rise, white or red. `red` mirrors the base up before the subtraction. -/
theorem chord_rise (b : Ecbs.Board) (red : Bool) (baseY accY : List Nat)
    (n moves peak : Nat)
    (hszH : b.sudo_5Board_4home.size = 8) (hszD : b.sudo_5Board_4held.size = 8)
    (hyB : baseY.length = n) (hyA : accY.length = n) (hpos : 0 < n)
    (htriB : allTritList baseY) (htriA : allTritList accY)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hfit : FitsLen (moves + 2 * n))
    (h6e : b.sudo_5Board_4held[6]'(by rw [hszD]; decide) = false)
    (h4t : b.sudo_5Board_4held[4]'(by rw [hszD]; decide) = true)
    (h4a : b.sudo_5Board_4home[4]'(by rw [hszH]; decide) = embed baseY)
    (h1t : b.sudo_5Board_4held[1]'(by rw [hszD]; decide) = true)
    (h1a : b.sudo_5Board_4home[1]'(by rw [hszH]; decide) = embed accY) :
    ∃ bR,
      (do
          let b ← Ecbs.copy_band b Ecbs.spare Ecbs.base_up red
          Ecbs.add b Ecbs.spare Ecbs.up true) = .ok bR ∧
      (∀ h : 6 < bR.sudo_5Board_4home.size,
        bR.sudo_5Board_4home[6] =
          embed (fieldSub n (if red then mirrorTrits baseY else baseY) accY)) ∧
      (∀ h : 6 < bR.sudo_5Board_4held.size, bR.sudo_5Board_4held[6] = true) ∧
      (∀ h : 1 < bR.sudo_5Board_4home.size, bR.sudo_5Board_4home[1] = embed accY) ∧
      (∀ h : 1 < bR.sudo_5Board_4held.size, bR.sudo_5Board_4held[1] = true) ∧
      (∀ h : 4 < bR.sudo_5Board_4home.size, bR.sudo_5Board_4home[4] = embed baseY) ∧
      (∀ h : 4 < bR.sudo_5Board_4held.size, bR.sudo_5Board_4held[4] = true) ∧
      bR.sudo_5Board_4held.size = 8 ∧
      bR.sudo_5Board_4home.size = 8 ∧
      bR.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) ∧
      bR.sudo_5Board_4cost.sudo_5Costs_5moves =
        ((moves + pegCount baseY + pegCount accY : Nat) : Int) ∧
      bR.sudo_5Board_9marker_on = b.sudo_5Board_9marker_on ∧
      (∀ h : 0 < bR.sudo_5Board_4home.size,
        bR.sudo_5Board_4home[0] = b.sudo_5Board_4home[0]'(by rw [hszH]; decide)) ∧
      (∀ h : 0 < bR.sudo_5Board_4held.size,
        bR.sudo_5Board_4held[0] = b.sudo_5Board_4held[0]'(by rw [hszD]; decide)) ∧
      (∀ h : 2 < bR.sudo_5Board_4home.size,
        bR.sudo_5Board_4home[2] = b.sudo_5Board_4home[2]'(by rw [hszH]; decide)) ∧
      (∀ h : 2 < bR.sudo_5Board_4held.size,
        bR.sudo_5Board_4held[2] = b.sudo_5Board_4held[2]'(by rw [hszD]; decide)) ∧
      (∀ h : 5 < bR.sudo_5Board_4home.size,
        bR.sudo_5Board_4home[5] = b.sudo_5Board_4home[5]'(by rw [hszH]; decide)) ∧
      (∀ h : 5 < bR.sudo_5Board_4held.size,
        bR.sudo_5Board_4held[5] = b.sudo_5Board_4held[5]'(by rw [hszD]; decide)) ∧
      bR.sudo_5Board_1t = b.sudo_5Board_1t ∧
      bR.sudo_5Board_6marker = b.sudo_5Board_6marker ∧
      bR.sudo_5Board_4cost.sudo_5Costs_4ctrl = b.sudo_5Board_4cost.sudo_5Costs_4ctrl ∧
      bR.sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
        b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max ∧
      bR.sudo_5Board_4cost.sudo_5Costs_6slides = b.sudo_5Board_4cost.sudo_5Costs_6slides ∧
      bR.sudo_5Board_4cost.sudo_5Costs_3ops = b.sudo_5Board_4cost.sudo_5Costs_3ops ∧
      bR.sudo_5Board_8bench_on = b.sudo_5Board_8bench_on ∧
      bR.sudo_5Board_5bench = b.sudo_5Board_5bench ∧
      bR.sudo_5Board_8bench_to = b.sudo_5Board_8bench_to ∧
      bR.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
        b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole ∧
      bR.sudo_5Board_4cost.sudo_5Costs_11peak_strict =
        b.sudo_5Board_4cost.sudo_5Costs_11peak_strict ∧
      (∃ pk, bR.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk) ∧
      bR.sudo_5Board_4cost.sudo_5Costs_15control_highest =
        b.sudo_5Board_4cost.sudo_5Costs_15control_highest ∧
      TailStay b bR ∧
      bR.sudo_5Board_3row = b.sudo_5Board_3row := by
  cases red
  · simpa using
      chord_rise_white b baseY accY n moves peak hszH hszD hyB hyA hpos htriB htriA
        hn hmoves hpeak hfit h6e h4t h4a h1t h1a
  · simpa using
      chord_rise_red b baseY accY n moves peak hszH hszD hyB hyA hpos htriB htriA
        hn hmoves hpeak hfit h6e h4t h4a h1t h1a

end EcbsLink2.Link2
