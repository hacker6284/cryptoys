/-
  The board a chord walk starts from. `FrameAt` is the painted ladder, the
  tally, and the park fields a `RunFrame` reads. `ChordAt` adds the seated
  homes. The cell list is arbitrary: `FitsLen` of its length replaces
  `cells.length = t.cells`, and `ChordAt` replaces a fresh `baseBoard`.
  The part-1 statements are the fresh board and a key of length `t.cells`.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.OpenBoard
import EcbsLink2.Link2.WalkPrefix

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open Ecbs
open EcbsLink2.Spec

/-- The control frame `RunFrame` keeps: the painted ladder, the tally, and
    the park fields. -/
structure FrameAt (b : Board) (t : Spec.Tier) : Prop where
  hlad : b.sudo_5Board_6ladder = embed (tierClimb t)
  hl0 : b.sudo_5Board_7ladder0 = Int.ofNat (t.script + 2)
  hnr : b.sudo_5Board_6nrungs = Int.ofNat (tierR t)
  hpark : b.sudo_5Board_9park_hole = Int.ofNat (t.script + 2 + tierR t)
  hfrom : b.sudo_5Board_11parked_from = -1
  hridx : b.sudo_5Board_8rung_idx = 0
  htally : b.sudo_5Board_9tally_len = 0
  ht0 : b.sudo_5Board_6tally0 = Int.ofNat (tallyOrigin t)
  hrow : b.sudo_5Board_3row = embed (paintedRow t)

/-- Homes 3 and 4 hold the base point, the accumulator homes are empty, and
    the control frame is `FrameAt`. This is the board before the first live
    cell, so home 0 is not yet the accumulator of a `RunFrame`. -/
structure ChordAt (b : Board) (t : Spec.Tier) (x y : List Nat) (moves peak : Nat) : Prop where
  frame : FrameAt b t
  szH : b.sudo_5Board_4home.size = 8
  szD : b.sudo_5Board_4held.size = 8
  bench : b.sudo_5Board_8bench_on = false
  marker : b.sudo_5Board_6marker = -1
  tier : b.sudo_5Board_1t = embTier t
  tierN : b.sudo_5Board_1t.sudo_4Tier_1n = (t.n : Int)
  hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int)
  hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int)
  held0 : b.sudo_5Board_4held[0]'(by rw [szD]; decide) = false
  held1 : b.sudo_5Board_4held[1]'(by rw [szD]; decide) = false
  held2 : b.sudo_5Board_4held[2]'(by rw [szD]; decide) = false
  held5 : b.sudo_5Board_4held[5]'(by rw [szD]; decide) = false
  held6 : b.sudo_5Board_4held[6]'(by rw [szD]; decide) = false
  held3 : b.sudo_5Board_4held[3]'(by rw [szD]; decide) = true
  home3 : b.sudo_5Board_4home[3]'(by rw [szH]; decide) = embed x
  held4 : b.sudo_5Board_4held[4]'(by rw [szD]; decide) = true
  home4 : b.sudo_5Board_4home[4]'(by rw [szH]; decide) = embed y

theorem built_frame (t : Spec.Tier) : FrameAt (builtBoard t) t where
  hlad := built_ladder_eq t
  hl0 := built_l0_eq t
  hnr := built_nr_eq t
  hpark := built_park_eq t
  hfrom := built_from_eq t
  hridx := built_ridx_eq t
  htally := built_tally0 t
  ht0 := built_t0_eq t
  hrow := built_row_eq t

theorem frame_place (b : Board) (t : Spec.Tier) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat) (h : FrameAt b t) :
    FrameAt (placeBoard b home hH hD xs moves peak) t where
  hlad := (place_ladder b home hH hD xs moves peak).trans h.hlad
  hl0 := (place_l0 b home hH hD xs moves peak).trans h.hl0
  hnr := (place_nr b home hH hD xs moves peak).trans h.hnr
  hpark := (place_park b home hH hD xs moves peak).trans h.hpark
  hfrom := (place_from b home hH hD xs moves peak).trans h.hfrom
  hridx := (place_ridx b home hH hD xs moves peak).trans h.hridx
  htally := (place_tally b home hH hD xs moves peak).trans h.htally
  ht0 := (place_t0 b home hH hD xs moves peak).trans h.ht0
  hrow := (place_row b home hH hD xs moves peak).trans h.hrow

theorem base_frame (t : Spec.Tier) (x y : List Nat) : FrameAt (baseBoard t x y) t where
  hlad := by simpa [baseBoard, putAcross] using built_ladder_eq t
  hl0 := by simpa [baseBoard, putAcross] using built_l0_eq t
  hnr := by simpa [baseBoard, putAcross] using built_nr_eq t
  hpark := by simpa [baseBoard, putAcross] using built_park_eq t
  hfrom := by simpa [baseBoard, putAcross] using built_from_eq t
  hridx := by simpa [baseBoard, putAcross] using built_ridx_eq t
  htally := by simpa [baseBoard, putAcross] using built_tally0 t
  ht0 := by simpa [baseBoard, putAcross] using built_t0_eq t
  hrow := by simpa [baseBoard, putAcross] using built_row_eq t

/-- The fresh base board is a `ChordAt`. Moves are the two home lengths and
    the peak is 2. -/
theorem base_chordAt (t : Spec.Tier) (x y : List Nat) :
    ChordAt (baseBoard t x y) t x y (pegCount x + pegCount y) 2 where
  frame := base_frame t x y
  szH := base_szH t x y
  szD := base_szD t x y
  bench := by simp [baseBoard, putAcross, built_bench_off]
  marker := by simp [baseBoard, putAcross, built_marker_down]
  tier := by simp [baseBoard, putAcross, built_tier_eq]
  tierN := by simp [baseBoard, putAcross, built_tier_eq, embTier, ofNat_eq_natCast]
  hmoves := by simp [baseBoard, ofNat_eq_natCast]
  hpeak := by simp [baseBoard, ofNat_eq_natCast]
  held0 := by simp [baseBoard, putAcross, Array.getElem_set, built_held_arr, Array.getElem_mkArray]
  held1 := by simp [baseBoard, putAcross, Array.getElem_set, built_held_arr, Array.getElem_mkArray]
  held2 := by simp [baseBoard, putAcross, Array.getElem_set, built_held_arr, Array.getElem_mkArray]
  held5 := by simp [baseBoard, putAcross, Array.getElem_set, built_held_arr, Array.getElem_mkArray]
  held6 := by simp [baseBoard, putAcross, Array.getElem_set, built_held_arr, Array.getElem_mkArray]
  held3 := by simp [baseBoard, putAcross, Array.getElem_set, built_held_arr, Array.getElem_mkArray]
  home3 := by simp [baseBoard, putAcross, Array.getElem_set]
  held4 := by simp [baseBoard, putAcross, Array.getElem_set]
  home4 := by simp [baseBoard, putAcross, Array.getElem_set]

/-- Every cell empty, on any `ChordAt` board. The homes stay. -/
theorem walk_chord_at_zeros (b : Board) (t : Spec.Tier) (x y : List Nat)
    (moves peak : Nat) (cells : List Nat) (acc : List Nat × List Nat)
    (hAt : ChordAt b t x y moves peak)
    (hfit : FitsLen cells.length) (hz : ∀ c ∈ cells, c = 0) :
    Ecbs.walk_chord b (embed cells) =
        .ok ((false, true), { b with sudo_5Board_9marker_on := false }) ∧
      walkRun t.n t.k t.benchlen (x, y) false acc cells = some (false, acc) := by
  obtain ⟨hch, hrun, _⟩ :=
    walk_chord_zeros_down b cells t.n t.k t.benchlen (x, y) acc hz hAt.marker hfit
  exact ⟨hch, hrun⟩

/-- Zeros, then one white cell, on any `ChordAt` board. Across and up become
    the seated point. -/
theorem walk_chord_at_white (b : Board) (t : Spec.Tier) (x y : List Nat)
    (moves peak : Nat) (zs : List Nat) (acc : List Nat × List Nat)
    (hAt : ChordAt b t x y moves peak)
    (hx : x.length = t.n) (hy : y.length = t.n)
    (hz : ∀ c ∈ zs, c = 0)
    (hf : FitsLen t.n)
    (hfitx : FitsLen (moves + pegCount x))
    (hfity : FitsLen (moves + pegCount x + pegCount y))
    (hfit : FitsLen (zs.length + 1)) :
    ∃ b',
      Ecbs.walk_chord b (embed (zs ++ [1])) =
        .ok ((true, true), b') ∧
      (∀ h : 0 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[0] = embed x) ∧
      (∀ h : 1 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[1] = embed y) ∧
      walkRun t.n t.k t.benchlen (x, y) false acc (zs ++ [1]) =
        some (true, (x, y)) := by
  obtain ⟨b2, hch, hx0, hy1, _hm, _hst, _hho, _hc, _hs, hrun, _⟩ :=
    walk_chord_white_down b zs x y t.n t.k t.benchlen moves peak acc hz
      hAt.szH hAt.szD hx hy hf hfitx hfity hAt.tierN hAt.hmoves hAt.hpeak
      hAt.marker hfit hAt.held0 hAt.held1 hAt.held3 hAt.home3 hAt.held4 hAt.home4
  refine ⟨{ b2 with sudo_5Board_9marker_on := false }, hch, ?_, ?_, hrun⟩
  · simpa using hx0
  · simpa using hy1

/-- Zeros, then one red cell, on any `ChordAt` board. Up is the negated base up. -/
theorem walk_chord_at_red (b : Board) (t : Spec.Tier) (x y : List Nat)
    (moves peak : Nat) (zs : List Nat) (acc : List Nat × List Nat)
    (hAt : ChordAt b t x y moves peak)
    (hx : x.length = t.n) (hy : y.length = t.n) (hpos : 0 < t.n)
    (htriY : allTritList y)
    (hz : ∀ c ∈ zs, c = 0)
    (hf : FitsLen t.n)
    (hfitx : FitsLen (moves + pegCount x))
    (hfity : FitsLen (moves + pegCount x + pegCount y))
    (hfit : FitsLen (zs.length + 1)) :
    ∃ b',
      Ecbs.walk_chord b (embed (zs ++ [2])) =
        .ok ((true, true), b') ∧
      (∀ h : 0 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[0] = embed x) ∧
      (∀ h : 1 < b'.sudo_5Board_4home.size,
        b'.sudo_5Board_4home[1] = embed (mirrorTrits y)) ∧
      walkRun t.n t.k t.benchlen (x, y) false acc (zs ++ [2]) =
        some (true, (x, mirrorTrits y)) := by
  obtain ⟨b2, hch, hx0, hy1, _hm, _hst, _hho, _hc, _hs, hrun, _⟩ :=
    walk_chord_red_down b zs x y t.n t.k t.benchlen moves peak acc hz
      hAt.szH hAt.szD hx hy hpos htriY hf hfitx hfity hAt.tierN hAt.hmoves hAt.hpeak
      hAt.marker hfit hAt.held0 hAt.held1 hAt.held3 hAt.home3 hAt.held4 hAt.home4
  refine ⟨{ b2 with sudo_5Board_9marker_on := false }, hch, ?_, ?_, hrun⟩
  · simpa using hx0
  · simpa using hy1

end EcbsLink2.Link2
