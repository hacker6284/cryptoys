/-
  The board a chord walk starts from. `PaintFrame` is the painted ladder, the
  tally, and the park fields a `RunFrame` reads. `ChordAt` adds the seated
  homes. The cell list is arbitrary: `FitsLen` of its length replaces
  `cells.length = t.cells`, and `ChordAt` replaces a fresh `baseBoard`.
  The part-1 statements are the fresh board and a key of length `t.cells`.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.OpenBoard
import EcbsLink2.Link2.TailStay
import EcbsLink2.Link2.WalkPrefix

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open Ecbs
open EcbsLink2.Spec

/-- The control frame `RunFrame` keeps: the painted ladder, the tally, and
    the park fields. -/
structure PaintFrame (b : Board) (t : Spec.Tier) : Prop where
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
    the control frame is `PaintFrame`. This is the board before the first live
    cell, so home 0 is not yet the accumulator of a `RunFrame`. -/
structure ChordAt (b : Board) (t : Spec.Tier) (x y : List Nat) (moves peak : Nat) : Prop where
  frame : PaintFrame b t
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

theorem built_frame (t : Spec.Tier) : PaintFrame (builtBoard t) t where
  hlad := built_ladder_eq t
  hl0 := built_l0_eq t
  hnr := built_nr_eq t
  hpark := built_park_eq t
  hfrom := built_from_eq t
  hridx := built_ridx_eq t
  htally := built_tally0 t
  ht0 := built_t0_eq t
  hrow := built_row_eq t

/-- A step that keeps `FrameScalar`, and the painted row, keeps `PaintFrame`. -/
theorem frame_scalar (b0 b : Board) (t : Spec.Tier) (h : PaintFrame b0 t)
    (s : FrameScalar b0 b) (hrow : b.sudo_5Board_3row = b0.sudo_5Board_3row) :
    PaintFrame b t where
  hlad := s.ladder.trans h.hlad
  hl0 := s.l0.trans h.hl0
  hnr := s.nr.trans h.hnr
  hpark := s.park.trans h.hpark
  hfrom := s.fromH.trans h.hfrom
  hridx := s.ridx.trans h.hridx
  htally := s.tlen.trans h.htally
  ht0 := s.t0.trans h.ht0
  hrow := hrow.trans h.hrow

theorem frame_place (b : Board) (t : Spec.Tier) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat) (h : PaintFrame b t) :
    PaintFrame (placeBoard b home hH hD xs moves peak) t where
  hlad := (place_ladder b home hH hD xs moves peak).trans h.hlad
  hl0 := (place_l0 b home hH hD xs moves peak).trans h.hl0
  hnr := (place_nr b home hH hD xs moves peak).trans h.hnr
  hpark := (place_park b home hH hD xs moves peak).trans h.hpark
  hfrom := (place_from b home hH hD xs moves peak).trans h.hfrom
  hridx := (place_ridx b home hH hD xs moves peak).trans h.hridx
  htally := (place_tally b home hH hD xs moves peak).trans h.htally
  ht0 := (place_t0 b home hH hD xs moves peak).trans h.ht0
  hrow := (place_row b home hH hD xs moves peak).trans h.hrow

theorem base_frame (t : Spec.Tier) (x y : List Nat) : PaintFrame (baseBoard t x y) t where
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

theorem frame_flag (b : Board) (t : Spec.Tier) (h : PaintFrame b t) :
    PaintFrame (chordFlag b) t where
  hlad := by simpa [chordFlag] using h.hlad
  hl0 := by simpa [chordFlag] using h.hl0
  hnr := by simpa [chordFlag] using h.hnr
  hpark := by simpa [chordFlag] using h.hpark
  hfrom := by simpa [chordFlag] using h.hfrom
  hridx := by simpa [chordFlag] using h.hridx
  htally := by simpa [chordFlag] using h.htally
  ht0 := by simpa [chordFlag] using h.ht0
  hrow := by simpa [chordFlag] using h.hrow

/-- Turning the walk flag on leaves the frame and the seated homes. -/
theorem chord_flag_at (b : Board) (t : Spec.Tier) (x y : List Nat) (moves peak : Nat)
    (hAt : ChordAt b t x y moves peak) :
    ChordAt (chordFlag b) t x y moves peak where
  frame := frame_flag b t hAt.frame
  szH := by simpa [chordFlag] using hAt.szH
  szD := by simpa [chordFlag] using hAt.szD
  bench := by simpa [chordFlag] using hAt.bench
  marker := by simpa [chordFlag] using hAt.marker
  tier := by simpa [chordFlag] using hAt.tier
  tierN := by simpa [chordFlag] using hAt.tierN
  hmoves := by simpa [chordFlag] using hAt.hmoves
  hpeak := by simpa [chordFlag] using hAt.hpeak
  held0 := by simpa [chordFlag] using hAt.held0
  held1 := by simpa [chordFlag] using hAt.held1
  held2 := by simpa [chordFlag] using hAt.held2
  held5 := by simpa [chordFlag] using hAt.held5
  held6 := by simpa [chordFlag] using hAt.held6
  held3 := by simpa [chordFlag] using hAt.held3
  home3 := by simpa [chordFlag] using hAt.home3
  held4 := by simpa [chordFlag] using hAt.held4
  home4 := by simpa [chordFlag] using hAt.home4

/-- Empty cells, then one nonzero cell, then a nonempty tail. The loop from
    the flagged board is the loop at the copied board. The length is the
    list's, not `t.cells`. -/
theorem chord_reach (bf b2 : Board) (zs rest : List Nat) (c : Nat)
    (hz : ∀ z ∈ zs, z = 0) (hc : c = 1 ∨ c = 2)
    (hcells : 0 < (zs ++ (c :: rest)).length)
    (hfit : FitsLen (zs ++ (c :: rest)).length)
    (hrest : 0 < rest.length)
    (hml : Ecbs.marker_lift bf = .ok bf)
    (hcopy :
      (do
          let board ← Ecbs.copy_band bf Ecbs.across Ecbs.base_across false
          Ecbs.copy_band board Ecbs.up Ecbs.base_up
            (SudoRt.SEq.beq (Int.ofNat c) (2 : Int))) = .ok b2) :
    let cells := zs ++ (c :: rest)
    let k := zs.length + 1
    let toN := cells.length - 1
    SudoRt.runLoopOn (Int.ofNat 0, (bf, false))
        (fuelRange (Int.ofNat 0) (Int.ofNat toN))
        (chordStep (embed cells) (Int.ofNat toN)) chordAfter (fun r => pure r) =
      SudoRt.runLoopOn (Int.ofNat k, (b2, true))
        (fuelRange (Int.ofNat k) (Int.ofNat toN))
        (chordStep (embed cells) (Int.ofNat toN)) chordAfter (fun r => pure r) := by
  intro cells k toN
  have hto : toN + 1 = cells.length := by
    have hpos : 0 < cells.length := hcells
    omega
  have hk : k ≤ toN := by
    have hlen : cells.length = zs.length + (rest.length + 1) := by
      simp [cells, List.length_append]
    omega
  have hlenC : cells.length = toN + 1 := hto.symm
  let Inv : Nat → Board × Bool → Prop := fun i st =>
    if i ≤ zs.length then st = (bf, false) else st = (b2, true)
  have h0 : Inv 0 (bf, false) := by simp [Inv]
  have hstep : ∀ i s, 0 ≤ i → i < k → Inv i s →
      ∃ s', Inv (i + 1) s' ∧
        chordStep (embed cells) (Int.ofNat toN) (Int.ofNat i, s) =
          .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), s')) := by
    intro i st _hi hlt hI
    have hiTo : i ≤ toN := by omega
    have hfiti : FitsLen (i + 1) := by
      apply FitsLen.of_le hfit
      have hto' : toN + 1 = (zs ++ (c :: rest)).length := by simpa [cells] using hto
      omega
    have hne : i ≠ toN := by omega
    by_cases hzero : i < zs.length
    · have hI0 : st = (bf, false) := by
        have hle : i ≤ zs.length := by omega
        simpa [Inv, hle] using hI
      have hcell : cells[i]'(by rw [hlenC]; omega) = 0 := by
        have hiL : i < zs.length := hzero
        have hlenI : i < (zs ++ (c :: rest)).length := by
          simp [List.length_append]
          omega
        have hget := List.getElem_append_left (bs := c :: rest) hiL (h' := hlenI)
        have hz0 : zs[i]'hiL = 0 := hz _ (List.getElem_mem _)
        simpa [cells] using hget.trans hz0
      have hst := chordStep_zero cells i toN bf bf hiTo hlenC hcell hml hfiti
      refine ⟨(bf, false), ?_, ?_⟩
      · have hle : i + 1 ≤ zs.length := by omega
        simp [Inv, hle]
      · rw [hI0, hst, if_neg hne]
    · have hI0 : st = (bf, false) := by
        have hle : i ≤ zs.length := by omega
        simpa [Inv, hle] using hI
      have hcell : cells[i]'(by rw [hlenC]; omega) = c := by
        have hiR : zs.length ≤ i := by omega
        have hlenI : i < (zs ++ (c :: rest)).length := by
          simp [List.length_append]
          omega
        have hget := List.getElem_append_right (bs := c :: rest) hiR (h₂ := hlenI)
        have h0i : i - zs.length = 0 := by omega
        have hhead : (c :: rest)[i - zs.length]'(by
            have hlenR : 0 < (c :: rest).length := by simp
            omega) = c := by simp [h0i]
        simpa [cells] using hget.trans hhead
      have hc0 : c ≠ 0 := by rcases hc with rfl | rfl <;> decide
      have hc2 : c ≤ 2 := by rcases hc with rfl | rfl <;> decide
      have hst := chordStep_fresh cells i toN c bf bf b2 hiTo hlenC hcell hc0 hc2
        hml hcopy hfiti
      refine ⟨(b2, true), ?_, ?_⟩
      · have hgt : ¬ i + 1 ≤ zs.length := by omega
        simp [Inv, hgt]
      · rw [hI0, hst, if_neg hne]
  obtain ⟨sK, hIK, heq⟩ := asc_resume
    (chordStep (embed cells) (Int.ofNat toN)) chordAfter (fun r => pure r)
    Inv 0 k toN (bf, false) (Nat.zero_le _) hk h0 hstep
  have hgt : ¬ k ≤ zs.length := by simp [k]
  have hsK : sK = (b2, true) := by simpa [Inv, hgt] using hIK
  simpa [hsK] using heq

private theorem chord_from_zero (b : Board) (cells : List Nat)
    (hpos : 0 < cells.length) (hfit : FitsLen cells.length) :
    Ecbs.walk_chord b (embed cells) =
      SudoRt.runLoopOn (Int.ofNat 0, (chordFlag b, false))
        (fuelRange (Int.ofNat 0) (Int.ofNat (cells.length - 1)))
        (chordStep (embed cells) (Int.ofNat (cells.length - 1)))
        chordAfter (fun r => pure r) := by
  rw [walk_chord_eq]
  unfold walkChordGo
  rw [listLen_embed, subI_ofNat_one cells.length hpos hfit, ok_bind]
  dsimp only
  rw [except_bind_pure]
  rw [show (0 : Int) = Int.ofNat 0 from rfl]

/-- A white opening on a `ChordAt` board, with cells still to run. The emitted
    walk from the start is the loop at the copied point. -/
theorem walk_chord_at_reach_white (b : Board) (t : Spec.Tier) (x y : List Nat)
    (moves peak : Nat) (zs rest : List Nat) (acc : List Nat × List Nat)
    (hAt : ChordAt b t x y moves peak)
    (hx : x.length = t.n) (hy : y.length = t.n)
    (hz : ∀ z ∈ zs, z = 0)
    (hf : FitsLen t.n)
    (hfitx : FitsLen (moves + pegCount x))
    (hfity : FitsLen (moves + pegCount x + pegCount y))
    (hfit : FitsLen (zs ++ (1 :: rest)).length)
    (hrest : 0 < rest.length) :
    ∃ b2,
      (∀ h : 0 < b2.sudo_5Board_4home.size, b2.sudo_5Board_4home[0] = embed x) ∧
      (∀ h : 1 < b2.sudo_5Board_4home.size, b2.sudo_5Board_4home[1] = embed y) ∧
      b2.sudo_5Board_6marker = -1 ∧
      let cells := zs ++ (1 :: rest)
      let k := zs.length + 1
      let toN := cells.length - 1
      Ecbs.walk_chord b (embed cells) =
        SudoRt.runLoopOn (Int.ofNat k, (b2, true))
          (fuelRange (Int.ofNat k) (Int.ofNat toN))
          (chordStep (embed cells) (Int.ofNat toN)) chordAfter (fun r => pure r) ∧
      walkRun t.n t.k t.benchlen (x, y) false acc (zs ++ [1]) = some (true, (x, y)) := by
  let bf := chordFlag b
  have hAtF := chord_flag_at b t x y moves peak hAt
  have hlift := marker_lift_down bf hAtF.marker
  obtain ⟨b2, _mv2, _pk2, hdo, hx0, hy1, _hmv, _hpk, _hsum, hmark, _hst, _hho, _hctrl, _hsl,
      _hstep⟩ :=
    chord_fresh_white_down bf x y t.n moves peak hAtF.szH hAtF.szD hx hy hf hfitx hfity
      hAtF.tierN hAtF.hmoves hAtF.hpeak hAtF.marker hAtF.held0 hAtF.held1
      hAtF.held3 hAtF.home3 hAtF.held4 hAtF.home4
  have hcopy : (do
      let board ← Ecbs.copy_band bf Ecbs.across Ecbs.base_across false
      Ecbs.copy_band board Ecbs.up Ecbs.base_up false) = .ok b2 := by
    rw [hlift, ok_bind] at hdo
    exact hdo
  have hbeq : SudoRt.SEq.beq (Int.ofNat 1) (2 : Int) = false := by decide
  have hreach := chord_reach bf b2 zs rest 1 hz (Or.inl rfl)
      (by simp [List.length_append]; omega) hfit hrest hlift (by simpa [hbeq] using hcopy)
  have hpos : 0 < (zs ++ (1 :: rest)).length := by
    simp [List.length_append]; omega
  have hloop := chord_from_zero b (zs ++ (1 :: rest)) hpos hfit
  refine ⟨b2, hx0, hy1, hmark, ?_, ?_⟩
  · simpa [bf] using hloop.trans hreach
  · have hwhite := walk_chord_at_white b t x y moves peak zs acc hAt hx hy hz hf hfitx hfity
      (FitsLen.of_le hfit (by simp [List.length_append]))
    obtain ⟨_, _, _, _, hrun⟩ := hwhite
    exact hrun

end EcbsLink2.Link2
