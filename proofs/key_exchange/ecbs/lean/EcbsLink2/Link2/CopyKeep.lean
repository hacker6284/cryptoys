/-
  The opening copy, as two `place`s of an abstract board. `place_*` carries
  the control frame: strict, hole, control, slides, the ladder, the row, the
  tally, and the ops array. The board stays a variable. Proof-only. Not a
  security claim.
-/
import EcbsLink2.Link2.OpenBoard
import EcbsLink2.Link2.ChordRise

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

attribute [local irreducible] placeBoard

/-- What the board handed to the opening copy already has. `place` does not
    write these, apart from homes 0 and 1 and the move and peak counters. -/
structure InLay (t : Spec.Tier) (b : Ecbs.Board) (x y : List Nat) (mv pk : Nat) : Prop where
  szH : b.sudo_5Board_4home.size = 8
  szD : b.sudo_5Board_4held.size = 8
  bench : b.sudo_5Board_8bench_on = false
  marker : b.sudo_5Board_6marker = -1
  flag : b.sudo_5Board_9marker_on = true
  strict : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = 0
  hole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = 0
  slides : b.sudo_5Board_4cost.sudo_5Costs_6slides = 0
  mx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = 0
  ctrl : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (tierR t)
  high : b.sudo_5Board_4cost.sudo_5Costs_15control_highest =
    Int.ofNat (t.script + tierR t + 1)
  tmax : b.sudo_5Board_4cost.sudo_5Costs_9tally_max = 0
  ops : b.sudo_5Board_4cost.sudo_5Costs_3ops = Array.mkArray 5 0
  tier : b.sudo_5Board_1t = embTier t
  row : b.sudo_5Board_3row = embed (paintedRow t)
  ladder : b.sudo_5Board_6ladder = embed (tierClimb t)
  l0 : b.sudo_5Board_7ladder0 = Int.ofNat (t.script + 2)
  nr : b.sudo_5Board_6nrungs = Int.ofNat (tierR t)
  park : b.sudo_5Board_9park_hole = Int.ofNat (t.script + 2 + tierR t)
  parked : b.sudo_5Board_11parked_from = -1
  ridx : b.sudo_5Board_8rung_idx = 0
  tally : b.sudo_5Board_9tally_len = 0
  t0 : b.sudo_5Board_6tally0 = Int.ofNat (tallyOrigin t)
  held0 : b.sudo_5Board_4held[0]'(by rw [szD]; decide) = false
  held1 : b.sudo_5Board_4held[1]'(by rw [szD]; decide) = false
  held2 : b.sudo_5Board_4held[2]'(by rw [szD]; decide) = false
  held3 : b.sudo_5Board_4held[3]'(by rw [szD]; decide) = true
  held4 : b.sudo_5Board_4held[4]'(by rw [szD]; decide) = true
  held5 : b.sudo_5Board_4held[5]'(by rw [szD]; decide) = false
  held6 : b.sudo_5Board_4held[6]'(by rw [szD]; decide) = false
  home3 : b.sudo_5Board_4home[3]'(by rw [szH]; decide) = embed x
  home4 : b.sudo_5Board_4home[4]'(by rw [szH]; decide) = embed y
  moves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int)
  peak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (pk : Int)
  tierN : b.sudo_5Board_1t.sudo_4Tier_1n = (t.n : Int)

/-- The board after the two copies. Homes 0 and 1 hold the copied point.
    The control frame is the one `InLay` recorded. -/
structure OutLay (t : Spec.Tier) (b : Ecbs.Board) (x y1 y4 : List Nat)
    (mv pk : Nat) : Prop where
  szH : b.sudo_5Board_4home.size = 8
  szD : b.sudo_5Board_4held.size = 8
  bench : b.sudo_5Board_8bench_on = false
  marker : b.sudo_5Board_6marker = -1
  flag : b.sudo_5Board_9marker_on = true
  strict : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = 0
  hole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = 0
  slides : b.sudo_5Board_4cost.sudo_5Costs_6slides = 0
  mx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = 0
  ctrl : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (tierR t)
  high : b.sudo_5Board_4cost.sudo_5Costs_15control_highest =
    Int.ofNat (t.script + tierR t + 1)
  tmax : b.sudo_5Board_4cost.sudo_5Costs_9tally_max = 0
  ops : b.sudo_5Board_4cost.sudo_5Costs_3ops = Array.mkArray 5 0
  tier : b.sudo_5Board_1t = embTier t
  row : b.sudo_5Board_3row = embed (paintedRow t)
  ladder : b.sudo_5Board_6ladder = embed (tierClimb t)
  l0 : b.sudo_5Board_7ladder0 = Int.ofNat (t.script + 2)
  nr : b.sudo_5Board_6nrungs = Int.ofNat (tierR t)
  park : b.sudo_5Board_9park_hole = Int.ofNat (t.script + 2 + tierR t)
  parked : b.sudo_5Board_11parked_from = -1
  ridx : b.sudo_5Board_8rung_idx = 0
  tally : b.sudo_5Board_9tally_len = 0
  t0 : b.sudo_5Board_6tally0 = Int.ofNat (tallyOrigin t)
  held0 : b.sudo_5Board_4held[0]'(by rw [szD]; decide) = true
  held1 : b.sudo_5Board_4held[1]'(by rw [szD]; decide) = true
  held2 : b.sudo_5Board_4held[2]'(by rw [szD]; decide) = false
  held3 : b.sudo_5Board_4held[3]'(by rw [szD]; decide) = true
  held4 : b.sudo_5Board_4held[4]'(by rw [szD]; decide) = true
  held5 : b.sudo_5Board_4held[5]'(by rw [szD]; decide) = false
  held6 : b.sudo_5Board_4held[6]'(by rw [szD]; decide) = false
  home0 : b.sudo_5Board_4home[0]'(by rw [szH]; decide) = embed x
  home1 : b.sudo_5Board_4home[1]'(by rw [szH]; decide) = embed y1
  home3 : b.sudo_5Board_4home[3]'(by rw [szH]; decide) = embed x
  home4 : b.sudo_5Board_4home[4]'(by rw [szH]; decide) = embed y4
  moves : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mv
  peak : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk

private theorem keep2 {α : Type} (proj : Ecbs.Board → α)
    (hkeep : ∀ (b : Ecbs.Board) (home : Nat)
      (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
      (xs : List Nat) (moves peak : Nat),
      proj (placeBoard b home hH hD xs moves peak) = proj b)
    (b : Ecbs.Board) (x y : List Nat)
    (h0H : 0 < b.sudo_5Board_4home.size) (h0D : 0 < b.sudo_5Board_4held.size)
    (moves peak : Nat)
    (h1H : 1 < (placeBoard b 0 h0H h0D x moves peak).sudo_5Board_4home.size)
    (h1D : 1 < (placeBoard b 0 h0H h0D x moves peak).sudo_5Board_4held.size)
    (mv1 pk1 : Nat) :
    proj (placeBoard (placeBoard b 0 h0H h0D x moves peak) 1 h1H h1D y mv1 pk1) =
      proj b :=
  (hkeep (placeBoard b 0 h0H h0D x moves peak) 1 h1H h1D y mv1 pk1).trans
    (hkeep b 0 h0H h0D x moves peak)

private theorem held_skip {v : Bool} (b : Ecbs.Board) (home j : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat)
    (hj : j < (placeBoard b home hH hD xs moves peak).sudo_5Board_4held.size)
    (hne : home ≠ j) (hjb : j < b.sudo_5Board_4held.size)
    (hval : b.sudo_5Board_4held[j] = v) :
    (placeBoard b home hH hD xs moves peak).sudo_5Board_4held[j] = v := by
  have hget := get_eq_of_array (place_held_eq b home hH hD xs moves peak) j hj
  simp only [Array.getElem_set, hne] at hget
  exact hget.trans hval

private theorem home_skip {v : Array Int} (b : Ecbs.Board) (home j : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat)
    (hj : j < (placeBoard b home hH hD xs moves peak).sudo_5Board_4home.size)
    (hne : home ≠ j) (hjb : j < b.sudo_5Board_4home.size)
    (hval : b.sudo_5Board_4home[j] = v) :
    (placeBoard b home hH hD xs moves peak).sudo_5Board_4home[j] = v := by
  have hget := get_eq_of_array (place_home_eq b home hH hD xs moves peak) j hj
  simp only [Array.getElem_set, hne] at hget
  exact hget.trans hval

/-- Two white copies. `b` is not reduced: each kept field is `place_*`. -/
theorem white_copy_kept (t : Spec.Tier) (b : Ecbs.Board) (x y : List Nat) (mv pk : Nat)
    (lay : InLay t b x y mv pk)
    (hx : x.length = t.n) (hy : y.length = t.n)
    (hf : FitsLen t.n)
    (hfitx : FitsLen (mv + pegCount x))
    (hfity : FitsLen (mv + pegCount x + pegCount y)) :
    ∃ b2 pk2,
      (do
          let board ← Ecbs.copy_band b Ecbs.across Ecbs.base_across false
          Ecbs.copy_band board Ecbs.up Ecbs.base_up false) = .ok b2 ∧
      OutLay t b2 x y y (mv + pegCount x + pegCount y) pk2 := by
  have h0H : 0 < b.sudo_5Board_4home.size := by rw [lay.szH]; decide
  have h0D : 0 < b.sudo_5Board_4held.size := by rw [lay.szD]; decide
  have h3H : 3 < b.sudo_5Board_4home.size := by rw [lay.szH]; decide
  have h3D : 3 < b.sudo_5Board_4held.size := by rw [lay.szD]; decide
  have h4H : 4 < b.sudo_5Board_4home.size := by rw [lay.szH]; decide
  have h4D : 4 < b.sudo_5Board_4held.size := by rw [lay.szD]; decide
  have h7 : 7 ≤ b.sudo_5Board_4held.size := by rw [lay.szD]; decide
  have hnx : b.sudo_5Board_1t.sudo_4Tier_1n = (x.length : Int) := by rw [lay.tierN, hx]
  have hcopy1 := copy_band_refines b 0 3 x mv pk
    h0H h0D h3H h3D h7 lay.held3 lay.home3 lay.held0 hnx
    (by simpa [hx] using hf) lay.moves (by rw [lay.peak]) hfitx
  let b1 := placeBoard b 0 h0H h0D x mv pk
  have hszH1 : b1.sudo_5Board_4home.size = 8 := by
    rw [place_home_eq, Array.size_set, lay.szH]
  have hszD1 : b1.sudo_5Board_4held.size = 8 := by
    rw [place_held_eq, Array.size_set, lay.szD]
  have h1H1 : 1 < b1.sudo_5Board_4home.size := by rw [hszH1]; decide
  have h1D1 : 1 < b1.sudo_5Board_4held.size := by rw [hszD1]; decide
  have h4H1 : 4 < b1.sudo_5Board_4home.size := by rw [hszH1]; decide
  have h4D1 : 4 < b1.sudo_5Board_4held.size := by rw [hszD1]; decide
  have h7_1 : 7 ≤ b1.sudo_5Board_4held.size := by rw [hszD1]; decide
  have hempty1 : b1.sudo_5Board_4held[1] = false :=
    held_skip b 0 1 h0H h0D x mv pk h1D1 (by decide) (by rw [lay.szD]; decide) lay.held1
  have h4t1 : b1.sudo_5Board_4held[4] = true :=
    held_skip b 0 4 h0H h0D x mv pk h4D1 (by decide) h4D lay.held4
  have h4a1 : b1.sudo_5Board_4home[4] = embed y :=
    home_skip b 0 4 h0H h0D x mv pk h4H1 (by decide) h4H lay.home4
  let mv1 := mv + pegCount x
  let pk1 := if pk < countHeld (b.sudo_5Board_4held.set ⟨0, h0D⟩ true) 7
    then countHeld (b.sudo_5Board_4held.set ⟨0, h0D⟩ true) 7 else pk
  have hmv1 : b1.sudo_5Board_4cost.sudo_5Costs_5moves = (mv1 : Int) := by
    rw [place_moves_eq]; exact ofNat_eq_natCast _
  have hpk1 : b1.sudo_5Board_4cost.sudo_5Costs_4peak = (pk1 : Int) := by
    rw [place_peak_nat b 0 h0H h0D x mv pk (by rw [lay.peak])]
    exact ofNat_eq_natCast _
  have hny : b1.sudo_5Board_1t.sudo_4Tier_1n = (y.length : Int) := by
    rw [place_tier_eq, lay.tierN, hy]
  have hcopy2 := copy_band_refines b1 1 4 y mv1 pk1
    h1H1 h1D1 h4H1 h4D1 h7_1 h4t1 h4a1 hempty1 hny (by simpa [hy] using hf)
    hmv1 hpk1 hfity
  let b2 := placeBoard b1 1 h1H1 h1D1 y mv1 pk1
  let pk2 := if pk1 < countHeld (b1.sudo_5Board_4held.set ⟨1, h1D1⟩ true) 7
    then countHeld (b1.sudo_5Board_4held.set ⟨1, h1D1⟩ true) 7 else pk1
  have hszH2 : b2.sudo_5Board_4home.size = 8 := by
    rw [place_home_eq, Array.size_set, hszH1]
  have hszD2 : b2.sudo_5Board_4held.size = 8 := by
    rw [place_held_eq, Array.size_set, hszD1]
  refine ⟨b2, pk2, ?_, ?_⟩
  · rw [show Ecbs.across = ((0 : Nat) : Int) from rfl,
        show Ecbs.base_across = ((3 : Nat) : Int) from rfl,
        show Ecbs.up = ((1 : Nat) : Int) from rfl,
        show Ecbs.base_up = ((4 : Nat) : Int) from rfl, hcopy1, ok_bind]
    simpa [b1, b2] using hcopy2
  · exact
    { szH := hszH2
      szD := hszD2
      bench := (keep2 (fun b => b.sudo_5Board_8bench_on) place_bench b x y h0H h0D mv pk
        h1H1 h1D1 mv1 pk1).trans lay.bench
      marker := (keep2 (fun b => b.sudo_5Board_6marker) place_marker_eq b x y h0H h0D mv pk
        h1H1 h1D1 mv1 pk1).trans lay.marker
      flag := (keep2 (fun b => b.sudo_5Board_9marker_on) place_flag b x y h0H h0D mv pk
        h1H1 h1D1 mv1 pk1).trans lay.flag
      strict := (keep2 (fun b => b.sudo_5Board_4cost.sudo_5Costs_11peak_strict) place_strict_eq
        b x y h0H h0D mv pk h1H1 h1D1 mv1 pk1).trans lay.strict
      hole := (keep2 (fun b => b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole) place_hole_eq
        b x y h0H h0D mv pk h1H1 h1D1 mv1 pk1).trans lay.hole
      slides := (keep2 (fun b => b.sudo_5Board_4cost.sudo_5Costs_6slides) place_slides_eq
        b x y h0H h0D mv pk h1H1 h1D1 mv1 pk1).trans lay.slides
      mx := (keep2 (fun b => b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max) place_mx_eq
        b x y h0H h0D mv pk h1H1 h1D1 mv1 pk1).trans lay.mx
      ctrl := (keep2 (fun b => b.sudo_5Board_4cost.sudo_5Costs_4ctrl) place_ctrl_eq
        b x y h0H h0D mv pk h1H1 h1D1 mv1 pk1).trans lay.ctrl
      high := (keep2 (fun b => b.sudo_5Board_4cost.sudo_5Costs_15control_highest) place_high
        b x y h0H h0D mv pk h1H1 h1D1 mv1 pk1).trans lay.high
      tmax := (keep2 (fun b => b.sudo_5Board_4cost.sudo_5Costs_9tally_max) place_tmax
        b x y h0H h0D mv pk h1H1 h1D1 mv1 pk1).trans lay.tmax
      ops := (keep2 (fun b => b.sudo_5Board_4cost.sudo_5Costs_3ops) place_ops_eq
        b x y h0H h0D mv pk h1H1 h1D1 mv1 pk1).trans lay.ops
      tier := (keep2 (fun b => b.sudo_5Board_1t) place_tier b x y h0H h0D mv pk
        h1H1 h1D1 mv1 pk1).trans lay.tier
      row := (keep2 (fun b => b.sudo_5Board_3row) place_row b x y h0H h0D mv pk
        h1H1 h1D1 mv1 pk1).trans lay.row
      ladder := (keep2 (fun b => b.sudo_5Board_6ladder) place_ladder b x y h0H h0D mv pk
        h1H1 h1D1 mv1 pk1).trans lay.ladder
      l0 := (keep2 (fun b => b.sudo_5Board_7ladder0) place_l0 b x y h0H h0D mv pk
        h1H1 h1D1 mv1 pk1).trans lay.l0
      nr := (keep2 (fun b => b.sudo_5Board_6nrungs) place_nr b x y h0H h0D mv pk
        h1H1 h1D1 mv1 pk1).trans lay.nr
      park := (keep2 (fun b => b.sudo_5Board_9park_hole) place_park b x y h0H h0D mv pk
        h1H1 h1D1 mv1 pk1).trans lay.park
      parked := (keep2 (fun b => b.sudo_5Board_11parked_from) place_from b x y h0H h0D mv pk
        h1H1 h1D1 mv1 pk1).trans lay.parked
      ridx := (keep2 (fun b => b.sudo_5Board_8rung_idx) place_ridx b x y h0H h0D mv pk
        h1H1 h1D1 mv1 pk1).trans lay.ridx
      tally := (keep2 (fun b => b.sudo_5Board_9tally_len) place_tally b x y h0H h0D mv pk
        h1H1 h1D1 mv1 pk1).trans lay.tally
      t0 := (keep2 (fun b => b.sudo_5Board_6tally0) place_t0 b x y h0H h0D mv pk
        h1H1 h1D1 mv1 pk1).trans lay.t0
      held0 := by
        have hget := get_eq_of_array (place_held_eq b1 1 h1H1 h1D1 y mv1 pk1) 0
          (by rw [hszD2]; decide)
        have hne : (1 : Nat) ≠ 0 := by decide
        simp only [Array.getElem_set, hne] at hget
        have hsrc := get_eq_of_array (place_held_eq b 0 h0H h0D x mv pk) 0
          (by rw [hszD1]; decide)
        simp only [Array.getElem_set] at hsrc
        exact hget.trans hsrc
      held1 := by
        have hget := get_eq_of_array (place_held_eq b1 1 h1H1 h1D1 y mv1 pk1) 1
          (by rw [hszD2]; decide)
        simp only [Array.getElem_set] at hget
        exact hget
      held2 := by
        have h1 := held_skip b 0 2 h0H h0D x mv pk (by rw [hszD1]; decide) (by decide)
          (by rw [lay.szD]; decide) lay.held2
        exact held_skip b1 1 2 h1H1 h1D1 y mv1 pk1 (by rw [hszD2]; decide) (by decide)
          (by rw [hszD1]; decide) h1
      held3 := by
        have h1 := held_skip b 0 3 h0H h0D x mv pk (by rw [hszD1]; decide) (by decide)
          h3D lay.held3
        exact held_skip b1 1 3 h1H1 h1D1 y mv1 pk1 (by rw [hszD2]; decide) (by decide)
          (by rw [hszD1]; decide) h1
      held4 := by
        exact held_skip b1 1 4 h1H1 h1D1 y mv1 pk1 (by rw [hszD2]; decide) (by decide)
          h4D1 h4t1
      held5 := by
        have h1 := held_skip b 0 5 h0H h0D x mv pk (by rw [hszD1]; decide) (by decide)
          (by rw [lay.szD]; decide) lay.held5
        exact held_skip b1 1 5 h1H1 h1D1 y mv1 pk1 (by rw [hszD2]; decide) (by decide)
          (by rw [hszD1]; decide) h1
      held6 := by
        have h1 := held_skip b 0 6 h0H h0D x mv pk (by rw [hszD1]; decide) (by decide)
          (by rw [lay.szD]; decide) lay.held6
        exact held_skip b1 1 6 h1H1 h1D1 y mv1 pk1 (by rw [hszD2]; decide) (by decide)
          (by rw [hszD1]; decide) h1
      home0 := by
        have hget := get_eq_of_array (place_home_eq b1 1 h1H1 h1D1 y mv1 pk1) 0
          (by rw [hszH2]; decide)
        have hne : (1 : Nat) ≠ 0 := by decide
        simp only [Array.getElem_set, hne] at hget
        have hsrc := get_eq_of_array (place_home_eq b 0 h0H h0D x mv pk) 0
          (by rw [hszH1]; decide)
        simp only [Array.getElem_set] at hsrc
        exact hget.trans hsrc
      home1 := by
        have hget := get_eq_of_array (place_home_eq b1 1 h1H1 h1D1 y mv1 pk1) 1
          (by rw [hszH2]; decide)
        simp only [Array.getElem_set] at hget
        exact hget
      home3 := by
        have h1 := home_skip b 0 3 h0H h0D x mv pk (by rw [hszH1]; decide) (by decide)
          h3H lay.home3
        exact home_skip b1 1 3 h1H1 h1D1 y mv1 pk1 (by rw [hszH2]; decide) (by decide)
          (by rw [hszH1]; decide) h1
      home4 := by
        exact home_skip b1 1 4 h1H1 h1D1 y mv1 pk1 (by rw [hszH2]; decide) (by decide)
          h4H1 h4a1
      moves := by
        rw [place_moves_eq]
      peak := by
        rw [place_peak_nat b1 1 h1H1 h1D1 y mv1 pk1 hpk1] }

end EcbsLink2.Link2
