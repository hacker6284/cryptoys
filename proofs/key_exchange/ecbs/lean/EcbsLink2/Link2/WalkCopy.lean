/-
  The first live cell of `walk_chord` when the cell is white: copy base across
  into across and base up into up. SPEC.md §3 R8 lines 158–159, the copy
  before any Frobenius. `placeBoard` is named; the second copy reads it by
  projection. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.Place
import EcbsLink2.Link2.MulSettle
import EcbsLink2.SpecBase

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

theorem place_held_eq (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat) :
    (placeBoard b home hH hD xs moves peak).sudo_5Board_4held =
      b.sudo_5Board_4held.set ⟨home, hD⟩ true := by
  unfold placeBoard
  dsimp only
  split <;> rfl

theorem place_home_eq (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat) :
    (placeBoard b home hH hD xs moves peak).sudo_5Board_4home =
      b.sudo_5Board_4home.set ⟨home, hH⟩ (embed xs) := by
  unfold placeBoard
  dsimp only
  split <;> rfl

theorem place_moves_eq (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat) :
    (placeBoard b home hH hD xs moves peak).sudo_5Board_4cost.sudo_5Costs_5moves =
      Int.ofNat (moves + pegCount xs) := by
  unfold placeBoard
  dsimp only
  split <;> rfl

theorem place_peak_nat (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int)) :
    (placeBoard b home hH hD xs moves peak).sudo_5Board_4cost.sudo_5Costs_4peak =
      Int.ofNat (if peak < countHeld (b.sudo_5Board_4held.set ⟨home, hD⟩ true) 7
        then countHeld (b.sudo_5Board_4held.set ⟨home, hD⟩ true) 7
        else peak) := by
  unfold placeBoard
  dsimp only
  by_cases hlt : peak < countHeld (b.sudo_5Board_4held.set ⟨home, hD⟩ true) 7
  · simp [hlt, ofNat_eq_natCast]
  · simp [hlt, hpeak, ofNat_eq_natCast]

theorem place_tier_eq (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat) :
    (placeBoard b home hH hD xs moves peak).sudo_5Board_1t = b.sudo_5Board_1t := by
  unfold placeBoard
  dsimp only
  split <;> rfl

theorem place_strict_eq (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat) :
    (placeBoard b home hH hD xs moves peak).sudo_5Board_4cost.sudo_5Costs_11peak_strict =
      b.sudo_5Board_4cost.sudo_5Costs_11peak_strict := by
  unfold placeBoard
  dsimp only
  split <;> rfl

theorem place_hole_eq (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat) :
    (placeBoard b home hH hD xs moves peak).sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole := by
  unfold placeBoard
  dsimp only
  split <;> rfl

theorem place_slides_eq (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat) :
    (placeBoard b home hH hD xs moves peak).sudo_5Board_4cost.sudo_5Costs_6slides =
      b.sudo_5Board_4cost.sudo_5Costs_6slides := by
  unfold placeBoard
  dsimp only
  split <;> rfl

theorem place_ctrl_eq (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat) :
    (placeBoard b home hH hD xs moves peak).sudo_5Board_4cost.sudo_5Costs_4ctrl =
      b.sudo_5Board_4cost.sudo_5Costs_4ctrl := by
  unfold placeBoard
  dsimp only
  split <;> rfl

theorem place_ops_eq (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat) :
    (placeBoard b home hH hD xs moves peak).sudo_5Board_4cost.sudo_5Costs_3ops =
      b.sudo_5Board_4cost.sudo_5Costs_3ops := by
  unfold placeBoard
  dsimp only
  split <;> rfl

theorem place_marker_eq (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat) :
    (placeBoard b home hH hD xs moves peak).sudo_5Board_6marker =
      b.sudo_5Board_6marker := by
  unfold placeBoard
  dsimp only
  split <;> rfl

theorem place_mx_eq (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat) :
    (placeBoard b home hH hD xs moves peak).sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
      b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max := by
  unfold placeBoard
  dsimp only
  split <;> rfl

attribute [local irreducible] placeBoard

/-- White cell, accumulator not yet live. Across and up receive the base point. -/
theorem walk_copy_white (b : Ecbs.Board) (x y : List Nat) (n moves peak : Nat)
    (hszH : b.sudo_5Board_4home.size = 8) (hszD : b.sudo_5Board_4held.size = 8)
    (hx : x.length = n) (hy : y.length = n)
    (hf : FitsLen n)
    (hfitx : FitsLen (moves + pegCount x))
    (hfity : FitsLen (moves + pegCount x + pegCount y))
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (h0 : b.sudo_5Board_4held[0]'(by rw [hszD]; decide) = false)
    (h1 : b.sudo_5Board_4held[1]'(by rw [hszD]; decide) = false)
    (h3t : b.sudo_5Board_4held[3]'(by rw [hszD]; decide) = true)
    (h3a : b.sudo_5Board_4home[3]'(by rw [hszH]; decide) = embed x)
    (h4t : b.sudo_5Board_4held[4]'(by rw [hszD]; decide) = true)
    (h4a : b.sudo_5Board_4home[4]'(by rw [hszH]; decide) = embed y) :
    ∃ b2 mv2 pk2,
      (do
          let b ← Ecbs.copy_band b Ecbs.across Ecbs.base_across false
          Ecbs.copy_band b Ecbs.up Ecbs.base_up false) = .ok b2 ∧
      b2.sudo_5Board_4home.size = 8 ∧
      b2.sudo_5Board_4held.size = 8 ∧
      (∀ (h : 0 < b2.sudo_5Board_4home.size), b2.sudo_5Board_4home[0] = embed x) ∧
      (∀ (h : 1 < b2.sudo_5Board_4home.size), b2.sudo_5Board_4home[1] = embed y) ∧
      (∀ (h : 0 < b2.sudo_5Board_4held.size), b2.sudo_5Board_4held[0] = true) ∧
      (∀ (h : 1 < b2.sudo_5Board_4held.size), b2.sudo_5Board_4held[1] = true) ∧
      (∀ (h : 3 < b2.sudo_5Board_4home.size), b2.sudo_5Board_4home[3] = embed x) ∧
      (∀ (h : 4 < b2.sudo_5Board_4home.size), b2.sudo_5Board_4home[4] = embed y) ∧
      b2.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mv2 ∧
      b2.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk2 ∧
      mv2 = moves + pegCount x + pegCount y ∧
      b2.sudo_5Board_6marker = b.sudo_5Board_6marker ∧
      b2.sudo_5Board_4cost.sudo_5Costs_11peak_strict =
        b.sudo_5Board_4cost.sudo_5Costs_11peak_strict ∧
      b2.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
        b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole ∧
      b2.sudo_5Board_4cost.sudo_5Costs_4ctrl =
        b.sudo_5Board_4cost.sudo_5Costs_4ctrl ∧
      b2.sudo_5Board_4cost.sudo_5Costs_6slides =
        b.sudo_5Board_4cost.sudo_5Costs_6slides := by
  have h0H : 0 < b.sudo_5Board_4home.size := by rw [hszH]; decide
  have h0D : 0 < b.sudo_5Board_4held.size := by rw [hszD]; decide
  have h1H : 1 < b.sudo_5Board_4home.size := by rw [hszH]; decide
  have h1D : 1 < b.sudo_5Board_4held.size := by rw [hszD]; decide
  have h3H : 3 < b.sudo_5Board_4home.size := by rw [hszH]; decide
  have h3D : 3 < b.sudo_5Board_4held.size := by rw [hszD]; decide
  have h4H : 4 < b.sudo_5Board_4home.size := by rw [hszH]; decide
  have h4D : 4 < b.sudo_5Board_4held.size := by rw [hszD]; decide
  have h7 : 7 ≤ b.sudo_5Board_4held.size := by rw [hszD]; decide
  have hnx : b.sudo_5Board_1t.sudo_4Tier_1n = (x.length : Int) := by rw [hn, hx]
  have hcopy1 := copy_band_refines b 0 3 x moves peak
    h0H h0D h3H h3D h7 h3t h3a h0 hnx (by simpa [hx] using hf)
    hmoves (by rw [hpeak]) hfitx
  let b1 := placeBoard b 0 h0H h0D x moves peak
  have hszH1 : b1.sudo_5Board_4home.size = 8 := by
    rw [place_home_eq, Array.size_set, hszH]
  have hszD1 : b1.sudo_5Board_4held.size = 8 := by
    rw [place_held_eq, Array.size_set, hszD]
  have h1D1 : 1 < b1.sudo_5Board_4held.size := by rw [hszD1]; decide
  have h1H1 : 1 < b1.sudo_5Board_4home.size := by rw [hszH1]; decide
  have h4D1 : 4 < b1.sudo_5Board_4held.size := by rw [hszD1]; decide
  have h4H1 : 4 < b1.sudo_5Board_4home.size := by rw [hszH1]; decide
  have h7_1 : 7 ≤ b1.sudo_5Board_4held.size := by rw [hszD1]; decide
  have hempty1 : b1.sudo_5Board_4held[1] = false := by
    have hget := get_eq_of_array (place_held_eq b 0 h0H h0D x moves peak) 1 h1D1
    have hne : (0 : Nat) ≠ 1 := by decide
    simp only [Array.getElem_set, hne] at hget
    exact hget.trans h1
  have h4t1 : b1.sudo_5Board_4held[4] = true := by
    have hget := get_eq_of_array (place_held_eq b 0 h0H h0D x moves peak) 4 h4D1
    have hne : (0 : Nat) ≠ 4 := by decide
    simp only [Array.getElem_set, hne] at hget
    exact hget.trans h4t
  have h4a1 : b1.sudo_5Board_4home[4] = embed y := by
    have hget := get_eq_of_array (place_home_eq b 0 h0H h0D x moves peak) 4 h4H1
    have hne : (0 : Nat) ≠ 4 := by decide
    simp only [Array.getElem_set, hne] at hget
    exact hget.trans h4a
  let mv1 := moves + pegCount x
  let pk1 := if peak < countHeld (b.sudo_5Board_4held.set ⟨0, h0D⟩ true) 7
    then countHeld (b.sudo_5Board_4held.set ⟨0, h0D⟩ true) 7 else peak
  have hmv1 : b1.sudo_5Board_4cost.sudo_5Costs_5moves = (mv1 : Int) := by
    rw [place_moves_eq]; exact ofNat_eq_natCast _
  have hpk1 : b1.sudo_5Board_4cost.sudo_5Costs_4peak = (pk1 : Int) := by
    rw [place_peak_nat b 0 h0H h0D x moves peak (by rw [hpeak])]
    exact ofNat_eq_natCast _
  have hny : b1.sudo_5Board_1t.sudo_4Tier_1n = (y.length : Int) := by
    rw [place_tier_eq, hn, hy]
  have hcopy2 := copy_band_refines b1 1 4 y mv1 pk1
    h1H1 h1D1 h4H1 h4D1 h7_1 h4t1 h4a1 hempty1 hny (by simpa [hy] using hf)
    hmv1 hpk1 hfity
  let b2 := placeBoard b1 1 h1H1 h1D1 y mv1 pk1
  refine ⟨b2, mv1 + pegCount y,
      if pk1 < countHeld (b1.sudo_5Board_4held.set ⟨1, h1D1⟩ true) 7
        then countHeld (b1.sudo_5Board_4held.set ⟨1, h1D1⟩ true) 7 else pk1,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_,
      (place_strict_eq b1 1 h1H1 h1D1 y mv1 pk1).trans
        (place_strict_eq b 0 h0H h0D x moves peak),
      (place_hole_eq b1 1 h1H1 h1D1 y mv1 pk1).trans
        (place_hole_eq b 0 h0H h0D x moves peak),
      (place_ctrl_eq b1 1 h1H1 h1D1 y mv1 pk1).trans
        (place_ctrl_eq b 0 h0H h0D x moves peak),
      (place_slides_eq b1 1 h1H1 h1D1 y mv1 pk1).trans
        (place_slides_eq b 0 h0H h0D x moves peak)⟩
  · rw [show Ecbs.across = ((0 : Nat) : Int) from rfl,
        show Ecbs.base_across = ((3 : Nat) : Int) from rfl,
        show Ecbs.up = ((1 : Nat) : Int) from rfl,
        show Ecbs.base_up = ((4 : Nat) : Int) from rfl,
        hcopy1, ok_bind]
    simpa [b1, b2] using hcopy2
  · rw [place_home_eq, Array.size_set, hszH1]
  · rw [place_held_eq, Array.size_set, hszD1]
  · intro h0
    have hget := get_eq_of_array (place_home_eq b1 1 h1H1 h1D1 y mv1 pk1) 0 h0
    have hne : (1 : Nat) ≠ 0 := by decide
    simp only [Array.getElem_set, hne] at hget
    have hsrc := get_eq_of_array (place_home_eq b 0 h0H h0D x moves peak) 0
      (by rw [hszH1]; decide)
    simp only [Array.getElem_set] at hsrc
    exact hget.trans hsrc
  · intro h1
    have hget := get_eq_of_array (place_home_eq b1 1 h1H1 h1D1 y mv1 pk1) 1 h1
    simp only [Array.getElem_set] at hget
    exact hget
  · intro h0
    have hget := get_eq_of_array (place_held_eq b1 1 h1H1 h1D1 y mv1 pk1) 0 h0
    have hne : (1 : Nat) ≠ 0 := by decide
    simp only [Array.getElem_set, hne] at hget
    have hsrc := get_eq_of_array (place_held_eq b 0 h0H h0D x moves peak) 0
      (by rw [hszD1]; decide)
    simp only [Array.getElem_set] at hsrc
    exact hget.trans hsrc
  · intro h1
    have hget := get_eq_of_array (place_held_eq b1 1 h1H1 h1D1 y mv1 pk1) 1 h1
    simp only [Array.getElem_set] at hget
    exact hget
  · intro h3
    have hget := get_eq_of_array (place_home_eq b1 1 h1H1 h1D1 y mv1 pk1) 3 h3
    have hne : (1 : Nat) ≠ 3 := by decide
    simp only [Array.getElem_set, hne] at hget
    have hsrc := get_eq_of_array (place_home_eq b 0 h0H h0D x moves peak) 3
      (by rw [hszH1]; decide)
    have hne0 : (0 : Nat) ≠ 3 := by decide
    simp only [Array.getElem_set, hne0] at hsrc
    exact hget.trans (hsrc.trans h3a)
  · intro h4
    have hget := get_eq_of_array (place_home_eq b1 1 h1H1 h1D1 y mv1 pk1) 4 h4
    have hne : (1 : Nat) ≠ 4 := by decide
    simp only [Array.getElem_set, hne] at hget
    exact hget.trans h4a1
  · rw [place_moves_eq]
  · rw [place_peak_nat b1 1 h1H1 h1D1 y mv1 pk1 (by rw [hpk1])]
  · rw [place_marker_eq b1 1 h1H1 h1D1 y mv1 pk1,
      place_marker_eq b 0 h0H h0D x moves peak]

/-- SPEC.md §3 R8 lines 158–159. A white cell while the accumulator is empty
    copies the base point. No Frobenius, no chord. -/
theorem walkStep_fresh_white (n k bench : Nat) (base acc : List Nat × List Nat) :
    Spec.walkStep n k bench base false acc 1 = some (true, base) := by
  unfold Spec.walkStep
  dsimp only
  simp

/-- A red cell while the accumulator is empty copies the base point with the
    up coordinate negated. -/
theorem walkStep_fresh_red (n k bench : Nat) (base acc : List Nat × List Nat) :
    Spec.walkStep n k bench base false acc 2 =
      some (true, (base.1, Spec.mirrorTrits base.2)) := by
  unfold Spec.walkStep
  dsimp only
  simp

end EcbsLink2.Link2
