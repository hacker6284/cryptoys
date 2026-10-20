/-
  One cell of `walk_chord` while the accumulator is still empty.
  A zero cell leaves the point homes alone. A white cell copies the base
  point. A red cell copies it with the up coordinate negated. Each cell
  lifts the script marker first. The board is abstract: homes, moves, and
  the marker are hypotheses. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.CopyMirror

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- The marker is on the script (`marker ≥ 0`). `marker_lift` picks it up:
    the index becomes `-1` and the control counter grows by one. Homes, held
    flags, moves, and peak stay. -/
theorem marker_lift_refines (b : Ecbs.Board) (marker ctrl : Nat)
    (hm : b.sudo_5Board_6marker = Int.ofNat marker)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hfit : FitsLen (ctrl + 1)) :
    Ecbs.marker_lift b =
      .ok { b with
        sudo_5Board_6marker := -1
        sudo_5Board_4cost := { b.sudo_5Board_4cost with
          sudo_5Costs_4ctrl := Int.ofNat (ctrl + 1) } } := by
  unfold Ecbs.marker_lift
  rw [hm]
  have hge : decide (Int.ofNat marker ≥ (0 : Int)) = true := by
    rw [decide_eq_true_eq]
    exact Int.ofNat_nonneg marker
  rw [hge, if_pos rfl, negI_one, ok_bind]
  dsimp
  rw [hc, addI_ofNat_one ctrl hfit, ok_bind, pure_eq_ok]
  rfl

/-- A zero cell, accumulator not live. The point homes are the ones
    `marker_lift` left, which are the homes it was given. -/
theorem chord_skip_cell (b : Ecbs.Board) (marker ctrl : Nat)
    (hm : b.sudo_5Board_6marker = Int.ofNat marker)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hfit : FitsLen (ctrl + 1)) :
    ∃ b1,
      Ecbs.marker_lift b = .ok b1 ∧
      b1.sudo_5Board_4home = b.sudo_5Board_4home ∧
      b1.sudo_5Board_4held = b.sudo_5Board_4held ∧
      b1.sudo_5Board_4cost.sudo_5Costs_5moves = b.sudo_5Board_4cost.sudo_5Costs_5moves ∧
      b1.sudo_5Board_4cost.sudo_5Costs_4peak = b.sudo_5Board_4cost.sudo_5Costs_4peak ∧
      b1.sudo_5Board_1t = b.sudo_5Board_1t ∧
      b1.sudo_5Board_6marker = -1 := by
  refine ⟨_, marker_lift_refines b marker ctrl hm hc hfit, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp

/-- SPEC.md §3 R8. An empty cell does not cube and does not add while the
    accumulator is empty. -/
theorem walkStep_skip (n k bench : Nat) (base acc : List Nat × List Nat) :
    walkStep n k bench base false acc 0 = some (false, acc) := by
  unfold walkStep
  simp

/-- White cell, accumulator not live. Marker lifts, then across and up receive
    the base point. This is the emitted not-live arm (`copy_band` twice, the
    up copy unmirrored) and `walkStep` on colour 1. -/
theorem chord_fresh_white (b : Ecbs.Board) (x y : List Nat) (n moves peak marker ctrl : Nat)
    (hszH : b.sudo_5Board_4home.size = 8) (hszD : b.sudo_5Board_4held.size = 8)
    (hx : x.length = n) (hy : y.length = n)
    (hf : FitsLen n)
    (hfitx : FitsLen (moves + pegCount x))
    (hfity : FitsLen (moves + pegCount x + pegCount y))
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hm : b.sudo_5Board_6marker = Int.ofNat marker)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hfitc : FitsLen (ctrl + 1))
    (h0 : b.sudo_5Board_4held[0]'(by rw [hszD]; decide) = false)
    (h1 : b.sudo_5Board_4held[1]'(by rw [hszD]; decide) = false)
    (h3t : b.sudo_5Board_4held[3]'(by rw [hszD]; decide) = true)
    (h3a : b.sudo_5Board_4home[3]'(by rw [hszH]; decide) = embed x)
    (h4t : b.sudo_5Board_4held[4]'(by rw [hszD]; decide) = true)
    (h4a : b.sudo_5Board_4home[4]'(by rw [hszH]; decide) = embed y) :
    ∃ b2 mv2 pk2,
      (do
          let b ← Ecbs.marker_lift b
          let b ← Ecbs.copy_band b Ecbs.across Ecbs.base_across false
          Ecbs.copy_band b Ecbs.up Ecbs.base_up false) = .ok b2 ∧
      (∀ (h : 0 < b2.sudo_5Board_4home.size), b2.sudo_5Board_4home[0] = embed x) ∧
      (∀ (h : 1 < b2.sudo_5Board_4home.size), b2.sudo_5Board_4home[1] = embed y) ∧
      b2.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mv2 ∧
      b2.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk2 ∧
      mv2 = moves + pegCount x + pegCount y ∧
      b2.sudo_5Board_6marker = -1 ∧
      walkStep n 0 0 (x, y) false (x, y) 1 = some (true, (x, y)) := by
  have hlift := marker_lift_refines b marker ctrl hm hc hfitc
  let b1 := { b with
    sudo_5Board_6marker := -1
    sudo_5Board_4cost := { b.sudo_5Board_4cost with
      sudo_5Costs_4ctrl := Int.ofNat (ctrl + 1) } }
  have hhome : b1.sudo_5Board_4home = b.sudo_5Board_4home := rfl
  have hheld : b1.sudo_5Board_4held = b.sudo_5Board_4held := rfl
  have hszH1 : b1.sudo_5Board_4home.size = 8 := by rw [hhome, hszH]
  have hszD1 : b1.sudo_5Board_4held.size = 8 := by rw [hheld, hszD]
  have hn1 : b1.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by
    simp [b1, hn]
  have hmoves1 : b1.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int) := by
    simp [b1, hmoves]
  have hpeak1 : b1.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int) := by
    simp [b1, hpeak]
  have h0' : b1.sudo_5Board_4held[0]'(by rw [hszD1]; decide) = false := by
    simpa [hheld] using h0
  have h1' : b1.sudo_5Board_4held[1]'(by rw [hszD1]; decide) = false := by
    simpa [hheld] using h1
  have h3t' : b1.sudo_5Board_4held[3]'(by rw [hszD1]; decide) = true := by
    simpa [hheld] using h3t
  have h3a' : b1.sudo_5Board_4home[3]'(by rw [hszH1]; decide) = embed x := by
    simpa [hhome] using h3a
  have h4t' : b1.sudo_5Board_4held[4]'(by rw [hszD1]; decide) = true := by
    simpa [hheld] using h4t
  have h4a' : b1.sudo_5Board_4home[4]'(by rw [hszH1]; decide) = embed y := by
    simpa [hhome] using h4a
  obtain ⟨b2, mv2, pk2, hcopy, _, _, hx0, hy1, _, _, _, _, hmv, hpk, hsum, hmark,
      _hst, _hho, _hctrl, _hsl, _, _⟩ :=
    walk_copy_white b1 x y n moves peak hszH1 hszD1 hx hy hf hfitx hfity
      hn1 hmoves1 hpeak1 h0' h1' h3t' h3a' h4t' h4a'
  refine ⟨b2, mv2, pk2, ?_, hx0, hy1, hmv, hpk, hsum, ?_, ?_⟩
  · rw [hlift, ok_bind]
    simpa [b1] using hcopy
  · rw [hmark]
  · simpa using walkStep_fresh_white n 0 0 (x, y) (x, y)

/-- Red cell, accumulator not live. Across receives the base across and up
    receives the negated base up. -/
theorem chord_fresh_red (b : Ecbs.Board) (x y : List Nat) (n moves peak marker ctrl : Nat)
    (hszH : b.sudo_5Board_4home.size = 8) (hszD : b.sudo_5Board_4held.size = 8)
    (hx : x.length = n) (hy : y.length = n) (hpos : 0 < n)
    (hyt : allTritList y) (hf : FitsLen n)
    (hfitx : FitsLen (moves + pegCount x))
    (hfity : FitsLen (moves + pegCount x + pegCount y))
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hm : b.sudo_5Board_6marker = Int.ofNat marker)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hfitc : FitsLen (ctrl + 1))
    (h0 : b.sudo_5Board_4held[0]'(by rw [hszD]; decide) = false)
    (h1 : b.sudo_5Board_4held[1]'(by rw [hszD]; decide) = false)
    (h3t : b.sudo_5Board_4held[3]'(by rw [hszD]; decide) = true)
    (h3a : b.sudo_5Board_4home[3]'(by rw [hszH]; decide) = embed x)
    (h4t : b.sudo_5Board_4held[4]'(by rw [hszD]; decide) = true)
    (h4a : b.sudo_5Board_4home[4]'(by rw [hszH]; decide) = embed y) :
    ∃ b2 mv2 pk2,
      (do
          let b ← Ecbs.marker_lift b
          let b ← Ecbs.copy_band b Ecbs.across Ecbs.base_across false
          Ecbs.copy_band b Ecbs.up Ecbs.base_up true) = .ok b2 ∧
      (∀ (h : 0 < b2.sudo_5Board_4home.size), b2.sudo_5Board_4home[0] = embed x) ∧
      (∀ (h : 1 < b2.sudo_5Board_4home.size),
        b2.sudo_5Board_4home[1] = embed (mirrorTrits y)) ∧
      b2.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mv2 ∧
      b2.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk2 ∧
      mv2 = moves + pegCount x + pegCount (mirrorTrits y) ∧
      b2.sudo_5Board_6marker = -1 ∧
      walkStep n 0 0 (x, y) false (x, y) 2 =
        some (true, (x, mirrorTrits y)) := by
  have hlift := marker_lift_refines b marker ctrl hm hc hfitc
  let b1 := { b with
    sudo_5Board_6marker := -1
    sudo_5Board_4cost := { b.sudo_5Board_4cost with
      sudo_5Costs_4ctrl := Int.ofNat (ctrl + 1) } }
  have hhome : b1.sudo_5Board_4home = b.sudo_5Board_4home := rfl
  have hheld : b1.sudo_5Board_4held = b.sudo_5Board_4held := rfl
  have hszH1 : b1.sudo_5Board_4home.size = 8 := by rw [hhome, hszH]
  have hszD1 : b1.sudo_5Board_4held.size = 8 := by rw [hheld, hszD]
  have hn1 : b1.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by simp [b1, hn]
  have hmoves1 : b1.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int) := by
    simp [b1, hmoves]
  have hpeak1 : b1.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int) := by
    simp [b1, hpeak]
  have h0' : b1.sudo_5Board_4held[0]'(by rw [hszD1]; decide) = false := by
    simpa [hheld] using h0
  have h1' : b1.sudo_5Board_4held[1]'(by rw [hszD1]; decide) = false := by
    simpa [hheld] using h1
  have h3t' : b1.sudo_5Board_4held[3]'(by rw [hszD1]; decide) = true := by
    simpa [hheld] using h3t
  have h3a' : b1.sudo_5Board_4home[3]'(by rw [hszH1]; decide) = embed x := by
    simpa [hhome] using h3a
  have h4t' : b1.sudo_5Board_4held[4]'(by rw [hszD1]; decide) = true := by
    simpa [hheld] using h4t
  have h4a' : b1.sudo_5Board_4home[4]'(by rw [hszH1]; decide) = embed y := by
    simpa [hhome] using h4a
  obtain ⟨b2, mv2, pk2, hcopy, hx0, hy1, hsum, hmv, hpk, hmark,
      _hst, _hho, _hctrl, _hsl⟩ :=
    walk_copy_red b1 x y n moves peak hszH1 hszD1 hx hy hpos hyt hf hfitx hfity
      hn1 hmoves1 hpeak1 h0' h1' h3t' h3a' h4t' h4a'
  refine ⟨b2, mv2, pk2, ?_, hx0, hy1, hmv, hpk, hsum, ?_, ?_⟩
  · rw [hlift, ok_bind]
    simpa [b1] using hcopy
  · rw [hmark]
  · simpa using walkStep_fresh_red n 0 0 (x, y) (x, y)

/-- The marker is already lifted (`-1`). `marker_lift` returns the same board. -/
theorem marker_lift_down (b : Ecbs.Board) (hm : b.sudo_5Board_6marker = -1) :
    Ecbs.marker_lift b = .ok b := by
  unfold Ecbs.marker_lift
  rw [hm]
  have hf : decide ((-1 : Int) ≥ (0 : Int)) = false := by decide
  rw [hf]
  simp [Bool.false_eq_true, if_false, pure_eq_ok]

/-- White opening when the marker is already `-1`. The lift is the board itself,
    so control does not move, and the two copies write the base point. -/
theorem chord_fresh_white_down (b : Ecbs.Board) (x y : List Nat) (n moves peak : Nat)
    (hszH : b.sudo_5Board_4home.size = 8) (hszD : b.sudo_5Board_4held.size = 8)
    (hx : x.length = n) (hy : y.length = n)
    (hf : FitsLen n)
    (hfitx : FitsLen (moves + pegCount x))
    (hfity : FitsLen (moves + pegCount x + pegCount y))
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hm : b.sudo_5Board_6marker = -1)
    (h0 : b.sudo_5Board_4held[0]'(by rw [hszD]; decide) = false)
    (h1 : b.sudo_5Board_4held[1]'(by rw [hszD]; decide) = false)
    (h3t : b.sudo_5Board_4held[3]'(by rw [hszD]; decide) = true)
    (h3a : b.sudo_5Board_4home[3]'(by rw [hszH]; decide) = embed x)
    (h4t : b.sudo_5Board_4held[4]'(by rw [hszD]; decide) = true)
    (h4a : b.sudo_5Board_4home[4]'(by rw [hszH]; decide) = embed y) :
    ∃ b2 mv2 pk2,
      (do
          let b ← Ecbs.marker_lift b
          let b ← Ecbs.copy_band b Ecbs.across Ecbs.base_across false
          Ecbs.copy_band b Ecbs.up Ecbs.base_up false) = .ok b2 ∧
      (∀ (h : 0 < b2.sudo_5Board_4home.size), b2.sudo_5Board_4home[0] = embed x) ∧
      (∀ (h : 1 < b2.sudo_5Board_4home.size), b2.sudo_5Board_4home[1] = embed y) ∧
      b2.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mv2 ∧
      b2.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk2 ∧
      mv2 = moves + pegCount x + pegCount y ∧
      b2.sudo_5Board_6marker = -1 ∧
      b2.sudo_5Board_4cost.sudo_5Costs_11peak_strict =
        b.sudo_5Board_4cost.sudo_5Costs_11peak_strict ∧
      b2.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
        b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole ∧
      b2.sudo_5Board_4cost.sudo_5Costs_4ctrl =
        b.sudo_5Board_4cost.sudo_5Costs_4ctrl ∧
      b2.sudo_5Board_4cost.sudo_5Costs_6slides =
        b.sudo_5Board_4cost.sudo_5Costs_6slides ∧
      walkStep n 0 0 (x, y) false (x, y) 1 = some (true, (x, y)) := by
  have hlift := marker_lift_down b hm
  obtain ⟨b2, mv2, pk2, hcopy, _, _, hx0, hy1, _, _, _, _, hmv, hpk, hsum, hmark,
      hst, hho, hctrl, hsl, _, _⟩ :=
    walk_copy_white b x y n moves peak hszH hszD hx hy hf hfitx hfity
      hn hmoves hpeak h0 h1 h3t h3a h4t h4a
  refine ⟨b2, mv2, pk2, ?_, hx0, hy1, hmv, hpk, hsum, ?_, hst, hho, hctrl, hsl, ?_⟩
  · rw [hlift, ok_bind]
    exact hcopy
  · rw [hmark, hm]
  · simpa using walkStep_fresh_white n 0 0 (x, y) (x, y)

/-- Red opening when the marker is already `-1`. The lift is the board itself,
    control does not move, and up receives the negated base up. -/
theorem chord_fresh_red_down (b : Ecbs.Board) (x y : List Nat) (n moves peak : Nat)
    (hszH : b.sudo_5Board_4home.size = 8) (hszD : b.sudo_5Board_4held.size = 8)
    (hx : x.length = n) (hy : y.length = n) (hpos : 0 < n)
    (hyt : allTritList y) (hf : FitsLen n)
    (hfitx : FitsLen (moves + pegCount x))
    (hfity : FitsLen (moves + pegCount x + pegCount y))
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hm : b.sudo_5Board_6marker = -1)
    (h0 : b.sudo_5Board_4held[0]'(by rw [hszD]; decide) = false)
    (h1 : b.sudo_5Board_4held[1]'(by rw [hszD]; decide) = false)
    (h3t : b.sudo_5Board_4held[3]'(by rw [hszD]; decide) = true)
    (h3a : b.sudo_5Board_4home[3]'(by rw [hszH]; decide) = embed x)
    (h4t : b.sudo_5Board_4held[4]'(by rw [hszD]; decide) = true)
    (h4a : b.sudo_5Board_4home[4]'(by rw [hszH]; decide) = embed y) :
    ∃ b2 mv2 pk2,
      (do
          let b ← Ecbs.marker_lift b
          let b ← Ecbs.copy_band b Ecbs.across Ecbs.base_across false
          Ecbs.copy_band b Ecbs.up Ecbs.base_up true) = .ok b2 ∧
      (∀ (h : 0 < b2.sudo_5Board_4home.size), b2.sudo_5Board_4home[0] = embed x) ∧
      (∀ (h : 1 < b2.sudo_5Board_4home.size),
        b2.sudo_5Board_4home[1] = embed (mirrorTrits y)) ∧
      b2.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mv2 ∧
      b2.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk2 ∧
      mv2 = moves + pegCount x + pegCount (mirrorTrits y) ∧
      b2.sudo_5Board_6marker = -1 ∧
      b2.sudo_5Board_4cost.sudo_5Costs_11peak_strict =
        b.sudo_5Board_4cost.sudo_5Costs_11peak_strict ∧
      b2.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
        b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole ∧
      b2.sudo_5Board_4cost.sudo_5Costs_4ctrl =
        b.sudo_5Board_4cost.sudo_5Costs_4ctrl ∧
      b2.sudo_5Board_4cost.sudo_5Costs_6slides =
        b.sudo_5Board_4cost.sudo_5Costs_6slides ∧
      walkStep n 0 0 (x, y) false (x, y) 2 =
        some (true, (x, mirrorTrits y)) := by
  have hlift := marker_lift_down b hm
  obtain ⟨b2, mv2, pk2, hcopy, hx0, hy1, hsum, hmv, hpk, hmark,
      hst, hho, hctrl, hsl⟩ :=
    walk_copy_red b x y n moves peak hszH hszD hx hy hpos hyt hf hfitx hfity
      hn hmoves hpeak h0 h1 h3t h3a h4t h4a
  refine ⟨b2, mv2, pk2, ?_, hx0, hy1, hmv, hpk, hsum, ?_, hst, hho, hctrl, hsl, ?_⟩
  · rw [hlift, ok_bind]
    exact hcopy
  · rw [hmark, hm]
  · simpa using walkStep_fresh_red n 0 0 (x, y) (x, y)

private theorem bind3_cont
    (m1 : Except SudoRt.Trap Ecbs.Board)
    (m2 m3 : Ecbs.Board → Except SudoRt.Trap Ecbs.Board) :
    (m1 >>= fun a => m2 a >>= fun b => m3 b >>= fun c =>
        pure (SudoRt.Flow.cont (ρ := (Bool × Bool) × Ecbs.Board) (c, true))) =
      ((m1 >>= fun a => m2 a >>= fun b => m3 b) >>= fun c =>
        pure (SudoRt.Flow.cont (ρ := (Bool × Bool) × Ecbs.Board) (c, true))) := by
  cases m1 with
  | error _ =>
    simp [ok_bind]
    rfl
  | ok a =>
    simp only [ok_bind]
    cases h2 : m2 a with
    | error _ =>
      simp [ok_bind]
      rfl
    | ok b =>
      simp [ok_bind, pure_eq_ok]

/-- One white cell. `walk_chord` turns the script marker on, runs that cell,
    then lifts a marker that is already up and turns the marker off.
    The result is live and ok, and across / up hold the base point. -/
theorem walk_chord_white_one (b : Ecbs.Board) (x y : List Nat)
    (n moves peak marker ctrl : Nat)
    (hszH : b.sudo_5Board_4home.size = 8) (hszD : b.sudo_5Board_4held.size = 8)
    (hx : x.length = n) (hy : y.length = n)
    (hf : FitsLen n)
    (hfitx : FitsLen (moves + pegCount x))
    (hfity : FitsLen (moves + pegCount x + pegCount y))
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hm : b.sudo_5Board_6marker = Int.ofNat marker)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hfitc : FitsLen (ctrl + 1))
    (h0 : b.sudo_5Board_4held[0]'(by rw [hszD]; decide) = false)
    (h1 : b.sudo_5Board_4held[1]'(by rw [hszD]; decide) = false)
    (h3t : b.sudo_5Board_4held[3]'(by rw [hszD]; decide) = true)
    (h3a : b.sudo_5Board_4home[3]'(by rw [hszH]; decide) = embed x)
    (h4t : b.sudo_5Board_4held[4]'(by rw [hszD]; decide) = true)
    (h4a : b.sudo_5Board_4home[4]'(by rw [hszH]; decide) = embed y) :
    ∃ bF,
      Ecbs.walk_chord b (embed [1]) = .ok ((true, true), bF) ∧
      (∀ (h : 0 < bF.sudo_5Board_4home.size), bF.sudo_5Board_4home[0] = embed x) ∧
      (∀ (h : 1 < bF.sudo_5Board_4home.size), bF.sudo_5Board_4home[1] = embed y) ∧
      bF.sudo_5Board_9marker_on = false := by
  let b0 : Ecbs.Board := { b with sudo_5Board_9marker_on := true }
  have hm0 : b0.sudo_5Board_6marker = Int.ofNat marker := by simp [b0, hm]
  have hc0 : b0.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl := by simp [b0, hc]
  have hn0 : b0.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by simp [b0, hn]
  have hmoves0 : b0.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int) := by simp [b0, hmoves]
  have hpeak0 : b0.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int) := by simp [b0, hpeak]
  have hszH0 : b0.sudo_5Board_4home.size = 8 := by simp [b0, hszH]
  have hszD0 : b0.sudo_5Board_4held.size = 8 := by simp [b0, hszD]
  have h00 : b0.sudo_5Board_4held[0]'(by rw [hszD0]; decide) = false := by simpa [b0] using h0
  have h10 : b0.sudo_5Board_4held[1]'(by rw [hszD0]; decide) = false := by simpa [b0] using h1
  have h3t0 : b0.sudo_5Board_4held[3]'(by rw [hszD0]; decide) = true := by simpa [b0] using h3t
  have h3a0 : b0.sudo_5Board_4home[3]'(by rw [hszH0]; decide) = embed x := by simpa [b0] using h3a
  have h4t0 : b0.sudo_5Board_4held[4]'(by rw [hszD0]; decide) = true := by simpa [b0] using h4t
  have h4a0 : b0.sudo_5Board_4home[4]'(by rw [hszH0]; decide) = embed y := by simpa [b0] using h4a
  obtain ⟨b2, mv2, pk2, hcell, hx0, hy1, hmv, hpk, hsum, hmark, _⟩ :=
    chord_fresh_white b0 x y n moves peak marker ctrl hszH0 hszD0 hx hy hf hfitx hfity
      hn0 hmoves0 hpeak0 hm0 hc0 hfitc h00 h10 h3t0 h3a0 h4t0 h4a0
  unfold Ecbs.walk_chord
  dsimp only
  rw [listLen_embed]
  have hlen1 : (([1] : List Nat).length) = 1 := rfl
  rw [hlen1, subI_ofNat_one 1 (by decide) (fits_small (by decide)), ok_bind]
  rw [show (0 : Int) = Int.ofNat 0 from rfl, fuelRange_eq]
  have hfuel : fuelRange (Int.ofNat 0) (Int.ofNat 0) = 0 + 1 := by
    rw [fuelRange_le (Nat.zero_le _)]
  rw [hfuel, runLoopOn_succ]
  dsimp only [Prod.fst, Prod.snd]
  rw [if_neg (show ¬ (Int.ofNat 0 > Int.ofNat (1 - 1)) from by decide)]
  rw [atL_embed [1] 0 (by decide), ok_bind]
  simp only [List.getElem_cons_zero]
  have hge : decide (Int.ofNat 1 ≥ Int.ofNat 0) = true := by decide
  have hle : decide (Int.ofNat 1 ≤ (2 : Int)) = true := by decide
  rw [hge, if_pos rfl, hle, pure_eq_ok, ok_bind, sudoAssert_true, ok_bind]
  have hff : ((false : Bool) = true) = False := by decide
  simp only [hff, if_false]
  rw [sEq_ofNat 1 0]
  have hz : decide ((1 : Nat) = 0) = false := by decide
  rw [hz]
  simp only [Bool.not_false, if_true]
  rw [show (2 : Int) = Int.ofNat 2 from rfl, sEq_ofNat 1 2]
  have h12 : decide ((1 : Nat) = 2) = false := by decide
  rw [h12]
  have hbody :
      (do
        let board ← Ecbs.marker_lift b0
        let board ← Ecbs.copy_band board Ecbs.across Ecbs.base_across false
        let board ← Ecbs.copy_band board Ecbs.up Ecbs.base_up false
        pure (SudoRt.Flow.cont (ρ := (Bool × Bool) × Ecbs.Board) (board, true))) =
      (pure (SudoRt.Flow.cont (ρ := (Bool × Bool) × Ecbs.Board) (b2, true)) :
        Except SudoRt.Trap (SudoRt.Flow (Ecbs.Board × Bool) ((Bool × Bool) × Ecbs.Board))) := by
    rw [bind3_cont, hcell, ok_bind, pure_eq_ok]
  rw [hbody, pure_eq_ok, ok_bind]
  have heq : (Int.ofNat 0 == Int.ofNat (1 - 1)) = true := by
    rw [show (1 - 1 : Nat) = 0 from rfl, beq_int_iff]
  rw [heq]
  simp only [if_true, pure_eq_ok]
  rw [marker_lift_down b2 hmark, ok_bind, ok_bind]
  refine ⟨{ b2 with sudo_5Board_9marker_on := false }, rfl, ?_, ?_, rfl⟩
  · intro h
    simpa using hx0 _
  · intro h
    simpa using hy1 _

end EcbsLink2.Link2
