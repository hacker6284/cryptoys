/-
  `start_walk`: the two opening copies, then a white peg in the bottom.
  Across receives the base across. Up receives the base up, or its negation
  when the cell is red. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.CopyKeep
import EcbsLink2.Link2.FformOpen

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

private theorem put_home_ne (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size)
    (hD : home < b.sudo_5Board_4held.size)
    (n moves j : Nat) (hne : home ≠ j)
    (hj : j < b.sudo_5Board_4home.size) :
    (whitePut b home hH hD n moves).sudo_5Board_4home[j]'(by
      simp [whitePut, Array.size_set]; exact hj) =
      b.sudo_5Board_4home[j] := by
  simp [whitePut, Array.getElem_set_ne, hne]

private theorem put_home_at (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size)
    (hD : home < b.sudo_5Board_4held.size)
    (n moves : Nat) :
    (whitePut b home hH hD n moves).sudo_5Board_4home[home]'(by
      simp [whitePut, Array.size_set]; exact hH) =
      embed (whiteHole0 n) := by
  simp [whitePut, Array.getElem_set_eq]

private theorem put_held_at (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size)
    (hD : home < b.sudo_5Board_4held.size)
    (n moves : Nat) :
    (whitePut b home hH hD n moves).sudo_5Board_4held[home]'(by
      simp [whitePut, Array.size_set]; exact hD) = true := by
  simp [whitePut, Array.getElem_set_eq]

private theorem tier_n_of (t : Spec.Tier) (b : Ecbs.Board)
    (h : b.sudo_5Board_1t = embTier t) :
    b.sudo_5Board_1t.sudo_4Tier_1n = (t.n : Int) := by
  rw [h]
  simp [embTier]

private theorem finish_walk (t : Spec.Tier) (b2 : Ecbs.Board)
    (x y1 y4 : List Nat) (mv2 pk2 : Nat)
    (out : OutLay t b2 x y1 y4 mv2 pk2)
    (hpos : 0 < t.n) (hf : FitsLen t.n) (hfit1 : FitsLen (mv2 + 1)) :
    Ecbs.white0 b2 Ecbs.bottom =
      .ok (peakBoard
        (whitePut b2 2 (by rw [out.szH]; decide) (by rw [out.szD]; decide) t.n mv2)
        pk2) := by
  have h2H : 2 < b2.sudo_5Board_4home.size := by rw [out.szH]; decide
  have h2D : 2 < b2.sudo_5Board_4held.size := by rw [out.szD]; decide
  have hwhite := white0_fresh b2 2 t.n mv2 pk2 h2H h2D out.held2 out.bench
    (tier_n_of t b2 out.tier) hpos out.moves
    (by simpa [ofNat_eq_natCast] using out.peak)
    (by rw [out.szD]; decide) hf hfit1
  simpa [show Ecbs.bottom = ((2 : Nat) : Int) from rfl] using hwhite

/-- White opening. Across and up are the base point, and the bottom is a
    white peg in hole 0. -/
theorem start_walk_white (t : Spec.Tier) (b : Ecbs.Board) (x y : List Nat)
    (mv pk : Nat) (lay : InLay t b x y mv pk)
    (hx : x.length = t.n) (hy : y.length = t.n)
    (hpos : 0 < t.n) (hf : FitsLen t.n)
    (hfitx : FitsLen (mv + pegCount x))
    (hfity : FitsLen (mv + pegCount x + pegCount y))
    (hfit1 : FitsLen (mv + pegCount x + pegCount y + 1)) :
    ∃ bW,
      Ecbs.start_walk b false = .ok bW ∧
      (∀ h0 : 0 < bW.sudo_5Board_4home.size, bW.sudo_5Board_4home[0] = embed x) ∧
      (∀ h1 : 1 < bW.sudo_5Board_4home.size, bW.sudo_5Board_4home[1] = embed y) ∧
      (∀ h2 : 2 < bW.sudo_5Board_4home.size,
        bW.sudo_5Board_4home[2] = embed (whiteHole0 t.n)) ∧
      (∀ h3 : 3 < bW.sudo_5Board_4home.size, bW.sudo_5Board_4home[3] = embed x) ∧
      (∀ h4 : 4 < bW.sudo_5Board_4home.size, bW.sudo_5Board_4home[4] = embed y) ∧
      (∀ h2 : 2 < bW.sudo_5Board_4held.size, bW.sudo_5Board_4held[2] = true) ∧
      bW.sudo_5Board_8bench_on = false ∧
      bW.sudo_5Board_9marker_on = true ∧
      bW.sudo_5Board_1t = embTier t ∧
      bW.sudo_5Board_4cost.sudo_5Costs_5moves =
        Int.ofNat (mv + pegCount x + pegCount y + 1) := by
  let mv2 := mv + pegCount x + pegCount y
  obtain ⟨b2, pk2, hcopy, out⟩ :=
    white_copy_kept t b x y mv pk lay hx hy hf hfitx hfity
  have hplant := finish_walk t b2 x y y mv2 pk2 out hpos hf hfit1
  refine ⟨peakBoard (whitePut b2 2 (by rw [out.szH]; decide)
      (by rw [out.szD]; decide) t.n mv2) pk2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Ecbs.start_walk
    conv => lhs; zeta
    rw [← bind_assoc, hcopy, ok_bind, hplant, ok_bind, pure_eq_ok]
  · intro _
    simp only [peakBoard]
    have hget := put_home_ne b2 2 (by rw [out.szH]; decide) (by rw [out.szD]; decide)
      t.n mv2 0 (by decide) (by rw [out.szH]; decide)
    simpa using hget.trans out.home0
  · intro _
    simp only [peakBoard]
    have hget := put_home_ne b2 2 (by rw [out.szH]; decide) (by rw [out.szD]; decide)
      t.n mv2 1 (by decide) (by rw [out.szH]; decide)
    simpa using hget.trans out.home1
  · intro _
    simp only [peakBoard]
    simpa using put_home_at b2 2 (by rw [out.szH]; decide) (by rw [out.szD]; decide) t.n mv2
  · intro _
    simp only [peakBoard]
    have hget := put_home_ne b2 2 (by rw [out.szH]; decide) (by rw [out.szD]; decide)
      t.n mv2 3 (by decide) (by rw [out.szH]; decide)
    simpa using hget.trans out.home3
  · intro _
    simp only [peakBoard]
    have hget := put_home_ne b2 2 (by rw [out.szH]; decide) (by rw [out.szD]; decide)
      t.n mv2 4 (by decide) (by rw [out.szH]; decide)
    simpa using hget.trans out.home4
  · intro _
    simp only [peakBoard]
    simpa using put_held_at b2 2 (by rw [out.szH]; decide) (by rw [out.szD]; decide) t.n mv2
  · simp only [peakBoard, whitePut, out.bench]
  · simp only [peakBoard, whitePut, out.flag]
  · simp only [peakBoard, whitePut, out.tier]
  · simp only [peakBoard, whitePut]

/-- Red opening. Up is the negated base up. The bottom is the same white peg. -/
theorem start_walk_red (t : Spec.Tier) (b : Ecbs.Board) (x y : List Nat)
    (mv pk : Nat) (lay : InLay t b x y mv pk)
    (hx : x.length = t.n) (hy : y.length = t.n)
    (hpos : 0 < t.n) (hyt : allTritList y) (hf : FitsLen t.n)
    (hfitx : FitsLen (mv + pegCount x))
    (hfity : FitsLen (mv + pegCount x + pegCount y))
    (hfit1 : FitsLen (mv + pegCount x + pegCount y + 1)) :
    ∃ bW,
      Ecbs.start_walk b true = .ok bW ∧
      (∀ h0 : 0 < bW.sudo_5Board_4home.size, bW.sudo_5Board_4home[0] = embed x) ∧
      (∀ h1 : 1 < bW.sudo_5Board_4home.size,
        bW.sudo_5Board_4home[1] = embed (mirrorTrits y)) ∧
      (∀ h2 : 2 < bW.sudo_5Board_4home.size,
        bW.sudo_5Board_4home[2] = embed (whiteHole0 t.n)) ∧
      (∀ h3 : 3 < bW.sudo_5Board_4home.size, bW.sudo_5Board_4home[3] = embed x) ∧
      (∀ h4 : 4 < bW.sudo_5Board_4home.size, bW.sudo_5Board_4home[4] = embed y) ∧
      (∀ h2 : 2 < bW.sudo_5Board_4held.size, bW.sudo_5Board_4held[2] = true) ∧
      bW.sudo_5Board_8bench_on = false ∧
      bW.sudo_5Board_9marker_on = true ∧
      bW.sudo_5Board_1t = embTier t ∧
      bW.sudo_5Board_4cost.sudo_5Costs_5moves =
        Int.ofNat (mv + pegCount x + pegCount y + 1) := by
  let mv2 := mv + pegCount x + pegCount y
  obtain ⟨b2, pk2, hcopy, out⟩ :=
    red_copy_kept t b x y mv pk lay hx hy hpos hyt hf hfitx hfity
  have hplant := finish_walk t b2 x (mirrorTrits y) y mv2 pk2 out hpos hf hfit1
  refine ⟨peakBoard (whitePut b2 2 (by rw [out.szH]; decide)
      (by rw [out.szD]; decide) t.n mv2) pk2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Ecbs.start_walk
    conv => lhs; zeta
    rw [← bind_assoc, hcopy, ok_bind, hplant, ok_bind, pure_eq_ok]
  · intro _
    simp only [peakBoard]
    have hget := put_home_ne b2 2 (by rw [out.szH]; decide) (by rw [out.szD]; decide)
      t.n mv2 0 (by decide) (by rw [out.szH]; decide)
    simpa using hget.trans out.home0
  · intro _
    simp only [peakBoard]
    have hget := put_home_ne b2 2 (by rw [out.szH]; decide) (by rw [out.szD]; decide)
      t.n mv2 1 (by decide) (by rw [out.szH]; decide)
    simpa using hget.trans out.home1
  · intro _
    simp only [peakBoard]
    simpa using put_home_at b2 2 (by rw [out.szH]; decide) (by rw [out.szD]; decide) t.n mv2
  · intro _
    simp only [peakBoard]
    have hget := put_home_ne b2 2 (by rw [out.szH]; decide) (by rw [out.szD]; decide)
      t.n mv2 3 (by decide) (by rw [out.szH]; decide)
    simpa using hget.trans out.home3
  · intro _
    simp only [peakBoard]
    have hget := put_home_ne b2 2 (by rw [out.szH]; decide) (by rw [out.szD]; decide)
      t.n mv2 4 (by decide) (by rw [out.szH]; decide)
    simpa using hget.trans out.home4
  · intro _
    simp only [peakBoard]
    simpa using put_held_at b2 2 (by rw [out.szH]; decide) (by rw [out.szD]; decide) t.n mv2
  · simp only [peakBoard, whitePut, out.bench]
  · simp only [peakBoard, whitePut, out.flag]
  · simp only [peakBoard, whitePut, out.tier]
  · simp only [peakBoard, whitePut]

private theorem plant_ops (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size)
    (hD : home < b.sudo_5Board_4held.size)
    (n moves pk : Nat) :
    (peakBoard (whitePut b home hH hD n moves) pk).sudo_5Board_4cost.sudo_5Costs_3ops =
      b.sudo_5Board_4cost.sudo_5Costs_3ops := by
  simp [peakBoard, whitePut]

private theorem zero_ops0 :
    (Array.mkArray 5 (0 : Int))[0]? = some (Int.ofNat 0) := by
  have h0 : 0 < (Array.mkArray 5 (0 : Int)).size := by simp [Array.size_mkArray]
  rw [Array.getElem?_eq_getElem h0]
  simp [Array.getElem_mkArray]

/-- `start_walk` copies the base point and plants the bottom peg. Neither
    write touches the ops array, so slot 0 stays the zero the fresh board
    was given. -/
theorem start_walk_ops0 (t : Spec.Tier) (b : Ecbs.Board) (x y : List Nat)
    (mv pk : Nat) (lay : InLay t b x y mv pk) (red : Bool)
    (hx : x.length = t.n) (hy : y.length = t.n)
    (hpos : 0 < t.n) (hyt : allTritList y) (hf : FitsLen t.n)
    (hfitx : FitsLen (mv + pegCount x))
    (hfity : FitsLen (mv + pegCount x + pegCount y))
    (hfit1 : FitsLen (mv + pegCount x + pegCount y + 1)) :
    ∃ bW, Ecbs.start_walk b red = .ok bW ∧
      bW.sudo_5Board_4cost.sudo_5Costs_3ops[0]? = some (Int.ofNat 0) := by
  let mv2 := mv + pegCount x + pegCount y
  cases red
  · obtain ⟨b2, pk2, hcopy, out⟩ :=
      white_copy_kept t b x y mv pk lay hx hy hf hfitx hfity
    let bW := peakBoard (whitePut b2 2 (by rw [out.szH]; decide)
      (by rw [out.szD]; decide) t.n mv2) pk2
    have hplant := finish_walk t b2 x y y mv2 pk2 out hpos hf hfit1
    refine ⟨bW, ?_, ?_⟩
    · unfold Ecbs.start_walk
      conv => lhs; zeta
      rw [← bind_assoc, hcopy, ok_bind, hplant, ok_bind, pure_eq_ok]
    · have hops := plant_ops b2 2 (by rw [out.szH]; decide) (by rw [out.szD]; decide)
        t.n mv2 pk2
      rw [show bW.sudo_5Board_4cost.sudo_5Costs_3ops =
          (peakBoard (whitePut b2 2 (by rw [out.szH]; decide)
            (by rw [out.szD]; decide) t.n mv2) pk2).sudo_5Board_4cost.sudo_5Costs_3ops from rfl,
        hops, out.ops]
      exact zero_ops0
  · obtain ⟨b2, pk2, hcopy, out⟩ :=
      red_copy_kept t b x y mv pk lay hx hy hpos hyt hf hfitx hfity
    let bW := peakBoard (whitePut b2 2 (by rw [out.szH]; decide)
      (by rw [out.szD]; decide) t.n mv2) pk2
    have hplant := finish_walk t b2 x (mirrorTrits y) y mv2 pk2 out hpos hf hfit1
    refine ⟨bW, ?_, ?_⟩
    · unfold Ecbs.start_walk
      conv => lhs; zeta
      rw [← bind_assoc, hcopy, ok_bind, hplant, ok_bind, pure_eq_ok]
    · have hops := plant_ops b2 2 (by rw [out.szH]; decide) (by rw [out.szD]; decide)
        t.n mv2 pk2
      rw [show bW.sudo_5Board_4cost.sudo_5Costs_3ops =
          (peakBoard (whitePut b2 2 (by rw [out.szH]; decide)
            (by rw [out.szD]; decide) t.n mv2) pk2).sudo_5Board_4cost.sudo_5Costs_3ops from rfl,
        hops, out.ops]
      exact zero_ops0

theorem demo_mul_cells : 13 * demo.cells = 26 := rfl
theorem toy_mul_cells : 13 * toy.cells = 208 := rfl
theorem hobby_mul_cells : 13 * hobby.cells = 663 := rfl
theorem serious_mul_cells : 13 * serious.cells = 2106 := rfl

private theorem ble_le (a b : Nat) (h : Nat.ble a b = true) : a ≤ b :=
  Nat.le_of_ble_eq_true h

theorem demo_mul_fit : FitsLen (13 * demo.cells) := by
  rw [demo_mul_cells]
  unfold FitsLen i64MaxNat
  exact ble_le _ _ rfl

theorem toy_mul_fit : FitsLen (13 * toy.cells) := by
  rw [toy_mul_cells]
  unfold FitsLen i64MaxNat
  exact ble_le _ _ rfl

theorem hobby_mul_fit : FitsLen (13 * hobby.cells) := by
  rw [hobby_mul_cells]
  unfold FitsLen i64MaxNat
  exact ble_le _ _ rfl

theorem serious_mul_fit : FitsLen (13 * serious.cells) := by
  rw [serious_mul_cells]
  unfold FitsLen i64MaxNat
  exact ble_le _ _ rfl

/-- The opening counter is 0, and every shipped tier leaves room for 13
    multiplies in each cell of the key. -/
theorem start_walk_mul_room (t : Spec.Tier)
    (h : t = demo ∨ t = toy ∨ t = hobby ∨ t = serious) :
    FitsLen (0 + 13 * (t.cells - 0)) := by
  rcases h with rfl | rfl | rfl | rfl
  · simpa using demo_mul_fit
  · simpa using toy_mul_fit
  · simpa using hobby_mul_fit
  · simpa using serious_mul_fit

theorem demo_cube_cells : 3 * demo.cells = 6 := rfl
theorem toy_cube_cells : 3 * toy.cells = 48 := rfl
theorem hobby_cube_cells : 3 * hobby.cells = 153 := rfl
theorem serious_cube_cells : 3 * serious.cells = 486 := rfl

theorem demo_cube_fit : FitsLen (3 * demo.cells) := by
  rw [demo_cube_cells]
  unfold FitsLen i64MaxNat
  exact ble_le _ _ rfl

theorem toy_cube_fit : FitsLen (3 * toy.cells) := by
  rw [toy_cube_cells]
  unfold FitsLen i64MaxNat
  exact ble_le _ _ rfl

theorem hobby_cube_fit : FitsLen (3 * hobby.cells) := by
  rw [hobby_cube_cells]
  unfold FitsLen i64MaxNat
  exact ble_le _ _ rfl

theorem serious_cube_fit : FitsLen (3 * serious.cells) := by
  rw [serious_cube_cells]
  unfold FitsLen i64MaxNat
  exact ble_le _ _ rfl

/-- The opening cube counter is 0, and every shipped tier leaves room for
    three cubes in each cell of the key. -/
theorem start_walk_cube_room (t : Spec.Tier)
    (h : t = demo ∨ t = toy ∨ t = hobby ∨ t = serious) :
    FitsLen (0 + 3 * (t.cells - 0)) := by
  rcases h with rfl | rfl | rfl | rfl
  · simpa using demo_cube_fit
  · simpa using toy_cube_fit
  · simpa using hobby_cube_fit
  · simpa using serious_cube_fit

end EcbsLink2.Link2
