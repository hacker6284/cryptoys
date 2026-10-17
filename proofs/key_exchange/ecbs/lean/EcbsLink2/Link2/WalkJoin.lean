/-
  `walk_chord` on the board a key walk actually starts from: the base point
  in homes 3 and 4, marker still `-1`. An empty key leaves the homes.
  A key whose only nonzero cell is the last one copies that base point
  (negated up when the cell is red) and stops. A later live cell is still
  to be joined. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.OpenBoard
import EcbsLink2.Link2.WalkPrefix

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

private theorem base_marker (t : Spec.Tier) (x y : List Nat) :
    (baseBoard t x y).sudo_5Board_6marker = -1 := by
  simp [baseBoard, putAcross, built_marker_down]

private theorem base_moves (t : Spec.Tier) (x y : List Nat) :
    (baseBoard t x y).sudo_5Board_4cost.sudo_5Costs_5moves =
      (pegCount x + pegCount y : Int) := by
  simp [baseBoard, ofNat_eq_natCast]

private theorem base_peak (t : Spec.Tier) (x y : List Nat) :
    (baseBoard t x y).sudo_5Board_4cost.sudo_5Costs_4peak = (2 : Int) := by
  simp [baseBoard, ofNat_eq_natCast]

private theorem base_tier_n (t : Spec.Tier) (x y : List Nat) :
    (baseBoard t x y).sudo_5Board_1t.sudo_4Tier_1n = (t.n : Int) := by
  simp [baseBoard, putAcross, built_tier_eq, embTier, ofNat_eq_natCast]

private theorem base_held0_false (t : Spec.Tier) (x y : List Nat) :
    (baseBoard t x y).sudo_5Board_4held[0]'(by rw [base_szD]; decide) = false := by
  simp [baseBoard, putAcross, Array.getElem_set, built_held_arr, Array.getElem_mkArray]

private theorem base_held1_false (t : Spec.Tier) (x y : List Nat) :
    (baseBoard t x y).sudo_5Board_4held[1]'(by rw [base_szD]; decide) = false := by
  simp [baseBoard, putAcross, Array.getElem_set, built_held_arr, Array.getElem_mkArray]

private theorem base_held3_true (t : Spec.Tier) (x y : List Nat) :
    (baseBoard t x y).sudo_5Board_4held[3]'(by rw [base_szD]; decide) = true := by
  simp [baseBoard, putAcross, Array.getElem_set, built_held_arr, Array.getElem_mkArray]

private theorem base_held4_true (t : Spec.Tier) (x y : List Nat) :
    (baseBoard t x y).sudo_5Board_4held[4]'(by rw [base_szD]; decide) = true := by
  simp [baseBoard, putAcross, Array.getElem_set]

private theorem base_home3 (t : Spec.Tier) (x y : List Nat) :
    (baseBoard t x y).sudo_5Board_4home[3]'(by rw [base_szH]; decide) = embed x := by
  simp [baseBoard, putAcross, Array.getElem_set]

private theorem base_home4 (t : Spec.Tier) (x y : List Nat) :
    (baseBoard t x y).sudo_5Board_4home[4]'(by rw [base_szH]; decide) = embed y := by
  simp [baseBoard, putAcross, Array.getElem_set]

private theorem cells_fit (t : Spec.Tier) (tw : TierWalk t) : FitsLen t.cells := by
  apply FitsLen.of_le tw.roomO
  have hpos : 0 < cellOpsCharge t := by
    unfold cellOpsCharge
    omega
  have hmul : t.cells ≤ t.cells * cellOpsCharge t :=
    Nat.le_mul_of_pos_right t.cells hpos
  calc
    t.cells ≤ t.cells * cellOpsCharge t := hmul
    _ ≤ t.cells * cellOpsCharge t + cellOpsCharge t := Nat.le_add_right _ _
    _ = (t.cells + 1) * cellOpsCharge t := by rw [Nat.succ_mul]

private theorem len_fit (t : Spec.Tier) (hsh : TierShape t) : FitsLen t.n := by
  apply geomFit t.n t.benchlen t.n hsh.n_small hsh.small.2.2.2
  omega

private theorem copy_fit (t : Spec.Tier) (x y : List Nat) (hsh : TierShape t)
    (hx : x.length = t.n) (hy : y.length = t.n) :
    FitsLen (pegCount x + pegCount y + pegCount x) ∧
      FitsLen (pegCount x + pegCount y + pegCount x + pegCount y) := by
  have hpx : pegCount x ≤ t.n := by rw [← hx]; exact pegCount_le x
  have hpy : pegCount y ≤ t.n := by rw [← hy]; exact pegCount_le y
  refine ⟨?_, ?_⟩
  · apply geomFit t.n t.benchlen _ hsh.n_small hsh.small.2.2.2
    omega
  · apply geomFit t.n t.benchlen _ hsh.n_small hsh.small.2.2.2
    omega

/-- Every cell empty. The homes stay, and the result is not live. -/
theorem walk_chord_base_zeros (t : Spec.Tier) (x y : List Nat) (cells : List Nat)
    (tw : TierWalk t) (acc : List Nat × List Nat)
    (hlen : cells.length = t.cells) (hz : ∀ c ∈ cells, c = 0) :
    Ecbs.walk_chord (baseBoard t x y) (embed cells) =
        .ok ((false, true),
          { baseBoard t x y with sudo_5Board_9marker_on := false }) ∧
      walkRun t.n t.k t.benchlen (x, y) false acc cells = some (false, acc) := by
  have hfit : FitsLen cells.length := by rw [hlen]; exact cells_fit t tw
  obtain ⟨hch, hrun, _⟩ :=
    walk_chord_zeros_down (baseBoard t x y) cells t.n t.k t.benchlen (x, y) acc
      hz (base_marker t x y) hfit
  exact ⟨hch, hrun⟩

/-- Empty cells, then one white cell, and that cell ends the key.
    Across and up become the base point. -/
theorem walk_chord_base_white (t : Spec.Tier) (x y : List Nat) (zs : List Nat)
    (tw : TierWalk t) (hsh : TierShape t) (acc : List Nat × List Nat)
    (hx : x.length = t.n) (hy : y.length = t.n)
    (hz : ∀ c ∈ zs, c = 0) (hlen : (zs ++ [1]).length = t.cells) :
    ∃ b',
      Ecbs.walk_chord (baseBoard t x y) (embed (zs ++ [1])) =
        .ok ((true, true), b') ∧
      (∀ h : 0 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[0] = embed x) ∧
      (∀ h : 1 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[1] = embed y) ∧
      walkRun t.n t.k t.benchlen (x, y) false acc (zs ++ [1]) =
        some (true, (x, y)) := by
  obtain ⟨hfitx, hfity⟩ := copy_fit t x y hsh hx hy
  have hfit : FitsLen (zs.length + 1) := by
    have hlen' : zs.length + 1 = t.cells := by simpa [List.length_append] using hlen
    rw [hlen']
    exact cells_fit t tw
  obtain ⟨b2, hch, hx0, hy1, _hm, _hst, _hho, _hc, _hs, hrun, _⟩ :=
    walk_chord_white_down (baseBoard t x y) zs x y t.n t.k t.benchlen
      (pegCount x + pegCount y) 2 acc hz (base_szH t x y) (base_szD t x y)
      hx hy (len_fit t hsh) hfitx hfity (base_tier_n t x y) (base_moves t x y)
      (base_peak t x y) (base_marker t x y) hfit
      (base_held0_false t x y) (base_held1_false t x y)
      (base_held3_true t x y) (base_home3 t x y)
      (base_held4_true t x y) (base_home4 t x y)
  refine ⟨{ b2 with sudo_5Board_9marker_on := false }, hch, ?_, ?_, hrun⟩
  · simpa using hx0
  · simpa using hy1

/-- Empty cells, then one red cell, and that cell ends the key.
    Up is the negated base up. -/
theorem walk_chord_base_red (t : Spec.Tier) (x y : List Nat) (zs : List Nat)
    (tw : TierWalk t) (hOk : BoardOk t) (hsh : TierShape t)
    (acc : List Nat × List Nat)
    (hx : x.length = t.n) (hy : y.length = t.n) (htriY : allTritList y)
    (hz : ∀ c ∈ zs, c = 0) (hlen : (zs ++ [2]).length = t.cells) :
    ∃ b',
      Ecbs.walk_chord (baseBoard t x y) (embed (zs ++ [2])) =
        .ok ((true, true), b') ∧
      (∀ h : 0 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[0] = embed x) ∧
      (∀ h : 1 < b'.sudo_5Board_4home.size,
        b'.sudo_5Board_4home[1] = embed (mirrorTrits y)) ∧
      walkRun t.n t.k t.benchlen (x, y) false acc (zs ++ [2]) =
        some (true, (x, mirrorTrits y)) := by
  obtain ⟨hfitx, hfity⟩ := copy_fit t x y hsh hx hy
  have hfit : FitsLen (zs.length + 1) := by
    have hlen' : zs.length + 1 = t.cells := by simpa [List.length_append] using hlen
    rw [hlen']
    exact cells_fit t tw
  obtain ⟨b2, hch, hx0, hy1, _hm, _hst, _hho, _hc, _hs, hrun, _⟩ :=
    walk_chord_red_down (baseBoard t x y) zs x y t.n t.k t.benchlen
      (pegCount x + pegCount y) 2 acc hz (base_szH t x y) (base_szD t x y)
      hx hy hOk.n_pos htriY (len_fit t hsh) hfitx hfity (base_tier_n t x y)
      (base_moves t x y) (base_peak t x y) (base_marker t x y) hfit
      (base_held0_false t x y) (base_held1_false t x y)
      (base_held3_true t x y) (base_home3 t x y)
      (base_held4_true t x y) (base_home4 t x y)
  refine ⟨{ b2 with sudo_5Board_9marker_on := false }, hch, ?_, ?_, hrun⟩
  · simpa using hx0
  · simpa using hy1

end EcbsLink2.Link2
