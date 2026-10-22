/-
  `walk_chord` on the board a key walk actually starts from: the base point
  in homes 3 and 4, marker still `-1`. An empty key leaves the homes.
  A key whose only nonzero cell is the last one copies that base point
  (negated up when the cell is red) and stops. A later live cell is still
  to be joined. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.OpenBoard
import EcbsLink2.Link2.WalkPrefix
import EcbsLink2.Link2.ChordAt

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

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
  exact walk_chord_at_zeros (baseBoard t x y) t x y (pegCount x + pegCount y) 2
    cells acc (base_chordAt t x y) hfit hz

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
  exact walk_chord_at_white (baseBoard t x y) t x y (pegCount x + pegCount y) 2
    zs acc (base_chordAt t x y) hx hy hz (len_fit t hsh) hfitx hfity hfit

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
  exact walk_chord_at_red (baseBoard t x y) t x y (pegCount x + pegCount y) 2
    zs acc (base_chordAt t x y) hx hy hOk.n_pos htriY hz (len_fit t hsh) hfitx hfity hfit

end EcbsLink2.Link2
