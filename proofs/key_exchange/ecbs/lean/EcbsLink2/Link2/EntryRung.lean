/-
  At climb entry the control row still holds `rungList` in build order.
  The gap copy does not write that row. `tally_start` writes a white peg at
  the origin, which sits strictly after the ladder, so every climb hole keeps
  its colour. Climb order is that list reversed: the first hole `climb_holes`
  visits is the head of the pending list, and it is not empty.
-/
import EcbsLink2.Link2.InvertTie

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- Build-order rungs painted from `ladder0 = script + 2`. -/
def paintedRow (t : Spec.Tier) : List Nat :=
  paint (List.replicate t.control 0) (t.script + 2) (rungList (t.n - 1))

/-- The same row after the first tally peg. -/
def entryRow (t : Spec.Tier) : List Nat :=
  (paintedRow t).set (tallyOrigin t) 1

theorem painted_len (t : Spec.Tier) : (paintedRow t).length = t.control := by
  unfold paintedRow
  rw [paintRow_length, List.length_replicate]

def climbIx (t : Spec.Tier) (k : Nat) : Nat :=
  t.script + 2 + tierR t - 1 - k

theorem climb_ix_lt (t : Spec.Tier) (h : BoardOk t) (k : Nat) (hk : k < tierR t) :
    climbIx t k < (paintedRow t).length := by
  rw [painted_len]
  unfold climbIx
  unfold tierR at hk ⊢
  have hL := h.ladder
  omega

theorem climb_before_origin (t : Spec.Tier) (k : Nat) (hk : k < tierR t) :
    climbIx t k ≠ tallyOrigin t := by
  unfold climbIx
  unfold tallyOrigin
  unfold tierR at hk ⊢
  omega

theorem climb_head_ix (t : Spec.Tier) :
    climbAt (t.script + 2) (tierR t) 0 = climbIx t 0 := by
  unfold climbAt climbIx
  omega

/-- Hole `k` in climb order is build-order rung `R - 1 - k`, before the tally peg. -/
theorem painted_colour (t : Spec.Tier) (h : BoardOk t) (k : Nat) (hk : k < tierR t) :
    (paintedRow t)[climbIx t k]'(climb_ix_lt t h k hk) =
      (tierClimb t)[k]'(by
        unfold tierClimb
        rw [List.length_reverse]
        simpa [tierR] using hk) := by
  unfold tierClimb
  have hj : (rungList (t.n - 1)).length - 1 - k < (rungList (t.n - 1)).length := by
    unfold tierR at hk
    omega
  rw [List.getElem_reverse]
  have hidx :
      (rungList (t.n - 1))[(rungList (t.n - 1)).length - 1 - k]'(by
        unfold tierR at hk; omega) =
      (rungList (t.n - 1))[tierR t - 1 - k]'(by
        unfold tierR at hk ⊢; omega) := by
    unfold tierR
    rfl
  rw [hidx]
  have hstart : climbIx t k = t.script + 2 + (tierR t - 1 - k) := by
    have hnum : t.script + 2 + tierR t - 1 - k = t.script + 2 + (tierR t - 1 - k) := by
      unfold tierR at hk ⊢
      omega
    unfold climbIx
    exact hnum
  have hpaint := paintRow_at (List.replicate t.control 0) (t.script + 2)
      (rungList (t.n - 1))
      (by rw [List.length_replicate]; simpa [tierR] using h.ladder)
      (tierR t - 1 - k) (by unfold tierR at hk ⊢; omega)
  rw [rowGet_idx hstart (climb_ix_lt t h k hk)]
  unfold paintedRow
  exact hpaint

theorem entry_ix_lt (t : Spec.Tier) (h : BoardOk t) (k : Nat) (hk : k < tierR t) :
    climbIx t k < (entryRow t).length := by
  unfold entryRow
  rw [List.length_set]
  exact climb_ix_lt t h k hk

/-- The tally peg is not a climb hole, so the colour stays. -/
theorem entry_colour (t : Spec.Tier) (h : BoardOk t) (k : Nat) (hk : k < tierR t) :
    (entryRow t)[climbIx t k]'(entry_ix_lt t h k hk) =
      (tierClimb t)[k]'(by
        unfold tierClimb
        rw [List.length_reverse]
        simpa [tierR] using hk) := by
  unfold entryRow
  have hne : tallyOrigin t ≠ climbIx t k := Ne.symm (climb_before_origin t k hk)
  rw [List.getElem_set, if_neg hne]
  exact painted_colour t h k hk

theorem entry_colour_ne (t : Spec.Tier) (k : Nat) (hk : k < tierR t) :
    (tierClimb t)[k]'(by
      unfold tierClimb
      rw [List.length_reverse]
      simpa [tierR] using hk) ≠ 0 := by
  unfold tierClimb
  rw [List.getElem_reverse]
  exact rung_ne_zero (t.n - 1) ((rungList (t.n - 1)).length - 1 - k)
    (by unfold tierR at hk; omega)

/-- The colour at the first climb hole is the head of the pending list. -/
theorem entry_nextRung (t : Spec.Tier) (h : BoardOk t) (hR : 0 < tierR t)
    (r : Nat) (rs : List Nat) (hrest : tierClimb t = r :: rs) :
    (entryRow t)[climbAt (t.script + 2) (tierR t) 0]'(by
      rw [climb_head_ix]
      exact entry_ix_lt t h 0 hR) = r ∧ r ≠ 0 := by
  have hcol := entry_colour t h 0 hR
  have hhead :
      (tierClimb t)[0]'(by
        unfold tierClimb
        rw [List.length_reverse]
        simpa [tierR] using hR) = r := by
    simp [hrest]
  refine ⟨?_, ?_⟩
  · have hi : climbAt (t.script + 2) (tierR t) 0 < (entryRow t).length := by
      rw [climb_head_ix]
      exact entry_ix_lt t h 0 hR
    exact (rowGet_idx (climb_head_ix t) hi).trans (hcol.trans hhead)
  · rw [← hhead]
    exact entry_colour_ne t 0 hR

theorem climb_k_ix (t : Spec.Tier) (k : Nat) :
    climbAt (t.script + 2) (tierR t) k = climbIx t k := by
  unfold climbAt climbIx
  rfl

/-- `ParkRead.ladderTail` at entry: rung index 0, the pending list still whole. -/
theorem entry_ladderTail (t : Spec.Tier) (h : BoardOk t)
    (k : Nat) (hk : k < (tierClimb t).length) :
    (entryRow t)[climbAt (t.script + 2) (tierR t) k]'(by
      rw [climb_k_ix]
      apply entry_ix_lt t h k
      unfold tierClimb at hk
      rw [List.length_reverse] at hk
      simpa [tierR] using hk) =
      (tierClimb t)[k]'hk ∧ (tierClimb t)[k]'hk ≠ 0 := by
  have hkR : k < tierR t := by
    unfold tierClimb at hk
    rw [List.length_reverse] at hk
    simpa [tierR] using hk
  have hi : climbAt (t.script + 2) (tierR t) k < (entryRow t).length := by
    rw [climb_k_ix]
    exact entry_ix_lt t h k hkR
  have hcol := entry_colour t h k hkR
  have hidx :
      (tierClimb t)[k]'(by
        unfold tierClimb
        rw [List.length_reverse]
        simpa [tierR] using hkR) =
      (tierClimb t)[k]'hk := rfl
  refine ⟨(rowGet_idx (climb_k_ix t k) hi).trans (hcol.trans hidx), ?_⟩
  · rw [← hidx]
    exact entry_colour_ne t k hkR

/-- The board `tally_start` returns on the gap copy. -/
def tallyBoard (t : Spec.Tier) (xs : List Nat) (sat : TierSat t) (hR : 0 < tierR t) :
    Ecbs.Board :=
  { gapBoard t xs with
    sudo_5Board_3row := (gapBoard t xs).sudo_5Board_3row.set
      ⟨tallyOrigin t, gap_row_lt t xs sat⟩ (1 : Int)
    sudo_5Board_9tally_len := 1
    sudo_5Board_4cost := { (gapBoard t xs).sudo_5Board_4cost with
      sudo_5Costs_15control_highest := ((tallyOrigin t : Nat) : Int)
      sudo_5Costs_4ctrl := Int.ofNat (tierR t + 1)
      sudo_5Costs_9tally_max := 1 } }

theorem tally_board_run (t : Spec.Tier) (h : BoardOk t) (xs : List Nat) (sat : TierSat t)
    (hR : 0 < tierR t) :
    Ecbs.tally_start (gapBoard t xs) = .ok (tallyBoard t xs sat hR) :=
  tally_gap t h xs sat hR

theorem array_get_eq {a b : Array Int} (h : a = b) {i : Nat}
    {ha : i < a.size} {hb : i < b.size} : a[i] = b[i] := by
  subst h
  rfl

/-- The emitted tally board stores the pending colour at climb hole `k`.
    The tally peg is a different index, so `tally_start` leaves this cell. -/
theorem entry_board_colour (t : Spec.Tier) (h : BoardOk t) (xs : List Nat) (sat : TierSat t)
    (hR : 0 < tierR t) (k : Nat) (hk : k < tierR t) :
    (tallyBoard t xs sat hR).sudo_5Board_3row[climbIx t k]'(by
      unfold tallyBoard
      rw [Array.size_set, gap_row, size_embed]
      exact climb_ix_lt t h k hk) =
      ((tierClimb t)[k]'(by
        unfold tierClimb
        rw [List.length_reverse]
        simpa [tierR] using hk) : Int) := by
  unfold tallyBoard
  have hne : tallyOrigin t ≠ climbIx t k := Ne.symm (climb_before_origin t k hk)
  rw [Array.getElem_set_ne (h := hne)]
  have harr := gap_row t xs
  have ha : climbIx t k < (gapBoard t xs).sudo_5Board_3row.size := by
    rw [harr, size_embed]
    exact climb_ix_lt t h k hk
  have hb : climbIx t k < (embed (paintedRow t)).size := by
    rw [size_embed]
    exact climb_ix_lt t h k hk
  rw [array_get_eq harr (ha := ha) (hb := hb)]
  have hpaint : climbIx t k <
      (paint (List.replicate t.control 0) (t.script + 2) (rungList (t.n - 1))).length := by
    exact climb_ix_lt t h k hk
  rw [embed_nat _ (climbIx t k) hpaint]
  exact congrArg Int.ofNat (painted_colour t h k hk)

/-- `tally_start` replaces the painted row by the same row with the origin peg. -/
theorem tally_row (t : Spec.Tier) (xs : List Nat) (sat : TierSat t) (hR : 0 < tierR t) :
    (tallyBoard t xs sat hR).sudo_5Board_3row = embed (entryRow t) := by
  unfold tallyBoard
  have hgap := gap_row t xs
  rw [Array.set_congr_arr hgap (gap_row_lt t xs sat) (1 : Int)]
  have hlen : tallyOrigin t < (paintedRow t).length := by
    rw [painted_len]
    exact origin_lt t sat
  have hpaint : paintedRow t =
      paint (List.replicate t.control 0) (t.script + 2) (rungList (t.n - 1)) := rfl
  rw [hpaint] at hlen
  have hsz : tallyOrigin t <
      (embed (paint (List.replicate t.control 0) (t.script + 2) (rungList (t.n - 1)))).size := by
    rw [size_embed]
    exact hlen
  have hfin :
      (⟨tallyOrigin t, hgap ▸ gap_row_lt t xs sat⟩ : Fin _) = ⟨tallyOrigin t, hsz⟩ :=
    Fin.ext rfl
  rw [hfin]
  have hembed := embed_set
      (paint (List.replicate t.control 0) (t.script + 2) (rungList (t.n - 1)))
      (tallyOrigin t) 1 hlen
  have hidx :
      (⟨tallyOrigin t, hsz⟩ : Fin _) =
        ⟨tallyOrigin t, by rw [size_embed]; exact hlen⟩ := Fin.ext rfl
  rw [hidx, show (1 : Int) = Int.ofNat 1 from rfl, hembed]
  unfold entryRow
  rw [← hpaint]

end EcbsLink2.Link2
