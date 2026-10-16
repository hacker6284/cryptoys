/-
  Climb entry is the board `tally_start` returns: the gap holds the input,
  the bench is off, and one white peg sits at the tally origin. `ClimbInvK`
  at the empty prefix is that board. The park hole is the cell just after the
  ladder, so the loop's park premise holds, and the pending colours are the
  climb-order rungs already proved on `entryRow`.
-/
import EcbsLink2.Link2.InvertOpen
import EcbsLink2.Link2.InvertDelta
import EcbsLink2.Link2.LoopInv

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- Grid equations and the control-counter fit the climb reads off a tier.
    The four shipped tiers satisfy it; `ctrlFit` is the same bound as
    `demo_ctrl_fit` and its siblings. -/
structure TierShape (t : Spec.Tier) : Prop where
  n_eq : t.n = t.w * t.h - 1
  k_le : t.k ≤ t.n
  gap : t.n - t.k = t.w * t.r
  w0 : 0 < t.w
  h0 : 0 < t.h
  r0 : 0 < t.r
  rlt : t.r < t.h
  script_ge : 2 ≤ t.script
  small : t.w ≤ 1000000 ∧ t.h ≤ 1000000 ∧ t.r ≤ 1000000 ∧ t.benchlen ≤ 1000001
  n_small : t.n ≤ 1000000
  ctrlFit : FitsLen (t.control + ((rungList (t.n - 1)).length + 1) * (3 * t.control + 5))

theorem demo_shape : TierShape Spec.demo where
  n_eq := by decide
  k_le := by decide
  gap := by decide
  w0 := by decide
  h0 := by decide
  r0 := by decide
  rlt := by decide
  script_ge := by decide
  small := by decide
  n_small := by decide
  ctrlFit := demo_ctrl_fit

theorem toy_shape : TierShape Spec.toy where
  n_eq := by decide
  k_le := by decide
  gap := by decide
  w0 := by decide
  h0 := by decide
  r0 := by decide
  rlt := by decide
  script_ge := by decide
  small := by decide
  n_small := by decide
  ctrlFit := toy_ctrl_fit

theorem hobby_shape : TierShape Spec.hobby where
  n_eq := by decide
  k_le := by decide
  gap := by decide
  w0 := by decide
  h0 := by decide
  r0 := by decide
  rlt := by decide
  script_ge := by decide
  small := by decide
  n_small := by decide
  ctrlFit := hobby_ctrl_fit

theorem serious_shape : TierShape Spec.serious where
  n_eq := by decide
  k_le := by decide
  gap := by decide
  w0 := by decide
  h0 := by decide
  r0 := by decide
  rlt := by decide
  script_ge := by decide
  small := by decide
  n_small := by decide
  ctrlFit := serious_ctrl_fit

theorem rungCharge_add (n bench a d : Nat) :
    rungCharge n bench (a + d) =
      rungCharge n bench a + d * pegCharge n bench := by
  unfold rungCharge
  have hcoef : a + d + 1 = a + 1 + d := by omega
  rw [hcoef, Nat.add_mul]
  omega

theorem geom_room_lt (t : Spec.Tier) (sat : TierSat t) : rowRoom t < geomCap t := by
  have hmiss := sat.geom_miss
  have hor := sat.origin_le
  unfold rowRoom at hmiss hor ⊢
  omega

theorem entry_copy_le (xs : List Nat) (n bench : Nat) (hx : xs.length = n) :
    pegCount xs + pegCount xs ≤ pegCharge n bench := by
  have hle := pegCount_le xs
  rw [hx] at hle
  unfold pegCharge
  omega

theorem entry_moves_le (t : Spec.Tier) (xs : List Nat) (hx : xs.length = t.n)
    (sat : TierSat t) (hR : 0 < tierR t) :
    pegCount xs + pegCount xs +
        tierR t * rungCharge t.n t.benchlen (rowRoom t) ≤
      tierChargeMoves t (geomCap t) := by
  have hcopy := entry_copy_le xs t.n t.benchlen hx
  have hlt := geom_room_lt t sat
  have hsplit : geomCap t = rowRoom t + (geomCap t - rowRoom t) := by omega
  have hadd := rungCharge_add t.n t.benchlen (rowRoom t) (geomCap t - rowRoom t)
  have hcoef : pegCharge t.n t.benchlen ≤
      tierR t * ((geomCap t - rowRoom t) * pegCharge t.n t.benchlen) := by
    have hd1 : 1 ≤ geomCap t - rowRoom t := by omega
    have hprod : 1 ≤ tierR t * (geomCap t - rowRoom t) := by
      have hmul : tierR t * 1 ≤ tierR t * (geomCap t - rowRoom t) :=
        Nat.mul_le_mul_left (tierR t) hd1
      have hR1 : 1 ≤ tierR t := hR
      omega
    calc
      pegCharge t.n t.benchlen
          = 1 * pegCharge t.n t.benchlen := by rw [Nat.one_mul]
      _ ≤ (tierR t * (geomCap t - rowRoom t)) * pegCharge t.n t.benchlen :=
            Nat.mul_le_mul_right _ hprod
      _ = tierR t * ((geomCap t - rowRoom t) * pegCharge t.n t.benchlen) := by
            rw [Nat.mul_assoc]
  have hmul := Nat.mul_add (tierR t)
      (rungCharge t.n t.benchlen (rowRoom t))
      ((geomCap t - rowRoom t) * pegCharge t.n t.benchlen)
  unfold tierChargeMoves
  rw [hsplit, hadd, hmul]
  omega

theorem entry_tail_moves_le (t : Spec.Tier) (xs : List Nat) (hx : xs.length = t.n)
    (sat : TierSat t) (hR : 0 < tierR t) :
    pegCount xs + pegCount xs +
        tierR t * rungCharge t.n t.benchlen (rowRoom t) +
        pegCharge t.n t.benchlen ≤
      tierChargeMoves t (geomCap t) + pegCharge t.n t.benchlen := by
  have h := entry_moves_le t xs hx sat hR
  unfold tierChargeMoves at *
  omega

/-- The two entry copies are at most `2 · n`, so the check multiply's extra
    `n` (one more copy) still sits under the `3 · n` in `TierSat.fitCheckM`. -/
theorem entry_check_le (t : Spec.Tier) (xs : List Nat) (hx : xs.length = t.n) :
    pegCount xs + pegCount xs +
        tierR t * rungCharge t.n t.benchlen (rowRoom t) +
        pegCharge t.n t.benchlen +
        t.n + t.n * (t.n + 1) + 3 * (t.benchlen - t.n) + 2 * t.n ≤
      tierChargeMoves t (rowRoom t) + pegCharge t.n t.benchlen +
        3 * t.n + t.n * (t.n + 1) + 3 * (t.benchlen - t.n) + 2 * t.n := by
  have hle := pegCount_le xs
  rw [hx] at hle
  unfold tierChargeMoves
  omega

theorem entry_ops_le (t : Spec.Tier) (sat : TierSat t) (hR : 0 < tierR t) :
    1 + tierR t * (rowRoom t + 3) ≤ tierChargeOps t (geomCap t) := by
  have hlt := geom_room_lt t sat
  unfold tierChargeOps
  have hsum : geomCap t + 3 = (rowRoom t + 3) + (geomCap t - rowRoom t) := by omega
  have hdiff : 1 ≤ tierR t * (geomCap t - rowRoom t) := by
    have hd1 : 1 ≤ geomCap t - rowRoom t := by omega
    calc
      1 ≤ tierR t := hR
      _ = tierR t * 1 := by rw [Nat.mul_one]
      _ ≤ tierR t * (geomCap t - rowRoom t) := Nat.mul_le_mul_left _ hd1
  calc
    1 + tierR t * (rowRoom t + 3)
        ≤ tierR t * (geomCap t - rowRoom t) + tierR t * (rowRoom t + 3) :=
          Nat.add_le_add_right hdiff _
    _ = tierR t * (rowRoom t + 3) + tierR t * (geomCap t - rowRoom t) :=
          Nat.add_comm _ _
    _ = tierR t * ((rowRoom t + 3) + (geomCap t - rowRoom t)) := by
          rw [← Nat.mul_add]
    _ = tierR t * (geomCap t + 3) := by rw [← hsum]

theorem entry_ctrl_le (t : Spec.Tier) (hOk : BoardOk t) :
    (tierR t + 1) + (tierR t + 1) * (3 * rowRoom t + 5) ≤
      t.control + (tierR t + 1) * (3 * t.control + 5) := by
  have hroom : 3 * rowRoom t + 5 ≤ 3 * t.control + 5 := by
    unfold rowRoom
    omega
  have hrest : tierR t + 1 ≤ t.control := by
    have hL := hOk.ladder
    unfold tierR at hL ⊢
    omega
  have hmul : (tierR t + 1) * (3 * rowRoom t + 5) ≤
      (tierR t + 1) * (3 * t.control + 5) :=
    Nat.mul_le_mul_left _ hroom
  calc
    (tierR t + 1) + (tierR t + 1) * (3 * rowRoom t + 5)
        ≤ (tierR t + 1) + (tierR t + 1) * (3 * t.control + 5) :=
          Nat.add_le_add_left hmul _
    _ ≤ t.control + (tierR t + 1) * (3 * t.control + 5) :=
          Nat.add_le_add_right hrest _

theorem entry_row_len (t : Spec.Tier) : (entryRow t).length = t.control := by
  unfold entryRow
  rw [List.length_set, painted_len]

theorem climb_nonempty (t : Spec.Tier) (hR : 0 < tierR t) :
    (tierClimb t).isEmpty = false := by
  have hlen : 0 < (tierClimb t).length := by
    unfold tierClimb
    rw [List.length_reverse]
    simpa [tierR] using hR
  cases h : tierClimb t with
  | nil => simp [h] at hlen
  | cons _ _ => simp

theorem entry_origin (t : Spec.Tier)
    (hix : tallyOrigin t < (entryRow t).length) :
    (entryRow t)[tallyOrigin t]'hix = 1 := by
  have hlen : tallyOrigin t < (paintedRow t).length := by
    rw [painted_len]
    rw [entry_row_len] at hix
    exact hix
  unfold entryRow
  rw [List.getElem_set_self]

/-- Cells strictly after the origin are still the blank row. The paint stops
    at the last rung, one hole before the park. -/
theorem entry_past (t : Spec.Tier) (j : Nat) (hj : tallyOrigin t < j)
    (hix : j < (entryRow t).length) : (entryRow t)[j]'hix = 0 := by
  have hne : tallyOrigin t ≠ j := Nat.ne_of_lt hj
  unfold entryRow
  rw [List.getElem_set, if_neg hne]
  have hstart : t.script + 2 + (rungList (t.n - 1)).length ≤ j := by
    unfold tallyOrigin tierR at hj
    omega
  have hrep : j < (List.replicate t.control 0).length := by
    rw [List.length_replicate]
    rw [entry_row_len] at hix
    exact hix
  have hhi := paintRow_hi (List.replicate t.control 0) (t.script + 2)
      (rungList (t.n - 1)) j hstart hrep
  unfold paintedRow
  rw [hhi]
  simp [List.getElem_replicate]

/-- The park cell, the hole after the last rung and before the tally peg. -/
theorem entry_park_cell (t : Spec.Tier)
    (hix : t.script + 2 + tierR t < (entryRow t).length) :
    (entryRow t)[t.script + 2 + tierR t]'hix = 0 := by
  have hne : tallyOrigin t ≠ t.script + 2 + tierR t := by
    unfold tallyOrigin
    omega
  unfold entryRow
  rw [List.getElem_set, if_neg hne]
  have hstart : t.script + 2 + (rungList (t.n - 1)).length ≤
      t.script + 2 + tierR t := by
    unfold tierR
    omega
  have hrep : t.script + 2 + tierR t < (List.replicate t.control 0).length := by
    rw [List.length_replicate]
    rw [entry_row_len] at hix
    exact hix
  have hhi := paintRow_hi (List.replicate t.control 0) (t.script + 2)
      (rungList (t.n - 1)) (t.script + 2 + tierR t) hstart hrep
  unfold paintedRow
  rw [hhi]
  simp [List.getElem_replicate]

theorem entry_seg (t : Spec.Tier) (sat : TierSat t) (hR : 0 < tierR t) :
    RowSeg (entryRow t) (tallyOrigin t) 1 (tierClimb t).isEmpty := by
  have hempty := climb_nonempty t hR
  refine ⟨?_, ?_, ?_⟩
  · rw [entry_row_len]
    have h := origin_lt t sat
    omega
  · intro j hj
    rw [hempty]
    have hj0 : j = 0 := by omega
    subst hj0
    have hix : tallyOrigin t + 0 < (entryRow t).length := by
      rw [entry_row_len]
      have h := origin_lt t sat
      omega
    have hget := entry_origin t (by
      rw [entry_row_len]
      exact origin_lt t sat)
    have hidx : tallyOrigin t + 0 = tallyOrigin t := by omega
    rw [rowGet_idx hidx hix, hget]
    rfl
  · intro _ j hj hix
    have hlt : tallyOrigin t < tallyOrigin t + j := by omega
    exact entry_past t (tallyOrigin t + j) hlt hix

theorem entry_double_room (t : Spec.Tier) (sat : TierSat t) :
    2 ≤ (tierClimb t).length → tallyOrigin t + 2 ≤ t.control := by
  intro h2
  have hpre := sat.prefixes
  cases hL : tierClimb t with
  | nil => simp [hL] at h2
  | cons r rs =>
      rw [hL] at hpre h2
      have hrs : rs ≠ [] := by
        intro hrs
        simp [hrs] at h2
      have hpair : 1 ≤ rowRoom t ∧
          tallyPrefixesLe (tallyAfter 1 r rs.isEmpty) (rowRoom t) rs = true := by
        simpa [tallyPrefixesLe] using hpre
      have hne : rs.isEmpty = false := by
        cases rs with
        | nil => exact absurd rfl hrs
        | cons => rfl
      have hta : 2 ≤ tallyAfter 1 r false := by
        unfold tallyAfter
        by_cases hr : r = 2 <;> simp [hr]
      have hle : tallyAfter 1 r false ≤ rowRoom t := by
        rw [hne] at hpair
        cases rs with
        | nil => exact absurd rfl hrs
        | cons r2 rs2 =>
            have h' : tallyAfter 1 r false ≤ rowRoom t ∧
                tallyPrefixesLe (tallyAfter (tallyAfter 1 r false) r2 rs2.isEmpty)
                  (rowRoom t) rs2 = true := by
              simpa [tallyPrefixesLe] using hpair.2
            exact h'.1
      have hroom : 2 ≤ rowRoom t := Nat.le_trans hta hle
      have hor := sat.origin_le
      unfold rowRoom at hroom
      omega

/-- The model at the first tally peg. Nothing is parked. The gap is the input. -/
def entryModel (t : Spec.Tier) (xs : List Nat) : ClimbModel where
  n := t.n
  k := t.k
  benchlen := t.benchlen
  gap := xs
  work := xs
  onBench := false
  tally := 1
  t0 := tallyOrigin t
  parkAt := t.script + 2 + tierR t
  parked := 0
  fromHole := -1
  ridx := 0
  ctrl := tierR t + 1
  high := tallyOrigin t
  row := entryRow t

/-- Counters on the tally board, and the room cap as the tally bound. -/
def entryBudget (t : Spec.Tier) (hOk : BoardOk t) (xs : List Nat)
    (hx : xs.length = t.n) (sat : TierSat t) (hR : 0 < tierR t)
    (lay : TierShape t) : ClimbBudget where
  n := t.n
  bench := t.benchlen
  moves0 := pegCount xs + pegCount xs
  slides0 := 0
  ops0 := 1
  peak0 := 2
  tally0 := 1
  tallyPos := by decide
  high0 := 0
  R := tierR t
  mMax := rowRoom t
  mMax_le := by simpa [geomCap] using sat.room_le_geom
  fitM := FitsLen.of_le sat.fitGeomM (entry_moves_le t xs hx sat hR)
  fitS := by simpa [tierChargeSlides, Nat.zero_add] using sat.fitRoomS
  fitO := by
    simpa [tierChargeOps] using
      (FitsLen.of_le sat.fitGeomO (entry_ops_le t sat hR))
  fitTailM := by
    simpa [tierChargeMoves] using
      (FitsLen.of_le sat.fitGeomTailM (entry_tail_moves_le t xs hx sat hR))
  fitTailS := by simpa [tierChargeSlides, Nat.zero_add] using sat.fitRoomTailS
  fitCheckM := FitsLen.of_le sat.fitCheckM (entry_check_le t xs hx)
  ctrl0 := tierR t + 1
  fitCtrl := FitsLen.of_le lay.ctrlFit (entry_ctrl_le t hOk)
  x := xs
  xHome := 2
  w := t.w
  h := t.h
  r := t.r
  cg := t.combgap
  control := t.control
  fitControl := fits_of hOk.fits_control
  ladder0 := t.script + 2
  side0 := []
  side1 := []
  side4 := []
  held0 := false
  held1 := false
  held4 := false
  tierSnap := embTier t
  markSnap := -1
  mxSnap := 0

theorem tally_home (t : Spec.Tier) (xs : List Nat) (sat : TierSat t) (hR : 0 < tierR t) :
    (tallyBoard t xs sat hR).sudo_5Board_4home = (gapBoard t xs).sudo_5Board_4home := by
  simp [tallyBoard]

theorem tally_held (t : Spec.Tier) (xs : List Nat) (sat : TierSat t) (hR : 0 < tierR t) :
    (tallyBoard t xs sat hR).sudo_5Board_4held = (gapBoard t xs).sudo_5Board_4held := by
  simp [tallyBoard]

theorem tally_tier (t : Spec.Tier) (xs : List Nat) (sat : TierSat t) (hR : 0 < tierR t) :
    (tallyBoard t xs sat hR).sudo_5Board_1t = (gapBoard t xs).sudo_5Board_1t := by
  simp [tallyBoard]

theorem gap_home_eq (t : Spec.Tier) (xs : List Nat) :
    (gapBoard t xs).sudo_5Board_4home =
      (bumpedBoard t xs).sudo_5Board_4home.set ⟨5, bumped_home5 t xs⟩ (embed xs) := by
  simp [gapBoard]

theorem gap_held_eq (t : Spec.Tier) (xs : List Nat) :
    (gapBoard t xs).sudo_5Board_4held =
      (bumpedBoard t xs).sudo_5Board_4held.set ⟨5, bumped_held5 t xs⟩ true := by
  simp [gapBoard]

theorem tally_home_size (t : Spec.Tier) (xs : List Nat) (sat : TierSat t) (hR : 0 < tierR t) :
    (tallyBoard t xs sat hR).sudo_5Board_4home.size = 8 := by
  rw [tally_home, gap_home_eq, Array.size_set]
  simp [bumpedBoard, bumpOp, bottomBoard, Array.size_set, built_home_blank, Array.size_mkArray]

theorem tally_held_size (t : Spec.Tier) (xs : List Nat) (sat : TierSat t) (hR : 0 < tierR t) :
    (tallyBoard t xs sat hR).sudo_5Board_4held.size = 8 := by
  rw [tally_held, gap_held_eq, Array.size_set]
  simp [bumpedBoard, bumpOp, bottomBoard, Array.size_set, built_held_blank, Array.size_mkArray]

theorem tally_home5 (t : Spec.Tier) (xs : List Nat) (sat : TierSat t) (hR : 0 < tierR t)
    (h : 5 < (tallyBoard t xs sat hR).sudo_5Board_4home.size) :
    (tallyBoard t xs sat hR).sudo_5Board_4home[5]'h = embed xs := by
  have harr : (tallyBoard t xs sat hR).sudo_5Board_4home =
      (bumpedBoard t xs).sudo_5Board_4home.set ⟨5, bumped_home5 t xs⟩ (embed xs) := by
    rw [tally_home, gap_home_eq]
  have h5 := bumped_home5 t xs
  have hsz : 5 < ((bumpedBoard t xs).sudo_5Board_4home.set ⟨5, h5⟩ (embed xs)).size := by
    rw [Array.size_set]; exact h5
  have hget := Array.getElem_set_eq (bumpedBoard t xs).sudo_5Board_4home ⟨5, h5⟩
      (embed xs) rfl hsz
  exact cell_eq_of harr hget

theorem tally_held5 (t : Spec.Tier) (xs : List Nat) (sat : TierSat t) (hR : 0 < tierR t)
    (h : 5 < (tallyBoard t xs sat hR).sudo_5Board_4held.size) :
    (tallyBoard t xs sat hR).sudo_5Board_4held[5]'h = true := by
  have harr : (tallyBoard t xs sat hR).sudo_5Board_4held =
      (bumpedBoard t xs).sudo_5Board_4held.set ⟨5, bumped_held5 t xs⟩ true := by
    rw [tally_held, gap_held_eq]
  have h5 := bumped_held5 t xs
  have hsz : 5 < ((bumpedBoard t xs).sudo_5Board_4held.set ⟨5, h5⟩ true).size := by
    rw [Array.size_set]; exact h5
  have hget := Array.getElem_set_eq (bumpedBoard t xs).sudo_5Board_4held ⟨5, h5⟩ true rfl hsz
  exact cell_eq_of harr hget

theorem bottom_held_eq (t : Spec.Tier) (xs : List Nat) :
    (bottomBoard t xs).sudo_5Board_4held =
      (builtBoard t).sudo_5Board_4held.set ⟨2, held2_lt t⟩ true := by
  simp [bottomBoard]

theorem bottom_home_eq (t : Spec.Tier) (xs : List Nat) :
    (bottomBoard t xs).sudo_5Board_4home =
      (builtBoard t).sudo_5Board_4home.set ⟨2, home2_lt t⟩ (embed xs) := by
  simp [bottomBoard]

theorem tally_held2 (t : Spec.Tier) (xs : List Nat) (sat : TierSat t) (hR : 0 < tierR t)
    (h : 2 < (tallyBoard t xs sat hR).sudo_5Board_4held.size) :
    (tallyBoard t xs sat hR).sudo_5Board_4held[2]'h = true := by
  have harr : (tallyBoard t xs sat hR).sudo_5Board_4held =
      (bumpedBoard t xs).sudo_5Board_4held.set ⟨5, bumped_held5 t xs⟩ true := by
    rw [tally_held, gap_held_eq]
  have h5 := bumped_held5 t xs
  have hsz : 2 < ((bumpedBoard t xs).sudo_5Board_4held.set ⟨5, h5⟩ true).size := by
    rw [Array.size_set]; exact bumped_held2 t xs
  have hne : (5 : Nat) ≠ 2 := by decide
  have hget := Array.getElem_set_ne (bumpedBoard t xs).sudo_5Board_4held ⟨5, h5⟩ true hsz hne
  have hsrc := bumped_src_held t xs
  have hcell : (tallyBoard t xs sat hR).sudo_5Board_4held[2]'h =
      (bumpedBoard t xs).sudo_5Board_4held[2]'(bumped_held2 t xs) := by
    have hfin : (⟨2, hsz⟩ : Fin _) = ⟨2, by rw [Array.size_set]; exact bumped_held2 t xs⟩ :=
      Fin.ext rfl
    simp [harr, hfin]
  exact hcell.trans hsrc

theorem tally_home2 (t : Spec.Tier) (xs : List Nat) (sat : TierSat t) (hR : 0 < tierR t)
    (h : 2 < (tallyBoard t xs sat hR).sudo_5Board_4home.size) :
    (tallyBoard t xs sat hR).sudo_5Board_4home[2]'h = embed xs := by
  have harr : (tallyBoard t xs sat hR).sudo_5Board_4home =
      (bumpedBoard t xs).sudo_5Board_4home.set ⟨5, bumped_home5 t xs⟩ (embed xs) := by
    rw [tally_home, gap_home_eq]
  have h5 := bumped_home5 t xs
  have hsz : 2 < ((bumpedBoard t xs).sudo_5Board_4home.set ⟨5, h5⟩ (embed xs)).size := by
    rw [Array.size_set]; exact bumped_home2 t xs
  have hne : (5 : Nat) ≠ 2 := by decide
  have hget := Array.getElem_set_ne (bumpedBoard t xs).sudo_5Board_4home ⟨5, h5⟩
      (embed xs) hsz hne
  have hsrc := bumped_src_arr t xs
  have hcell : (tallyBoard t xs sat hR).sudo_5Board_4home[2]'h =
      (bumpedBoard t xs).sudo_5Board_4home[2]'(bumped_home2 t xs) := by
    have hfin : (⟨2, hsz⟩ : Fin _) = ⟨2, by rw [Array.size_set]; exact bumped_home2 t xs⟩ :=
      Fin.ext rfl
    simp [harr, hfin]
  exact hcell.trans hsrc

theorem tally_held6 (t : Spec.Tier) (xs : List Nat) (sat : TierSat t) (hR : 0 < tierR t)
    (h : 6 < (tallyBoard t xs sat hR).sudo_5Board_4held.size) :
    (tallyBoard t xs sat hR).sudo_5Board_4held[6]'h = false := by
  have hblank := built_held_blank t
  have h6blank : 6 < (Array.mkArray 8 false).size := by simp [Array.size_mkArray]
  have hzero : (Array.mkArray 8 false)[6]'h6blank = false := by simp [Array.getElem_mkArray]
  have hbuilt : (builtBoard t).sudo_5Board_4held[6]'(by rw [hblank]; exact h6blank) = false := by
    rw [idx_get hblank 6 (by rw [hblank]; exact h6blank)]
    exact hzero
  have hbot := bottom_held_eq t xs
  have h6set : 6 < ((builtBoard t).sudo_5Board_4held.set ⟨2, held2_lt t⟩ true).size := by
    rw [Array.size_set, hblank]; exact h6blank
  have hne2 : (2 : Nat) ≠ 6 := by decide
  have hset := Array.getElem_set_ne (builtBoard t).sudo_5Board_4held ⟨2, held2_lt t⟩
      true h6set hne2
  have hbottom : (bottomBoard t xs).sudo_5Board_4held[6]'(by rw [hbot]; exact h6set) = false :=
    (cell_eq_of hbot (hset.trans hbuilt))
  have hbump : (bumpedBoard t xs).sudo_5Board_4held =
      (bottomBoard t xs).sudo_5Board_4held := by simp [bumpedBoard, bumpOp]
  have hbumped : (bumpedBoard t xs).sudo_5Board_4held[6]'(by rw [hbump, hbot]; exact h6set) =
      false := cell_eq_of hbump hbottom
  have harr : (tallyBoard t xs sat hR).sudo_5Board_4held =
      (bumpedBoard t xs).sudo_5Board_4held.set ⟨5, bumped_held5 t xs⟩ true :=
    (tally_held t xs sat hR).trans (gap_held_eq t xs)
  have h5 := bumped_held5 t xs
  have hsz : 6 < ((bumpedBoard t xs).sudo_5Board_4held.set ⟨5, h5⟩ true).size := by
    rw [Array.size_set, hbump, hbot]; exact h6set
  have hne5 : (5 : Nat) ≠ 6 := by decide
  have hgap := Array.getElem_set_ne (bumpedBoard t xs).sudo_5Board_4held ⟨5, h5⟩ true hsz hne5
  exact cell_eq_of harr (hgap.trans hbumped)

theorem tally_moves (t : Spec.Tier) (xs : List Nat) (sat : TierSat t) (hR : 0 < tierR t) :
    (tallyBoard t xs sat hR).sudo_5Board_4cost.sudo_5Costs_5moves =
      Int.ofNat (pegCount xs + pegCount xs) := by
  simp [tallyBoard, gapBoard]

theorem tally_peak (t : Spec.Tier) (xs : List Nat) (sat : TierSat t) (hR : 0 < tierR t) :
    (tallyBoard t xs sat hR).sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat 2 := by
  simp [tallyBoard, gapBoard]

theorem tally_plain (t : Spec.Tier) (xs : List Nat) (sat : TierSat t) (hR : 0 < tierR t) :
    (tallyBoard t xs sat hR).sudo_5Board_8bench_on = false ∧
      (tallyBoard t xs sat hR).sudo_5Board_9marker_on = false ∧
      (tallyBoard t xs sat hR).sudo_5Board_8rung_idx = 0 ∧
      (tallyBoard t xs sat hR).sudo_5Board_11parked_from = -1 ∧
      (tallyBoard t xs sat hR).sudo_5Board_4cost.sudo_5Costs_6slides = 0 ∧
      (tallyBoard t xs sat hR).sudo_5Board_4cost.sudo_5Costs_11peak_strict = 0 ∧
      (tallyBoard t xs sat hR).sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = 0 ∧
      (tallyBoard t xs sat hR).sudo_5Board_7ladder0 = Int.ofNat (t.script + 2) ∧
      (tallyBoard t xs sat hR).sudo_5Board_6nrungs = Int.ofNat (tierR t) ∧
      (tallyBoard t xs sat hR).sudo_5Board_9park_hole =
        Int.ofNat (t.script + 2 + tierR t) := by
  simp [tallyBoard, gapBoard, bumpedBoard, bumpOp, bottomBoard, builtBoard, midBoard, placed,
    blankOf, tierR]

theorem tally_ops_arr (t : Spec.Tier) (xs : List Nat) (sat : TierSat t) (hR : 0 < tierR t) :
    (tallyBoard t xs sat hR).sudo_5Board_4cost.sudo_5Costs_3ops =
      (Array.mkArray 5 (0 : Int)).set ⟨2, by simp [Array.size_mkArray]⟩ (Int.ofNat 1) := by
  have ht : (tallyBoard t xs sat hR).sudo_5Board_4cost.sudo_5Costs_3ops =
      (gapBoard t xs).sudo_5Board_4cost.sudo_5Costs_3ops := by
    simp [tallyBoard]
  have hg : (gapBoard t xs).sudo_5Board_4cost.sudo_5Costs_3ops =
      (bumpedBoard t xs).sudo_5Board_4cost.sudo_5Costs_3ops := by
    simp [gapBoard]
  rw [ht, hg]
  have hb : (bumpedBoard t xs).sudo_5Board_4cost.sudo_5Costs_3ops =
      (bottomBoard t xs).sudo_5Board_4cost.sudo_5Costs_3ops.set
        ⟨2, bottom_ops2 t xs⟩ (1 : Int) := by
    simp [bumpedBoard, bumpOp, Nat.zero_add]
  rw [hb]
  apply Array.ext
  · simp [bottom_ops, Array.size_set, Array.size_mkArray]
  · intro i hi1 hi2
    simp [bottom_ops, Array.getElem_set, Array.getElem_mkArray, ofNat_eq_natCast]

theorem gap_emb (t : Spec.Tier) (xs : List Nat) :
    (gapBoard t xs).sudo_5Board_1t = embTier t := by
  simp [gapBoard, bumpedBoard, bumpOp, bottomBoard, builtBoard, midBoard, placed, blankOf]

theorem tally_emb (t : Spec.Tier) (xs : List Nat) (sat : TierSat t) (hR : 0 < tierR t) :
    (tallyBoard t xs sat hR).sudo_5Board_1t = embTier t := by
  rw [tally_tier, gap_emb]

theorem entry_inv (t : Spec.Tier) (xs : List Nat) (sat : TierSat t) (hR : 0 < tierR t) :
    ClimbInv (tallyBoard t xs sat hR) (entryModel t xs) := by
  have hsizeH := tally_home_size t xs sat hR
  have hsizeD := tally_held_size t xs sat hR
  have hplain := tally_plain t xs sat hR
  rcases hplain with ⟨-, hmark, hridx, hfrom, -, -, -, -, -, hpark⟩
  refine
    { hG := by rw [hsizeH]; decide
      hGs := by rw [hsizeD]; decide
      marker := hmark
      len := by simp [tallyBoard, entryModel]
      ctrl := by simp [tallyBoard, entryModel]
      high := by simp [tallyBoard, entryModel]
      t0 := by
        have h0 : (tallyBoard t xs sat hR).sudo_5Board_6tally0 =
            (gapBoard t xs).sudo_5Board_6tally0 := by simp [tallyBoard]
        simp [entryModel, h0, gap_tally0, ofNat_eq_natCast]
      row := by simp [entryModel, tally_row t xs sat hR]
      park := by simp [entryModel, hpark, ofNat_eq_natCast]
      fromP := by simp [entryModel, hfrom]
      ridx := by simp [entryModel, hridx]
      gapHome := by
        intro _
        refine ⟨?_, ?_⟩
        · exact tally_held5 t xs sat hR (by rw [hsizeD]; decide)
        · have hhome := tally_home5 t xs sat hR (by rw [hsizeH]; decide)
          simpa [entryModel] using hhome
      gapBench := by
        intro h
        simp [entryModel] at h }

theorem entry_park_lt (t : Spec.Tier) (sat : TierSat t) :
    t.script + 2 + tierR t < (entryRow t).length := by
  rw [entry_row_len]
  have h := origin_lt t sat
  unfold tallyOrigin at h
  omega

theorem entry_hole_lt (t : Spec.Tier) (hOk : BoardOk t) (hR : 0 < tierR t) :
    climbAt (t.script + 2) (tierR t) 0 < (entryRow t).length := by
  rw [climb_head_ix]
  exact entry_ix_lt t hOk 0 hR

theorem entry_park (t : Spec.Tier) (hOk : BoardOk t) (xs : List Nat)
    (hx : xs.length = t.n) (sat : TierSat t) (hR : 0 < tierR t) (lay : TierShape t) :
    ParkRead (tallyBoard t xs sat hR) (entryModel t xs) (tierClimb t)
      (entryBudget t hOk xs hx sat hR lay) := by
  have hplain := tally_plain t xs sat hR
  rcases hplain with ⟨-, -, -, -, -, -, -, hlad, hnr, -⟩
  refine
    { ladder0B := by simp [entryBudget, hlad]
      nrungsB := by simp [entryBudget, hnr, ofNat_eq_natCast]
      climbH := by
        apply climb_holes_refines (tallyBoard t xs sat hR) (t.script + 2) (tierR t)
        · simp [hlad]
        · simp [hnr, ofNat_eq_natCast]
        · omega
        · exact FitsLen.of_le (fits_of hOk.fits_script) (by omega)
        · apply FitsLen.of_le (fits_of hOk.fits_control)
          have hL := hOk.ladder
          unfold tierR at hL ⊢
          omega
      holeLt := by simpa [entryModel, entryBudget] using entry_hole_lt t hOk hR
      parkLt := by simpa [entryModel] using entry_park_lt t sat
      parkNe := by
        simp [entryModel, entryBudget, climbAt]
        omega
      parkLe := by
        simp [entryModel]
        unfold tallyOrigin
        omega
      parkIn := by
        simp [entryModel, entryBudget]
        have h := origin_lt t sat
        unfold tallyOrigin at h
        omega
      parkCell := by
        intro _
        simp [entryModel, entry_park_cell t (entry_park_lt t sat)]
      fromIdle := by
        intro _
        simp [entryModel]
      fromNat := by
        intro h
        simp [entryModel] at h
      srcOk := by
        intro h
        simp [entryModel] at h
      parkHeld := by
        intro h
        simp [entryModel] at h
      nextRung := by
        intro r rs hrest
        simpa [entryModel, entryBudget] using entry_nextRung t hOk hR r rs hrest
      ladderTail := by
        intro k hk hlt
        simpa [entryModel, entryBudget] using entry_ladderTail t hOk k hk
      fit2 := by
        simp [entryModel]
        apply FitsLen.of_le (fits_of hOk.fits_control)
        have hL := hOk.ladder
        unfold tierR at hL ⊢
        omega
      fit4 := by
        simp [entryModel]
        apply FitsLen.of_le (fits_of hOk.fits_control)
        have hL := hOk.ladder
        have hs := lay.script_ge
        unfold tierR at hL ⊢
        omega
      fitI := by simp [entryModel, FitsLen, i64MaxNat]
      l0pos := by simp [entryBudget]
      fitL0 := by
        simp [entryBudget]
        exact FitsLen.of_le (fits_of hOk.fits_script) (by omega)
      fitLR := by
        simp [entryBudget]
        apply FitsLen.of_le (fits_of hOk.fits_control)
        have hL := hOk.ladder
        unfold tierR at hL ⊢
        omega }

theorem entry_peg (t : Spec.Tier) (hOk : BoardOk t) (xs : List Nat)
    (hx : xs.length = t.n) (htri : allTritList xs) (sat : TierSat t) (hR : 0 < tierR t)
    (lay : TierShape t) :
    PegRead (tallyBoard t xs sat hR) (entryModel t xs)
      (entryBudget t hOk xs hx sat hR lay) := by
  have hplain := tally_plain t xs sat hR
  rcases hplain with ⟨-, -, -, -, -, hstrict, hhole, -, -, -⟩
  have hops : (tallyBoard t xs sat hR).sudo_5Board_4cost.sudo_5Costs_3ops.size = 5 := by
    rw [tally_ops_arr, Array.size_set, Array.size_mkArray]
  refine
    { opsGt := by rw [hops]; decide
      cOps := by
        refine ⟨0, ?_⟩
        have harr := tally_ops_arr t xs sat hR
        have hi : 1 < (tallyBoard t xs sat hR).sudo_5Board_4cost.sudo_5Costs_3ops.size := by
          rw [hops]; decide
        rw [idx_get harr 1 hi, Array.getElem_set, if_neg (by decide : (2 : Nat) ≠ 1)]
        simp [Array.getElem_mkArray]
      peakS := ⟨0, hstrict⟩
      holeM := ⟨0, hhole⟩
      trits := by simpa [entryModel] using htri
      top := by
        intro _
        simp [entryModel]
      fitRow := by
        simp [entryModel]
        apply FitsLen.of_le (fits_of hOk.fits_control)
        have h := origin_lt t sat
        omega
      fitTall := by
        simp [entryModel]
        unfold FitsLen i64MaxNat
        decide
      fitCtrl := by
        simp [entryModel]
        apply FitsLen.of_le (fits_of hOk.fits_control)
        have hL := hOk.ladder
        unfold tierR at hL ⊢
        omega
      n_pos := by simpa [entryModel] using hOk.n_pos
      span := by simpa [entryModel, entryBudget] using sat.cube_span
      small := by simpa [entryModel, entryBudget] using lay.small
      n_small := by simpa [entryModel] using lay.n_small
      fitN := by
        simp [entryModel]
        exact FitsLen.of_le (fits_of hOk.fits_n) (by omega)
      fitBn := by
        simp [entryModel]
        exact FitsLen.of_le (by unfold FitsLen i64MaxNat; decide) lay.small.2.2.2
      fit3 := by
        simp [entryModel]
        exact FitsLen.of_le (fits_of hOk.fits_n) (by omega) }

/-- A fresh tally board's homes other than 2 and 5 are the blank `new_board` left. -/
theorem tally_side_held (t : Spec.Tier) (xs : List Nat) (sat : TierSat t) (hR : 0 < tierR t)
    (i : Nat) (hi : i < 8) (hne2 : i ≠ 2) (hne5 : i ≠ 5) :
    (tallyBoard t xs sat hR).sudo_5Board_4held[i]'(by
      rw [tally_held_size t xs sat hR]; exact hi) = false := by
  have hblank := built_held_blank t
  have hib : i < (Array.mkArray 8 false).size := by simp [Array.size_mkArray]; exact hi
  have hzero : (Array.mkArray 8 false)[i]'hib = false := by simp [Array.getElem_mkArray]
  have hbuilt : (builtBoard t).sudo_5Board_4held[i]'(by rw [hblank]; exact hib) = false := by
    rw [idx_get hblank i (by rw [hblank]; exact hib)]
    exact hzero
  have hbot := bottom_held_eq t xs
  have hiset : i < ((builtBoard t).sudo_5Board_4held.set ⟨2, held2_lt t⟩ true).size := by
    rw [Array.size_set, hblank]; exact hib
  have hset := Array.getElem_set_ne (builtBoard t).sudo_5Board_4held ⟨2, held2_lt t⟩
      true hiset (Ne.symm hne2)
  have hbottom : (bottomBoard t xs).sudo_5Board_4held[i]'(by rw [hbot]; exact hiset) = false :=
    cell_eq_of hbot (hset.trans hbuilt)
  have hbump : (bumpedBoard t xs).sudo_5Board_4held = (bottomBoard t xs).sudo_5Board_4held := by
    simp [bumpedBoard, bumpOp]
  have hbumped : (bumpedBoard t xs).sudo_5Board_4held[i]'(by rw [hbump, hbot]; exact hiset) =
      false := cell_eq_of hbump hbottom
  have harr : (tallyBoard t xs sat hR).sudo_5Board_4held =
      (bumpedBoard t xs).sudo_5Board_4held.set ⟨5, bumped_held5 t xs⟩ true :=
    (tally_held t xs sat hR).trans (gap_held_eq t xs)
  have h5 := bumped_held5 t xs
  have hsz : i < ((bumpedBoard t xs).sudo_5Board_4held.set ⟨5, h5⟩ true).size := by
    rw [Array.size_set, hbump, hbot]; exact hiset
  have hgap := Array.getElem_set_ne (bumpedBoard t xs).sudo_5Board_4held ⟨5, h5⟩ true hsz
    (Ne.symm hne5)
  exact cell_eq_of harr (hgap.trans hbumped)

theorem tally_side_home (t : Spec.Tier) (xs : List Nat) (sat : TierSat t) (hR : 0 < tierR t)
    (i : Nat) (hi : i < 8) (hne2 : i ≠ 2) (hne5 : i ≠ 5) :
    (tallyBoard t xs sat hR).sudo_5Board_4home[i]'(by
      rw [tally_home_size t xs sat hR]; exact hi) = embed [] := by
  have hblank := built_home_blank t
  have hib : i < (Array.mkArray 8 (#[] : Array Int)).size := by
    simp [Array.size_mkArray]; exact hi
  have hzero : (Array.mkArray 8 (#[] : Array Int))[i]'hib = #[] := by
    simp [Array.getElem_mkArray]
  have hbuilt : (builtBoard t).sudo_5Board_4home[i]'(by rw [hblank]; exact hib) = #[] := by
    rw [idx_get hblank i (by rw [hblank]; exact hib)]
    exact hzero
  have hbot := bottom_home_eq t xs
  have hiset : i < ((builtBoard t).sudo_5Board_4home.set ⟨2, home2_lt t⟩ (embed xs)).size := by
    rw [Array.size_set, hblank]; exact hib
  have hset := Array.getElem_set_ne (builtBoard t).sudo_5Board_4home ⟨2, home2_lt t⟩
      (embed xs) hiset (Ne.symm hne2)
  have hbottom : (bottomBoard t xs).sudo_5Board_4home[i]'(by rw [hbot]; exact hiset) = #[] :=
    cell_eq_of hbot (hset.trans hbuilt)
  have hbump : (bumpedBoard t xs).sudo_5Board_4home = (bottomBoard t xs).sudo_5Board_4home := by
    simp [bumpedBoard, bumpOp]
  have hbumped : (bumpedBoard t xs).sudo_5Board_4home[i]'(by rw [hbump, hbot]; exact hiset) =
      #[] := cell_eq_of hbump hbottom
  have harr : (tallyBoard t xs sat hR).sudo_5Board_4home =
      (bumpedBoard t xs).sudo_5Board_4home.set ⟨5, bumped_home5 t xs⟩ (embed xs) :=
    (tally_home t xs sat hR).trans (gap_home_eq t xs)
  have h5 := bumped_home5 t xs
  have hsz : i < ((bumpedBoard t xs).sudo_5Board_4home.set ⟨5, h5⟩ (embed xs)).size := by
    rw [Array.size_set, hbump, hbot]; exact hiset
  have hgap := Array.getElem_set_ne (bumpedBoard t xs).sudo_5Board_4home ⟨5, h5⟩
      (embed xs) hsz (Ne.symm hne5)
  have hcell : (tallyBoard t xs sat hR).sudo_5Board_4home[i]'(by
      rw [tally_home_size t xs sat hR]; exact hi) = #[] :=
    cell_eq_of harr (hgap.trans (idx_irrel.trans hbumped))
  have hempty : (#[] : Array Int) = embed [] := by simp [embed]
  exact hcell.trans hempty

theorem entry_shape (t : Spec.Tier) (hOk : BoardOk t) (xs : List Nat)
    (hx : xs.length = t.n) (htri : allTritList xs) (sat : TierSat t) (hR : 0 < tierR t)
    (lay : TierShape t) :
    ClimbShape (tallyBoard t xs sat hR) (entryModel t xs) (tierClimb t)
      (entryBudget t hOk xs hx sat hR lay) := by
  have hsizeH := tally_home_size t xs sat hR
  have hsizeD := tally_held_size t xs sat hR
  have hplain := tally_plain t xs sat hR
  rcases hplain with ⟨hbench, -, -, -, -, -, -, -, -, -⟩
  have hem := tally_emb t xs sat hR
  refine
    { spareH := by rw [hsizeH]; decide
      spareD := by rw [hsizeD]; decide
      spareE := tally_held6 t xs sat hR (by rw [hsizeD]; decide)
      h7 := by rw [hsizeD]; decide
      gapClear := by
        intro h
        simp [entryModel] at h
      offWhenHome := by
        intro _
        exact hbench
      xD := by simp [entryBudget, hsizeD]
      xH := by simp [entryBudget, hsizeH]
      xHeld := tally_held2 t xs sat hR (by rw [hsizeD]; decide)
      xArr := by
        have hhome := tally_home2 t xs sat hR (by rw [hsizeH]; decide)
        simpa [entryBudget] using hhome
      xNe5 := by simp [entryBudget]
      xNe6 := by simp [entryBudget]
      gapLen := by simp [entryModel, hx]
      seg := by simpa [entryModel] using entry_seg t sat hR
      tierN := by rw [hem]; simp [entryModel, embTier]
      tierK := by rw [hem]; simp [entryModel, embTier]
      tierB := by rw [hem]; simp [entryModel, embTier]
      tierW := by rw [hem]; simp [entryBudget, embTier]
      tierH := by rw [hem]; simp [entryBudget, embTier]
      tierR := by rw [hem]; simp [entryBudget, embTier]
      tierCg := by rw [hem]; simp [entryBudget, embTier]
      tierC := by rw [hem]; simp [entryBudget, embTier]
      rowLen := by simp [entryModel, entryBudget, entry_row_len]
      w0 := by simpa [entryBudget] using lay.w0
      h0 := by simpa [entryBudget] using lay.h0
      r0 := by simpa [entryBudget] using lay.r0
      rlt := by simpa [entryBudget] using lay.rlt
      n_eq := by simpa [entryModel, entryBudget] using lay.n_eq
      k_le := by simpa [entryModel] using lay.k_le
      gap_eq := by simpa [entryModel, entryBudget] using lay.gap
      side :=
        { h0H := by rw [hsizeH]; decide
          h0D := by rw [hsizeD]; decide
          h1H := by rw [hsizeH]; decide
          h1D := by rw [hsizeD]; decide
          h4H := by rw [hsizeH]; decide
          h4D := by rw [hsizeD]; decide
          home0 := by
            simpa [entryBudget] using
              tally_side_home t xs sat hR 0 (by decide) (by decide) (by decide)
          held0 := by
            simpa [entryBudget] using
              tally_side_held t xs sat hR 0 (by decide) (by decide) (by decide)
          home1 := by
            simpa [entryBudget] using
              tally_side_home t xs sat hR 1 (by decide) (by decide) (by decide)
          held1 := by
            simpa [entryBudget] using
              tally_side_held t xs sat hR 1 (by decide) (by decide) (by decide)
          home4 := by
            simpa [entryBudget] using
              tally_side_home t xs sat hR 4 (by decide) (by decide) (by decide)
          held4 := by
            simpa [entryBudget] using
              tally_side_held t xs sat hR 4 (by decide) (by decide) (by decide) }
      quiet :=
        { szH := hsizeH
          szD := hsizeD
          tier := by rw [tally_emb t xs sat hR]; rfl
          marker := by
            simp [tallyBoard, gapBoard, bumpedBoard, bumpOp, bottomBoard, builtBoard,
              midBoard, placed, blankOf, entryBudget]
          mx := by
            simp [tallyBoard, gapBoard, bumpedBoard, bumpOp, bottomBoard, builtBoard,
              midBoard, placed, blankOf, entryBudget] }
      park := entry_park t hOk xs hx sat hR lay
      peg := entry_peg t hOk xs hx htri sat hR lay }

theorem entry_ops_slot (t : Spec.Tier) (xs : List Nat) (sat : TierSat t) (hR : 0 < tierR t)
    (i : Nat) (hi : i < (tallyBoard t xs sat hR).sudo_5Board_4cost.sudo_5Costs_3ops.size) :
    ∃ c : Nat,
      (tallyBoard t xs sat hR).sudo_5Board_4cost.sudo_5Costs_3ops[i]'hi = (c : Int) ∧
        c ≤ 1 := by
  have harr := tally_ops_arr t xs sat hR
  rw [idx_get harr i hi]
  by_cases h2 : i = 2
  · subst h2
    refine ⟨1, ?_, ?_⟩
    · rw [Array.getElem_set, if_pos rfl]
      simp [ofNat_eq_natCast]
    · omega
  · refine ⟨0, ?_, ?_⟩
    · rw [Array.getElem_set, if_neg (Ne.symm h2)]
      simp [Array.getElem_mkArray]
    · omega

/-- `ClimbInvK` on the tally board, before any rung. Reservations are the
    counters already on that board, and `done.length = 0`. -/
theorem entry_climbInv (t : Spec.Tier) (hOk : BoardOk t) (xs : List Nat)
    (hx : xs.length = t.n) (htri : allTritList xs) (sat : TierSat t)
    (hR : 0 < tierR t) (lay : TierShape t) :
    ClimbInvK [] (tierClimb t) (tallyBoard t xs sat hR) (entryModel t xs)
      (entryBudget t hOk xs hx sat hR lay) := by
  refine
    { inv := entry_inv t xs sat hR
      idx := by simp [entryModel]
      hn := by simp [entryModel, entryBudget]
      hbench := by simp [entryModel, entryBudget]
      htally0 := by simp [entryModel, entryBudget, climbTallyPrefix]
      kLe := by
        simp [entryBudget]
        unfold tierClimb tierR
        rw [List.length_reverse]
        exact Nat.le_refl _
      shape := entry_shape t hOk xs hx htri sat hR lay
      moves := by
        refine ⟨pegCount xs + pegCount xs, ?_, ?_⟩
        · simpa [entryBudget] using tally_moves t xs sat hR
        · simp [entryModel, entryBudget]
      slides := by
        refine ⟨0, ?_, ?_⟩
        · have hplain := tally_plain t xs sat hR
          rcases hplain with ⟨-, -, -, -, hslides, -, -, -, -, -⟩
          simp [entryBudget, hslides]
        · simp [entryModel, entryBudget]
      ops := by
        intro i hi
        obtain ⟨c, hc, hle⟩ := entry_ops_slot t xs sat hR i hi
        refine ⟨c, hc, ?_⟩
        simp [entryModel, entryBudget]
        omega
      peak := by
        refine ⟨2, ?_, ?_⟩
        · simpa [entryBudget] using tally_peak t xs sat hR
        · simp [entryBudget]
          omega
      highTop := by
        show (entryModel t xs).high =
          max (entryBudget t hOk xs hx sat hR lay).high0
            ((entryModel t xs).t0 + (entryModel t xs).tally - 1)
        simp [entryModel, entryBudget, Nat.max_eq_right (Nat.zero_le _)]
      parkBelow := by
        simp [entryModel]
        unfold tallyOrigin
        omega
      holeBelow := by
        simp [entryModel, entryBudget, climbAt]
        unfold tallyOrigin
        omega
      fromBelow := by
        intro h
        simp [entryModel] at h
      finalLe := by
        simpa [entryModel, entryBudget] using climbTally_ge 1 (tierClimb t)
      tailFit := by
        have hpre : tallyPrefixesLe 1 (rowRoom t) (tierClimb t ++ []) = true := by
          simpa using sat.prefixes
        have hct : climbTally 1 (tierClimb t) ≤ rowRoom t := by
          rw [← climbTallyPrefix_full]
          exact tallyPrefixesLe_spec 1 (rowRoom t) (tierClimb t) [] hpre
        simp [entryModel, entryBudget, entry_row_len]
        have hor := sat.origin_le
        unfold rowRoom at hct
        omega
      tailZero := by
        intro k hk1 _ hix
        have hlt : tallyOrigin t < tallyOrigin t + k := by
          simp [entryModel] at hk1
          omega
        simpa [entryModel] using entry_past t (tallyOrigin t + k) hlt hix
      openRoom := by
        intro h2
        have hroom := entry_double_room t sat h2
        simpa [entryModel, entryBudget] using hroom
      openZero := by
        intro _ k hk hix
        have hk0 : k = 0 := by
          simp [entryModel] at hk
          omega
        subst hk0
        have hix' : tallyOrigin t + 1 < (entryRow t).length := by
          simpa [entryModel] using hix
        have hpast := entry_past t (tallyOrigin t + 1) (by omega) hix'
        simpa [entryModel] using hpast
      tmaxLt := by
        refine ⟨1, ?_, ?_⟩
        · simp [tallyBoard]
        · intro _
          simp [entryModel]
      ctrlLe := by simp [entryModel, entryBudget]
      srcAbove := by
        intro h
        simp [entryModel] at h }

/-- Park sits on the cell just after the ladder: `ladder0 + R`. -/
theorem entry_park_top (t : Spec.Tier) (hOk : BoardOk t) (xs : List Nat)
    (hx : xs.length = t.n) (sat : TierSat t) (hR : 0 < tierR t) (lay : TierShape t) :
    (entryModel t xs).parkAt =
      (entryBudget t hOk xs hx sat hR lay).ladder0 +
        (entryBudget t hOk xs hx sat hR lay).R := by
  simp [entryModel, entryBudget]

theorem entry_cap (t : Spec.Tier) (hOk : BoardOk t) (xs : List Nat)
    (hx : xs.length = t.n) (sat : TierSat t) (hR : 0 < tierR t) (lay : TierShape t)
    (done rest : List Nat) (hsplit : tierClimb t = done ++ rest) :
    climbTallyPrefix (entryBudget t hOk xs hx sat hR lay).tally0 done rest ≤
      (entryBudget t hOk xs hx sat hR lay).mMax := by
  simpa [entryBudget] using tallyPrefixesLe_spec 1 (rowRoom t) done rest
    (by simpa [hsplit] using sat.prefixes)

/-- The loop predicate at index 0 on the tally board. The park hole is the
    cell just after the ladder. -/
theorem entry_climbL (t : Spec.Tier) (hOk : BoardOk t) (xs : List Nat)
    (hx : xs.length = t.n) (htri : allTritList xs) (sat : TierSat t)
    (hR : 0 < tierR t) (lay : TierShape t) :
    ∃ inv : ClimbInvL (tierClimb t) 0 (tallyBoard t xs sat hR)
        (entryBudget t hOk xs hx sat hR lay),
      inv.s.parkAt =
        (entryBudget t hOk xs hx sat hR lay).ladder0 +
          (entryBudget t hOk xs hx sat hR lay).R := by
  refine ⟨
    { done := []
      rest := tierClimb t
      s := entryModel t xs
      split := by simp
      k_eq := rfl
      inv := entry_climbInv t hOk xs hx htri sat hR lay
      ladder := tally_ladder t xs sat hR
      m_pos := by simp [entryModel]
      m_le := by
        simp [entryModel, entryBudget]
        have hL := hOk.ladder
        unfold tierR at hL
        omega
      m_len := by simp [entryModel, tallyBoard, ofNat_eq_natCast] },
    ?_⟩
  simp [entryModel, entryBudget]

/-- The emitted inverse, from the fresh input board, is the climb of the tally
    board bound into the final tail. -/
theorem invert_emit (t : Spec.Tier) (hOk : BoardOk t) (xs : List Nat)
    (hx : xs.length = t.n) (htri : allTritList xs) (sat : TierSat t)
    (hR : 0 < tierR t) (lay : TierShape t) :
    Ecbs.invert (bottomBoard t xs) ((2 : Nat) : Int) =
      climbEmit (climbStepBoard ((2 : Nat) : Int)) (tallyBoard t xs sat hR)
        (tierClimb t) >>= finalTail := by
  rw [invert_steps (bottomBoard t xs) ((2 : Nat) : Int),
    invertWith_named_loop (bottomBoard t xs) ((2 : Nat) : Int)]
  have hbump := bump_bottom t xs
  have hcopy := copy_gap_board t hOk xs hx
  have htally := tally_board_run t hOk xs sat hR
  suffices
      (do
        let b ← (do
          let ix := Ecbs.op_inv
          let t1 ← SudoRt.atL (bottomBoard t xs).sudo_5Board_4cost.sudo_5Costs_3ops ix
          let t2 ← SudoRt.addI t1 (1 : Int)
          let t3 ← SudoRt.putL (bottomBoard t xs).sudo_5Board_4cost.sudo_5Costs_3ops ix t2
          pure ({ bottomBoard t xs with sudo_5Board_4cost :=
            { (bottomBoard t xs).sudo_5Board_4cost with sudo_5Costs_3ops := t3 } }))
        let b ← Ecbs.copy_band b Ecbs.gap ((2 : Nat) : Int) false
        let b ← Ecbs.tally_start b
        let nr := SudoRt.listLen b.sudo_5Board_6ladder
        let toV ← SudoRt.subI nr (1 : Int)
        let fromV := (0 : Int)
        let fuel : Nat := if fromV > toV then 1 else (toV - fromV).natAbs + 1
        let out ← SudoRt.runLoopOn (ρ := Ecbs.Board) (fromV, b) fuel
          (invertIdx ((2 : Nat) : Int) nr toV)
          (fun σ => finalTail σ.2)
          (fun r => pure r)
        pure out) =
      climbEmit (climbStepBoard ((2 : Nat) : Int)) (tallyBoard t xs sat hR)
        (tierClimb t) >>= finalTail by
    simpa using this
  rw [hbump, ok_bind, hcopy, ok_bind, htally, ok_bind]
  obtain ⟨invL, hpark⟩ := entry_climbL t hOk xs hx htri sat hR lay
  have hpos : 0 < (tierClimb t).length := by
    simpa [tierClimb, List.length_reverse, tierR] using hR
  have hfit : FitsLen (tierClimb t).length := by
    simpa [tierClimb, List.length_reverse, tierR] using tierR_fit t hOk
  have hxLen : (entryBudget t hOk xs hx sat hR lay).x.length =
      (entryBudget t hOk xs hx sat hR lay).n := by
    simpa [entryBudget] using hx
  have hxT : allTritList (entryBudget t hOk xs hx sat hR lay).x := by
    simpa [entryBudget] using htri
  simpa [entryBudget] using
    invertWith_on_inv invL hpos hfit hpark
      (entry_cap t hOk xs hx sat hR lay) hxLen hxT

/-- After the ladder the gap and the tally are `invClimb` of the input, and the
    rest of `invert` is the final tail on that board. -/
theorem invert_climbed (t : Spec.Tier) (hOk : BoardOk t) (xs : List Nat)
    (hx : xs.length = t.n) (htri : allTritList xs) (sat : TierSat t)
    (hR : 0 < tierR t) (lay : TierShape t) :
    ∃ b' s',
      Ecbs.invert (bottomBoard t xs) ((2 : Nat) : Int) = finalTail b' ∧
      (s'.gap, s'.tally) =
        invClimb t.n t.k t.benchlen xs (xs, 1) (tierClimb t) ∧
      ClimbInvK (tierClimb t) [] b' s' (entryBudget t hOk xs hx sat hR lay) := by
  have hem := invert_emit t hOk xs hx htri sat hR lay
  have hxLen : (entryBudget t hOk xs hx sat hR lay).x.length =
      (entryBudget t hOk xs hx sat hR lay).n := by
    simpa [entryBudget] using hx
  have hxT : allTritList (entryBudget t hOk xs hx sat hR lay).x := by
    simpa [entryBudget] using htri
  obtain ⟨b', s', hrun, _, hK, hgap, _⟩ := climb_refines_emit (tierClimb t)
      (tallyBoard t xs sat hR) (entryModel t xs)
      (entryBudget t hOk xs hx sat hR lay)
      (entry_climbInv t hOk xs hx htri sat hR lay)
      (entry_park_top t hOk xs hx sat hR lay)
      (by simp [entryModel])
      (entry_cap t hOk xs hx sat hR lay) hxLen hxT
  have hrun' :
      climbEmit (climbStepBoard ((2 : Nat) : Int)) (tallyBoard t xs sat hR) (tierClimb t) =
        .ok b' := by
    simpa [entryBudget] using hrun
  refine ⟨b', s', ?_, ?_, hK⟩
  · rw [hem, hrun', ok_bind]
  · simpa [entryModel, entryBudget] using hgap

/-- The emitted inverse returns a board. -/
theorem invert_ok (t : Spec.Tier) (hOk : BoardOk t) (xs : List Nat)
    (hx : xs.length = t.n) (htri : allTritList xs) (sat : TierSat t)
    (hR : 0 < tierR t) (lay : TierShape t) :
    ∃ bZ, Ecbs.invert (bottomBoard t xs) ((2 : Nat) : Int) = .ok bZ := by
  have hem := invert_emit t hOk xs hx htri sat hR lay
  have hpos : 0 < (tierClimb t).length := by
    simpa [tierClimb, List.length_reverse, tierR] using hR
  have hxLen : (entryBudget t hOk xs hx sat hR lay).x.length =
      (entryBudget t hOk xs hx sat hR lay).n := by
    simpa [entryBudget] using hx
  have hxT : allTritList (entryBudget t hOk xs hx sat hR lay).x := by
    simpa [entryBudget] using htri
  obtain ⟨bZ, hrun⟩ := climb_then_tail
      (entry_climbInv t hOk xs hx htri sat hR lay) hpos
      (entry_park_top t hOk xs hx sat hR lay)
      (by simp [entryModel])
      (entry_cap t hOk xs hx sat hR lay) hxLen hxT
  exact ⟨bZ, hem.trans hrun⟩

theorem modelClimb_params (s : ClimbModel) (x : List Nat)
    (hole : ClimbModel → Nat → Bool → Nat) (rs : List Nat) :
    (modelClimb s x hole rs).n = s.n ∧
      (modelClimb s x hole rs).k = s.k ∧
      (modelClimb s x hole rs).benchlen = s.benchlen := by
  induction rs generalizing s with
  | nil => simp [modelClimb]
  | cons r rs ih =>
      rw [modelClimb]
      simpa [modelRung] using
        ih (modelRung s x r (hole s r rs.isEmpty) rs.isEmpty)

/-- A climb that starts from a positive tally stays positive. -/
theorem invClimb_tally_pos (n k bench : Nat) (x g : List Nat) (tally : Nat)
    (rs : List Nat) (ht : 0 < tally) :
    0 < (invClimb n k bench x (g, tally) rs).2 := by
  induction rs generalizing g tally with
  | nil => simpa [invClimb] using ht
  | cons r rs ih =>
      simp only [invClimb]
      exact ih (invRung n k bench x g tally r rs.isEmpty).1
        (invRung n k bench x g tally r rs.isEmpty).2
        (by
          rw [invRung_tally]
          exact Nat.lt_of_lt_of_le ht (tallyAfter_ge tally r rs.isEmpty))

/-- Home 5 after `invert` is the field cube of the climbed input. That list is
    `invGap` before the hole-0 check. -/
theorem invert_gap (t : Spec.Tier) (hOk : BoardOk t) (xs : List Nat)
    (hx : xs.length = t.n) (htri : allTritList xs) (sat : TierSat t)
    (hR : 0 < tierR t) (lay : TierShape t) :
    ∃ (bZ : Ecbs.Board) (h5 : 5 < bZ.sudo_5Board_4home.size),
      Ecbs.invert (bottomBoard t xs) ((2 : Nat) : Int) = .ok bZ ∧
      bZ.sudo_5Board_4home[5]'h5 =
        embed (fieldCube t.n t.k t.benchlen
          (invClimb t.n t.k t.benchlen xs (xs, 1) (tierClimb t)).1) := by
  have hem := invert_emit t hOk xs hx htri sat hR lay
  have hxLen : (entryBudget t hOk xs hx sat hR lay).x.length =
      (entryBudget t hOk xs hx sat hR lay).n := by
    simpa [entryBudget] using hx
  have hxT : allTritList (entryBudget t hOk xs hx sat hR lay).x := by
    simpa [entryBudget] using htri
  obtain ⟨b', s', hrun, hs', hK, hgap, htmax⟩ := climb_refines_emit (tierClimb t)
      (tallyBoard t xs sat hR) (entryModel t xs)
      (entryBudget t hOk xs hx sat hR lay)
      (entry_climbInv t hOk xs hx htri sat hR lay)
      (entry_park_top t hOk xs hx sat hR lay)
      (by simp [entryModel])
      (entry_cap t hOk xs hx sat hR lay) hxLen hxT
  have hpos : 0 < (tierClimb t).length := by
    simpa [tierClimb, List.length_reverse, tierR] using hR
  cases hL : tierClimb t with
  | nil => simp [hL] at hpos
  | cons r rs =>
      let hole : ClimbModel → Nat → Bool → Nat :=
        fun s _ _ =>
          climbAt (entryBudget t hOk xs hx sat hR lay).ladder0
            (entryBudget t hOk xs hx sat hR lay).R s.ridx
      let x := (entryBudget t hOk xs hx sat hR lay).x
      have hon : s'.onBench = true := by
        rw [hs', hL]
        exact modelClimb_onBench (entryModel t xs) x hole r rs
      have hge : 0 ≤ s'.fromHole := by
        rw [hs', hL]
        exact modelClimb_fromHole (entryModel t xs) x hole r rs
      have hm : 0 < s'.tally := by
        rw [hs', modelClimb_tally]
        simp [entryModel]
        exact Nat.lt_of_lt_of_le (by decide : (0 : Nat) < 1)
          (climbTally_ge 1 (tierClimb t))
      obtain ⟨bU, bC, bOut, bZ, hun, hc, hset, hz, hhome⟩ :=
        final_cube_home hK hon hge htmax hm
      have hrun' :
          climbEmit (climbStepBoard ((2 : Nat) : Int)) (tallyBoard t xs sat hR)
              (tierClimb t) =
            .ok b' := by
        simpa [entryBudget] using hrun
      have hok : Ecbs.invert (bottomBoard t xs) ((2 : Nat) : Int) = .ok bZ := by
        rw [hem, hrun', ok_bind]
        simp [finalTail, hun, hc, hset, hz, ok_bind]
      have hlay := modelClimb_params (entryModel t xs) x hole (tierClimb t)
      have hpair : (s'.gap, s'.tally) =
          invClimb t.n t.k t.benchlen xs (xs, 1) (tierClimb t) := by
        simpa [entryModel, entryBudget] using hgap
      have hgap1 : s'.gap =
          (invClimb t.n t.k t.benchlen xs (xs, 1) (tierClimb t)).1 :=
        congrArg Prod.fst hpair
      have hn : s'.n = t.n := by
        rw [hs']
        simpa [entryModel] using hlay.1
      have hk : s'.k = t.k := by
        rw [hs']
        simpa [entryModel] using hlay.2.1
      have hb : s'.benchlen = t.benchlen := by
        rw [hs']
        simpa [entryModel] using hlay.2.2
      refine ⟨bZ, hhome.h5, hok, ?_⟩
      rw [← hL]
      refine hhome.arr.trans (congrArg embed ?_)
      rw [hn, hk, hb, hgap1]

/-- `invGap` is that field cube. It is the list `fieldInv` checks, before the
    hole-0 test and the optional mirror. -/
theorem invGap_cube (t : Spec.Tier) (xs : List Nat) :
    invGap t.n t.k t.benchlen xs =
      fieldCube t.n t.k t.benchlen
        (invClimb t.n t.k t.benchlen xs (xs, 1) (tierClimb t)).1 := by
  simp [invGap, tierClimb]

/-- `fieldCube` keeps the first `n` holes of a bench-length strip. -/
theorem fieldCube_length (n k bench : Nat) (x : List Nat) (hn : n ≤ bench) :
    (fieldCube n k bench x).length = n := by
  unfold fieldCube
  change ((laneFold n (n - k) (combStrip n bench x)).take n).length = n
  rw [List.length_take]
  have hfold :=
    laneFold_length n (n - k) (combStrip n bench x) (by rw [combStrip_length]; exact hn)
  rw [hfold, combStrip_length]
  omega

/-- Cubing writes trits when the comb reaches, and `k ≤ n` so the fold gap fits. -/
theorem fieldCube_trits (n k bench : Nat) (x : List Nat)
    (hxs : allTritList x) (hspan : 3 * (n - 1) < bench) (hk : k ≤ n) :
    allTritList (fieldCube n k bench x) := by
  have hn : n ≤ bench := by omega
  have hcs := combStrip_trits x n bench hxs hspan
  have hnb : n ≤ (combStrip n bench x).length := by
    rw [combStrip_length]; exact hn
  have hlf := laneFold_trits n (n - k) (combStrip n bench x) hcs (by omega) hnb
  simpa [fieldCube, laneFold] using allTritList_take hlf n

/-- Home 5 after `invert` is `invGap` of the input. -/
theorem invert_invGap (t : Spec.Tier) (hOk : BoardOk t) (xs : List Nat)
    (hx : xs.length = t.n) (htri : allTritList xs) (sat : TierSat t)
    (hR : 0 < tierR t) (lay : TierShape t) :
    ∃ (bZ : Ecbs.Board) (h5 : 5 < bZ.sudo_5Board_4home.size),
      Ecbs.invert (bottomBoard t xs) ((2 : Nat) : Int) = .ok bZ ∧
      bZ.sudo_5Board_4home[5]'h5 = embed (invGap t.n t.k t.benchlen xs) := by
  obtain ⟨bZ, h5, hok, harr⟩ := invert_gap t hOk xs hx htri sat hR lay
  refine ⟨bZ, h5, hok, ?_⟩
  simp [invGap, tierClimb]
  exact harr

/-- Settled gap, the check-multiply frame, and the four tail steps, from one run. -/
theorem final_cube_both
    {done : List Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvK done [] b s base) (hon : s.onBench = true) (hge : 0 ≤ s.fromHole)
    (ht : s.tally ≤ base.mMax) (hm : 0 < s.tally) :
    ∃ (bU bC bOut bZ : Ecbs.Board),
      Ecbs.unpark_rung b = .ok bU ∧
      Ecbs.cube bU Ecbs.gap Ecbs.gap = .ok bC ∧
      Ecbs.settle bC = .ok bOut ∧
      Ecbs.tally_clear bOut = .ok bZ ∧
      SettledHome bZ (fieldCube s.n s.k s.benchlen s.gap) ∧
      CheckRead b bZ ∧
      SideKeep bZ base ∧
      QuietKeep bZ base ∧
      PostCubeBound bZ base ∧
      bZ.sudo_5Board_4cost.sudo_5Costs_15control_highest = (s.high : Int) :=
  Exists.elim (final_cube_settle h hon hge ht hm) fun bU p1 =>
  Exists.elim p1 fun bC p2 =>
  Exists.elim p2 fun bOut p3 =>
  Exists.elim p3 fun bZ p4 =>
  Exists.elim p4 fun _mv p5 =>
  Exists.elim p5 fun _sl p6 =>
  Exists.elim p6 fun _row hpack =>
    ⟨bU, bC, bOut, bZ, hpack.1, hpack.2.1, hpack.2.2.1, hpack.2.2.2.1,
      hpack.2.2.2.2.2.2.2.2.2.2.2.2.1,
      hpack.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      hpack.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      hpack.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      hpack.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      hpack.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-- The check multiply: home 5 holds `invGap`, home 2 still holds the input,
    and `Ecbs.mul` with the export flags is `fieldMul` of that pair. -/
theorem check_mul (t : Spec.Tier) (hOk : BoardOk t) (xs : List Nat)
    (hx : xs.length = t.n) (htri : allTritList xs) (sat : TierSat t)
    (hR : 0 < tierR t) (lay : TierShape t) :
    ∃ (bZ bM bR : Ecbs.Board) (v : Array Int) (h5 : 5 < bR.sudo_5Board_4home.size),
      Ecbs.invert (bottomBoard t xs) ((2 : Nat) : Int) = .ok bZ ∧
      Ecbs.mul bZ Ecbs.check_target Ecbs.gap ((2 : Nat) : Int) true false false = .ok bM ∧
      Ecbs.bench_read_and_clear bM = .ok (v, bR) ∧
      v = embed (fieldMul t.n t.k t.benchlen (invGap t.n t.k t.benchlen xs) xs) ∧
      bR.sudo_5Board_4home[5]'h5 = embed (invGap t.n t.k t.benchlen xs) ∧
      bR.sudo_5Board_8bench_on = false ∧
      (∃ (h5D : 5 < bR.sudo_5Board_4held.size) (mv : Nat),
        bR.sudo_5Board_4held[5]'h5D = true ∧
        bR.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int) ∧
        FitsLen (mv + t.n) ∧
        bR.sudo_5Board_1t.sudo_4Tier_1n = (t.n : Int)) ∧
      (laneFold t.n (t.n - t.k)
          (school t.n (invGap t.n t.k t.benchlen xs) xs (List.replicate t.benchlen 0) false)).take
        t.n = fieldMul t.n t.k t.benchlen (invGap t.n t.k t.benchlen xs) xs := by
  have hem := invert_emit t hOk xs hx htri sat hR lay
  have hxLen : (entryBudget t hOk xs hx sat hR lay).x.length =
      (entryBudget t hOk xs hx sat hR lay).n := by simpa [entryBudget] using hx
  have hxT : allTritList (entryBudget t hOk xs hx sat hR lay).x := by
    simpa [entryBudget] using htri
  obtain ⟨b', s', hrun, hs', hK, hgap, htmax⟩ := climb_refines_emit (tierClimb t)
      (tallyBoard t xs sat hR) (entryModel t xs) (entryBudget t hOk xs hx sat hR lay)
      (entry_climbInv t hOk xs hx htri sat hR lay)
      (entry_park_top t hOk xs hx sat hR lay) (by simp [entryModel])
      (entry_cap t hOk xs hx sat hR lay) hxLen hxT
  have hpos : 0 < (tierClimb t).length := by
    simpa [tierClimb, List.length_reverse, tierR] using hR
  cases hL : tierClimb t with
  | nil => simp [hL] at hpos
  | cons r rs =>
      let hole : ClimbModel → Nat → Bool → Nat := fun s _ _ =>
        climbAt (entryBudget t hOk xs hx sat hR lay).ladder0
          (entryBudget t hOk xs hx sat hR lay).R s.ridx
      let x := (entryBudget t hOk xs hx sat hR lay).x
      have hon : s'.onBench = true := by
        rw [hs', hL]; exact modelClimb_onBench (entryModel t xs) x hole r rs
      have hge : 0 ≤ s'.fromHole := by
        rw [hs', hL]; exact modelClimb_fromHole (entryModel t xs) x hole r rs
      have hm : 0 < s'.tally := by
        rw [hs', modelClimb_tally]; simp [entryModel]
        exact Nat.lt_of_lt_of_le (by decide : (0 : Nat) < 1) (climbTally_ge 1 (tierClimb t))
      obtain ⟨bU, bC, bOut, bZ, hun, hc, hset, hz, hsg, hread, _hside, _hquiet, _hbound, _hhigh⟩ :=
        final_cube_both hK hon hge htmax hm
      have hrun' : climbEmit (climbStepBoard ((2 : Nat) : Int)) (tallyBoard t xs sat hR)
          (tierClimb t) = .ok b' := by simpa [entryBudget] using hrun
      have hok : Ecbs.invert (bottomBoard t xs) ((2 : Nat) : Int) = .ok bZ := by
        rw [hem, hrun', ok_bind]
        simp [finalTail, hun, hc, hset, hz, ok_bind]
      have hlay := modelClimb_params (entryModel t xs) x hole (tierClimb t)
      have hn : s'.n = t.n := by rw [hs']; simpa [entryModel] using hlay.1
      have hkS : s'.k = t.k := by rw [hs']; simpa [entryModel] using hlay.2.1
      have hbL : s'.benchlen = t.benchlen := by rw [hs']; simpa [entryModel] using hlay.2.2
      have hpair : (s'.gap, s'.tally) =
          invClimb t.n t.k t.benchlen xs (xs, 1) (tierClimb t) := by
        simpa [entryModel, entryBudget] using hgap
      have hgap1 : s'.gap = (invClimb t.n t.k t.benchlen xs (xs, 1) (tierClimb t)).1 :=
        congrArg Prod.fst hpair
      have hcube : fieldCube s'.n s'.k s'.benchlen s'.gap =
          invGap t.n t.k t.benchlen xs := by
        rw [hn, hkS, hbL, hgap1]
        exact (invGap_cube t xs).symm
      have hArr : bZ.sudo_5Board_4home[5]'hsg.h5 = embed (invGap t.n t.k t.benchlen xs) := by
        exact hsg.arr.trans (congrArg embed hcube)
      let mv := hread.moves.choose
      have hmv := hread.moves.choose_spec
      let pk := hread.peak.choose
      have hpk := hread.peak.choose_spec
      let pS := hread.peakS.choose
      have hpS := hread.peakS.choose_spec
      let cOps := hread.ops0.choose
      have hcOps := hread.ops0.choose_spec
      let holeN := hread.hole.choose
      have hholeN := hread.hole.choose_spec
      let mvB := hread.fitMul.choose
      have hB1 := hread.fitMul.choose_spec
      let nB := hB1.choose
      have hB2 := hB1.choose_spec
      let benchB := hB2.choose
      have hB3 := hB2.choose_spec
      have hmvB : bZ.sudo_5Board_4cost.sudo_5Costs_5moves = (mvB : Int) := hB3.1
      have hnB : bZ.sudo_5Board_1t.sudo_4Tier_1n = (nB : Int) := hB3.2.1
      have hbB : bZ.sudo_5Board_1t.sudo_4Tier_8benchlen = (benchB : Int) := hB3.2.2.1
      have hfitB : FitsLen (mvB + nB + nB * (nB + 1) + 3 * (benchB - nB) + 2 * nB) :=
        hB3.2.2.2
      have hmvEq : mv = mvB := by
        apply Int.ofNat.inj
        rw [ofNat_eq_natCast, ofNat_eq_natCast]
        exact hmv.symm.trans hmvB
      have hnEq : nB = t.n := by
        apply Int.ofNat.inj
        rw [ofNat_eq_natCast, ofNat_eq_natCast]
        have htn : bZ.sudo_5Board_1t.sudo_4Tier_1n = (t.n : Int) := by
          rw [hread.tierEq, hK.shape.tierN, hn]
        exact hnB.symm.trans htn
      have hbEq : benchB = t.benchlen := by
        apply Int.ofNat.inj
        rw [ofNat_eq_natCast, ofNat_eq_natCast]
        have htb : bZ.sudo_5Board_1t.sudo_4Tier_8benchlen = (t.benchlen : Int) := by
          rw [hread.tierEq, hK.shape.tierB, hbL]
        exact hbB.symm.trans htb
      have hfitBig : FitsLen (mv + t.n + t.n * (t.n + 1) + 3 * (t.benchlen - t.n) +
          2 * t.n) := by
        rw [← hmvEq, hnEq, hbEq] at hfitB
        exact hfitB
      have hpeg : pegCount xs ≤ t.n := by
        rw [← hx]
        exact pegCount_le xs
      have hmul := mul_refines bZ 7 5 2 (invGap t.n t.k t.benchlen xs) xs t.w t.h t.r t.n t.k mv holeN t.benchlen pk pS cOps hread.marker hread.benchOff hread.opsGt hcOps.1 hcOps.2 (by rw [hread.tierEq]; simpa [hbL] using hK.shape.tierB) hread.h5D hsg.h5 hread.held5 hArr hread.h2D hread.h2H (by
            have hheld : b'.sudo_5Board_4held[2]'hread.h2D0 = true := by
              simpa [entryBudget] using hK.shape.xHeld
            exact hread.held2.trans hheld) (by
            have hhome : b'.sudo_5Board_4home[2]'hread.h2H0 = embed xs := by
              simpa [entryBudget] using hK.shape.xArr
            exact hread.home2.trans hhome) hread.spareD hread.spareH hread.spareE hread.h7 (by decide) (by decide) (by simpa [hn] using hK.shape.peg.n_pos) (by rw [hread.tierEq]; simpa [hn] using hK.shape.tierN) (by
            rw [invGap_cube]
            exact fieldCube_length t.n t.k t.benchlen
              (invClimb t.n t.k t.benchlen xs (xs, 1) (tierClimb t)).1
              (by
                have hs := sat.mul_span
                omega)) hx (by simpa [hn] using hK.shape.peg.fitN) hmv hpk hpS (by
            apply FitsLen.of_le hfitBig
            omega) sat.mul_span (by
            have hsp : 3 * (s'.n - 1) < s'.benchlen := by
              have hs := hK.shape.peg.span
              omega
            have htriG := fieldCube_trits s'.n s'.k s'.benchlen s'.gap
              hK.shape.peg.trits hsp hK.shape.k_le
            rw [hcube] at htriG
            exact htriG) (by
            apply FitsLen.of_le (by simpa [hn] using hK.shape.peg.fit3)
            omega) (by
            apply FitsLen.of_le hfitBig
            omega) ⟨lay.w0, lay.h0, lay.rlt, lay.r0, lay.n_eq, lay.k_le, lay.gap⟩ (by rw [hread.tierEq]; simpa using hK.shape.tierW) (by rw [hread.tierEq]; simpa using hK.shape.tierH) (by rw [hread.tierEq]; simpa using hK.shape.tierR) (by rw [hread.tierEq]; simpa [hkS] using hK.shape.tierK) (by rw [hholeN, ofNat_eq_natCast]) (by simpa [hbL] using hK.shape.peg.small) (by simpa [hn] using hK.shape.peg.n_small) (by simpa [hbL] using hK.shape.peg.fitBn) (by
            apply FitsLen.of_le hfitBig
            omega)
      obtain ⟨bM, hmulOk, hon, -, hbench, htake, hrest⟩ := hmul
      obtain ⟨-, hmov, -, -, htM, hsz, hheld, h5keep, _hframe, _hmk, _hops, _hstrict, _hhole⟩ := hrest
      have h5M : 5 < bM.sudo_5Board_4home.size := by
        rw [hsz]; exact hsg.h5
      have hhomeM : bM.sudo_5Board_4home[5]'h5M = embed (invGap t.n t.k t.benchlen xs) :=
        (h5keep hsg.h5 h5M).trans hArr
      let gapL := invGap t.n t.k t.benchlen xs
      let lane := laneFold t.n (t.n - t.k)
        (school t.n gapL xs (List.replicate t.benchlen 0) false)
      have htakeL : lane.take t.n = fieldMul t.n t.k t.benchlen gapL xs := by
        simpa [lane, gapL, invGap] using htake
      have hlenSch : (school t.n gapL xs (List.replicate t.benchlen 0) false).length =
          t.benchlen := by
        rw [school_length, List.length_replicate]
      have hlenL : lane.length = t.benchlen := by
        rw [laneFold_length, hlenSch]
        · rw [hlenSch]
          have hs := sat.mul_span
          omega
      have hnle : t.n ≤ lane.length := by
        rw [hlenL]
        have hs := sat.mul_span
        omega
      have hpref := prefix_refines lane t.n hnle (by simpa [hn] using hK.shape.peg.fitN)
      have hszV : (embed (lane.take t.n)).size = t.n := by
        rw [size_embed, List.length_take, hlenL]
        have hs := sat.mul_span
        omega
      have hnp := npeg_refines (embed (lane.take t.n)) (by
        rw [hszV]
        simpa [hn] using hK.shape.peg.fitN)
      let mvM := mulMoves mv gapL xs t.n t.k t.benchlen
      have hmvM : bM.sudo_5Board_4cost.sudo_5Costs_5moves = (mvM : Int) := by
        simpa [mvM, gapL, ofNat_eq_natCast] using hmov
      let nz := nnz (embed (lane.take t.n)).toList
      have hnz : nz ≤ t.n := by
        have hle := nnz_length_le (embed (lane.take t.n)).toList
        rw [toList_embed, List.length_map] at hle
        exact Nat.le_trans hle (List.length_take_le t.n lane)
      have hschool : schoolMoves gapL xs t.n t.n ≤ t.n * (t.n + 1) :=
        schoolMoves_bound gapL xs t.n
      have hfoldC : foldCharge t.n (t.n - t.k)
          (school t.n gapL xs (List.replicate t.benchlen 0) false) ≤
          3 * (t.benchlen - t.n) := by
        have hF := foldCharge_bound t.n (t.n - t.k)
          (school t.n gapL xs (List.replicate t.benchlen 0) false)
        rw [hlenSch] at hF
        exact hF
      have hpegY : pegCount xs ≤ t.n := hpeg
      have hmvLe : mvM + nz ≤ mv + t.n + t.n * (t.n + 1) + 3 * (t.benchlen - t.n) +
          2 * t.n := by
        have hdef : mvM = mv + pegCount xs + schoolMoves gapL xs t.n t.n +
            foldCharge t.n (t.n - t.k)
              (school t.n gapL xs (List.replicate t.benchlen 0) false) := rfl
        omega
      have hfitM : FitsLen (mvM + nz) := FitsLen.of_le hfitBig hmvLe
      have hnT : bM.sudo_5Board_1t.sudo_4Tier_1n = (t.n : Int) := by
        rw [htM, hread.tierEq, hK.shape.tierN, hn]
      let bR := { { bM with sudo_5Board_4cost :=
        { bM.sudo_5Board_4cost with sudo_5Costs_5moves := Int.ofNat (mvM + nz) } }
          with sudo_5Board_8bench_on := false }
      have hreadM : Ecbs.bench_read_and_clear bM = .ok (embed (lane.take t.n), bR) := by
        unfold Ecbs.bench_read_and_clear
        rw [hbench, hnT, ← ofNat_eq_natCast t.n]
        rw [hpref, ok_bind]
        conv => zeta
        rw [hnp, ok_bind]
        conv => zeta
        rw [hmvM]
        rw [← ofNat_eq_natCast mvM]
        have hzn : nnz (embed (lane.take t.n)).toList = nz := rfl
        rw [hzn, addI_ofNat mvM nz hfitM, ok_bind]
        simp only [pure_eq_ok, bR, hbench]
      have h5R : 5 < bR.sudo_5Board_4home.size := by
        simpa [bR] using h5M
      have hhomeR : bR.sudo_5Board_4home[5]'h5R = embed gapL := by
        have hEq : bR.sudo_5Board_4home = bM.sudo_5Board_4home := by simp [bR]
        exact cell_eq_of hEq hhomeM
      let heldInner := bZ.sudo_5Board_4held.set ⟨6, hread.spareD⟩ true
      let heldClear := heldInner.set ⟨6, by rw [Array.size_set]; exact hread.spareD⟩ false
      have hheldDef : bM.sudo_5Board_4held = heldClear := by
        simpa [heldClear, heldInner] using hheld
      have h5DM : 5 < bM.sudo_5Board_4held.size := by
        have hs := congrArg Array.size hheldDef
        rw [Array.size_set, Array.size_set] at hs
        exact hs.symm ▸ hread.h5D
      have h5DR : 5 < bR.sudo_5Board_4held.size := by
        simpa [bR] using h5DM
      have hheldR : bR.sudo_5Board_4held[5]'h5DR = true := by
        have hEq : bR.sudo_5Board_4held = bM.sudo_5Board_4held := by simp [bR]
        have hget : heldClear[5]'(by rw [Array.size_set, Array.size_set]; exact hread.h5D) =
            bZ.sudo_5Board_4held[5]'hread.h5D := by
          simp [heldClear, heldInner, Array.getElem_set, show (5 : Nat) ≠ 6 by decide]
        have hM : bM.sudo_5Board_4held[5]'h5DM = true :=
          (cell_eq_of hheldDef hget).trans hread.held5
        exact (cell_eq_of hEq hM).trans rfl
      have hmvR : bR.sudo_5Board_4cost.sudo_5Costs_5moves = ((mvM + nz : Nat) : Int) := by
        simp [bR, ofNat_eq_natCast]
      have hfitR : FitsLen (mvM + nz + t.n) := by
        apply FitsLen.of_le hfitBig
        have hdef : mvM = mv + pegCount xs + schoolMoves gapL xs t.n t.n +
            foldCharge t.n (t.n - t.k)
              (school t.n gapL xs (List.replicate t.benchlen 0) false) := rfl
        omega
      have hnR : bR.sudo_5Board_1t.sudo_4Tier_1n = (t.n : Int) := by
        simp [bR, hnT]
      refine ⟨bZ, bM, bR, embed (lane.take t.n), h5R, hok, ?_, hreadM, ?_, hhomeR, rfl,
        ⟨h5DR, mvM + nz, hheldR, hmvR, hfitR, hnR⟩, ?_⟩
      · simpa [Ecbs.check_target, Ecbs.gap] using hmulOk
      · exact congrArg embed htakeL
      · simpa [lane, gapL, invGap] using htake

end EcbsLink2.Link2
