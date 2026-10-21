/-
  The emitted climb, the tier saturation facts, and the rung that follows them.
  Split out of `Invert` so that file stays under the per-file memory line.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.RungCharge

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

attribute [local irreducible] bumpOp

/-- The emitted climb, one rung at a time. `last` is the empty tail. -/
def climbEmit (step : Ecbs.Board → Nat → Bool → Except SudoRt.Trap Ecbs.Board)
    (b : Ecbs.Board) : List Nat → Except SudoRt.Trap Ecbs.Board
  | [] => .ok b
  | r :: rs => do
      let b ← step b r rs.isEmpty
      climbEmit step b rs

/-- Running tally along a rung list, checked before every rung and on the value
    that rung leaves. `room` is how many control-row holes sit at the tally origin. -/
def tallyPrefixesLe (tally room : Nat) : List Nat → Bool
  | [] => decide (tally ≤ room)
  | r :: rs =>
    decide (tally ≤ room) &&
      tallyPrefixesLe (tallyAfter tally r rs.isEmpty) room rs

theorem tallyPrefixesLe_spec (tally room : Nat) (done rest : List Nat)
    (h : tallyPrefixesLe tally room (done ++ rest) = true) :
    climbTallyPrefix tally done rest ≤ room := by
  induction done generalizing tally rest with
  | nil =>
    simp [climbTallyPrefix]
    cases rest with
    | nil =>
      simpa [tallyPrefixesLe] using h
    | cons r rs =>
      have h' : tally ≤ room ∧
          tallyPrefixesLe (tallyAfter tally r rs.isEmpty) room rs = true := by
        simpa [tallyPrefixesLe] using h
      exact h'.1
  | cons r done ih =>
    simp [climbTallyPrefix]
    have h' : tally ≤ room ∧
        tallyPrefixesLe (tallyAfter tally r ((done ++ rest).isEmpty)) room
          (done ++ rest) = true := by
      simpa [tallyPrefixesLe, List.cons_append] using h
    exact ih (tallyAfter tally r ((done ++ rest).isEmpty)) rest h'.2

/-- How many rungs `invert` climbs on this tier. -/
def tierR (t : Spec.Tier) : Nat := (rungList (t.n - 1)).length

/-- Climb order: the ladder `new_board` stores, which is build order reversed. -/
def tierClimb (t : Spec.Tier) : List Nat := (rungList (t.n - 1)).reverse

/-- Control-row index of the first tally peg on a fresh board. `ladder0` is
    `script + 2`, the park hole is the next hole after the rungs, and tally
    starts at the hole after the park. -/
def tallyOrigin (t : Spec.Tier) : Nat := t.script + 3 + tierR t

/-- Holes left in the control row at that origin. -/
def rowRoom (t : Spec.Tier) : Nat := t.control - tallyOrigin t

/-- Geometric tally cap `(1 + 1) · 2 ^ R` for a climb that starts at length 1. -/
def geomCap (t : Spec.Tier) : Nat := (1 + 1) * 2 ^ tierR t

def tierChargeMoves (t : Spec.Tier) (m : Nat) : Nat :=
  tierR t * rungCharge t.n t.benchlen m

def tierChargeSlides (t : Spec.Tier) (m : Nat) : Nat :=
  tierR t * rungSlideCharge t.n m

def tierChargeOps (t : Spec.Tier) (m : Nat) : Nat :=
  tierR t * (m + 3)

/-- The tally and charge side of the `invert_number` domain on one tier.
    `geom_miss` is why the geometric cap is not the cap: it does not fit the
    control row. `room_fit` and `prefixes` are the tightened cap, the holes
    `BoardOk` leaves after the tally origin. The charge `FitsLen` facts hold
    at that room and, separately, at the geometric cap, so the i64 bound was
    not what failed. `cube_span` and `mul_span` are the reaches `cube_number`
    and `multiply` assert; `FieldLay` already packages the mul reach. -/
structure TierSat (t : Spec.Tier) : Prop where
  geom_miss : tallyOrigin t + geomCap t > t.control
  origin_le : tallyOrigin t ≤ t.control
  room_le_geom : rowRoom t ≤ geomCap t
  room_fit : tallyOrigin t + rowRoom t ≤ t.control
  prefixes : tallyPrefixesLe 1 (rowRoom t) (tierClimb t) = true
  fitRoomM : FitsLen (tierChargeMoves t (rowRoom t))
  fitRoomS : FitsLen (tierChargeSlides t (rowRoom t))
  fitRoomO : FitsLen (tierChargeOps t (rowRoom t))
  fitGeomM : FitsLen (tierChargeMoves t (geomCap t))
  fitGeomS : FitsLen (tierChargeSlides t (geomCap t))
  fitGeomO : FitsLen (tierChargeOps t (geomCap t))
  /-- Post-ladder move headroom at the control-row cap. Not part of the rung charge. -/
  fitRoomTailM : FitsLen (tierChargeMoves t (rowRoom t) + pegCharge t.n t.benchlen)
  fitRoomTailS : FitsLen (tierChargeSlides t (rowRoom t) + 2 * t.n)
  fitGeomTailM : FitsLen (tierChargeMoves t (geomCap t) + pegCharge t.n t.benchlen)
  fitGeomTailS : FitsLen (tierChargeSlides t (geomCap t) + 2 * t.n)
  /-- Check multiply after the tail, at the control-row cap. One copy (`n`),
      the schoolbook, and the fold, on top of `fitRoomTailM`. -/
  fitCheckM : FitsLen (tierChargeMoves t (rowRoom t) + pegCharge t.n t.benchlen +
    3 * t.n + t.n * (t.n + 1) + 3 * (t.benchlen - t.n) + 2 * t.n)
  cube_span : 3 * (t.n - 1) + t.combgap < t.benchlen
  mul_span : 2 * (t.n - 1) < t.benchlen

/-- `rungList` is well-founded, so `decide` does not unfold it. Each shipped
    tier's list is the `rungList_gt` / `rungList_le` chain, and the numeric
    checks below are `decide` on the resulting numerals. -/
theorem demo_rungs : rungList (Spec.demo.n - 1) = [1, 2] := by
  have h6 : Spec.demo.n - 1 = 6 := by decide
  rw [h6, rungList_gt (by decide : 1 < 6), show (6 : Nat) / 2 = 3 by decide,
    rungList_gt (by decide : 1 < 3), show (3 : Nat) / 2 = 1 by decide,
    rungList_le (by decide : (1 : Nat) ≤ 1)]
  unfold rungColour
  decide

theorem toy_rungs : rungList (Spec.toy.n - 1) = [1, 2, 2, 1] := by
  have h : Spec.toy.n - 1 = 22 := by decide
  rw [h, rungList_gt (by decide : 1 < 22), show (22 : Nat) / 2 = 11 by decide,
    rungList_gt (by decide : 1 < 11), show (11 : Nat) / 2 = 5 by decide,
    rungList_gt (by decide : 1 < 5), show (5 : Nat) / 2 = 2 by decide,
    rungList_gt (by decide : 1 < 2), show (2 : Nat) / 2 = 1 by decide,
    rungList_le (by decide : (1 : Nat) ≤ 1)]
  unfold rungColour
  decide

theorem hobby_rungs : rungList (Spec.hobby.n - 1) = [1, 2, 1, 2, 2] := by
  have h : Spec.hobby.n - 1 = 58 := by decide
  rw [h, rungList_gt (by decide : 1 < 58), show (58 : Nat) / 2 = 29 by decide,
    rungList_gt (by decide : 1 < 29), show (29 : Nat) / 2 = 14 by decide,
    rungList_gt (by decide : 1 < 14), show (14 : Nat) / 2 = 7 by decide,
    rungList_gt (by decide : 1 < 7), show (7 : Nat) / 2 = 3 by decide,
    rungList_gt (by decide : 1 < 3), show (3 : Nat) / 2 = 1 by decide,
    rungList_le (by decide : (1 : Nat) ≤ 1)]
  unfold rungColour
  decide

theorem serious_rungs : rungList (Spec.serious.n - 1) = [1, 2, 1, 1, 2, 2, 1] := by
  have h : Spec.serious.n - 1 = 178 := by decide
  rw [h, rungList_gt (by decide : 1 < 178), show (178 : Nat) / 2 = 89 by decide,
    rungList_gt (by decide : 1 < 89), show (89 : Nat) / 2 = 44 by decide,
    rungList_gt (by decide : 1 < 44), show (44 : Nat) / 2 = 22 by decide,
    rungList_gt (by decide : 1 < 22), show (22 : Nat) / 2 = 11 by decide,
    rungList_gt (by decide : 1 < 11), show (11 : Nat) / 2 = 5 by decide,
    rungList_gt (by decide : 1 < 5), show (5 : Nat) / 2 = 2 by decide,
    rungList_gt (by decide : 1 < 2), show (2 : Nat) / 2 = 1 by decide,
    rungList_le (by decide : (1 : Nat) ≤ 1)]
  unfold rungColour
  decide

theorem tierSat_num (t : Spec.Tier) (origin room geom r : Nat) (climb : List Nat)
    (hO : tallyOrigin t = origin) (hRoom : rowRoom t = room) (hG : geomCap t = geom)
    (hR : tierR t = r) (hClimb : tierClimb t = climb)
    (hmiss : origin + geom > t.control) (horigin : origin ≤ t.control)
    (hroomG : room ≤ geom) (hroom : origin + room ≤ t.control)
    (hpre : tallyPrefixesLe 1 room climb = true)
    (hRm : r * rungCharge t.n t.benchlen room ≤ i64MaxNat)
    (hRs : r * rungSlideCharge t.n room ≤ i64MaxNat)
    (hRo : r * (room + 3) ≤ i64MaxNat)
    (hGm : r * rungCharge t.n t.benchlen geom ≤ i64MaxNat)
    (hGs : r * rungSlideCharge t.n geom ≤ i64MaxNat)
    (hGo : r * (geom + 3) ≤ i64MaxNat)
    (hRmT : r * rungCharge t.n t.benchlen room + pegCharge t.n t.benchlen ≤ i64MaxNat)
    (hRsT : r * rungSlideCharge t.n room + 2 * t.n ≤ i64MaxNat)
    (hGmT : r * rungCharge t.n t.benchlen geom + pegCharge t.n t.benchlen ≤ i64MaxNat)
    (hGsT : r * rungSlideCharge t.n geom + 2 * t.n ≤ i64MaxNat)
    (hcube : 3 * (t.n - 1) + t.combgap < t.benchlen)
    (hmul : 2 * (t.n - 1) < t.benchlen)
    (hCk : r * rungCharge t.n t.benchlen room + pegCharge t.n t.benchlen +
        3 * t.n + t.n * (t.n + 1) + 3 * (t.benchlen - t.n) + 2 * t.n ≤ i64MaxNat) : TierSat t := by
  refine
    { geom_miss := by rw [hO, hG]; exact hmiss
      origin_le := by rw [hO]; exact horigin
      room_le_geom := by rw [hRoom, hG]; exact hroomG
      room_fit := by rw [hO, hRoom]; exact hroom
      prefixes := by rw [hRoom, hClimb]; exact hpre
      fitRoomM := by unfold FitsLen tierChargeMoves; rw [hR, hRoom]; exact hRm
      fitRoomS := by unfold FitsLen tierChargeSlides; rw [hR, hRoom]; exact hRs
      fitRoomO := by unfold FitsLen tierChargeOps; rw [hR, hRoom]; exact hRo
      fitGeomM := by unfold FitsLen tierChargeMoves; rw [hR, hG]; exact hGm
      fitGeomS := by unfold FitsLen tierChargeSlides; rw [hR, hG]; exact hGs
      fitGeomO := by unfold FitsLen tierChargeOps; rw [hR, hG]; exact hGo
      fitRoomTailM := by
        unfold FitsLen tierChargeMoves
        rw [hR, hRoom]
        exact hRmT
      fitRoomTailS := by
        unfold FitsLen tierChargeSlides
        rw [hR, hRoom]
        exact hRsT
      fitGeomTailM := by
        unfold FitsLen tierChargeMoves
        rw [hR, hG]
        exact hGmT
      fitGeomTailS := by
        unfold FitsLen tierChargeSlides
        rw [hR, hG]
        exact hGsT
      fitCheckM := by
        unfold FitsLen tierChargeMoves
        rw [hR, hRoom]
        exact hCk
      cube_span := hcube
      mul_span := hmul }

theorem demo_tier_sat : TierSat Spec.demo := by
  have hR : tierR Spec.demo = 2 := by unfold tierR; rw [demo_rungs]; decide
  have hClimb : tierClimb Spec.demo = [2, 1] := by unfold tierClimb; rw [demo_rungs]; decide
  have hO : tallyOrigin Spec.demo = 10 := by unfold tallyOrigin; rw [hR]; decide
  have hRoom : rowRoom Spec.demo = 6 := by unfold rowRoom; rw [hO]; decide
  have hG : geomCap Spec.demo = 8 := by unfold geomCap; rw [hR]
  exact tierSat_num Spec.demo 10 6 8 2 [2, 1] hO hRoom hG hR hClimb
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

theorem toy_tier_sat : TierSat Spec.toy := by
  have hR : tierR Spec.toy = 4 := by unfold tierR; rw [toy_rungs]; decide
  have hClimb : tierClimb Spec.toy = [1, 2, 2, 1] := by unfold tierClimb; rw [toy_rungs]; decide
  have hO : tallyOrigin Spec.toy = 22 := by unfold tallyOrigin; rw [hR]; decide
  have hRoom : rowRoom Spec.toy = 18 := by unfold rowRoom; rw [hO]; decide
  have hG : geomCap Spec.toy = 32 := by unfold geomCap; rw [hR]
  exact tierSat_num Spec.toy 22 18 32 4 [1, 2, 2, 1] hO hRoom hG hR hClimb
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

theorem hobby_tier_sat : TierSat Spec.hobby := by
  have hR : tierR Spec.hobby = 5 := by unfold tierR; rw [hobby_rungs]; decide
  have hClimb : tierClimb Spec.hobby = [2, 2, 1, 2, 1] := by
    unfold tierClimb; rw [hobby_rungs]; decide
  have hO : tallyOrigin Spec.hobby = 23 := by unfold tallyOrigin; rw [hR]; decide
  have hRoom : rowRoom Spec.hobby = 57 := by unfold rowRoom; rw [hO]; decide
  have hG : geomCap Spec.hobby = 64 := by unfold geomCap; rw [hR]
  exact tierSat_num Spec.hobby 23 57 64 5 [2, 2, 1, 2, 1] hO hRoom hG hR hClimb
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

theorem serious_tier_sat : TierSat Spec.serious := by
  have hR : tierR Spec.serious = 7 := by unfold tierR; rw [serious_rungs]; decide
  have hClimb : tierClimb Spec.serious = [1, 2, 2, 1, 1, 2, 1] := by
    unfold tierClimb; rw [serious_rungs]; decide
  have hO : tallyOrigin Spec.serious = 25 := by unfold tallyOrigin; rw [hR]; decide
  have hRoom : rowRoom Spec.serious = 175 := by unfold rowRoom; rw [hO]; decide
  have hG : geomCap Spec.serious = 256 := by unfold geomCap; rw [hR]
  exact tierSat_num Spec.serious 25 175 256 7 [1, 2, 2, 1, 1, 2, 1] hO hRoom hG hR hClimb
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

theorem demo_climb_cap (done rest : List Nat)
    (hrs : tierClimb Spec.demo = done ++ rest) :
    climbTallyPrefix 1 done rest ≤ rowRoom Spec.demo := by
  have h := demo_tier_sat.prefixes
  rw [hrs] at h
  exact tallyPrefixesLe_spec 1 (rowRoom Spec.demo) done rest h

theorem toy_climb_cap (done rest : List Nat)
    (hrs : tierClimb Spec.toy = done ++ rest) :
    climbTallyPrefix 1 done rest ≤ rowRoom Spec.toy := by
  have h := toy_tier_sat.prefixes
  rw [hrs] at h
  exact tallyPrefixesLe_spec 1 (rowRoom Spec.toy) done rest h

theorem hobby_climb_cap (done rest : List Nat)
    (hrs : tierClimb Spec.hobby = done ++ rest) :
    climbTallyPrefix 1 done rest ≤ rowRoom Spec.hobby := by
  have h := hobby_tier_sat.prefixes
  rw [hrs] at h
  exact tallyPrefixesLe_spec 1 (rowRoom Spec.hobby) done rest h

theorem serious_climb_cap (done rest : List Nat)
    (hrs : tierClimb Spec.serious = done ++ rest) :
    climbTallyPrefix 1 done rest ≤ rowRoom Spec.serious := by
  have h := serious_tier_sat.prefixes
  rw [hrs] at h
  exact tallyPrefixesLe_spec 1 (rowRoom Spec.serious) done rest h

/-
  The final tally of a tier climb is `climbTally 1 (tierClimb t)`. The rung
  list is the reversed exponent bits of `t.n - 1`, so the value depends only
  on the tier, not on the polynomial being inverted. Each shipped tier's
  tally sits inside that tier's control-row room, and strictly below twice
  the room. `ClimbInvK.tmaxLt` is the per-board form of the same bound.
-/

theorem demo_row_room : rowRoom Spec.demo = 6 := by
  unfold rowRoom tallyOrigin tierR
  rw [demo_rungs]
  decide

theorem demo_final_tally : climbTally 1 (tierClimb Spec.demo) = 3 := by
  have hClimb : tierClimb Spec.demo = [2, 1] := by
    unfold tierClimb
    rw [demo_rungs]
    decide
  rw [hClimb]
  simp [climbTally, tallyAfter]

theorem demo_final_in_room : climbTally 1 (tierClimb Spec.demo) ≤ rowRoom Spec.demo := by
  rw [demo_final_tally, demo_row_room]
  decide

theorem demo_origin_final_fit :
    tallyOrigin Spec.demo + climbTally 1 (tierClimb Spec.demo) ≤ Spec.demo.control :=
  Nat.le_trans (Nat.add_le_add_left demo_final_in_room _) demo_tier_sat.room_fit

theorem demo_final_lt_twice :
    climbTally 1 (tierClimb Spec.demo) < 2 * rowRoom Spec.demo := by
  rw [demo_final_tally, demo_row_room]
  decide

theorem toy_row_room : rowRoom Spec.toy = 18 := by
  unfold rowRoom tallyOrigin tierR
  rw [toy_rungs]
  decide

theorem toy_final_tally : climbTally 1 (tierClimb Spec.toy) = 11 := by
  have hClimb : tierClimb Spec.toy = [1, 2, 2, 1] := by
    unfold tierClimb
    rw [toy_rungs]
    decide
  rw [hClimb]
  simp [climbTally, tallyAfter]

theorem toy_final_in_room : climbTally 1 (tierClimb Spec.toy) ≤ rowRoom Spec.toy := by
  rw [toy_final_tally, toy_row_room]
  decide

theorem toy_origin_final_fit :
    tallyOrigin Spec.toy + climbTally 1 (tierClimb Spec.toy) ≤ Spec.toy.control :=
  Nat.le_trans (Nat.add_le_add_left toy_final_in_room _) toy_tier_sat.room_fit

theorem toy_final_lt_twice :
    climbTally 1 (tierClimb Spec.toy) < 2 * rowRoom Spec.toy := by
  rw [toy_final_tally, toy_row_room]
  decide

theorem hobby_row_room : rowRoom Spec.hobby = 57 := by
  unfold rowRoom tallyOrigin tierR
  rw [hobby_rungs]
  decide

theorem hobby_final_tally : climbTally 1 (tierClimb Spec.hobby) = 29 := by
  have hClimb : tierClimb Spec.hobby = [2, 2, 1, 2, 1] := by
    unfold tierClimb
    rw [hobby_rungs]
    decide
  rw [hClimb]
  simp [climbTally, tallyAfter]

theorem hobby_final_in_room : climbTally 1 (tierClimb Spec.hobby) ≤ rowRoom Spec.hobby := by
  rw [hobby_final_tally, hobby_row_room]
  decide

theorem hobby_origin_final_fit :
    tallyOrigin Spec.hobby + climbTally 1 (tierClimb Spec.hobby) ≤ Spec.hobby.control :=
  Nat.le_trans (Nat.add_le_add_left hobby_final_in_room _) hobby_tier_sat.room_fit

theorem hobby_final_lt_twice :
    climbTally 1 (tierClimb Spec.hobby) < 2 * rowRoom Spec.hobby := by
  rw [hobby_final_tally, hobby_row_room]
  decide

theorem serious_row_room : rowRoom Spec.serious = 175 := by
  unfold rowRoom tallyOrigin tierR
  rw [serious_rungs]
  decide

theorem serious_final_tally : climbTally 1 (tierClimb Spec.serious) = 89 := by
  have hClimb : tierClimb Spec.serious = [1, 2, 2, 1, 1, 2, 1] := by
    unfold tierClimb
    rw [serious_rungs]
    decide
  rw [hClimb]
  simp [climbTally, tallyAfter]

theorem serious_final_in_room :
    climbTally 1 (tierClimb Spec.serious) ≤ rowRoom Spec.serious := by
  rw [serious_final_tally, serious_row_room]
  decide

theorem serious_origin_final_fit :
    tallyOrigin Spec.serious + climbTally 1 (tierClimb Spec.serious) ≤
      Spec.serious.control :=
  Nat.le_trans (Nat.add_le_add_left serious_final_in_room _) serious_tier_sat.room_fit

theorem serious_final_lt_twice :
    climbTally 1 (tierClimb Spec.serious) < 2 * rowRoom Spec.serious := by
  rw [serious_final_tally, serious_row_room]
  decide

/-- Clear home 5. The spare and every other home stay. The gap home is empty. -/
theorem clearHeld_gap (b : Ecbs.Board) (xs : List Nat) (moves : Nat)
    (hH : 5 < b.sudo_5Board_4home.size) (hD : 5 < b.sudo_5Board_4held.size) :
    (clearHeldBoard b 5 xs moves hH hD).sudo_5Board_4held[5]'(by
      simp [clearHeldBoard, Array.size_set]; exact hD) = false := by
  simp [clearHeldBoard, Array.getElem_set]

theorem clearHeld_keep (b : Ecbs.Board) (home other : Nat) (xs : List Nat) (moves : Nat)
    (hin : HomeIn b home)
    (hO : other < b.sudo_5Board_4held.size) (hne : other ≠ home)
    (h : b.sudo_5Board_4held[other] = false) :
    (clearHeldBoard b home xs moves hin.hH hin.hD).sudo_5Board_4held[other]'(by
      simp [clearHeldBoard, Array.size_set]; exact hO) = false := by
  simp [clearHeldBoard, Array.getElem_set, Ne.symm hne, h]

theorem clearHeld_keep_held (b : Ecbs.Board) (home other : Nat) (xs : List Nat) (moves : Nat)
    (hin : HomeIn b home)
    (hO : other < b.sudo_5Board_4held.size) (hne : other ≠ home)
    (h : b.sudo_5Board_4held[other] = true) :
    (clearHeldBoard b home xs moves hin.hH hin.hD).sudo_5Board_4held[other]'(by
      simp [clearHeldBoard, Array.size_set]; exact hO) = true := by
  simp [clearHeldBoard, Array.getElem_set, Ne.symm hne, h]

/-- Re-establish the shape on a board that still holds the input, still has an
    empty spare, and has cleared the gap, with the model's new tally segment. -/
theorem shape_refresh {b : Ecbs.Board} {s : ClimbModel} {done : List Nat}
    {base : ClimbBudget} (h : ClimbShape b s done base)
    (b' : Ecbs.Board) (s' : ClimbModel) (rest : List Nat)
    (hn : s'.n = s.n) (hk : s'.k = s.k) (_hb : s'.benchlen = s.benchlen)
    (hgap : s'.gap.length = s'.n)
    (hseg : RowSeg s'.row s'.t0 s'.tally rest.isEmpty)
    (hspareD : 6 < b'.sudo_5Board_4held.size)
    (hspareH : 6 < b'.sudo_5Board_4home.size)
    (hspare : b'.sudo_5Board_4held[6] = false)
    (h7 : 7 ≤ b'.sudo_5Board_4held.size)
    (hclear : s'.onBench = true →
      b'.sudo_5Board_4held[5]'(Nat.lt_of_lt_of_le (by decide : (5 : Nat) < 7) h7) = false)
    (hoff : s'.onBench = false → b'.sudo_5Board_8bench_on = false)
    (hxD : base.xHome < b'.sudo_5Board_4held.size)
    (hxH : base.xHome < b'.sudo_5Board_4home.size)
    (hx : b'.sudo_5Board_4held[base.xHome] = true)
    (harr : b'.sudo_5Board_4home[base.xHome] = embed base.x)
    (hN : b'.sudo_5Board_1t.sudo_4Tier_1n = (s'.n : Int))
    (hK : b'.sudo_5Board_1t.sudo_4Tier_1k = (s'.k : Int))
    (hB : b'.sudo_5Board_1t.sudo_4Tier_8benchlen = (s'.benchlen : Int))
    (hW : b'.sudo_5Board_1t.sudo_4Tier_1w = (base.w : Int))
    (hHt : b'.sudo_5Board_1t.sudo_4Tier_1h = (base.h : Int))
    (hR : b'.sudo_5Board_1t.sudo_4Tier_1r = (base.r : Int))
    (hCg : b'.sudo_5Board_1t.sudo_4Tier_7combgap = (base.cg : Int))
    (hC : b'.sudo_5Board_1t.sudo_4Tier_7control = (base.control : Int))
    (hrow : s'.row.length = base.control)
    (hpark : ParkRead b' s' rest base)
    (hpeg : PegRead b' s' base)
    (hside : SideKeep b' base)
    (hquiet : QuietKeep b' base) :
    ClimbShape b' s' rest base := by
  refine
    { spareH := hspareH
      spareD := hspareD
      spareE := hspare
      h7 := h7
      gapClear := hclear
      offWhenHome := hoff
      xD := hxD
      xH := hxH
      xHeld := hx
      xArr := harr
      xNe5 := h.xNe5
      xNe6 := h.xNe6
      gapLen := hgap
      seg := hseg
      tierN := hN
      tierK := hK
      tierB := hB
      tierW := hW
      tierH := hHt
      tierR := hR
      tierCg := hCg
      tierC := hC
      rowLen := hrow
      w0 := h.w0
      h0 := h.h0
      r0 := h.r0
      rlt := h.rlt
      n_eq := by rw [hn]; exact h.n_eq
      k_le := by rw [hk, hn]; exact h.k_le
      gap_eq := by rw [hn, hk]; exact h.gap_eq
      side := hside
      quiet := hquiet
      park := hpark
      peg := hpeg }

/-- Later rung: the gap is on the bench and home 5 is clear, so the spare copy
    reads the bench. The spare is empty. `place` leaves the bench aimed at the gap. -/
theorem copy_gap_bench (b : Ecbs.Board) (s : ClimbModel) (rest : List Nat)
    (base : ClimbBudget) (moves peak : Nat)
    (hinv : ClimbInv b s) (hshape : ClimbShape b s rest base)
    (hon : s.onBench = true)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hf : FitsLen s.n)
    (_hnb : s.n ≤ s.benchlen)
    (hfit : FitsLen (moves + pegCount s.gap)) :
    Ecbs.copy_band b ((6 : Nat) : Int) ((5 : Nat) : Int) false =
      .ok (placeBoard b 6 hshape.spareH hshape.spareD s.gap moves peak) := by
  have hpad : (s.gap.take s.n ++ List.replicate (s.benchlen - s.n) 0).take s.n = s.gap := by
    have hlen : s.gap.length = s.n := hshape.gapLen
    rw [List.take_append_of_le_length (by rw [List.length_take, hlen]; omega),
      List.take_take, Nat.min_self]
    rw [← hlen]
    exact List.take_length s.gap
  have hbench := hinv.gapBench hon
  have hcopy := copy_band_bench_refines b 6 5
      (s.gap.take s.n ++ List.replicate (s.benchlen - s.n) 0) s.n moves peak
      hshape.spareH hshape.spareD hinv.hGs hshape.h7 (hshape.gapClear hon)
      hbench.1 hbench.2.1 hbench.2.2.1 hshape.spareE
      (by rw [hshape.tierN])
      (by
        rw [List.length_append, List.length_take, List.length_replicate, hshape.gapLen]
        omega)
      hf hmoves hpeak
      (by simpa [hpad] using hfit)
  simpa [hpad] using hcopy

theorem downFromLen (hi k : Nat) : (downFrom hi k).length = k := by
  induction k generalizing hi with
  | zero => rfl
  | succ k ih => simp [downFrom, ih]

theorem downFromAt (hi k i : Nat) (hik : i < k) :
    (downFrom hi k)[i]'(by rw [downFromLen]; exact hik) = hi - i := by
  induction k generalizing hi i with
  | zero => cases hik
  | succ k ih =>
    cases i with
    | zero => simp [downFrom]
    | succ i =>
      have ih' := ih (hi - 1) i (Nat.lt_of_succ_lt_succ hik)
      simp [downFrom, List.getElem_cons_succ, ih']
      omega

theorem embed_nat (xs : List Nat) (i : Nat) (hi : i < xs.length) :
    (embed xs)[i]'(by rw [size_embed]; exact hi) = (xs[i] : Int) := by
  simp [embed, Array.getElem_mk, ofNat_eq_natCast]

private theorem row_nat (b : Ecbs.Board) (xs : List Nat) (i c : Nat)
    (hrow : b.sudo_5Board_3row = embed xs)
    (hi : i < xs.length) (hc : xs[i]'hi = c) :
    b.sudo_5Board_3row[i]'(by rw [hrow, size_embed]; exact hi) = (c : Int) := by
  have hget := embed_nat xs i hi
  simp [hrow, hget, hc]

/-- Rung 0 keeps the park. A later rung is `park_rung_resume`. -/
theorem park_of_shape {done rest : List Nat} {r : Nat} {b : Ecbs.Board}
    {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvKCore done (r :: rest) b s base) :
    ∃ bPark, Ecbs.park_rung b (r : Int) = .ok bPark ∧
      bPark.sudo_5Board_11parked_from =
        ((climbAt base.ladder0 base.R s.ridx : Nat) : Int) ∧
      bPark.sudo_5Board_8rung_idx = Int.ofNat (s.ridx + 1) ∧
      (s.fromHole < 0 →
        ∃ (hRowP : s.parkAt < b.sudo_5Board_3row.size)
          (hRowH : climbAt base.ladder0 base.R s.ridx < b.sudo_5Board_3row.size),
          bPark = parkKeepBoard b (climbAt base.ladder0 base.R s.ridx) s.parkAt r
            s.ridx s.ctrl hRowP hRowH) := by
  let hole := climbAt base.ladder0 base.R s.ridx
  let holes := downFrom (base.ladder0 + base.R - 1) base.R
  have hidxN : s.ridx < base.R := by
    rw [h.idx]
    have hk := h.kLe
    simp [List.length_append, List.length_cons] at hk
    omega
  have hAt : s.ridx < holes.length := by
    simpa [holes, downFromLen] using hidxN
  have hHole : holes[s.ridx] = hole := by
    simpa [holes, hole, climbAt] using
      downFromAt (base.ladder0 + base.R - 1) base.R s.ridx hidxN
  have hr := h.shape.park.nextRung r rest rfl
  have hRowH : hole < b.sudo_5Board_3row.size := by
    rw [h.inv.row, size_embed]; exact h.shape.park.holeLt
  have hRowP : s.parkAt < b.sudo_5Board_3row.size := by
    rw [h.inv.row, size_embed]; exact h.shape.park.parkLt
  have hColour : b.sudo_5Board_3row[hole] = (r : Int) := by
    simpa [hole] using row_nat b s.row hole r h.inv.row h.shape.park.holeLt hr.1
  have hpos : r ≠ 0 := hr.2
  by_cases hF : s.fromHole < 0
  · have hIdleB : b.sudo_5Board_11parked_from = -1 := by
      rw [h.inv.fromP, h.shape.park.fromIdle hF]
    have hZero : b.sudo_5Board_3row[s.parkAt] = 0 := by
      simpa using row_nat b s.row s.parkAt 0 h.inv.row h.shape.park.parkLt
        (h.shape.park.parkCell hF)
    have hkeep := park_rung_keep_eq b holes s.ridx hole s.parkAt r s.high base.control s.ctrl
      h.shape.park.climbH h.inv.ridx hAt hHole hIdleB h.inv.park hRowH hRowP hColour hZero
      hpos h.shape.tierC h.shape.park.parkIn h.inv.high h.shape.park.parkLe h.inv.ctrl
      h.shape.park.fit2 h.shape.park.parkNe h.shape.park.fitI
    refine ⟨parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH, hkeep, ?_, ?_, ?_⟩
    · simp [parkKeepBoard]
    · simp [parkKeepBoard, ofNat_eq_natCast]
    · intro _
      exact ⟨hRowP, hRowH, rfl⟩
  · have hge : 0 ≤ s.fromHole := by omega
    obtain ⟨prev, hprev⟩ := h.shape.park.parkHeld hge
    have hsrc := h.shape.park.srcOk hge
    have hFrom : b.sudo_5Board_11parked_from = (s.fromHole.toNat : Int) := by
      rw [h.inv.fromP]
      exact h.shape.park.fromNat hge
    have hPrevB : b.sudo_5Board_3row[s.parkAt] = (prev : Int) := by
      simpa using row_nat b s.row s.parkAt prev h.inv.row h.shape.park.parkLt hprev
    have hRowS : s.fromHole.toNat < b.sudo_5Board_3row.size := by
      rw [h.inv.row, size_embed]; exact hsrc.1
    have hres := park_rung_resume b holes s.ridx s.fromHole.toNat hole s.parkAt prev r
      s.high base.control s.ctrl h.shape.park.climbH h.inv.ridx hAt hHole hFrom h.inv.park
      hRowS hRowH hRowP hPrevB hColour hpos h.shape.tierC hsrc.2.1 h.shape.park.parkIn
      h.inv.high hsrc.2.2.1 h.shape.park.parkLe h.inv.ctrl h.shape.park.fit2 h.shape.park.fit4
      h.shape.park.parkNe (Ne.symm hsrc.2.2.2) h.shape.park.fitI
    refine ⟨_, hres, ?_, ?_, ?_⟩
    · simp [unparkedBoard]
    · simp [unparkedBoard, ofNat_eq_natCast]
    · intro hlt
      omega

/-- One `rungCharge` contains the leading `2 · n`. -/
theorem rung_ge_two (n bench m : Nat) : 2 * n ≤ rungCharge n bench m := by
  unfold rungCharge
  omega

/-- One slide charge contains one settle of `2 · n`. -/
theorem slide_ge_two (n m : Nat) : 2 * n ≤ rungSlideCharge n m := by
  unfold rungSlideCharge
  have hsplit : (m + 3) * (2 * n) = m * (2 * n) + 3 * (2 * n) := by
    rw [Nat.add_mul]
  have hone : 2 * n ≤ 3 * (2 * n) := by
    have hmul := Nat.mul_le_mul_right (2 * n) (by decide : (1 : Nat) ≤ 3)
    simpa [Nat.one_mul] using hmul
  rw [hsplit]
  exact Nat.le_trans hone (Nat.le_add_left _ _)

/-- Copy plus the tally pegs sit in the tight remainder `rungCharge − 2 · n`. -/
theorem gap_copy_room (n bench mMax tally pegs : Nat)
    (hpeg : pegs ≤ n) (ht : tally ≤ mMax) :
    pegs + tally * pegCharge n bench ≤ rungCharge n bench mMax - 2 * n := by
  have hmono := rungCharge_mono n bench tally mMax ht
  have hge := rung_ge_two n bench tally
  have h4 : 4 * n ≤ pegCharge n bench := by
    unfold pegCharge
    exact Nat.le_add_right _ _
  have h2 : 2 * n ≤ pegCharge n bench := by
    exact Nat.le_trans (Nat.mul_le_mul_right n (by decide : (2 : Nat) ≤ 4)) h4
  have h3 : 3 * n ≤ pegCharge n bench := by
    exact Nat.le_trans (Nat.mul_le_mul_right n (by decide : (3 : Nat) ≤ 4)) h4
  have h3eq : n + 2 * n = 3 * n := by omega
  have hsplit : (tally + 1) * pegCharge n bench =
      tally * pegCharge n bench + pegCharge n bench := by
    rw [Nat.succ_mul]
  have hleft : pegs + 2 * n ≤ pegCharge n bench := by
    have hsum : pegs + 2 * n ≤ n + 2 * n := Nat.add_le_add_right hpeg _
    rw [h3eq] at hsum
    exact Nat.le_trans hsum h3
  have hre : pegs + tally * pegCharge n bench + 2 * n =
      tally * pegCharge n bench + (pegs + 2 * n) := by
    rw [Nat.add_assoc, Nat.add_left_comm]
  have hbody : pegs + tally * pegCharge n bench + 2 * n ≤
      (tally + 1) * pegCharge n bench := by
    rw [hre, hsplit]
    exact Nat.add_le_add_left hleft _
  have hrc : (tally + 1) * pegCharge n bench ≤ rungCharge n bench tally := by
    unfold rungCharge
    exact Nat.le_trans (Nat.le_add_left _ (2 * n))
      (Nat.le_add_right _ (2 * mulCharge n bench))
  have hsum : pegs + tally * pegCharge n bench + 2 * n ≤ rungCharge n bench tally :=
    Nat.le_trans hbody hrc
  exact Nat.le_trans (Nat.le_sub_of_add_le hsum) (Nat.sub_le_sub_right hmono _)

/-- The bench-off cube-peg loop's context. The gap sits in home 5, so the bench
    is off and the spare is empty. Copying the gap into the spare is `place`.
    That board is the `PegCtx`: home 6 holds the gap, the bench stays off, and
    the move counter has grown by the nonzero count of the gap. The cube-loop
    budget is one rung charge of the climb, which already covers that copy. -/
theorem peg_of_shape {done rest : List Nat} {r : Nat} {b : Ecbs.Board} {s : ClimbModel}
    {base : ClimbBudget} (h : ClimbInvKCore done (r :: rest) b s base)
    (hM : MoveHeadroom b base.n base.bench base.mMax)
    (hS : SlideHeadroom b base.n base.mMax)
    (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax)
    (hhome : s.onBench = false) :
    ∃ (mv pk sl : Nat) (c : PegCtx),
      b.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int) ∧
      b.sudo_5Board_4cost.sudo_5Costs_4peak = (pk : Int) ∧
      b.sudo_5Board_4cost.sudo_5Costs_6slides = (sl : Int) ∧
      c.b0 = placeBoard b 6 h.shape.spareH h.shape.spareD s.gap mv pk ∧
      Ecbs.copy_band b ((6 : Nat) : Int) ((5 : Nat) : Int) false = .ok c.b0 ∧
      c.src = 6 ∧ c.g = s.gap ∧ c.m = s.tally ∧ c.row0 = s.row ∧
      c.n = s.n ∧ c.k = s.k ∧ c.bench = s.benchlen ∧
      c.moves0 = mv + pegCount s.gap ∧ c.slides0 = sl ∧ c.t0 = s.t0 ∧
      c.ctrl0 = s.ctrl ∧ c.high = s.high ∧ c.control = base.control ∧
      c.b0.sudo_5Board_9tally_len = (s.tally : Int) ∧
      c.b0.sudo_5Board_4cost.sudo_5Costs_9tally_max =
        b.sudo_5Board_4cost.sudo_5Costs_9tally_max := by
  have hmv := hM.eq
  have hsl := hS.eq
  let mv := hM.mv
  let sl := hS.sl
  obtain ⟨cOps, hcOps⟩ := h.shape.peg.cOps
  obtain ⟨pkS, hpkS⟩ := h.shape.peg.peakS
  obtain ⟨holeM, hhole⟩ := h.shape.peg.holeM
  obtain ⟨pk, hpk, _⟩ := h.peak
  have hgapH := h.inv.gapHome hhome
  have hoff0 : b.sudo_5Board_8bench_on = false := h.shape.offWhenHome hhome
  have hk : done.length + 1 ≤ base.R := by
    have hlen := h.kLe
    rw [List.length_append, List.length_cons] at hlen
    omega
  have hpegN : pegCount s.gap ≤ s.n := by
    rw [← h.shape.gapLen]
    exact pegCount_le s.gap
  have hcharge : pegCount s.gap + s.tally * pegCharge s.n s.benchlen ≤
      rungCharge base.n base.bench base.mMax := by
    unfold rungCharge
    have hmul : s.tally * pegCharge s.n s.benchlen ≤
        (base.mMax + 1) * pegCharge s.n s.benchlen :=
      Nat.mul_le_mul_right _ (Nat.le_succ_of_le hT)
    have hsum : pegCount s.gap + s.tally * pegCharge s.n s.benchlen ≤
        s.n + (base.mMax + 1) * pegCharge s.n s.benchlen := by
      exact Nat.add_le_add hpegN (Nat.le_trans hmul (Nat.le_refl _))
    have hrest : s.n + (base.mMax + 1) * pegCharge s.n s.benchlen ≤
        2 * s.n + (base.mMax + 1) * pegCharge s.n s.benchlen +
          2 * mulCharge s.n s.benchlen := by
      omega
    have hn : s.n = base.n := h.hn
    have hb : s.benchlen = base.bench := h.hbench
    exact Nat.le_trans hsum (by simpa [hn, hb] using hrest)
  have hmovFit : FitsLen (mv + pegCount s.gap + s.tally * pegCharge s.n s.benchlen) := by
    apply FitsLen.of_le (MoveHeadroom.at hM hmv)
    rw [Nat.add_assoc]
    apply Nat.add_le_add_left
    rw [h.hn, h.hbench]
    exact gap_copy_room base.n base.bench base.mMax s.tally (pegCount s.gap)
      (by rw [← h.hn]; exact hpegN) hT
  have hfitCopy : FitsLen (mv + pegCount s.gap) :=
    FitsLen.of_le hmovFit (by omega)
  have hcopy := copy_band_refines b 6 5 s.gap mv pk
    h.shape.spareH h.shape.spareD h.inv.hG h.inv.hGs h.shape.h7
    hgapH.1 hgapH.2 h.shape.spareE
    (by rw [h.shape.gapLen]; exact h.shape.tierN)
    (by rw [h.shape.gapLen]; exact h.shape.peg.fitN)
    hmv hpk hfitCopy
  let b1 := placeBoard b 6 h.shape.spareH h.shape.spareD s.gap mv pk
  have hbook := place_book b 6 ⟨h.shape.spareH, h.shape.spareD⟩ s.gap mv pk
  have hidle := place_idle b 6 ⟨h.shape.spareH, h.shape.spareD⟩ s.gap mv pk
  have hlen0 : b1.sudo_5Board_9tally_len = (s.tally : Int) := by
    rw [hbook.2.2.2.1, h.inv.len]
  have hmax0 : b1.sudo_5Board_4cost.sudo_5Costs_9tally_max =
      b.sudo_5Board_4cost.sudo_5Costs_9tally_max := by
    simp [b1, placeBoard]
    split <;> rfl
  let pk1 := if pk < countHeld (b.sudo_5Board_4held.set ⟨6, h.shape.spareD⟩ true) 7
    then countHeld (b.sudo_5Board_4held.set ⟨6, h.shape.spareD⟩ true) 7 else pk
  refine ⟨mv, pk, sl, {
    b0 := b1
    src := 6
    g := s.gap
    row0 := s.row
    w := base.w
    h := base.h
    r := base.r
    n := s.n
    k := s.k
    bench := s.benchlen
    cg := base.cg
    moves0 := mv + pegCount s.gap
    slides0 := sl
    hole0 := holeM
    peak0 := pk1
    peakS0 := pkS
    cOps0 := cOps
    t0 := s.t0
    high := s.high
    control := base.control
    ctrl0 := s.ctrl
    m := s.tally
    hm := hm
    hmk := by rw [hidle.1]; exact h.inv.marker
    hoff := by rw [hidle.2.1]; exact hoff0
    hops0 := by rw [hidle.2.2.1]; exact h.shape.peg.opsGt
    hop10 := by
      have hsz : 1 < b1.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
        rw [hidle.2.2.1]; exact h.shape.peg.opsGt
      have hget := idx_get hidle.2.2.1 1 hsz
      exact hget.trans hcOps
    hbl := by rw [hidle.2.2.2.2.1, h.shape.tierB]; exact ofNat_eq_natCast s.benchlen
    hcg := by rw [hidle.2.2.2.2.1, h.shape.tierCg]; exact ofNat_eq_natCast base.cg
    hspan := h.shape.peg.span
    hF := by rw [hbook.2.2.2.2.2.2.2.2.2]; exact h.shape.spareD
    hHome := by rw [hbook.2.2.2.2.2.2.2.2.1]; exact h.shape.spareH
    hHF := by
      have hF : 6 < b1.sudo_5Board_4held.size := by
        rw [hbook.2.2.2.2.2.2.2.2.2]; exact h.shape.spareD
      simpa using place_held_here b 6 ⟨h.shape.spareH, h.shape.spareD⟩ s.gap mv pk hF
    hArr := by
      have hF : 6 < b1.sudo_5Board_4home.size := by
        rw [hbook.2.2.2.2.2.2.2.2.1]; exact h.shape.spareH
      simpa using place_home_here b 6 ⟨h.shape.spareH, h.shape.spareD⟩ s.gap mv pk hF
    h7 := by rw [hbook.2.2.2.2.2.2.2.2.2]; exact h.shape.h7
    hn0 := h.shape.peg.n_pos
    hn := by rw [hidle.2.2.2.2.1]; exact h.shape.tierN
    hlenx := h.shape.gapLen
    hf := h.shape.peg.fitN
    hmoves0 := by
      rw [place_moves b 6 ⟨h.shape.spareH, h.shape.spareD⟩ s.gap mv pk]
      exact ofNat_eq_natCast _
    hpeak0 := by
      rw [place_peak b 6 ⟨h.shape.spareH, h.shape.spareD⟩ s.gap mv pk hpk]
      exact ofNat_eq_natCast _
    hpeakS0 := by rw [hidle.2.2.2.2.2.1]; exact hpkS
    hxsT := h.shape.peg.trits
    h3 := h.shape.peg.fit3
    hw0 := h.shape.w0
    hh0 := h.shape.h0
    hrR := h.shape.rlt
    hrP := h.shape.r0
    hnE := h.shape.n_eq
    hkLe := h.shape.k_le
    hgap := h.shape.gap_eq
    hwF := by rw [hidle.2.2.2.2.1, h.shape.tierW]; exact ofNat_eq_natCast base.w
    hhF := by rw [hidle.2.2.2.2.1, h.shape.tierH]; exact ofNat_eq_natCast base.h
    hrF := by rw [hidle.2.2.2.2.1, h.shape.tierR]; exact ofNat_eq_natCast base.r
    hkF := by rw [hidle.2.2.2.2.1, h.shape.tierK]; exact ofNat_eq_natCast s.k
    hHole0 := by rw [hidle.2.2.2.2.2.2]; exact hhole
    hsm := by
      have hs := h.shape.peg.small
      have hb : s.benchlen = base.bench := h.hbench
      simpa [hb] using hs
    hnsm := h.shape.peg.n_small
    hfitB := h.shape.peg.fitBn
    hT0 := by rw [hbook.2.2.2.2.1, h.inv.t0]
    hRow := by rw [hbook.1, h.inv.row]
    hRoom := h.shape.seg.room
    hCtrlN := by rw [hidle.2.2.2.2.1]; exact h.shape.tierC
    hHigh := by rw [hbook.2.2.2.2.2.2.1, h.inv.high]
    hTop := h.shape.peg.top hm
    hIn := by rw [← h.shape.rowLen]; exact h.shape.seg.room
    hCtrl0 := by rw [hbook.2.2.2.2.2.2.2.1, h.inv.ctrl]
    hslides0 := by rw [hidle.2.2.2.1, hsl]; exact ofNat_eq_natCast sl
    hfitRow := h.shape.peg.fitRow
    hfitM := h.shape.peg.fitTall
    hBudget := hmovFit
    hSlide := by
      apply FitsLen.of_le (SlideHeadroom.at hS hsl)
      have hn : s.n = base.n := h.hn
      have hmul : s.tally * (2 * base.n) + 2 * base.n ≤
          rungSlideCharge base.n base.mMax := by
        unfold rungSlideCharge
        rw [Nat.add_mul]
        have hle : s.tally + 1 ≤ base.mMax + 3 := by omega
        have h := Nat.mul_le_mul_right (2 * base.n) hle
        rw [Nat.succ_mul, Nat.add_mul] at h
        exact h
      have hsub : s.tally * (2 * base.n) ≤
          rungSlideCharge base.n base.mMax - 2 * base.n :=
        Nat.le_sub_of_add_le hmul
      rw [hn]
      exact Nat.add_le_add_left hsub sl
    hOpsB := by
      obtain ⟨c0, hc0, hcle⟩ := h.ops 1 h.shape.peg.opsGt
      have hc : cOps = c0 := ofNat_inj_nat (hcOps.symm.trans hc0)
      apply FitsLen.of_le base.fitO
      have hstep : cOps + s.tally ≤
          base.ops0 + (done.length + 1) * (base.mMax + 3) := by
        have hsucc : (done.length + 1) * (base.mMax + 3) =
            done.length * (base.mMax + 3) + (base.mMax + 3) := by rw [Nat.succ_mul]
        have ht : s.tally ≤ base.mMax + 3 := Nat.le_trans hT (Nat.le_add_right _ _)
        omega
      have hR : (done.length + 1) * (base.mMax + 3) ≤ base.R * (base.mMax + 3) :=
        Nat.mul_le_mul_right _ hk
      omega
    hCtrlB := h.shape.peg.fitCtrl
  }, hmv, hpk, hsl, rfl, hcopy, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hlen0, hmax0⟩

/-- Park writes two, then the peg loop writes one per tally peg. `tally ≥ 1` makes
    that at most `3 · tally`, which `double_ctrl_fit` already bounds. -/
theorem ctrl_add_peg_le (ctrl tally : Nat) (hm : 0 < tally) :
    ctrl + 2 + tally ≤ ctrl + 3 * tally := by
  omega

theorem ctrl_park_peg_fit {ctrl tally ctrl0 done R mMax : Nat}
    (hctrl : ctrl ≤ ctrl0 + done * (3 * mMax + 5))
    (ht : tally ≤ mMax) (hm : 0 < tally) (hd : done ≤ R)
    (hf : FitsLen (ctrl0 + (R + 1) * (3 * mMax + 5))) :
    FitsLen (ctrl + 2 + tally) :=
  FitsLen.of_le (double_ctrl_fit hctrl ht hd hf).1 (ctrl_add_peg_le ctrl tally hm)

/-- The gap copy, the tally pegs, and one live mul stay inside one `rungCharge`. -/
theorem gap_mul_le_rung (n bench mMax tally pegs : Nat)
    (hpeg : pegs ≤ n) (ht : tally ≤ mMax) :
    pegs + tally * pegCharge n bench + mulCharge n bench ≤
      rungCharge n bench mMax := by
  unfold rungCharge
  have hmul : tally * pegCharge n bench ≤ (mMax + 1) * pegCharge n bench :=
    Nat.mul_le_mul_right _ (Nat.le_succ_of_le ht)
  have hsum : pegs + tally * pegCharge n bench + mulCharge n bench ≤
      n + (mMax + 1) * pegCharge n bench + mulCharge n bench :=
    Nat.add_le_add_right (Nat.add_le_add hpeg hmul) _
  let X := (mMax + 1) * pegCharge n bench
  have h2 : n ≤ 2 * n := by
    rw [Nat.two_mul]
    exact Nat.le_add_left n n
  have h3 : mulCharge n bench ≤ 2 * mulCharge n bench := by
    rw [Nat.two_mul]
    exact Nat.le_add_left _ _
  refine Nat.le_trans hsum ?_
  calc
    n + X + mulCharge n bench ≤ 2 * n + X + mulCharge n bench :=
      Nat.add_le_add_right (Nat.add_le_add_right h2 X) _
    _ ≤ 2 * n + X + 2 * mulCharge n bench := Nat.add_le_add_left h3 _

theorem gap_copy_le_rung (n bench mMax tally pegs : Nat)
    (hpeg : pegs ≤ n) (ht : tally ≤ mMax) :
    pegs + tally * pegCharge n bench ≤ rungCharge n bench mMax :=
  Nat.le_trans (Nat.le_add_right _ (mulCharge n bench))
    (gap_mul_le_rung n bench mMax tally pegs hpeg ht)

/-- The loose white piece already sits in `rungCharge − 2 · n`. -/
theorem white_piece_room (n bench m : Nat) :
    n + m * pegCharge n bench + mulCharge n bench + n ≤
      rungCharge n bench m - 2 * n := by
  have h4 : 4 * n ≤ pegCharge n bench := by
    unfold pegCharge
    exact Nat.le_add_right _ _
  have h2n : 2 * n ≤ pegCharge n bench :=
    Nat.le_trans (Nat.mul_le_mul_right n (by decide : (2 : Nat) ≤ 4)) h4
  have hsum : n + m * pegCharge n bench + mulCharge n bench + n + 2 * n ≤
      rungCharge n bench m := by
    unfold rungCharge
    rw [Nat.succ_mul m (pegCharge n bench), Nat.two_mul (mulCharge n bench)]
    omega
  exact Nat.le_sub_of_add_le hsum

/-- Anything at most the loose white piece sits in the tight move remainder. -/
theorem white_piece_in_room (n bench m mv piece : Nat)
    (h : piece ≤ mv + n + m * pegCharge n bench + mulCharge n bench + n) :
    piece ≤ mv + (rungCharge n bench m - 2 * n) := by
  have hW := white_piece_room n bench m
  have hflat : mv + n + m * pegCharge n bench + mulCharge n bench + n =
      mv + (n + m * pegCharge n bench + mulCharge n bench + n) := by
    omega
  exact Nat.le_trans h (Nat.le_trans (Nat.le_of_eq hflat) (Nat.add_le_add_left hW mv))

/-- A short clear is `2 · n` under the tally's `rungCharge`. -/
theorem short_clear_move_tight (n bench m mv mvC : Nat)
    (h : mvC + 2 * n ≤ mv + n + m * pegCharge n bench + mulCharge n bench + n) :
    mvC + 2 * n ≤ mv + rungCharge n bench m := by
  have hW := white_piece_room n bench m
  have hflat : mv + n + m * pegCharge n bench + mulCharge n bench + n =
      mv + (n + m * pegCharge n bench + mulCharge n bench + n) := by
    omega
  exact Nat.le_trans h (Nat.le_trans (Nat.le_of_eq hflat)
    (Nat.add_le_add_left (Nat.le_trans hW (Nat.sub_le _ _)) mv))

/-- Gap-mul slides `≤ tally · (2 · n)` are `2 · n` under the slide charge. -/
theorem short_clear_slide_tight (n m sl slC : Nat)
    (h : slC ≤ sl + m * (2 * n)) :
    slC + 2 * n ≤ sl + rungSlideCharge n m := by
  unfold rungSlideCharge
  have hsplit : (m + 3) * (2 * n) = m * (2 * n) + 3 * (2 * n) := by
    rw [Nat.add_mul]
  omega

/-- Loose clear slides, one extra `2 · n`, still sit in the tight slide remainder. -/
theorem loose_slide_in_room (n m mMax sl extra : Nat)
    (hT : m ≤ mMax)
    (h : extra ≤ sl + m * (2 * n) + 2 * n) :
    extra ≤ sl + (rungSlideCharge n mMax - 2 * n) := by
  have hmono := rungSlideCharge_mono n m mMax hT
  have hge := slide_ge_two n m
  have hpiece : m * (2 * n) + 2 * n + 2 * n ≤ rungSlideCharge n m := by
    unfold rungSlideCharge
    rw [Nat.add_mul]
    omega
  have hlocal : extra + 2 * n ≤ sl + rungSlideCharge n m := by
    omega
  have hsub0 : extra ≤ (sl + rungSlideCharge n m) - 2 * n :=
    Nat.le_sub_of_add_le hlocal
  have hsub : extra ≤ sl + (rungSlideCharge n m - 2 * n) := by
    rwa [Nat.add_sub_assoc hge] at hsub0
  exact Nat.le_trans hsub (Nat.add_le_add_left (Nat.sub_le_sub_right hmono _) sl)

/-- The live-mul fold `loop + 2 · pegs + n · (n + 1) + 3 · (bench − n)` sits in
    the tight remainder once the loop is at most the copy plus `m` peg charges. -/
theorem mul_fold_in_room (n bench m mv pegs loop pegTake : Nat)
    (hpeg : pegs ≤ n) (htake : pegTake ≤ n)
    (hloop : loop ≤ mv + pegs + m * pegCharge n bench) :
    loop + 2 * pegTake + n * (n + 1) + 3 * (bench - n) ≤
      mv + (rungCharge n bench m - 2 * n) := by
  have hmul : 2 * pegTake + n * (n + 1) + 3 * (bench - n) ≤ mulCharge n bench := by
    unfold mulCharge
    have h2 : 2 * pegTake ≤ 2 * n := Nat.mul_le_mul_left 2 htake
    omega
  have h1 : loop + 2 * pegTake + n * (n + 1) + 3 * (bench - n) ≤
      mv + pegs + m * pegCharge n bench + mulCharge n bench := by
    omega
  have h2 : pegs + m * pegCharge n bench + mulCharge n bench ≤
      n + m * pegCharge n bench + mulCharge n bench + n := by
    omega
  have hflat : mv + pegs + m * pegCharge n bench + mulCharge n bench =
      mv + (pegs + m * pegCharge n bench + mulCharge n bench) := by
    omega
  have hflat2 : mv + n + m * pegCharge n bench + mulCharge n bench + n =
      mv + (n + m * pegCharge n bench + mulCharge n bench + n) := by
    omega
  exact white_piece_in_room n bench m mv _
    (Nat.le_trans h1 (Nat.le_trans (Nat.le_of_eq hflat)
      (Nat.le_trans (Nat.add_le_add_left h2 mv) (Nat.le_of_eq hflat2.symm))))

/-- The cleared counter plus one peg charge still sits in the tight remainder.
    That is the red cube's fold, and `mulCharge ≥ 2 · n` pays for the leading pair. -/
theorem clear_fold_room (n bench m mv mvC peg : Nat)
    (hC : mvC ≤ mv + n + m * pegCharge n bench + mulCharge n bench + n)
    (hp : peg ≤ n) :
    mvC + 2 * peg + 2 * n + 3 * (bench - n) ≤
      mv + (rungCharge n bench m - 2 * n) := by
  have h2 : 2 * peg ≤ 2 * n := Nat.mul_le_mul_left 2 hp
  have h4eq : 2 * n + 2 * n = 4 * n := by
    have : 2 * n + 2 * n = (2 + 2) * n := by rw [Nat.add_mul]
    simpa using this
  have hpeg : 2 * peg + 2 * n + 3 * (bench - n) ≤ pegCharge n bench := by
    unfold pegCharge
    have hleft : 2 * peg + 2 * n ≤ 4 * n :=
      Nat.le_trans (Nat.add_le_add_right h2 _) (Nat.le_of_eq h4eq)
    exact Nat.add_le_add_right hleft _
  have hmul : 2 * n ≤ mulCharge n bench := by
    unfold mulCharge
    exact Nat.le_trans (Nat.le_add_right (2 * n) (n * (n + 1)))
      (Nat.le_add_right _ (3 * (bench - n)))
  have hsplit : (m + 1) * pegCharge n bench =
      m * pegCharge n bench + pegCharge n bench := by
    rw [Nat.succ_mul]
  have hpiece : n + m * pegCharge n bench + mulCharge n bench + n + pegCharge n bench +
      2 * n ≤ rungCharge n bench m := by
    unfold rungCharge
    rw [hsplit, Nat.two_mul (mulCharge n bench)]
    omega
  have hfold : mvC + 2 * peg + 2 * n + 3 * (bench - n) ≤ mvC + pegCharge n bench := by
    omega
  have hW : mvC + pegCharge n bench + 2 * n ≤
      mv + (n + m * pegCharge n bench + mulCharge n bench + n) + pegCharge n bench + 2 * n := by
    omega
  have hflat : mv + (n + m * pegCharge n bench + mulCharge n bench + n) + pegCharge n bench +
      2 * n =
      mv + (n + m * pegCharge n bench + mulCharge n bench + n + pegCharge n bench + 2 * n) := by
    omega
  have hcap : mvC + pegCharge n bench + 2 * n ≤ mv + rungCharge n bench m := by
    exact Nat.le_trans hW (Nat.le_trans (Nat.le_of_eq hflat) (Nat.add_le_add_left hpiece mv))
  have hboth : mvC + 2 * peg + 2 * n + 3 * (bench - n) + 2 * n ≤
      mv + rungCharge n bench m := by
    have hstep : mvC + 2 * peg + 2 * n + 3 * (bench - n) + 2 * n ≤
        mvC + pegCharge n bench + 2 * n :=
      Nat.add_le_add_right hfold _
    exact Nat.le_trans hstep hcap
  have h0 := Nat.le_sub_of_add_le hboth
  rwa [Nat.add_sub_assoc (rung_ge_two n bench m)] at h0

/-- The red mul, once the clear is `2 · n` under the white piece. -/
theorem red_mul_tight (n bench m mv mvC mvRed : Nat)
    (hC : mvC + 2 * n ≤ mv + n + m * pegCharge n bench + mulCharge n bench + n)
    (hRed : mvRed ≤ mvC + pegCharge n bench + mulCharge n bench) :
    mvRed + 2 * n ≤ mv + rungCharge n bench m := by
  have hred := charge_final_red n bench m
  omega

/-- A short clear plus at most two settles stays `2 · n` under the slide charge. -/
theorem red_slide_tight (n m sl slC slR : Nat)
    (hW : slC ≤ sl + m * (2 * n))
    (hR : slR ≤ slC + 2 * n + 2 * n) :
    slR + 2 * n ≤ sl + rungSlideCharge n m := by
  unfold rungSlideCharge
  have hsplit : (m + 3) * (2 * n) = m * (2 * n) + 3 * (2 * n) := by
    rw [Nat.add_mul]
  omega

/-- Two extra settles still sit in the tight slide remainder of the `mMax` charge. -/
theorem red_slide_headroom (n m mMax sl extra : Nat)
    (hT : m ≤ mMax)
    (h : extra ≤ sl + m * (2 * n) + 2 * n + 2 * n) :
    extra ≤ sl + (rungSlideCharge n mMax - 2 * n) := by
  have hmono := rungSlideCharge_mono n m mMax hT
  have hge := slide_ge_two n m
  have hpiece : m * (2 * n) + 2 * n + 2 * n + 2 * n ≤ rungSlideCharge n m := by
    unfold rungSlideCharge
    rw [Nat.add_mul]
    omega
  have hlocal : extra + 2 * n ≤ sl + rungSlideCharge n m := by
    omega
  have hsub0 : extra ≤ (sl + rungSlideCharge n m) - 2 * n :=
    Nat.le_sub_of_add_le hlocal
  have hsub : extra ≤ sl + (rungSlideCharge n m - 2 * n) := by
    rwa [Nat.add_sub_assoc hge] at hsub0
  exact Nat.le_trans hsub (Nat.add_le_add_left (Nat.sub_le_sub_right hmono _) sl)

/-- The red mul's fold sits in the tight remainder when the clear is short. -/
theorem red_fold_headroom (n bench m mv mvC mvCube peg : Nat)
    (hC : mvC + 2 * n ≤ mv + n + m * pegCharge n bench + mulCharge n bench + n)
    (hCube : mvCube ≤ mvC + pegCharge n bench)
    (hp : peg ≤ n) :
    mvCube + 2 * peg + n * (n + 1) + 3 * (bench - n) ≤
      mv + (rungCharge n bench m - 2 * n) := by
  have h2 : 2 * peg ≤ 2 * n := Nat.mul_le_mul_left 2 hp
  have hpiece : 2 * peg + n * (n + 1) + 3 * (bench - n) ≤ mulCharge n bench := by
    unfold mulCharge
    exact Nat.add_le_add_right (Nat.add_le_add_right h2 _) _
  have hfold : mvCube + 2 * peg + n * (n + 1) + 3 * (bench - n) ≤
      mvCube + mulCharge n bench := by omega
  have hup : mvCube + mulCharge n bench + 2 * n ≤
      mv + rungCharge n bench m := by
    have h1 : mvCube + mulCharge n bench ≤ mvC + pegCharge n bench + mulCharge n bench := by
      omega
    have h2n : mvC + pegCharge n bench + mulCharge n bench + 2 * n ≤
        mv + (n + m * pegCharge n bench + mulCharge n bench + n) +
          pegCharge n bench + mulCharge n bench := by omega
    have hred := charge_final_red n bench m
    have hflat : mv + (n + m * pegCharge n bench + mulCharge n bench + n +
        pegCharge n bench + mulCharge n bench) =
        mv + (n + m * pegCharge n bench + mulCharge n bench + n) +
          pegCharge n bench + mulCharge n bench := by omega
    have hcap : mv + (n + m * pegCharge n bench + mulCharge n bench + n) +
        pegCharge n bench + mulCharge n bench ≤ mv + rungCharge n bench m := by
      rw [← hflat]
      exact Nat.add_le_add_left hred mv
    omega
  have hboth : mvCube + 2 * peg + n * (n + 1) + 3 * (bench - n) + 2 * n ≤
      mv + rungCharge n bench m := by omega
  have h0 := Nat.le_sub_of_add_le hboth
  rwa [Nat.add_sub_assoc (rung_ge_two n bench m)] at h0

/-- `mv` after `done` rungs, plus the tight remainder of one more charge, fits
    the `R`-charge budget. `done + 1 ≤ R` because `rest` is a suffix of `r :: rest`. -/
theorem move_headroom_of (moves0 R done n bench mMax mv : Nat)
    (hk : done + 1 ≤ R)
    (hmv : mv ≤ moves0 + done * rungCharge n bench mMax)
    (hf : FitsLen (moves0 + R * rungCharge n bench mMax)) :
    FitsLen (mv + (rungCharge n bench mMax - 2 * n)) := by
  apply FitsLen.of_le hf
  have hge := rung_ge_two n bench mMax
  have hsub : mv + (rungCharge n bench mMax - 2 * n) ≤ mv + rungCharge n bench mMax :=
    Nat.add_le_add_left (Nat.sub_le _ _) _
  have hstep : mv + rungCharge n bench mMax ≤
      moves0 + (done + 1) * rungCharge n bench mMax := by
    have hsucc : moves0 + done * rungCharge n bench mMax + rungCharge n bench mMax =
        moves0 + (done + 1) * rungCharge n bench mMax := by
      rw [Nat.add_assoc, ← Nat.succ_mul]
    exact Nat.le_trans (Nat.add_le_add_right hmv _) (Nat.le_of_eq hsucc)
  have hR : (done + 1) * rungCharge n bench mMax ≤ R * rungCharge n bench mMax :=
    Nat.mul_le_mul_right _ hk
  exact Nat.le_trans hsub (Nat.le_trans hstep (Nat.add_le_add_left hR moves0))

/-- The slid counter is `mv + 2 · pegs`. The invariant already reserves `2 · n`
    on a bench-on counter, so `mv + 2 · pegs + (rungCharge − 2 · n)` sits inside
    one more charge of `moves0`. -/
theorem bench_headroom_of (moves0 R done n bench mMax mv pegs : Nat)
    (hk : done + 1 ≤ R)
    (hmv : mv + 2 * n ≤ moves0 + done * rungCharge n bench mMax)
    (hpeg : pegs ≤ n)
    (hf : FitsLen (moves0 + R * rungCharge n bench mMax)) :
    FitsLen (mv + 2 * pegs + (rungCharge n bench mMax - 2 * n)) := by
  apply FitsLen.of_le hf
  have hge := rung_ge_two n bench mMax
  have hpeg2 : 2 * pegs ≤ 2 * n := Nat.mul_le_mul_left 2 hpeg
  have hmid : mv + 2 * pegs + (rungCharge n bench mMax - 2 * n) ≤
      (mv + 2 * n) + rungCharge n bench mMax - 2 * n := by
    have h1 : mv + 2 * pegs + (rungCharge n bench mMax - 2 * n) ≤
        mv + 2 * n + (rungCharge n bench mMax - 2 * n) :=
      Nat.add_le_add_right (Nat.add_le_add_left hpeg2 mv) _
    have h2 : mv + 2 * n + (rungCharge n bench mMax - 2 * n) =
        (mv + 2 * n) + rungCharge n bench mMax - 2 * n := by
      rw [← Nat.add_sub_assoc hge]
    exact Nat.le_trans h1 (Nat.le_of_eq h2)
  have htop : (mv + 2 * n) + rungCharge n bench mMax - 2 * n ≤
      moves0 + (done + 1) * rungCharge n bench mMax := by
    have hsub : (mv + 2 * n) + rungCharge n bench mMax - 2 * n ≤
        (mv + 2 * n) + rungCharge n bench mMax := Nat.sub_le _ _
    have hle : (mv + 2 * n) + rungCharge n bench mMax ≤
        moves0 + done * rungCharge n bench mMax + rungCharge n bench mMax :=
      Nat.add_le_add_right hmv _
    have hsucc : moves0 + done * rungCharge n bench mMax + rungCharge n bench mMax =
        moves0 + (done + 1) * rungCharge n bench mMax := by
      rw [Nat.add_assoc, ← Nat.succ_mul]
    exact Nat.le_trans hsub (Nat.le_trans hle (Nat.le_of_eq hsucc))
  have hR : moves0 + (done + 1) * rungCharge n bench mMax ≤
      moves0 + R * rungCharge n bench mMax :=
    Nat.add_le_add_left (Nat.mul_le_mul_right _ hk) _
  exact Nat.le_trans hmid (Nat.le_trans htop hR)

/-- Same headroom for the slide counter. -/
theorem slide_headroom_of (slides0 R done n mMax sl : Nat)
    (hk : done + 1 ≤ R)
    (hsl : sl ≤ slides0 + done * rungSlideCharge n mMax)
    (hf : FitsLen (slides0 + R * rungSlideCharge n mMax)) :
    FitsLen (sl + (rungSlideCharge n mMax - 2 * n)) := by
  apply FitsLen.of_le hf
  have hge := slide_ge_two n mMax
  have hsub : sl + (rungSlideCharge n mMax - 2 * n) ≤ sl + rungSlideCharge n mMax :=
    Nat.add_le_add_left (Nat.sub_le _ _) _
  have hstep : sl + rungSlideCharge n mMax ≤
      slides0 + (done + 1) * rungSlideCharge n mMax := by
    have hsucc : slides0 + done * rungSlideCharge n mMax + rungSlideCharge n mMax =
        slides0 + (done + 1) * rungSlideCharge n mMax := by
      rw [Nat.add_assoc, ← Nat.succ_mul]
    exact Nat.le_trans (Nat.add_le_add_right hsl _) (Nat.le_of_eq hsucc)
  have hR : (done + 1) * rungSlideCharge n mMax ≤ R * rungSlideCharge n mMax :=
    Nat.mul_le_mul_right _ hk
  exact Nat.le_trans hsub (Nat.le_trans hstep (Nat.add_le_add_left hR slides0))

/-- Slid slides `sl + 2 · pegs`. The bench reservation of `2 · n` absorbs that
    slide, and the tight remainder still fits one more slide charge. -/
theorem bench_slide_headroom_of (slides0 R done n mMax sl pegs : Nat)
    (hk : done + 1 ≤ R)
    (hsl : sl + 2 * n ≤ slides0 + done * rungSlideCharge n mMax)
    (hpeg : pegs ≤ n)
    (hf : FitsLen (slides0 + R * rungSlideCharge n mMax)) :
    FitsLen (sl + 2 * pegs + (rungSlideCharge n mMax - 2 * n)) := by
  apply FitsLen.of_le hf
  have hge := slide_ge_two n mMax
  have hpeg2 : 2 * pegs ≤ 2 * n := Nat.mul_le_mul_left 2 hpeg
  have hmid : sl + 2 * pegs + (rungSlideCharge n mMax - 2 * n) ≤
      (sl + 2 * n) + rungSlideCharge n mMax - 2 * n := by
    have h1 : sl + 2 * pegs + (rungSlideCharge n mMax - 2 * n) ≤
        sl + 2 * n + (rungSlideCharge n mMax - 2 * n) :=
      Nat.add_le_add_right (Nat.add_le_add_left hpeg2 sl) _
    have h2 : sl + 2 * n + (rungSlideCharge n mMax - 2 * n) =
        (sl + 2 * n) + rungSlideCharge n mMax - 2 * n := by
      rw [← Nat.add_sub_assoc hge]
    exact Nat.le_trans h1 (Nat.le_of_eq h2)
  have htop : (sl + 2 * n) + rungSlideCharge n mMax - 2 * n ≤
      slides0 + (done + 1) * rungSlideCharge n mMax := by
    have hsub : (sl + 2 * n) + rungSlideCharge n mMax - 2 * n ≤
        (sl + 2 * n) + rungSlideCharge n mMax := Nat.sub_le _ _
    have hle : (sl + 2 * n) + rungSlideCharge n mMax ≤
        slides0 + done * rungSlideCharge n mMax + rungSlideCharge n mMax :=
      Nat.add_le_add_right hsl _
    have hsucc : slides0 + done * rungSlideCharge n mMax + rungSlideCharge n mMax =
        slides0 + (done + 1) * rungSlideCharge n mMax := by
      rw [Nat.add_assoc, ← Nat.succ_mul]
    exact Nat.le_trans hsub (Nat.le_trans hle (Nat.le_of_eq hsucc))
  have hR : slides0 + (done + 1) * rungSlideCharge n mMax ≤
      slides0 + R * rungSlideCharge n mMax :=
    Nat.add_le_add_left (Nat.mul_le_mul_right _ hk) _
  exact Nat.le_trans hmid (Nat.le_trans htop hR)

/-- A cons-tail rung has one charge of tight headroom on the stored move counter. -/
noncomputable def moveHeadroom_of_cons {done rest : List Nat} {r : Nat} {b : Ecbs.Board}
    {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvK done (r :: rest) b s base) :
    MoveHeadroom b base.n base.bench base.mMax :=
  let mv := Classical.choose h.moves
  have hspec := Classical.choose_spec h.moves
  have hloose : mv ≤ base.moves0 + done.length * rungCharge base.n base.bench base.mMax := by
    have h := hspec.2
    cases hs : s.onBench <;> simp [hs] at h <;> omega
  have hk : done.length + 1 ≤ base.R := by
    have hlen := h.kLe
    rw [List.length_append, List.length_cons] at hlen
    omega
  ⟨mv, hspec.1, move_headroom_of base.moves0 base.R done.length base.n base.bench base.mMax
    mv hk hloose base.fitM⟩

/-- A cons-tail rung has one charge of tight headroom on the stored slide counter. -/
noncomputable def slideHeadroom_of_cons {done rest : List Nat} {r : Nat} {b : Ecbs.Board}
    {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvK done (r :: rest) b s base) :
    SlideHeadroom b base.n base.mMax :=
  let sl := Classical.choose h.slides
  have hspec := Classical.choose_spec h.slides
  have hloose : sl ≤ base.slides0 + done.length * rungSlideCharge base.n base.mMax := by
    have h := hspec.2
    cases hs : s.onBench <;> simp [hs] at h <;> omega
  have hk : done.length + 1 ≤ base.R := by
    have hlen := h.kLe
    rw [List.length_append, List.length_cons] at hlen
    omega
  ⟨sl, hspec.1, slide_headroom_of base.slides0 base.R done.length base.n base.mMax
    sl hk hloose base.fitS⟩

/-- `pegs + rest` sits inside the headroom on the actual counter. -/
theorem copy_then_pegs_fit (mv room pegs rest : Nat)
    (hroom : FitsLen (mv + room))
    (hex : pegs + rest ≤ room) :
    FitsLen (mv + pegs + rest) :=
  FitsLen.of_le hroom (by
    rw [Nat.add_assoc]
    exact Nat.add_le_add_left hex mv)

/-- The bench-off cube-peg context on the idle `park_rung` board. `peg_of_shape`
    builds the same context on the entry board, so its row is `s.row` and its
    counter is `s.ctrl`. Here the copy reads the keep-park board: the row is
    `afterPark`, the counter has already grown by two, and the parked-from hole,
    the rung index, and the tally length are the park board's. `place` copies
    those five. -/
theorem parked_peg_ctx {done rest : List Nat} {r : Nat} {b : Ecbs.Board}
    {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvKCore done (r :: rest) b s base)
    (hM : MoveHeadroom b base.n base.bench base.mMax)
    (hS : SlideHeadroom b base.n base.mMax)
    (hF : s.fromHole < 0) (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax)
    (hhome : s.onBench = false) :
    ∃ (bPark : Ecbs.Board) (c : PegCtx),
      Ecbs.park_rung b (r : Int) = .ok bPark ∧
      Ecbs.copy_band bPark ((6 : Nat) : Int) ((5 : Nat) : Int) false = .ok c.b0 ∧
      c.row0 = afterPark s.row (-1) s.parkAt (climbAt base.ladder0 base.R s.ridx) r ∧
      c.ctrl0 = s.ctrl + 2 ∧
      c.m = s.tally ∧
      c.t0 = s.t0 ∧
      c.g = s.gap ∧
      c.n = s.n ∧
      c.k = s.k ∧
      c.bench = s.benchlen ∧
      c.src = 6 ∧
      c.b0.sudo_5Board_11parked_from =
        ((climbAt base.ladder0 base.R s.ridx : Nat) : Int) ∧
      c.b0.sudo_5Board_8rung_idx = ((s.ridx + 1 : Nat) : Int) ∧
      c.b0.sudo_5Board_9tally_len = (s.tally : Int) ∧
      (∃ (mv pk sl : Nat)
        (h6H : 6 < bPark.sudo_5Board_4home.size)
        (h6D : 6 < bPark.sudo_5Board_4held.size),
        b.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int) ∧
        b.sudo_5Board_4cost.sudo_5Costs_4peak = (pk : Int) ∧
        b.sudo_5Board_4cost.sudo_5Costs_6slides = (sl : Int) ∧
        c.moves0 = mv + pegCount s.gap ∧
        c.slides0 = sl ∧
        c.b0 = placeBoard bPark 6 h6H h6D s.gap mv pk) := by
  let hole := climbAt base.ladder0 base.R s.ridx
  obtain ⟨bPark0, hpark, _hfrom, _hridx, hkeep⟩ := park_of_shape h
  obtain ⟨hRowP, hRowH, hEq⟩ := hkeep hF
  let bPark := parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH
  have hparkEq : Ecbs.park_rung b (r : Int) = .ok bPark := by
    simpa [bPark, hEq] using hpark
  have hAP : afterPark s.row (-1) s.parkAt hole r =
      (s.row.set s.parkAt r).set hole 0 := by
    unfold afterPark
    rw [if_pos (by decide : (-1 : Int) < 0)]
  have hmv := hM.eq
  have hsl := hS.eq
  let mv := hM.mv
  let sl := hS.sl
  obtain ⟨cOps, hcOps⟩ := h.shape.peg.cOps
  obtain ⟨pkS, hpkS⟩ := h.shape.peg.peakS
  obtain ⟨holeM, hhole⟩ := h.shape.peg.holeM
  obtain ⟨pk, hpk, _⟩ := h.peak
  have hgapH := h.inv.gapHome hhome
  have hoff0 : b.sudo_5Board_8bench_on = false := h.shape.offWhenHome hhome
  have hk : done.length + 1 ≤ base.R := by
    have hlen := h.kLe
    rw [List.length_append, List.length_cons] at hlen
    omega
  have hdoneLe : done.length ≤ base.R := by
    have hlen := h.kLe
    simp [List.length_append, List.length_cons] at hlen
    omega
  have hpegN : pegCount s.gap ≤ s.n := by
    rw [← h.shape.gapLen]
    exact pegCount_le s.gap
  have hcharge : pegCount s.gap + s.tally * pegCharge s.n s.benchlen ≤
      rungCharge base.n base.bench base.mMax := by
    unfold rungCharge
    have hmul : s.tally * pegCharge s.n s.benchlen ≤
        (base.mMax + 1) * pegCharge s.n s.benchlen :=
      Nat.mul_le_mul_right _ (Nat.le_succ_of_le hT)
    have hsum : pegCount s.gap + s.tally * pegCharge s.n s.benchlen ≤
        s.n + (base.mMax + 1) * pegCharge s.n s.benchlen := by
      exact Nat.add_le_add hpegN (Nat.le_trans hmul (Nat.le_refl _))
    have hrest : s.n + (base.mMax + 1) * pegCharge s.n s.benchlen ≤
        2 * s.n + (base.mMax + 1) * pegCharge s.n s.benchlen +
          2 * mulCharge s.n s.benchlen := by
      omega
    have hn : s.n = base.n := h.hn
    have hb : s.benchlen = base.bench := h.hbench
    exact Nat.le_trans hsum (by simpa [hn, hb] using hrest)
  have hmovFit : FitsLen (mv + pegCount s.gap + s.tally * pegCharge s.n s.benchlen) := by
    apply FitsLen.of_le (MoveHeadroom.at hM hmv)
    rw [Nat.add_assoc]
    apply Nat.add_le_add_left
    rw [h.hn, h.hbench]
    exact gap_copy_room base.n base.bench base.mMax s.tally (pegCount s.gap)
      (by rw [← h.hn]; exact hpegN) hT
  have hfitCopy : FitsLen (mv + pegCount s.gap) :=
    FitsLen.of_le hmovFit (by omega)
  have hmvP : bPark.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int) := by
    simpa [bPark, parkKeepBoard] using hmv
  have hpkP : bPark.sudo_5Board_4cost.sudo_5Costs_4peak = (pk : Int) := by
    simpa [bPark, parkKeepBoard] using hpk
  have hslP : bPark.sudo_5Board_4cost.sudo_5Costs_6slides = (sl : Int) := by
    simpa [bPark, parkKeepBoard] using hsl
  have h6H : 6 < bPark.sudo_5Board_4home.size := by
    simpa [bPark, parkKeepBoard] using h.shape.spareH
  have h6D : 6 < bPark.sudo_5Board_4held.size := by
    simpa [bPark, parkKeepBoard] using h.shape.spareD
  have h5H : 5 < bPark.sudo_5Board_4home.size := by
    simpa [bPark, parkKeepBoard] using h.inv.hG
  have h5D : 5 < bPark.sudo_5Board_4held.size := by
    simpa [bPark, parkKeepBoard] using h.inv.hGs
  have h7P : 7 ≤ bPark.sudo_5Board_4held.size := by
    simpa [bPark, parkKeepBoard] using h.shape.h7
  have hsrcP : bPark.sudo_5Board_4held[5] = true := by
    simpa [bPark, parkKeepBoard] using hgapH.1
  have harrP : bPark.sudo_5Board_4home[5] = embed s.gap := by
    simpa [bPark, parkKeepBoard] using hgapH.2
  have hemptyP : bPark.sudo_5Board_4held[6] = false := by
    simpa [bPark, parkKeepBoard] using h.shape.spareE
  have hnP : bPark.sudo_5Board_1t.sudo_4Tier_1n = (s.gap.length : Int) := by
    simpa [bPark, parkKeepBoard] using (show b.sudo_5Board_1t.sudo_4Tier_1n =
      (s.gap.length : Int) by rw [h.shape.gapLen]; exact h.shape.tierN)
  have hcopy := copy_band_refines bPark 6 5 s.gap mv pk
    h6H h6D h5H h5D h7P hsrcP harrP hemptyP hnP
    (by rw [h.shape.gapLen]; exact h.shape.peg.fitN)
    hmvP hpkP hfitCopy
  let b1 := placeBoard bPark 6 h6H h6D s.gap mv pk
  have hbook := place_book bPark 6 ⟨h6H, h6D⟩ s.gap mv pk
  have hidle := place_idle bPark 6 ⟨h6H, h6D⟩ s.gap mv pk
  have hlen0 : b1.sudo_5Board_9tally_len = (s.tally : Int) := by
    rw [hbook.2.2.2.1]
    simpa [bPark, parkKeepBoard] using h.inv.len
  have hfromB : b1.sudo_5Board_11parked_from = ((hole : Nat) : Int) := by
    rw [hbook.2.1]
    rfl
  have hridxB : b1.sudo_5Board_8rung_idx = ((s.ridx + 1 : Nat) : Int) := by
    rw [hbook.2.2.1]
    exact ofNat_eq_natCast _
  have hmarkP : bPark.sudo_5Board_9marker_on = b.sudo_5Board_9marker_on := by
    simp [bPark, parkKeepBoard]
  have hoffP : bPark.sudo_5Board_8bench_on = b.sudo_5Board_8bench_on := by
    simp [bPark, parkKeepBoard]
  have hopsP : bPark.sudo_5Board_4cost.sudo_5Costs_3ops =
      b.sudo_5Board_4cost.sudo_5Costs_3ops := by
    simp [bPark, parkKeepBoard]
  have htierP : bPark.sudo_5Board_1t = b.sudo_5Board_1t := by
    simp [bPark, parkKeepBoard]
  have hstrictP : bPark.sudo_5Board_4cost.sudo_5Costs_11peak_strict =
      b.sudo_5Board_4cost.sudo_5Costs_11peak_strict := by
    simp [bPark, parkKeepBoard]
  have hholeP : bPark.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole := by
    simp [bPark, parkKeepBoard]
  have ht0P : bPark.sudo_5Board_6tally0 = b.sudo_5Board_6tally0 := by
    simp [bPark, parkKeepBoard]
  have hhighP : bPark.sudo_5Board_4cost.sudo_5Costs_15control_highest =
      b.sudo_5Board_4cost.sudo_5Costs_15control_highest := by
    simp [bPark, parkKeepBoard]
  let pk1 := if pk < countHeld (bPark.sudo_5Board_4held.set ⟨6, h6D⟩ true) 7
    then countHeld (bPark.sudo_5Board_4held.set ⟨6, h6D⟩ true) 7 else pk
  refine ⟨bPark, {
    b0 := b1
    src := 6
    g := s.gap
    row0 := afterPark s.row (-1) s.parkAt hole r
    w := base.w
    h := base.h
    r := base.r
    n := s.n
    k := s.k
    bench := s.benchlen
    cg := base.cg
    moves0 := mv + pegCount s.gap
    slides0 := sl
    hole0 := holeM
    peak0 := pk1
    peakS0 := pkS
    cOps0 := cOps
    t0 := s.t0
    high := s.high
    control := base.control
    ctrl0 := s.ctrl + 2
    m := s.tally
    hm := hm
    hmk := by rw [hidle.1, hmarkP]; exact h.inv.marker
    hoff := by rw [hidle.2.1, hoffP]; exact hoff0
    hops0 := by rw [hidle.2.2.1, hopsP]; exact h.shape.peg.opsGt
    hop10 := by
      have hsz : 1 < b1.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
        rw [hidle.2.2.1, hopsP]; exact h.shape.peg.opsGt
      have hget := idx_get (hidle.2.2.1.trans hopsP) 1 hsz
      exact hget.trans hcOps
    hbl := by rw [hidle.2.2.2.2.1, htierP, h.shape.tierB]; exact ofNat_eq_natCast s.benchlen
    hcg := by rw [hidle.2.2.2.2.1, htierP, h.shape.tierCg]; exact ofNat_eq_natCast base.cg
    hspan := h.shape.peg.span
    hF := by rw [hbook.2.2.2.2.2.2.2.2.2]; exact h6D
    hHome := by rw [hbook.2.2.2.2.2.2.2.2.1]; exact h6H
    hHF := by
      have hF : 6 < b1.sudo_5Board_4held.size := by
        rw [hbook.2.2.2.2.2.2.2.2.2]; exact h6D
      simpa using place_held_here bPark 6 ⟨h6H, h6D⟩ s.gap mv pk hF
    hArr := by
      have hF : 6 < b1.sudo_5Board_4home.size := by
        rw [hbook.2.2.2.2.2.2.2.2.1]; exact h6H
      simpa using place_home_here bPark 6 ⟨h6H, h6D⟩ s.gap mv pk hF
    h7 := by rw [hbook.2.2.2.2.2.2.2.2.2]; exact h7P
    hn0 := h.shape.peg.n_pos
    hn := by rw [hidle.2.2.2.2.1, htierP]; exact h.shape.tierN
    hlenx := h.shape.gapLen
    hf := h.shape.peg.fitN
    hmoves0 := by
      rw [place_moves bPark 6 ⟨h6H, h6D⟩ s.gap mv pk]
      exact ofNat_eq_natCast _
    hpeak0 := by
      rw [place_peak bPark 6 ⟨h6H, h6D⟩ s.gap mv pk hpkP]
      exact ofNat_eq_natCast _
    hpeakS0 := by rw [hidle.2.2.2.2.2.1, hstrictP]; exact hpkS
    hxsT := h.shape.peg.trits
    h3 := h.shape.peg.fit3
    hw0 := h.shape.w0
    hh0 := h.shape.h0
    hrR := h.shape.rlt
    hrP := h.shape.r0
    hnE := h.shape.n_eq
    hkLe := h.shape.k_le
    hgap := h.shape.gap_eq
    hwF := by rw [hidle.2.2.2.2.1, htierP, h.shape.tierW]; exact ofNat_eq_natCast base.w
    hhF := by rw [hidle.2.2.2.2.1, htierP, h.shape.tierH]; exact ofNat_eq_natCast base.h
    hrF := by rw [hidle.2.2.2.2.1, htierP, h.shape.tierR]; exact ofNat_eq_natCast base.r
    hkF := by rw [hidle.2.2.2.2.1, htierP, h.shape.tierK]; exact ofNat_eq_natCast s.k
    hHole0 := by rw [hidle.2.2.2.2.2.2, hholeP]; exact hhole
    hsm := by
      have hs := h.shape.peg.small
      have hb : s.benchlen = base.bench := h.hbench
      simpa [hb] using hs
    hnsm := h.shape.peg.n_small
    hfitB := h.shape.peg.fitBn
    hT0 := by rw [hbook.2.2.2.2.1, ht0P, h.inv.t0]
    hRow := by
      rw [hbook.1]
      rw [parkKeep_row b s.row hole s.parkAt r s.ridx s.ctrl hRowP hRowH h.inv.row
        h.shape.park.parkLt h.shape.park.holeLt, ← hAP]
    hRoom := by
      have hlenR : (afterPark s.row (-1) s.parkAt hole r).length = s.row.length := by
        rw [hAP]
        simp [List.length_set]
      rw [hlenR]
      exact h.shape.seg.room
    hCtrlN := by rw [hidle.2.2.2.2.1, htierP]; exact h.shape.tierC
    hHigh := by rw [hbook.2.2.2.2.2.2.1, hhighP, h.inv.high]
    hTop := h.shape.peg.top hm
    hIn := by rw [← h.shape.rowLen]; exact h.shape.seg.room
    hCtrl0 := by
      rw [hbook.2.2.2.2.2.2.2.1]
      exact ofNat_eq_natCast _
    hslides0 := by rw [hidle.2.2.2.1, hslP]; exact ofNat_eq_natCast sl
    hfitRow := h.shape.peg.fitRow
    hfitM := h.shape.peg.fitTall
    hBudget := hmovFit
    hSlide := by
      apply FitsLen.of_le (SlideHeadroom.at hS hsl)
      have hn : s.n = base.n := h.hn
      have hmul : s.tally * (2 * base.n) + 2 * base.n ≤
          rungSlideCharge base.n base.mMax := by
        unfold rungSlideCharge
        rw [Nat.add_mul]
        have hle : s.tally + 1 ≤ base.mMax + 3 := by omega
        have h := Nat.mul_le_mul_right (2 * base.n) hle
        rw [Nat.succ_mul, Nat.add_mul] at h
        exact h
      have hsub : s.tally * (2 * base.n) ≤
          rungSlideCharge base.n base.mMax - 2 * base.n :=
        Nat.le_sub_of_add_le hmul
      rw [hn]
      exact Nat.add_le_add_left hsub sl
    hOpsB := by
      obtain ⟨c0, hc0, hcle⟩ := h.ops 1 h.shape.peg.opsGt
      have hc : cOps = c0 := ofNat_inj_nat (hcOps.symm.trans hc0)
      apply FitsLen.of_le base.fitO
      have hstep : cOps + s.tally ≤
          base.ops0 + (done.length + 1) * (base.mMax + 3) := by
        have hsucc : (done.length + 1) * (base.mMax + 3) =
            done.length * (base.mMax + 3) + (base.mMax + 3) := by rw [Nat.succ_mul]
        have ht : s.tally ≤ base.mMax + 3 := Nat.le_trans hT (Nat.le_add_right _ _)
        omega
      have hR : (done.length + 1) * (base.mMax + 3) ≤ base.R * (base.mMax + 3) :=
        Nat.mul_le_mul_right _ hk
      omega
    hCtrlB := ctrl_park_peg_fit h.ctrlLe hT hm hdoneLe base.fitCtrl
  }, hparkEq, hcopy, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hfromB, hridxB, hlen0,
    ⟨mv, pk, sl, h6H, h6D, hmv, hpk, hsl, rfl, rfl, rfl⟩⟩

/-- A home other than the cube source, and ops slot 0, as read off a board. -/
structure HomeKeep (b : Ecbs.Board) (first : Nat) (xs0 : List Nat) (cMul : Nat) : Prop where
  heldLt : first < b.sudo_5Board_4held.size
  held : b.sudo_5Board_4held[first]'heldLt = true
  homeLt : first < b.sudo_5Board_4home.size
  arr : b.sudo_5Board_4home[first]'homeLt = embed xs0
  opsLt : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size
  op0 : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]'opsLt = (cMul : Int)

/-- Homes other than `src`, and ops slot 0, survive the bench-off peg.
    That cube writes home `src` and ops slot 1. The red peg does not. -/
private theorem offPeg_keep (c : PegCtx) (first : Nat) (xs0 : List Nat) (cMul : Nat)
    (hFD : first < c.b0.sudo_5Board_4held.size)
    (hFH : first < c.b0.sudo_5Board_4home.size)
    (hne : first ≠ c.src)
    (hHeld : c.b0.sudo_5Board_4held[first] = true)
    (hArr : c.b0.sudo_5Board_4home[first] = embed xs0)
    (hopsZ : 0 < c.b0.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hopZ : c.b0.sudo_5Board_4cost.sudo_5Costs_3ops[0] = (cMul : Int)) :
    HomeKeep (offPeg c) first xs0 cMul := by
  have hHeldEq : (offPeg c).sudo_5Board_4held =
      c.b0.sudo_5Board_4held.set ⟨c.src, c.hF⟩ false := by
    unfold offPeg pegStep
    rw [cube_off_held]
  have hHomeEq : (offPeg c).sudo_5Board_4home =
      c.b0.sudo_5Board_4home.set ⟨c.src, c.hHome⟩ #[] := by
    unfold offPeg pegStep
    rw [cube_off_home]
  have hOpsEq : (offPeg c).sudo_5Board_4cost.sudo_5Costs_3ops =
      c.b0.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨1, c.hops0⟩
        (Int.ofNat (c.cOps0 + 1)) := by
    unfold offPeg pegStep
    rw [cube_off_ops]
  have heldLt : first < (offPeg c).sudo_5Board_4held.size := by
    rw [hHeldEq, Array.size_set]; exact hFD
  have held : (offPeg c).sudo_5Board_4held[first] = true := by
    rw [show (offPeg c).sudo_5Board_4held[first] =
        (c.b0.sudo_5Board_4held.set ⟨c.src, c.hF⟩ false)[first]'(hHeldEq ▸ heldLt) from
      idx_get hHeldEq first heldLt]
    rw [Array.getElem_set, if_neg (Ne.symm hne)]
    exact hHeld
  have homeLt : first < (offPeg c).sudo_5Board_4home.size := by
    rw [hHomeEq, Array.size_set]; exact hFH
  have arr : (offPeg c).sudo_5Board_4home[first] = embed xs0 := by
    rw [show (offPeg c).sudo_5Board_4home[first] =
        (c.b0.sudo_5Board_4home.set ⟨c.src, c.hHome⟩ #[])[first]'(hHomeEq ▸ homeLt) from
      idx_get hHomeEq first homeLt]
    rw [Array.getElem_set, if_neg (Ne.symm hne)]
    exact hArr
  have opsLt : 0 < (offPeg c).sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [hOpsEq, Array.size_set]; exact hopsZ
  have op0 : (offPeg c).sudo_5Board_4cost.sudo_5Costs_3ops[0] = (cMul : Int) := by
    rw [show (offPeg c).sudo_5Board_4cost.sudo_5Costs_3ops[0] =
        (c.b0.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨1, c.hops0⟩
          (Int.ofNat (c.cOps0 + 1)))[0]'(hOpsEq ▸ opsLt) from idx_get hOpsEq 0 opsLt]
    rw [Array.getElem_set, if_neg (by decide : (1 : Nat) ≠ 0)]
    exact hopZ
  exact { heldLt, held, homeLt, arr, opsLt, op0 }

/-- The same facts after one live peg. The live cube settles into `src` and
    then cubes it, so it still writes only that home and ops slot 1. -/
private theorem livePeg_keep (c : PegCtx) {i : Nat} (d : LivePeg c i) (hi : i < c.m)
    (first : Nat) (xs0 : List Nat) (cMul : Nat)
    (hFD : first < d.b.sudo_5Board_4held.size)
    (hFH : first < d.b.sudo_5Board_4home.size)
    (hne : first ≠ c.src)
    (hHeld : d.b.sudo_5Board_4held[first] = true)
    (hArr : d.b.sudo_5Board_4home[first] = embed xs0)
    (hopsZ : 0 < d.b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hopZ : d.b.sudo_5Board_4cost.sudo_5Costs_3ops[0] = (cMul : Int)) :
    HomeKeep (livePegBoard c d hi) first xs0 cMul := by
  let bC := cubeLiveBoard d.b c.src c.src d.xs ⟨c.n, c.k, d.moves, d.slides, d.hole, c.bench, d.peak, d.peakS, d.cOps, d.hops⟩ ⟨d.hH, d.hD⟩
  have hLiveH : (livePegBoard c d hi).sudo_5Board_4held = bC.sudo_5Board_4held := by
    unfold livePegBoard pegStep; rfl
  have hLiveHome : (livePegBoard c d hi).sudo_5Board_4home = bC.sudo_5Board_4home := by
    unfold livePegBoard pegStep; rfl
  have hLiveOps : (livePegBoard c d hi).sudo_5Board_4cost.sudo_5Costs_3ops =
      bC.sudo_5Board_4cost.sudo_5Costs_3ops := by
    unfold livePegBoard pegStep; rfl
  have hC := cube_live_held d.b c.src c.src d.xs ⟨c.n, c.k, d.moves, d.slides, d.hole, c.bench, d.peak, d.peakS, d.cOps, d.hops⟩ ⟨d.hH, d.hD⟩
  have hS := settle_held_eq d.b c.src ⟨d.hH, d.hD⟩ d.xs c.n d.moves d.slides d.peak
  have hHomeEq : bC.sudo_5Board_4home =
      d.b.sudo_5Board_4home.set ⟨c.src, d.hH⟩ #[] :=
    cube_live_home d.b c.src c.src d.xs ⟨c.n, c.k, d.moves, d.slides, d.hole, c.bench, d.peak, d.peakS, d.cOps, d.hops⟩ ⟨d.hH, d.hD⟩
  have hOpsEq : bC.sudo_5Board_4cost.sudo_5Costs_3ops =
      d.b.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨1, d.hops⟩ (Int.ofNat (d.cOps + 1)) :=
    cube_live_ops d.b c.src c.src d.xs ⟨c.n, c.k, d.moves, d.slides, d.hole, c.bench, d.peak, d.peakS, d.cOps, d.hops⟩ ⟨d.hH, d.hD⟩
  have heldLt : first < (livePegBoard c d hi).sudo_5Board_4held.size := by
    rw [hLiveH]
    have hsz : bC.sudo_5Board_4held.size = d.b.sudo_5Board_4held.size := by
      rw [hC]
      simp only [Array.size_set]
      rw [hS]
      simp only [Array.size_set]
    rw [hsz]
    exact hFD
  have held : (livePegBoard c d hi).sudo_5Board_4held[first] = true := by
    have h1 := idx_get hLiveH first heldLt
    rw [h1]
    have hsz : first < bC.sudo_5Board_4held.size := by rw [← hLiveH]; exact heldLt
    have h2 := idx_get hC first hsz
    rw [h2, Array.getElem_set, if_neg (Ne.symm hne)]
    have hszS : first <
        (settleBoard d.b c.src d.hH d.hD d.xs c.n d.moves d.slides d.peak).sudo_5Board_4held.size := by
      rw [hS, Array.size_set]; exact hFD
    have h3 := idx_get hS first hszS
    rw [h3, Array.getElem_set, if_neg (Ne.symm hne)]
    exact hHeld
  have homeLt : first < (livePegBoard c d hi).sudo_5Board_4home.size := by
    rw [hLiveHome, hHomeEq, Array.size_set]; exact hFH
  have arr : (livePegBoard c d hi).sudo_5Board_4home[first] = embed xs0 := by
    have h1 := idx_get hLiveHome first homeLt
    rw [h1]
    have hsz : first < bC.sudo_5Board_4home.size := by rw [← hLiveHome]; exact homeLt
    have h2 := idx_get hHomeEq first hsz
    rw [h2, Array.getElem_set, if_neg (Ne.symm hne)]
    exact hArr
  have opsLt : 0 < (livePegBoard c d hi).sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [hLiveOps, hOpsEq, Array.size_set]; exact hopsZ
  have op0 : (livePegBoard c d hi).sudo_5Board_4cost.sudo_5Costs_3ops[0] = (cMul : Int) := by
    have h1 := idx_get hLiveOps 0 opsLt
    rw [h1]
    have hsz : 0 < bC.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
      rw [← hLiveOps]; exact opsLt
    have h2 := idx_get hOpsEq 0 hsz
    rw [h2, Array.getElem_set, if_neg (by decide : (1 : Nat) ≠ 0)]
    exact hopZ
  exact { heldLt, held, homeLt, arr, opsLt, op0 }

/-- After every positive number of cube-pegs, a home other than `src` is unchanged
    and ops slot 0 is the count the loop started with. -/
theorem pegPack_keep (c : PegCtx) (first : Nat) (xs0 : List Nat) (cMul : Nat)
    (i : Nat) (h0 : 0 < i) (hle : i ≤ c.m)
    (hFD : first < c.b0.sudo_5Board_4held.size)
    (hFH : first < c.b0.sudo_5Board_4home.size)
    (hne : first ≠ c.src)
    (hHeld : c.b0.sudo_5Board_4held[first] = true)
    (hArr : c.b0.sudo_5Board_4home[first] = embed xs0)
    (hopsZ : 0 < c.b0.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hopZ : c.b0.sudo_5Board_4cost.sudo_5Costs_3ops[0] = (cMul : Int)) :
    HomeKeep (pegPack c i h0 hle).b first xs0 cMul := by
  match i with
  | 0 => exact absurd h0 (Nat.not_lt_zero 0)
  | 1 =>
    simpa [pegPack, pegFromOff] using
      offPeg_keep c first xs0 cMul hFD hFH hne hHeld hArr hopsZ hopZ
  | n + 2 =>
    have hle1 : n + 1 ≤ c.m := Nat.le_of_succ_le hle
    have ih := pegPack_keep c first xs0 cMul (n + 1) (Nat.succ_pos n) hle1
      hFD hFH hne hHeld hArr hopsZ hopZ
    have hlive := livePeg_keep c (pegPack c (n + 1) (Nat.succ_pos n) hle1)
      (Nat.lt_of_succ_le hle) first xs0 cMul
      ih.heldLt ih.homeLt hne ih.held ih.arr ih.opsLt ih.op0
    simpa [pegPack, pegNext] using hlive

theorem quiet_pegStep {b : Ecbs.Board} {base : ClimbBudget}
    (h : QuietKeep b base) (t0 j : Nat)
    (hrow : t0 + j < b.sudo_5Board_3row.size) (ctrl : Nat) :
    QuietKeep (pegStep b t0 j hrow ctrl) base :=
  quiet_of h rfl rfl rfl rfl rfl

theorem quiet_cubeLive {b : Ecbs.Board} {base : ClimbBudget}
    (h : QuietKeep b base) (dst src : Nat) (xs : List Nat)
    (bud : Budget b 1) (hin : HomeIn b src) :
    QuietKeep (cubeLiveBoard b dst src xs bud hin) base := by
  refine quiet_of h ?_ ?_ (cube_live_tier b dst src xs bud hin)
    (cube_live_ix b dst src xs bud hin) (cube_live_mx b dst src xs bud hin)
  · rw [cube_live_home b dst src xs bud hin, Array.size_set]
  · rw [cube_live_held b dst src xs bud hin, Array.size_set,
      settle_held_eq b src hin xs bud.n bud.moves bud.slides bud.peak, Array.size_set]

theorem quiet_mulLive {b : Ecbs.Board} {base : ClimbBudget}
    (h : QuietKeep b base) (dst second : Nat) (xs ys : List Nat)
    (bud : Budget b 0) (hin : HomeIn b second) :
    QuietKeep (mulNoLiveBoard b dst second xs ys bud hin) base := by
  refine quiet_of h ?_ ?_ (mul_live_tier b dst second xs ys bud hin)
    (mul_live_ix b dst second xs ys bud hin) (mul_live_mx b dst second xs ys bud hin)
  · rw [mul_live_home b dst second xs ys bud hin, Array.size_set]
  · rw [mul_live_held b dst second xs ys bud hin, Array.size_set,
      settle_held_eq b second hin ys bud.n bud.moves bud.slides bud.peak, Array.size_set]

theorem quiet_offPeg (c : PegCtx) {base : ClimbBudget}
    (h : QuietKeep c.b0 base) : QuietKeep (offPeg c) base := by
  have hCube : QuietKeep
      (cubeOffBoard c.b0 c.src c.src c.g c.n c.k c.moves0 c.hole0 c.bench
        c.peak0 c.peakS0 c.cOps0 c.hops0 c.hF c.hHome) base := by
    refine quiet_of h ?_ ?_
      (cube_off_tier c.b0 c.src c.src c.g c.n c.k c.moves0 c.hole0 c.bench
        c.peak0 c.peakS0 c.cOps0 c.hops0 c.hF c.hHome)
      (cube_off_ix c.b0 c.src c.src c.g c.n c.k c.moves0 c.hole0 c.bench
        c.peak0 c.peakS0 c.cOps0 c.hops0 c.hF c.hHome)
      (cube_off_mx c.b0 c.src c.src c.g c.n c.k c.moves0 c.hole0 c.bench
        c.peak0 c.peakS0 c.cOps0 c.hops0 c.hF c.hHome)
    · rw [cube_off_home, Array.size_set]
    · rw [cube_off_held, Array.size_set]
  unfold offPeg
  exact quiet_pegStep hCube c.t0 0 (offRowPr c) c.ctrl0

theorem quiet_livePeg (c : PegCtx) {i : Nat} (d : LivePeg c i) (hi : i < c.m)
    {base : ClimbBudget} (h : QuietKeep d.b base) :
    QuietKeep (livePegBoard c d hi) base := by
  have hCube := quiet_cubeLive h c.src c.src d.xs
    ⟨c.n, c.k, d.moves, d.slides, d.hole, c.bench, d.peak, d.peakS, d.cOps, d.hops⟩
    ⟨d.hH, d.hD⟩
  unfold livePegBoard
  exact quiet_pegStep hCube c.t0 i (liveRowPr c d hi) d.ctrl

theorem quiet_pegPack (c : PegCtx) {base : ClimbBudget}
    (h : QuietKeep c.b0 base) (i : Nat) (h0 : 0 < i) (hle : i ≤ c.m) :
    QuietKeep (pegPack c i h0 hle).b base := by
  match i with
  | 0 => exact absurd h0 (Nat.not_lt_zero 0)
  | 1 => simpa [pegPack, pegFromOff] using quiet_offPeg c h
  | n + 2 =>
    have hle1 : n + 1 ≤ c.m := Nat.le_of_succ_le hle
    have ih := quiet_pegPack c h (n + 1) (Nat.succ_pos n) hle1
    have hlive := quiet_livePeg c (pegPack c (n + 1) (Nat.succ_pos n) hle1)
      (Nat.lt_of_succ_le hle) ih
    simpa [pegPack, pegNext] using hlive

theorem quiet_pegBoard (c : PegCtx) {base : ClimbBudget}
    (h : QuietKeep c.b0 base) : QuietKeep (pegBoard c c.m) base := by
  have hpack := quiet_pegPack c h c.m c.hm (Nat.le_refl _)
  have hboard := (pegPack_board c c.m c.hm (Nat.le_refl _)).1
  exact quiet_of hpack
    (congrArg Array.size (congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_4home) hboard.symm))
    (congrArg Array.size (congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_4held) hboard.symm))
    (congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_1t) hboard.symm)
    (congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_6marker) hboard.symm)
    (congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_4cost.sudo_5Costs_17script_marker_max) hboard.symm)

/-- The bench-off peg writes home `src`. Homes 0, 1, 3, and 4 stay. -/
theorem side_offPeg (c : PegCtx) {base : ClimbBudget}
    (h : SideKeep c.b0 base)
    (hne0 : c.src ≠ 0) (hne1 : c.src ≠ 1) (hne4 : c.src ≠ 4) (hne3 : c.src ≠ 3) :
    SideKeep (offPeg c) base := by
  have hHeldEq : (offPeg c).sudo_5Board_4held =
      c.b0.sudo_5Board_4held.set ⟨c.src, c.hF⟩ false := by
    unfold offPeg pegStep
    rw [cube_off_held]
  have hHomeEq : (offPeg c).sudo_5Board_4home =
      c.b0.sudo_5Board_4home.set ⟨c.src, c.hHome⟩ #[] := by
    unfold offPeg pegStep
    rw [cube_off_home]
  exact side_arrays (side_set h c.src c.hHome c.hF hne0 hne1 hne4 hne3 #[] false)
    hHomeEq hHeldEq

/-- One live peg settles into `src` and then cubes it. Homes 0, 1, 3, and 4 stay. -/
theorem side_livePeg (c : PegCtx) {i : Nat} (d : LivePeg c i) (hi : i < c.m)
    {base : ClimbBudget} (h : SideKeep d.b base)
    (hne0 : c.src ≠ 0) (hne1 : c.src ≠ 1) (hne4 : c.src ≠ 4) (hne3 : c.src ≠ 3) :
    SideKeep (livePegBoard c d hi) base := by
  let bC := cubeLiveBoard d.b c.src c.src d.xs
    ⟨c.n, c.k, d.moves, d.slides, d.hole, c.bench, d.peak, d.peakS, d.cOps, d.hops⟩
    ⟨d.hH, d.hD⟩
  have hLiveH : (livePegBoard c d hi).sudo_5Board_4held = bC.sudo_5Board_4held := by
    unfold livePegBoard pegStep; rfl
  have hLiveHome : (livePegBoard c d hi).sudo_5Board_4home = bC.sudo_5Board_4home := by
    unfold livePegBoard pegStep; rfl
  have hC := cube_live_held d.b c.src c.src d.xs
    ⟨c.n, c.k, d.moves, d.slides, d.hole, c.bench, d.peak, d.peakS, d.cOps, d.hops⟩
    ⟨d.hH, d.hD⟩
  have hS := settle_held_eq d.b c.src ⟨d.hH, d.hD⟩ d.xs c.n d.moves d.slides d.peak
  have hHomeEq : bC.sudo_5Board_4home =
      d.b.sudo_5Board_4home.set ⟨c.src, d.hH⟩ #[] :=
    cube_live_home d.b c.src c.src d.xs
      ⟨c.n, c.k, d.moves, d.slides, d.hole, c.bench, d.peak, d.peakS, d.cOps, d.hops⟩
      ⟨d.hH, d.hD⟩
  have hszH : bC.sudo_5Board_4home.size = d.b.sudo_5Board_4home.size := by
    rw [hHomeEq, Array.size_set]
  have hszD : bC.sudo_5Board_4held.size = d.b.sudo_5Board_4held.size := by
    rw [hC, Array.size_set, hS, Array.size_set]
  have h0H : 0 < (livePegBoard c d hi).sudo_5Board_4home.size := by
    rw [hLiveHome, hszH]; exact h.h0H
  have h0D : 0 < (livePegBoard c d hi).sudo_5Board_4held.size := by
    rw [hLiveH, hszD]; exact h.h0D
  have h1H : 1 < (livePegBoard c d hi).sudo_5Board_4home.size := by
    rw [hLiveHome, hszH]; exact h.h1H
  have h1D : 1 < (livePegBoard c d hi).sudo_5Board_4held.size := by
    rw [hLiveH, hszD]; exact h.h1D
  have h4H : 4 < (livePegBoard c d hi).sudo_5Board_4home.size := by
    rw [hLiveHome, hszH]; exact h.h4H
  have h4D : 4 < (livePegBoard c d hi).sudo_5Board_4held.size := by
    rw [hLiveH, hszD]; exact h.h4D
  have h3H : 3 < (livePegBoard c d hi).sudo_5Board_4home.size := by
    rw [hLiveHome, hszH]; exact h.h3H
  have h3D : 3 < (livePegBoard c d hi).sudo_5Board_4held.size := by
    rw [hLiveH, hszD]; exact h.h3D
  have homeAt (k : Nat) (hk : k < d.b.sudo_5Board_4home.size) (hne : c.src ≠ k)
      (hk' : k < (livePegBoard c d hi).sudo_5Board_4home.size) :
      (livePegBoard c d hi).sudo_5Board_4home[k]'hk' =
        d.b.sudo_5Board_4home[k]'hk := by
    have h1 := idx_get hLiveHome k hk'
    rw [h1]
    have hsz : k < bC.sudo_5Board_4home.size := by rw [← hLiveHome]; exact hk'
    have h2 := idx_get hHomeEq k hsz
    rw [h2, Array.getElem_set, if_neg hne]
  have heldAt (k : Nat) (hk : k < d.b.sudo_5Board_4held.size) (hne : c.src ≠ k)
      (hk' : k < (livePegBoard c d hi).sudo_5Board_4held.size) :
      (livePegBoard c d hi).sudo_5Board_4held[k]'hk' =
        d.b.sudo_5Board_4held[k]'hk := by
    have h1 := idx_get hLiveH k hk'
    rw [h1]
    have hsz : k < bC.sudo_5Board_4held.size := by rw [← hLiveH]; exact hk'
    have h2 := idx_get hC k hsz
    rw [h2, Array.getElem_set, if_neg hne]
    have hszS : k <
        (settleBoard d.b c.src d.hH d.hD d.xs c.n d.moves d.slides d.peak).sudo_5Board_4held.size := by
      rw [hS, Array.size_set]; exact hk
    have h3 := idx_get hS k hszS
    rw [h3, Array.getElem_set, if_neg hne]
  exact side_copy h h0H h0D h1H h1D h4H h4D h3H h3D
    (homeAt 0 h.h0H hne0 h0H) (heldAt 0 h.h0D hne0 h0D)
    (homeAt 1 h.h1H hne1 h1H) (heldAt 1 h.h1D hne1 h1D)
    (homeAt 4 h.h4H hne4 h4H) (heldAt 4 h.h4D hne4 h4D)
    (homeAt 3 h.h3H hne3 h3H) (heldAt 3 h.h3D hne3 h3D)

/-- A live cube writes `src` only. Homes 0, 1, 3, and 4 stay. -/
theorem side_cubeLive {b : Ecbs.Board} {base : ClimbBudget}
    (h : SideKeep b base) (dst src : Nat) (xs : List Nat)
    (bud : Budget b 1) (hin : HomeIn b src)
    (hne0 : src ≠ 0) (hne1 : src ≠ 1) (hne4 : src ≠ 4) (hne3 : src ≠ 3) :
    SideKeep (cubeLiveBoard b dst src xs bud hin) base := by
  have hHomeEq : (cubeLiveBoard b dst src xs bud hin).sudo_5Board_4home =
      b.sudo_5Board_4home.set ⟨src, hin.hH⟩ #[] :=
    cube_live_home b dst src xs bud hin
  have hC := cube_live_held b dst src xs bud hin
  have hS := settle_held_eq b src hin xs bud.n bud.moves bud.slides bud.peak
  have hszH : (cubeLiveBoard b dst src xs bud hin).sudo_5Board_4home.size =
      b.sudo_5Board_4home.size := by rw [hHomeEq, Array.size_set]
  have hszD : (cubeLiveBoard b dst src xs bud hin).sudo_5Board_4held.size =
      b.sudo_5Board_4held.size := by rw [hC, Array.size_set, hS, Array.size_set]
  let b' := cubeLiveBoard b dst src xs bud hin
  have h0H : 0 < b'.sudo_5Board_4home.size := by rw [hszH]; exact h.h0H
  have h0D : 0 < b'.sudo_5Board_4held.size := by rw [hszD]; exact h.h0D
  have h1H : 1 < b'.sudo_5Board_4home.size := by rw [hszH]; exact h.h1H
  have h1D : 1 < b'.sudo_5Board_4held.size := by rw [hszD]; exact h.h1D
  have h4H : 4 < b'.sudo_5Board_4home.size := by rw [hszH]; exact h.h4H
  have h4D : 4 < b'.sudo_5Board_4held.size := by rw [hszD]; exact h.h4D
  have h3H : 3 < b'.sudo_5Board_4home.size := by rw [hszH]; exact h.h3H
  have h3D : 3 < b'.sudo_5Board_4held.size := by rw [hszD]; exact h.h3D
  have homeAt (k : Nat) (hk : k < b.sudo_5Board_4home.size) (hne : src ≠ k)
      (hk' : k < b'.sudo_5Board_4home.size) :
      b'.sudo_5Board_4home[k]'hk' = b.sudo_5Board_4home[k]'hk := by
    have h2 := idx_get hHomeEq k hk'
    rw [h2, Array.getElem_set, if_neg hne]
  have heldAt (k : Nat) (hk : k < b.sudo_5Board_4held.size) (hne : src ≠ k)
      (hk' : k < b'.sudo_5Board_4held.size) :
      b'.sudo_5Board_4held[k]'hk' = b.sudo_5Board_4held[k]'hk := by
    have h2 := idx_get hC k hk'
    rw [h2, Array.getElem_set, if_neg hne]
    have hszS : k <
        (settleBoard b src hin.hH hin.hD xs bud.n bud.moves bud.slides bud.peak).sudo_5Board_4held.size := by
      rw [hS, Array.size_set]; exact hk
    have h3 := idx_get hS k hszS
    rw [h3, Array.getElem_set, if_neg hne]
  exact side_copy h h0H h0D h1H h1D h4H h4D h3H h3D
    (homeAt 0 h.h0H hne0 h0H) (heldAt 0 h.h0D hne0 h0D)
    (homeAt 1 h.h1H hne1 h1H) (heldAt 1 h.h1D hne1 h1D)
    (homeAt 4 h.h4H hne4 h4H) (heldAt 4 h.h4D hne4 h4D)
    (homeAt 3 h.h3H hne3 h3H) (heldAt 3 h.h3D hne3 h3D)

/-- A live nocopy mul writes the spare. Homes 0, 1, 3, and 4 stay. -/
theorem side_mulLive {b : Ecbs.Board} {base : ClimbBudget}
    (h : SideKeep b base) (dst second : Nat) (xs ys : List Nat)
    (bud : Budget b 0) (hin : HomeIn b second)
    (hne0 : second ≠ 0) (hne1 : second ≠ 1) (hne4 : second ≠ 4) (hne3 : second ≠ 3) :
    SideKeep (mulNoLiveBoard b dst second xs ys bud hin) base := by
  have hHomeEq : (mulNoLiveBoard b dst second xs ys bud hin).sudo_5Board_4home =
      b.sudo_5Board_4home.set ⟨second, hin.hH⟩ #[] :=
    mul_live_home b dst second xs ys bud hin
  have hC := mul_live_held b dst second xs ys bud hin
  have hS := settle_held_eq b second hin ys bud.n bud.moves bud.slides bud.peak
  have hszH : (mulNoLiveBoard b dst second xs ys bud hin).sudo_5Board_4home.size =
      b.sudo_5Board_4home.size := by rw [hHomeEq, Array.size_set]
  have hszD : (mulNoLiveBoard b dst second xs ys bud hin).sudo_5Board_4held.size =
      b.sudo_5Board_4held.size := by rw [hC, Array.size_set, hS, Array.size_set]
  let b' := mulNoLiveBoard b dst second xs ys bud hin
  have h0H : 0 < b'.sudo_5Board_4home.size := by rw [hszH]; exact h.h0H
  have h0D : 0 < b'.sudo_5Board_4held.size := by rw [hszD]; exact h.h0D
  have h1H : 1 < b'.sudo_5Board_4home.size := by rw [hszH]; exact h.h1H
  have h1D : 1 < b'.sudo_5Board_4held.size := by rw [hszD]; exact h.h1D
  have h4H : 4 < b'.sudo_5Board_4home.size := by rw [hszH]; exact h.h4H
  have h4D : 4 < b'.sudo_5Board_4held.size := by rw [hszD]; exact h.h4D
  have h3H : 3 < b'.sudo_5Board_4home.size := by rw [hszH]; exact h.h3H
  have h3D : 3 < b'.sudo_5Board_4held.size := by rw [hszD]; exact h.h3D
  have homeAt (k : Nat) (hk : k < b.sudo_5Board_4home.size) (hne : second ≠ k)
      (hk' : k < b'.sudo_5Board_4home.size) :
      b'.sudo_5Board_4home[k]'hk' = b.sudo_5Board_4home[k]'hk := by
    have h2 := idx_get hHomeEq k hk'
    rw [h2, Array.getElem_set, if_neg hne]
  have heldAt (k : Nat) (hk : k < b.sudo_5Board_4held.size) (hne : second ≠ k)
      (hk' : k < b'.sudo_5Board_4held.size) :
      b'.sudo_5Board_4held[k]'hk' = b.sudo_5Board_4held[k]'hk := by
    have h2 := idx_get hC k hk'
    rw [h2, Array.getElem_set, if_neg hne]
    have hszS : k <
        (settleBoard b second hin.hH hin.hD ys bud.n bud.moves bud.slides bud.peak).sudo_5Board_4held.size := by
      rw [hS, Array.size_set]; exact hk
    have h3 := idx_get hS k hszS
    rw [h3, Array.getElem_set, if_neg hne]
  exact side_copy h h0H h0D h1H h1D h4H h4D h3H h3D
    (homeAt 0 h.h0H hne0 h0H) (heldAt 0 h.h0D hne0 h0D)
    (homeAt 1 h.h1H hne1 h1H) (heldAt 1 h.h1D hne1 h1D)
    (homeAt 4 h.h4H hne4 h4H) (heldAt 4 h.h4D hne4 h4D)
    (homeAt 3 h.h3H hne3 h3H) (heldAt 3 h.h3D hne3 h3D)

/-- Every positive prefix of the cube-peg loop keeps homes 0, 1, 3, and 4. -/
theorem side_pegPack (c : PegCtx) {base : ClimbBudget}
    (h : SideKeep c.b0 base)
    (i : Nat) (h0 : 0 < i) (hle : i ≤ c.m)
    (hne0 : c.src ≠ 0) (hne1 : c.src ≠ 1) (hne4 : c.src ≠ 4) (hne3 : c.src ≠ 3) :
    SideKeep (pegPack c i h0 hle).b base := by
  match i with
  | 0 => exact absurd h0 (Nat.not_lt_zero 0)
  | 1 =>
    simpa [pegPack, pegFromOff] using side_offPeg c h hne0 hne1 hne4 hne3
  | n + 2 =>
    have hle1 : n + 1 ≤ c.m := Nat.le_of_succ_le hle
    have ih := side_pegPack c h (n + 1) (Nat.succ_pos n) hle1 hne0 hne1 hne4 hne3
    simpa [pegPack, pegNext] using
      side_livePeg c (pegPack c (n + 1) (Nat.succ_pos n) hle1)
        (Nat.lt_of_succ_le hle) ih hne0 hne1 hne4 hne3

/-- The peg board at the end of the loop is that pack. Homes 0, 1, 3, and 4 stay. -/
theorem side_pegBoard (c : PegCtx) {base : ClimbBudget}
    (h : SideKeep c.b0 base)
    (hne0 : c.src ≠ 0) (hne1 : c.src ≠ 1) (hne4 : c.src ≠ 4) (hne3 : c.src ≠ 3) :
    SideKeep (pegBoard c c.m) base := by
  have hpack := side_pegPack c h c.m c.hm (Nat.le_refl _) hne0 hne1 hne4 hne3
  have hboard := (pegPack_board c c.m c.hm (Nat.le_refl _)).1
  exact side_arrays hpack
    (congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_4home) hboard.symm)
    (congrArg (fun bd : Ecbs.Board => bd.sudo_5Board_4held) hboard.symm)

/-- The emitted gap mul, started from the idle park's peg loop, keeps that
    loop's row, counter, parked-from hole, rung index, and tally length.
    Home 5 still holds the gap. The loop started from the keep-park board. -/
theorem parked_gap_mul
    {done rest : List Nat} {r : Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvKCore done (r :: rest) b s base)
    (hM : MoveHeadroom b base.n base.bench base.mMax)
    (hS : SlideHeadroom b base.n base.mMax)
    (hF : s.fromHole < 0) (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax)
    (hhome : s.onBench = false) :
    ∃ (c : PegCtx) (bMul : Ecbs.Board),
      Ecbs.mul (pegBoard c c.m) ((5 : Nat) : Int) ((5 : Nat) : Int) ((6 : Nat) : Int)
          false false false = .ok bMul ∧
      bMul.sudo_5Board_3row = embed (paintRed c.row0 c.t0 c.m) ∧
      bMul.sudo_5Board_4cost.sudo_5Costs_4ctrl = ((c.ctrl0 + c.m : Nat) : Int) ∧
      bMul.sudo_5Board_11parked_from = c.b0.sudo_5Board_11parked_from ∧
      bMul.sudo_5Board_8rung_idx = c.b0.sudo_5Board_8rung_idx ∧
      bMul.sudo_5Board_9tally_len = c.b0.sudo_5Board_9tally_len ∧
      c.row0 = afterPark s.row (-1) s.parkAt (climbAt base.ladder0 base.R s.ridx) r ∧
      c.ctrl0 = s.ctrl + 2 ∧
      c.m = s.tally ∧
      c.t0 = s.t0 ∧
      c.b0.sudo_5Board_11parked_from =
        ((climbAt base.ladder0 base.R s.ridx : Nat) : Int) ∧
      c.b0.sudo_5Board_8rung_idx = ((s.ridx + 1 : Nat) : Int) ∧
      c.b0.sudo_5Board_9tally_len = (s.tally : Int) ∧
      (∃ (ys : List Nat) (moves slides hole peak peakS cOps : Nat)
        (hH : 6 < (pegBoard c c.m).sudo_5Board_4home.size)
        (hD : 6 < (pegBoard c c.m).sudo_5Board_4held.size)
        (hops : 0 < (pegBoard c c.m).sudo_5Board_4cost.sudo_5Costs_3ops.size),
        bMul = mulNoLiveBoard (pegBoard c c.m) 5 6 c.g ys ⟨c.n, c.k, moves, slides, hole, c.bench, peak, peakS, cOps, hops⟩ ⟨hH, hD⟩ ∧
        ys = cubeBenchIter c.n c.k c.bench c.g c.m ∧
        moves = (pegPack c c.m c.hm (Nat.le_refl _)).moves ∧
        slides = (pegPack c c.m c.hm (Nat.le_refl _)).slides ∧
        hole = (pegPack c c.m c.hm (Nat.le_refl _)).hole ∧
        peak = (pegPack c c.m c.hm (Nat.le_refl _)).peak ∧
        peakS = (pegPack c c.m c.hm (Nat.le_refl _)).peakS ∧
        (pegBoard c c.m).sudo_5Board_4cost.sudo_5Costs_3ops[0]'hops = (cOps : Int) ∧
        c.src = 6 ∧ c.g = s.gap ∧ c.n = s.n ∧ c.k = s.k ∧ c.bench = s.benchlen ∧
        (∃ bPark, Ecbs.park_rung b (r : Int) = .ok bPark ∧
          Ecbs.copy_band bPark ((6 : Nat) : Int) ((5 : Nat) : Int) false = .ok c.b0) ∧
        (∃ (h5D : 5 < bMul.sudo_5Board_4held.size)
            (h5H : 5 < bMul.sudo_5Board_4home.size),
          bMul.sudo_5Board_4held[5]'h5D = true ∧
          bMul.sudo_5Board_4home[5]'h5H = embed c.g)) := by
  obtain ⟨bPark, c, hpark, hcopy, hrow0, hctrl0, hmEq, ht0, hg, hn, hkN, hbch, hsrc,
      hfrom, hridx, hlen, _hplace⟩ := parked_peg_ctx h hM hS hF hm hT hhome
  let hole := climbAt base.ladder0 base.R s.ridx
  obtain ⟨_b0, hpark0, _, _, hkeep⟩ := park_of_shape h
  obtain ⟨hRowP, hRowH, hEq⟩ := hkeep hF
  have hPK : bPark = parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH := by
    have hboard : bPark = _b0 := by injection hpark.symm.trans hpark0
    exact hboard.trans hEq
  have hmv := hM.eq
  have hsl := hS.eq
  let mv := hM.mv
  let sl := hS.sl
  have h6H : 6 < bPark.sudo_5Board_4home.size := by
    rw [hPK]; simpa [parkKeepBoard] using h.shape.spareH
  have h6D : 6 < bPark.sudo_5Board_4held.size := by
    rw [hPK]; simpa [parkKeepBoard] using h.shape.spareD
  have hmvP : bPark.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int) := by
    rw [hPK]; simpa [parkKeepBoard] using hmv
  have hpk : ∃ pk : Nat, b.sudo_5Board_4cost.sudo_5Costs_4peak = (pk : Int) := by
    obtain ⟨pk, hpk, _⟩ := h.peak
    exact ⟨pk, hpk⟩
  obtain ⟨pk, hpk⟩ := hpk
  have hpkP : bPark.sudo_5Board_4cost.sudo_5Costs_4peak = (pk : Int) := by
    rw [hPK]; simpa [parkKeepBoard] using hpk
  have h5H : 5 < bPark.sudo_5Board_4home.size := by
    rw [hPK]; simpa [parkKeepBoard] using h.inv.hG
  have h5D : 5 < bPark.sudo_5Board_4held.size := by
    rw [hPK]; simpa [parkKeepBoard] using h.inv.hGs
  have h7P : 7 ≤ bPark.sudo_5Board_4held.size := by
    rw [hPK]; simpa [parkKeepBoard] using h.shape.h7
  have hgapH := h.inv.gapHome hhome
  have hsrcP : bPark.sudo_5Board_4held[5] = true := by
    subst hPK
    simpa [parkKeepBoard] using hgapH.1
  have harrP : bPark.sudo_5Board_4home[5] = embed s.gap := by
    subst hPK
    simpa [parkKeepBoard] using hgapH.2
  have hemptyP : bPark.sudo_5Board_4held[6] = false := by
    subst hPK
    simpa [parkKeepBoard] using h.shape.spareE
  have hnP : bPark.sudo_5Board_1t.sudo_4Tier_1n = (s.gap.length : Int) := by
    rw [hPK]
    simpa [parkKeepBoard] using
      (show b.sudo_5Board_1t.sudo_4Tier_1n = (s.gap.length : Int) by
        rw [h.shape.gapLen]; exact h.shape.tierN)
  have hk : done.length + 1 ≤ base.R := by
    have hlenK := h.kLe
    rw [List.length_append, List.length_cons] at hlenK
    omega
  have hpegN0 : pegCount s.gap ≤ s.n := by
    rw [← h.shape.gapLen]; exact pegCount_le s.gap
  have hmovFit : FitsLen (mv + pegCount s.gap + s.tally * pegCharge s.n s.benchlen) := by
    have hpegB : pegCount s.gap ≤ base.n := by
      rw [h.hn] at hpegN0
      exact hpegN0
    rw [h.hn, h.hbench]
    exact copy_then_pegs_fit mv (rungCharge base.n base.bench base.mMax - 2 * base.n)
      (pegCount s.gap) (s.tally * pegCharge base.n base.bench)
      (MoveHeadroom.at hM hmv)
      (gap_copy_room base.n base.bench base.mMax s.tally (pegCount s.gap) hpegB hT)
  have hfitCopy : FitsLen (mv + pegCount s.gap) := FitsLen.of_le hmovFit (by omega)
  have hcopy2 := copy_band_refines bPark 6 5 s.gap mv pk
    h6H h6D h5H h5D h7P hsrcP harrP hemptyP hnP
    (by rw [h.shape.gapLen]; exact h.shape.peg.fitN) hmvP hpkP hfitCopy
  have hb0 : c.b0 = placeBoard bPark 6 h6H h6D s.gap mv pk := by
    injection hcopy.symm.trans hcopy2
  have hbook := place_book bPark 6 ⟨h6H, h6D⟩ s.gap mv pk
  have hidle := place_idle bPark 6 ⟨h6H, h6D⟩ s.gap mv pk
  have hmv0 : c.moves0 = mv + pegCount s.gap := by
    have hcast : (c.moves0 : Int) = ((mv + pegCount s.gap : Nat) : Int) := by
      rw [← c.hmoves0, hb0]
      exact (place_moves bPark 6 ⟨h6H, h6D⟩ s.gap mv pk).trans (ofNat_eq_natCast _)
    exact ofNat_inj_nat hcast
  have hsl0 : c.slides0 = sl := by
    have hcast : Int.ofNat c.slides0 = (sl : Int) := by
      rw [← c.hslides0, hb0, hidle.2.2.2.1, hPK]
      simpa [parkKeepBoard] using hsl
    exact ofNat_inj_nat ((ofNat_eq_natCast _).trans hcast)
  have hFD : 5 < c.b0.sudo_5Board_4held.size := by
    rw [hb0, hbook.2.2.2.2.2.2.2.2.2]; exact h5D
  have hFH : 5 < c.b0.sudo_5Board_4home.size := by
    rw [hb0, hbook.2.2.2.2.2.2.2.2.1]; exact h5H
  have hHeldEq : c.b0.sudo_5Board_4held =
      (placeBoard bPark 6 h6H h6D s.gap mv pk).sudo_5Board_4held := by rw [hb0]
  have hHomeEq5 : c.b0.sudo_5Board_4home =
      (placeBoard bPark 6 h6H h6D s.gap mv pk).sudo_5Board_4home := by rw [hb0]
  have hHeld5 : c.b0.sudo_5Board_4held[5] = true :=
    (idx_get hHeldEq 5 hFD).trans
      ((place_held_other bPark 6 5 ⟨h6H, h6D⟩ s.gap mv pk (by decide) h5D (hHeldEq ▸ hFD)).trans hsrcP)
  have hArr5 : c.b0.sudo_5Board_4home[5] = embed c.g := by
    rw [(idx_get hHomeEq5 5 hFH).trans
        (place_home_other bPark 6 5 ⟨h6H, h6D⟩ s.gap mv pk (by decide) h5H (hHomeEq5 ▸ hFH)), harrP, hg]
  have hopsP : bPark.sudo_5Board_4cost.sudo_5Costs_3ops =
      b.sudo_5Board_4cost.sudo_5Costs_3ops := by rw [hPK]; simp [parkKeepBoard]
  have hOpsEq : c.b0.sudo_5Board_4cost.sudo_5Costs_3ops =
      b.sudo_5Board_4cost.sudo_5Costs_3ops := by
    rw [hb0]; exact hidle.2.2.1.trans hopsP
  have hopsZ : 0 < c.b0.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [hOpsEq]; exact Nat.lt_trans (by decide : (0 : Nat) < 1) h.shape.peg.opsGt
  obtain ⟨cMul, hcMul, hcLe⟩ := h.ops 0 (by rw [← hOpsEq]; exact hopsZ)
  have hopZ : c.b0.sudo_5Board_4cost.sudo_5Costs_3ops[0] = (cMul : Int) :=
    (idx_get hOpsEq 0 hopsZ).trans hcMul
  have hne5 : (5 : Nat) ≠ c.src := by rw [hsrc]; decide
  have hkeep := pegPack_keep c 5 c.g cMul c.m c.hm (Nat.le_refl _)
    hFD hFH hne5 hHeld5 hArr5 hopsZ hopZ
  let d := pegPack c c.m c.hm (Nat.le_refl _)
  have hPack := pegPack_board c c.m c.hm (Nat.le_refl _)
  have hpTake : pegCount (d.xs.take c.n) ≤ c.n := pegCount_take_le d.xs c.n
  have hlenY : d.xs.length = c.bench := by
    rw [d.hxs, cubeBenchIter_length c.n c.k c.bench c.g c.n_le c.m c.hm]
  have hfitL : FitsLen d.xs.length := by rw [hlenY]; exact c.hfitB
  have hspan2 : 2 * (c.n - 1) < c.bench := by
    have hs := c.hspan
    omega
  have hfi : FitsLen (2 * (c.n - 1)) := FitsLen.of_le c.h3 (by omega)
  have hsum : d.moves + 2 * pegCount (d.xs.take c.n) + c.n * (c.n + 1) +
      3 * (c.bench - c.n) ≤
      c.moves0 + c.m * pegCharge c.n c.bench + mulCharge c.n c.bench := by
    have hge := mulCharge_ge c.n c.bench d.moves d.xs d.xs c.k c.n_le hpTake
    exact Nat.le_trans hge (Nat.add_le_add_right d.hmovB _)
  have hfold : FitsLen (d.moves + 2 * pegCount (d.xs.take c.n) + c.n * (c.n + 1) +
      3 * (c.bench - c.n)) := by
    apply FitsLen.of_le (MoveHeadroom.at hM hmv)
    have hpegN : pegCount s.gap ≤ base.n := by
      have h1 : pegCount s.gap ≤ s.gap.length := pegCount_le s.gap
      rw [h.shape.gapLen, h.hn] at h1
      exact h1
    have hpiece : d.moves + 2 * pegCount (d.xs.take c.n) + c.n * (c.n + 1) +
        3 * (c.bench - c.n) ≤
        mv + base.n + s.tally * pegCharge base.n base.bench +
          mulCharge base.n base.bench + base.n := by
      have hpc : pegCharge c.n c.bench = pegCharge base.n base.bench := by
        rw [hn.trans h.hn, hbch.trans h.hbench]
      have hmc : mulCharge c.n c.bench = mulCharge base.n base.bench := by
        rw [hn.trans h.hn, hbch.trans h.hbench]
      have hright : c.moves0 + c.m * pegCharge c.n c.bench + mulCharge c.n c.bench =
          mv + pegCount s.gap + s.tally * pegCharge base.n base.bench +
            mulCharge base.n base.bench := by
        rw [hmv0, hmEq, hpc, hmc]
      have hmid := Nat.le_trans hsum (Nat.le_of_eq hright)
      exact Nat.le_trans hmid (by
        have hpeg := hpegN
        omega)
    have hbody := white_piece_in_room base.n base.bench s.tally mv _ hpiece
    exact Nat.le_trans hbody (Nat.add_le_add_left
      (Nat.sub_le_sub_right (rungCharge_mono base.n base.bench s.tally base.mMax hT) _) mv)
  have hfm : FitsLen (d.moves + 2 * pegCount (d.xs.take c.n) + c.n * (c.n + 1)) :=
    FitsLen.of_le hfold (by omega)
  have hfitM : FitsLen (d.moves + 2 * pegCount (d.xs.take c.n)) :=
    FitsLen.of_le hfm (by omega)
  have hpegF : FitsLen (2 * pegCount (d.xs.take c.n)) := FitsLen.of_le hfitM (by omega)
  have hlocS : d.slides + 2 * pegCount (d.xs.take c.n) ≤
      sl + s.tally * (2 * base.n) + 2 * base.n := by
    have h2 : 2 * pegCount (d.xs.take c.n) ≤ 2 * c.n := by omega
    have hSlidesEq : c.slides0 + c.m * (2 * c.n) = sl + s.tally * (2 * s.n) := by
      rw [hsl0, hmEq, hn]
    have hprev' : d.slides ≤ sl + s.tally * (2 * s.n) :=
      Nat.le_trans d.hsldB (Nat.le_of_eq hSlidesEq)
    have h2s : 2 * pegCount (d.xs.take c.n) ≤ 2 * s.n := by rw [← hn]; exact h2
    have hmul : (s.tally + 1) * (2 * s.n) = s.tally * (2 * s.n) + 2 * s.n := by
      rw [Nat.succ_mul]
    have hloc : d.slides + 2 * pegCount (d.xs.take c.n) ≤
        sl + (s.tally + 1) * (2 * s.n) := by omega
    rw [h.hn] at hloc
    have hsplit : (s.tally + 1) * (2 * base.n) =
        s.tally * (2 * base.n) + 2 * base.n := by
      rw [Nat.succ_mul]
    rw [hsplit] at hloc
    simpa [Nat.add_assoc] using hloc
  have hfitS : FitsLen (d.slides + 2 * pegCount (d.xs.take c.n)) :=
    FitsLen.of_le (SlideHeadroom.at hS hsl)
      (loose_slide_in_room base.n s.tally base.mMax sl _ hT hlocS)
  have hfops : FitsLen (cMul + 1) := by
    apply FitsLen.of_le base.fitO
    have hone : (1 : Nat) ≤ base.mMax + 3 := Nat.le_add_left 1 (base.mMax + 2)
    have h1 : cMul + 1 ≤ base.ops0 + done.length * (base.mMax + 3) + (base.mMax + 3) :=
      Nat.add_le_add hcLe hone
    have h2 : base.ops0 + done.length * (base.mMax + 3) + (base.mMax + 3) =
        base.ops0 + (done.length + 1) * (base.mMax + 3) := by
      rw [Nat.add_assoc, ← Nat.succ_mul]
    have h3 : base.ops0 + (done.length + 1) * (base.mMax + 3) ≤
        base.ops0 + base.R * (base.mMax + 3) :=
      Nat.add_le_add_left (Nat.mul_le_mul_right _ hk) _
    exact Nat.le_trans h1 (Nat.le_trans (Nat.le_of_eq h2) h3)
  have hH6 : 6 < d.b.sudo_5Board_4home.size := by rw [← hsrc]; exact d.hH
  have hD6 : 6 < d.b.sudo_5Board_4held.size := by rw [← hsrc]; exact d.hD
  have hempty : d.b.sudo_5Board_4held[6] = false := by simpa [hsrc] using d.hempty
  have hto : d.b.sudo_5Board_8bench_to = ((6 : Nat) : Int) := by rw [d.toB, hsrc]
  have hnB : d.b.sudo_5Board_1t.sudo_4Tier_1n = (c.n : Int) := by rw [d.tier]; exact c.hn
  have hbl : d.b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat c.bench := by
    rw [d.tier]; exact c.hbl
  have hwF : d.b.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat c.w := by rw [d.tier]; exact c.hwF
  have hhF : d.b.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat c.h := by rw [d.tier]; exact c.hhF
  have hrF : d.b.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat c.r := by rw [d.tier]; exact c.hrF
  have hkF : d.b.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat c.k := by rw [d.tier]; exact c.hkF
  have hmul := mul_eq_live d.b 5 5 6 c.g d.xs c.w c.h c.r c.n c.k d.moves d.slides d.hole c.bench d.peak d.peakS cMul d.marker d.onB hto hH6 hD6 d.h7 hempty d.hbench hnB c.hn0 d.hpos d.hnle d.hzero c.hf hfitL d.hmoves d.hslides d.hpeak hpegF hfitM hfitS hkeep.opsLt hkeep.op0 hfops hbl hkeep.heldLt hkeep.homeLt hkeep.held hkeep.arr (by decide) c.hlenx hspan2 c.hxsT hfi hfm ⟨c.hw0, c.hh0, c.hrR, c.hrP, c.hnE, c.hkLe, c.hgap⟩ hwF hhF hrF hkF d.hHole d.hpeakS c.hsm c.hnsm c.hfitB hfold
  let bMul := mulNoLiveBoard d.b 5 6 c.g d.xs ⟨c.n, c.k, d.moves, d.slides, d.hole, c.bench, d.peak, d.peakS, cMul, hkeep.opsLt⟩ ⟨hH6, hD6⟩
  have hCar := mulLive_carries d.b 5 6 c.g d.xs ⟨c.n, c.k, d.moves, d.slides, d.hole, c.bench, d.peak, d.peakS, cMul, hkeep.opsLt⟩ ⟨hH6, hD6⟩
  have hmulP : Ecbs.mul (pegBoard c c.m) ((5 : Nat) : Int) ((5 : Nat) : Int) ((6 : Nat) : Int)
      false false false = .ok bMul := by
    rw [← hPack.1]
    exact hmul
  have hrowM : bMul.sudo_5Board_3row = embed (paintRed c.row0 c.t0 c.m) := by
    rw [hCar.2.2.2.2, d.hrow]
  have hctrlM : bMul.sudo_5Board_4cost.sudo_5Costs_4ctrl = ((c.ctrl0 + c.m : Nat) : Int) := by
    rw [hCar.2.2.2.1, d.hctrl, d.hctrlN]
  have hfromM : bMul.sudo_5Board_11parked_from = c.b0.sudo_5Board_11parked_from := by
    rw [hCar.1, hPack.2.1]
  have hridxM : bMul.sudo_5Board_8rung_idx = c.b0.sudo_5Board_8rung_idx := by
    rw [hCar.2.1, hPack.2.2.1]
  have hlenM : bMul.sudo_5Board_9tally_len = c.b0.sudo_5Board_9tally_len := by
    rw [hCar.2.2.1, hPack.2.2.2.1]
  let hHg : 6 < (pegBoard c c.m).sudo_5Board_4home.size := hPack.1 ▸ hH6
  let hDg : 6 < (pegBoard c c.m).sudo_5Board_4held.size := hPack.1 ▸ hD6
  let hopsG : 0 < (pegBoard c c.m).sudo_5Board_4cost.sudo_5Costs_3ops.size :=
    hPack.1 ▸ hkeep.opsLt
  have hnamed : bMul = mulNoLiveBoard (pegBoard c c.m) 5 6 c.g d.xs ⟨c.n, c.k, d.moves, d.slides, d.hole, c.bench, d.peak, d.peakS, cMul, hopsG⟩ ⟨hHg, hDg⟩ := by
    have htr := mulNoLiveBoard_transport hPack.1 5 6 c.g d.xs ⟨c.n, c.k, d.moves, d.slides, d.hole, c.bench, d.peak, d.peakS, cMul, hkeep.opsLt⟩ ⟨hH6, hD6⟩
    simpa [bMul] using htr
  have hHeldM := mul_live_held d.b 5 6 c.g d.xs ⟨c.n, c.k, d.moves, d.slides, d.hole, c.bench, d.peak, d.peakS, cMul, hkeep.opsLt⟩ ⟨hH6, hD6⟩
  have hHomeM := mul_live_home d.b 5 6 c.g d.xs ⟨c.n, c.k, d.moves, d.slides, d.hole, c.bench, d.peak, d.peakS, cMul, hkeep.opsLt⟩ ⟨hH6, hD6⟩
  have h5D : 5 < bMul.sudo_5Board_4held.size := by
    have hsz : bMul.sudo_5Board_4held.size = d.b.sudo_5Board_4held.size := by
      rw [hHeldM]
      simp only [Array.size_set]
      rw [settle_held_eq d.b 6 ⟨hH6, hD6⟩ d.xs c.n d.moves d.slides d.peak, Array.size_set]
    rw [hsz]
    exact hkeep.heldLt
  have h5held : bMul.sudo_5Board_4held[5]'h5D = true := by
    have h1 := idx_get hHeldM 5 h5D
    rw [h1, Array.getElem_set, if_neg (by decide : (6 : Nat) ≠ 5)]
    have hszS : 5 <
        (settleBoard d.b 6 hH6 hD6 d.xs c.n d.moves d.slides d.peak).sudo_5Board_4held.size := by
      rw [settle_held_eq d.b 6 ⟨hH6, hD6⟩ d.xs c.n d.moves d.slides d.peak, Array.size_set]
      exact hkeep.heldLt
    have h2 := idx_get (settle_held_eq d.b 6 ⟨hH6, hD6⟩ d.xs c.n d.moves d.slides d.peak) 5 hszS
    rw [h2, Array.getElem_set, if_neg (by decide : (6 : Nat) ≠ 5)]
    exact hkeep.held
  have h5H : 5 < bMul.sudo_5Board_4home.size := by
    rw [hHomeM, Array.size_set]
    exact hkeep.homeLt
  have h5arr : bMul.sudo_5Board_4home[5]'h5H = embed c.g := by
    have h1 := idx_get hHomeM 5 h5H
    rw [h1, Array.getElem_set, if_neg (by decide : (6 : Nat) ≠ 5)]
    exact hkeep.arr
  exact ⟨c, bMul, hmulP, hrowM, hctrlM, hfromM, hridxM, hlenM, hrow0, hctrl0, hmEq, ht0,
    hfrom, hridx, hlen,
    ⟨d.xs, d.moves, d.slides, d.hole, d.peak, d.peakS, cMul, hHg, hDg, hopsG,
      hnamed, d.hxs, rfl, rfl, rfl, rfl, rfl,
      (by
        have hget := idx_get
          (congrArg (fun b => b.sudo_5Board_4cost.sudo_5Costs_3ops) hPack.1.symm) 0 hopsG
        exact hget.trans hkeep.op0),
      hsrc, hg, hn, hkN, hbch, ⟨bPark, hpark, hcopy⟩,
      ⟨h5D, h5H, h5held, h5arr⟩⟩⟩


/-- One home and the array it holds. -/
structure CellKeep (b : Ecbs.Board) (first : Nat) (xs0 : List Nat) : Prop where
  heldLt : first < b.sudo_5Board_4held.size
  held : b.sudo_5Board_4held[first] = true
  homeLt : first < b.sudo_5Board_4home.size
  arr : b.sudo_5Board_4home[first] = embed xs0

/-- After the bench-off cube-peg loop, `mul gap gap spare` is the live nocopy mul.
    The gap is still held at home 5. The spare is empty and the bench is on, aimed
    at the spare, holding `cubeBenchIter` of that gap. The move, slide, and mul-op
    fits are one rung charge of the climb. -/
theorem mul_of_shape {done rest : List Nat} {r : Nat} {b : Ecbs.Board} {s : ClimbModel}
    {base : ClimbBudget} (h : ClimbInvKCore done (r :: rest) b s base)
    (hM : MoveHeadroom b base.n base.bench base.mMax)
    (hS : SlideHeadroom b base.n base.mMax)
    (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax)
    (hhome : s.onBench = false) :
    ∃ (c : PegCtx) (bM : Ecbs.Board) (ys : List Nat)
      (moves slides hole peak peakS cOps : Nat)
      (hH : 6 < bM.sudo_5Board_4home.size)
      (hD : 6 < bM.sudo_5Board_4held.size)
      (hops : 0 < bM.sudo_5Board_4cost.sudo_5Costs_3ops.size),
      Ecbs.copy_band b ((6 : Nat) : Int) ((5 : Nat) : Int) false = .ok c.b0 ∧
      c.src = 6 ∧ c.g = s.gap ∧ c.m = s.tally ∧
      c.n = s.n ∧ c.k = s.k ∧ c.bench = s.benchlen ∧
      bM = pegBoard c c.m ∧
      ys = cubeBenchIter c.n c.k c.bench c.g c.m ∧
      CellKeep bM 5 c.g ∧
      CellKeep bM base.xHome base.x ∧
      (∃ (cCube : Nat) (h1 : 1 < bM.sudo_5Board_4cost.sudo_5Costs_3ops.size),
        bM.sudo_5Board_4cost.sudo_5Costs_3ops[1] = (cCube : Int) ∧
          FitsLen (cCube + 1)) ∧
      bM.sudo_5Board_3row = embed (paintRed s.row s.t0 s.tally) ∧
      bM.sudo_5Board_1t = c.b0.sudo_5Board_1t ∧
      bM.sudo_5Board_9marker_on = false ∧
      7 ≤ bM.sudo_5Board_4held.size ∧
      bM.sudo_5Board_4cost.sudo_5Costs_3ops[0]'(hops) = (cOps : Int) ∧
      cOps ≤ base.ops0 + done.length * (base.mMax + 3) ∧
      c.ctrl0 = s.ctrl ∧ c.high = s.high ∧ c.control = base.control ∧
      c.b0.sudo_5Board_9tally_len = (s.tally : Int) ∧
      c.b0.sudo_5Board_4cost.sudo_5Costs_9tally_max =
        b.sudo_5Board_4cost.sudo_5Costs_9tally_max ∧
      c.t0 = s.t0 ∧
      Ecbs.mul bM ((5 : Nat) : Int) ((5 : Nat) : Int) ((6 : Nat) : Int)
          false false false =
        .ok (mulNoLiveBoard bM 5 6 c.g ys ⟨c.n, c.k, moves, slides, hole, c.bench, peak, peakS, cOps, hops⟩ ⟨hH, hD⟩) ∧
      c.row0 = s.row ∧
      bM.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves ∧
      bM.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides ∧
      bM.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole ∧
      bM.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak ∧
      bM.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int) ∧
      (∃ mvE : Nat, b.sudo_5Board_4cost.sudo_5Costs_5moves = (mvE : Int) ∧
        moves + 2 * base.n ≤ mvE + base.n + s.tally * pegCharge base.n base.bench) ∧
      (∃ slE : Nat, b.sudo_5Board_4cost.sudo_5Costs_6slides = (slE : Int) ∧
        slides + 2 * base.n ≤ slE + s.tally * (2 * base.n)) ∧
      (∀ (row : Array Int) (ctrl fromHole ridx : Int),
        Ecbs.mul (withPark bM row ctrl fromHole ridx)
            ((5 : Nat) : Int) ((5 : Nat) : Int) ((6 : Nat) : Int)
            false false false =
          .ok (withPark
            (mulNoLiveBoard bM 5 6 c.g ys ⟨c.n, c.k, moves, slides, hole, c.bench, peak, peakS, cOps, hops⟩ ⟨hH, hD⟩)
            row ctrl fromHole ridx)) := by
  obtain ⟨mv, pk, sl, c, hmv, hpk, hsl, hb0, hcopy, hsrc, hg, hmEq, hrow0,
      hn, hkN, hbch, hmv0, hsl0, ht0, hctrl0, hhigh0, hcontrol, hlen0, hmax0⟩ :=
    peg_of_shape h hM hS hm hT hhome
  have hk : done.length + 1 ≤ base.R := by
    have hlen := h.kLe
    rw [List.length_append, List.length_cons] at hlen
    omega
  have hbook := place_book b 6 ⟨h.shape.spareH, h.shape.spareD⟩ s.gap mv pk
  have hidle := place_idle b 6 ⟨h.shape.spareH, h.shape.spareD⟩ s.gap mv pk
  have hFD : 5 < c.b0.sudo_5Board_4held.size := by
    rw [hb0, hbook.2.2.2.2.2.2.2.2.2]
    exact h.inv.hGs
  have hFH : 5 < c.b0.sudo_5Board_4home.size := by
    rw [hb0, hbook.2.2.2.2.2.2.2.2.1]
    exact h.inv.hG
  have hHeldEq : c.b0.sudo_5Board_4held =
      (placeBoard b 6 h.shape.spareH h.shape.spareD s.gap mv pk).sudo_5Board_4held := by
    rw [hb0]
  have hHomeEq5 : c.b0.sudo_5Board_4home =
      (placeBoard b 6 h.shape.spareH h.shape.spareD s.gap mv pk).sudo_5Board_4home := by
    rw [hb0]
  have hHeld5 : c.b0.sudo_5Board_4held[5] = true := by
    exact (idx_get hHeldEq 5 hFD).trans
      ((place_held_other b 6 5 ⟨h.shape.spareH, h.shape.spareD⟩ s.gap mv pk (by decide) h.inv.hGs (hHeldEq ▸ hFD)).trans (h.inv.gapHome hhome).1)
  have hArr5 : c.b0.sudo_5Board_4home[5] = embed c.g := by
    rw [(idx_get hHomeEq5 5 hFH).trans
        (place_home_other b 6 5 ⟨h.shape.spareH, h.shape.spareD⟩ s.gap mv pk (by decide) h.inv.hG (hHomeEq5 ▸ hFH)),
      (h.inv.gapHome hhome).2, hg]
  have hOpsEq : c.b0.sudo_5Board_4cost.sudo_5Costs_3ops =
      b.sudo_5Board_4cost.sudo_5Costs_3ops := by
    rw [hb0]; exact hidle.2.2.1
  have hopsZ : 0 < c.b0.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [hOpsEq]
    exact Nat.lt_trans (by decide : (0 : Nat) < 1) h.shape.peg.opsGt
  obtain ⟨cMul, hcMul, hcLe⟩ := h.ops 0 (by rw [← hOpsEq]; exact hopsZ)
  have hopZ : c.b0.sudo_5Board_4cost.sudo_5Costs_3ops[0] = (cMul : Int) :=
    (idx_get hOpsEq 0 hopsZ).trans hcMul
  have hne5 : (5 : Nat) ≠ c.src := by rw [hsrc]; decide
  have hkeep := pegPack_keep c 5 c.g cMul c.m c.hm (Nat.le_refl _)
    hFD hFH hne5 hHeld5 hArr5 hopsZ hopZ
  let d := pegPack c c.m c.hm (Nat.le_refl _)
  have hPack := pegPack_board c c.m c.hm (Nat.le_refl _)
  have hpTake : pegCount (d.xs.take c.n) ≤ c.n := pegCount_take_le d.xs c.n
  have hlenY : d.xs.length = c.bench := by
    rw [d.hxs, cubeBenchIter_length c.n c.k c.bench c.g c.n_le c.m c.hm]
  have hfitL : FitsLen d.xs.length := by rw [hlenY]; exact c.hfitB
  have hspan2 : 2 * (c.n - 1) < c.bench := by
    have hs := c.hspan
    omega
  have hfi : FitsLen (2 * (c.n - 1)) := FitsLen.of_le c.h3 (by omega)
  have hge := mulCharge_ge c.n c.bench d.moves d.xs d.xs c.k c.n_le hpTake
  have hprev := d.hmovB
  have hsum : d.moves + 2 * pegCount (d.xs.take c.n) + c.n * (c.n + 1) +
      3 * (c.bench - c.n) ≤
      c.moves0 + c.m * pegCharge c.n c.bench + mulCharge c.n c.bench := by
    omega
  have hfold : FitsLen (d.moves + 2 * pegCount (d.xs.take c.n) + c.n * (c.n + 1) +
      3 * (c.bench - c.n)) := by
    apply FitsLen.of_le (MoveHeadroom.at hM hmv)
    have hpegN : pegCount s.gap ≤ base.n := by
      have h1 : pegCount s.gap ≤ s.gap.length := pegCount_le s.gap
      rw [h.shape.gapLen, h.hn] at h1
      exact h1
    have hpiece : d.moves + 2 * pegCount (d.xs.take c.n) + c.n * (c.n + 1) +
        3 * (c.bench - c.n) ≤
        mv + base.n + s.tally * pegCharge base.n base.bench +
          mulCharge base.n base.bench + base.n := by
      have hpc : pegCharge c.n c.bench = pegCharge base.n base.bench := by
        rw [hn.trans h.hn, hbch.trans h.hbench]
      have hmc : mulCharge c.n c.bench = mulCharge base.n base.bench := by
        rw [hn.trans h.hn, hbch.trans h.hbench]
      have hright : c.moves0 + c.m * pegCharge c.n c.bench + mulCharge c.n c.bench =
          mv + pegCount s.gap + s.tally * pegCharge base.n base.bench +
            mulCharge base.n base.bench := by
        rw [hmv0, hmEq, hpc, hmc]
      have hmid := Nat.le_trans hsum (Nat.le_of_eq hright)
      exact Nat.le_trans hmid (by
        have hpeg := hpegN
        omega)
    have hbody := white_piece_in_room base.n base.bench s.tally mv _ hpiece
    exact Nat.le_trans hbody (Nat.add_le_add_left
      (Nat.sub_le_sub_right (rungCharge_mono base.n base.bench s.tally base.mMax hT) _) mv)
  have hfm : FitsLen (d.moves + 2 * pegCount (d.xs.take c.n) + c.n * (c.n + 1)) :=
    FitsLen.of_le hfold (by omega)
  have hfitM : FitsLen (d.moves + 2 * pegCount (d.xs.take c.n)) :=
    FitsLen.of_le hfm (by omega)
  have hpegF : FitsLen (2 * pegCount (d.xs.take c.n)) := FitsLen.of_le hfitM (by omega)
  have hsPrev := d.hsldB
  have hlocS : d.slides + 2 * pegCount (d.xs.take c.n) ≤
      sl + s.tally * (2 * base.n) + 2 * base.n := by
    have h2 : 2 * pegCount (d.xs.take c.n) ≤ 2 * c.n := by omega
    have hSlidesEq : c.slides0 + c.m * (2 * c.n) = sl + s.tally * (2 * s.n) := by
      rw [hsl0, hmEq, hn]
    have hprev' : d.slides ≤ sl + s.tally * (2 * s.n) :=
      Nat.le_trans hsPrev (Nat.le_of_eq hSlidesEq)
    have h2s : 2 * pegCount (d.xs.take c.n) ≤ 2 * s.n := by rw [← hn]; exact h2
    have hmul : (s.tally + 1) * (2 * s.n) = s.tally * (2 * s.n) + 2 * s.n := by
      rw [Nat.succ_mul]
    have hloc : d.slides + 2 * pegCount (d.xs.take c.n) ≤
        sl + (s.tally + 1) * (2 * s.n) := by omega
    rw [h.hn] at hloc
    have hsplit : (s.tally + 1) * (2 * base.n) =
        s.tally * (2 * base.n) + 2 * base.n := by
      rw [Nat.succ_mul]
    rw [hsplit] at hloc
    simpa [Nat.add_assoc] using hloc
  have hfitS : FitsLen (d.slides + 2 * pegCount (d.xs.take c.n)) :=
    FitsLen.of_le (SlideHeadroom.at hS hsl)
      (loose_slide_in_room base.n s.tally base.mMax sl _ hT hlocS)
  have hfops : FitsLen (cMul + 1) := by
    apply FitsLen.of_le base.fitO
    have hone : 1 ≤ base.mMax + 3 := by omega
    have hsucc : (done.length + 1) * (base.mMax + 3) =
        done.length * (base.mMax + 3) + (base.mMax + 3) := by
      rw [Nat.succ_mul]
    have hR : (done.length + 1) * (base.mMax + 3) ≤ base.R * (base.mMax + 3) :=
      Nat.mul_le_mul_right _ hk
    omega
  have hH6 : 6 < d.b.sudo_5Board_4home.size := by
    rw [← hsrc]; exact d.hH
  have hD6 : 6 < d.b.sudo_5Board_4held.size := by
    rw [← hsrc]; exact d.hD
  have hempty : d.b.sudo_5Board_4held[6] = false := by
    simpa [hsrc] using d.hempty
  have hto : d.b.sudo_5Board_8bench_to = ((6 : Nat) : Int) := by
    rw [d.toB, hsrc]
  have hnB : d.b.sudo_5Board_1t.sudo_4Tier_1n = (c.n : Int) := by
    rw [d.tier]; exact c.hn
  have hbl : d.b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat c.bench := by
    rw [d.tier]; exact c.hbl
  have hwF : d.b.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat c.w := by
    rw [d.tier]; exact c.hwF
  have hhF : d.b.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat c.h := by
    rw [d.tier]; exact c.hhF
  have hrF : d.b.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat c.r := by
    rw [d.tier]; exact c.hrF
  have hkF : d.b.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat c.k := by
    rw [d.tier]; exact c.hkF
  have hmul := mul_eq_live d.b 5 5 6 c.g d.xs c.w c.h c.r c.n c.k d.moves d.slides d.hole c.bench d.peak d.peakS cMul d.marker d.onB hto hH6 hD6 d.h7 hempty d.hbench hnB c.hn0 d.hpos d.hnle d.hzero c.hf hfitL d.hmoves d.hslides d.hpeak hpegF hfitM hfitS hkeep.opsLt hkeep.op0 hfops hbl hkeep.heldLt hkeep.homeLt hkeep.held hkeep.arr (by decide) c.hlenx hspan2 c.hxsT hfi hfm ⟨c.hw0, c.hh0, c.hrR, c.hrP, c.hnE, c.hkLe, c.hgap⟩ hwF hhF hrF hkF d.hHole d.hpeakS c.hsm c.hnsm c.hfitB hfold
  have hmulW : ∀ (row : Array Int) (ctrl fromHole ridx : Int),
      Ecbs.mul (withPark d.b row ctrl fromHole ridx)
          ((5 : Nat) : Int) ((5 : Nat) : Int) ((6 : Nat) : Int) false false false =
        .ok (withPark
          (mulNoLiveBoard d.b 5 6 c.g d.xs ⟨c.n, c.k, d.moves, d.slides, d.hole, c.bench, d.peak, d.peakS, cMul, hkeep.opsLt⟩ ⟨hH6, hD6⟩)
          row ctrl fromHole ridx) := by
    intro row ctrl fromHole ridx
    exact mul_eq_live_withPark d.b 5 5 6 c.g d.xs c.w c.h c.r c.n c.k d.moves d.slides d.hole c.bench d.peak d.peakS cMul d.marker d.onB hto hH6 hD6 d.h7 hempty d.hbench hnB c.hn0 d.hpos d.hnle d.hzero c.hf hfitL d.hmoves d.hslides d.hpeak hpegF hfitM hfitS hkeep.opsLt hkeep.op0 hfops hbl hkeep.heldLt hkeep.homeLt hkeep.held hkeep.arr (by decide) c.hlenx hspan2 c.hxsT hfi hfm ⟨c.hw0, c.hh0, c.hrR, c.hrP, c.hnE, c.hkLe, c.hgap⟩ hwF hhF hrF hkF d.hHole d.hpeakS c.hsm c.hnsm c.hfitB hfold row ctrl fromHole ridx
  have hXFD0 : base.xHome < c.b0.sudo_5Board_4held.size := by
    rw [hb0, hbook.2.2.2.2.2.2.2.2.2]
    exact h.shape.xD
  have hXFH0 : base.xHome < c.b0.sudo_5Board_4home.size := by
    rw [hb0, hbook.2.2.2.2.2.2.2.2.1]
    exact h.shape.xH
  have hXHeldEq : c.b0.sudo_5Board_4held =
      (placeBoard b 6 h.shape.spareH h.shape.spareD s.gap mv pk).sudo_5Board_4held := by
    rw [hb0]
  have hXHomeEq : c.b0.sudo_5Board_4home =
      (placeBoard b 6 h.shape.spareH h.shape.spareD s.gap mv pk).sudo_5Board_4home := by
    rw [hb0]
  have hXHeld0 : c.b0.sudo_5Board_4held[base.xHome] = true :=
    (idx_get hXHeldEq base.xHome hXFD0).trans
      ((place_held_other b 6 base.xHome ⟨h.shape.spareH, h.shape.spareD⟩ s.gap mv pk (Ne.symm h.shape.xNe6) h.shape.xD (hXHeldEq ▸ hXFD0)).trans h.shape.xHeld)
  have hXArr0 : c.b0.sudo_5Board_4home[base.xHome] = embed base.x := by
    rw [(idx_get hXHomeEq base.xHome hXFH0).trans
        (place_home_other b 6 base.xHome ⟨h.shape.spareH, h.shape.spareD⟩ s.gap mv pk (Ne.symm h.shape.xNe6) h.shape.xH (hXHomeEq ▸ hXFH0)),
      h.shape.xArr]
  have hXne : base.xHome ≠ c.src := by rw [hsrc]; exact h.shape.xNe6
  have hXkeep := pegPack_keep c base.xHome base.x cMul c.m c.hm (Nat.le_refl _)
    hXFD0 hXFH0 hXne hXHeld0 hXArr0 hopsZ hopZ
  obtain ⟨c0, hc0, hcle⟩ := h.ops 1 h.shape.peg.opsGt
  have hCubeNat : d.cOps = c0 + c.m := by
    rw [d.hcOps]
    have hOpsP : c.b0.sudo_5Board_4cost.sudo_5Costs_3ops =
        b.sudo_5Board_4cost.sudo_5Costs_3ops := by
      rw [hb0]; exact hidle.2.2.1
    have hsz : 1 < c.b0.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
      rw [hOpsP]; exact h.shape.peg.opsGt
    have hget := idx_get hOpsP 1 hsz
    have hc : c.cOps0 = c0 :=
      ofNat_inj_nat ((c.hop10).symm.trans (hget.trans hc0))
    rw [hc]
  have hCubeFit : FitsLen (d.cOps + 1) := by
    apply FitsLen.of_le base.fitO
    rw [hCubeNat, hmEq]
    have hstep : c0 + s.tally + 1 ≤
        base.ops0 + (done.length + 1) * (base.mMax + 3) := by
      have hsucc : (done.length + 1) * (base.mMax + 3) =
          done.length * (base.mMax + 3) + (base.mMax + 3) := by rw [Nat.succ_mul]
      have ht : s.tally + 1 ≤ base.mMax + 3 := by omega
      omega
    have hR : (done.length + 1) * (base.mMax + 3) ≤ base.R * (base.mMax + 3) :=
      Nat.mul_le_mul_right _ hk
    omega
  refine ⟨c, d.b, d.xs, d.moves, d.slides, d.hole, d.peak, d.peakS, cMul,
    hH6, hD6, hkeep.opsLt, hcopy, hsrc, hg, hmEq, hn, hkN, hbch, hPack.1, d.hxs,
    { heldLt := hkeep.heldLt, held := hkeep.held, homeLt := hkeep.homeLt, arr := hkeep.arr },
    { heldLt := hXkeep.heldLt, held := hXkeep.held, homeLt := hXkeep.homeLt, arr := hXkeep.arr },
    ⟨d.cOps, d.hops, d.hop1, hCubeFit⟩,
    (by rw [d.hrow, hrow0, ht0, hmEq]),
    d.tier, d.marker,
    (by
      rw [hPack.2.2.2.2.2.2.2.2]
      exact c.h7),
    hkeep.op0, hcLe, hctrl0, hhigh0, hcontrol, hlen0, hmax0, ht0,
    hmul, hrow0, d.hmoves, d.hslides, d.hHole, d.hpeak, d.hpeakS,
    ⟨mv, hmv, by
      have hslack := pegPack_move_slack c c.m c.hm (Nat.le_refl _)
      have hpeg : pegCount s.gap ≤ base.n := by
        have hlen : pegCount s.gap ≤ s.gap.length := pegCount_le s.gap
        rw [h.shape.gapLen, h.hn] at hlen
        exact hlen
      have hsum : c.moves0 + c.m * pegCharge c.n c.bench =
          mv + pegCount s.gap + s.tally * pegCharge base.n base.bench := by
        rw [hmv0, hmEq, hn, hbch, h.hn, h.hbench]
      have h1 : d.moves + 2 * c.n ≤
          mv + pegCount s.gap + s.tally * pegCharge base.n base.bench := by
        rw [hsum] at hslack
        exact hslack
      have hnB : c.n = base.n := hn.trans h.hn
      rw [hnB] at h1
      exact Nat.le_trans h1
        (Nat.add_le_add_right (Nat.add_le_add_left hpeg mv) _)⟩,
    ⟨sl, hsl, by
      have hslack := pegPack_slide_slack c c.m c.hm (Nat.le_refl _)
      have hsum : c.slides0 + c.m * (2 * c.n) = sl + s.tally * (2 * base.n) := by
        rw [hsl0, hmEq, hn, h.hn]
      have h1 : d.slides + 2 * c.n ≤ sl + s.tally * (2 * base.n) := by
        rw [hsum] at hslack
        exact hslack
      have hnB : c.n = base.n := hn.trans h.hn
      rw [hnB] at h1
      exact h1⟩, hmulW⟩

/-- `ClimbInvK` supplies the core and one charge of tight headroom. -/
def park_of_shape_ofK {done rest : List Nat} {r : Nat} {b : Ecbs.Board}
    {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvK done (r :: rest) b s base) :=
  park_of_shape h.toCore

noncomputable def peg_of_shape_ofK {done rest : List Nat} {r : Nat} {b : Ecbs.Board}
    {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvK done (r :: rest) b s base)
    (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax) (hhome : s.onBench = false) :=
  peg_of_shape h.toCore (moveHeadroom_of_cons h) (slideHeadroom_of_cons h) hm hT hhome

noncomputable def parked_peg_ctx_ofK {done rest : List Nat} {r : Nat} {b : Ecbs.Board}
    {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvK done (r :: rest) b s base)
    (hF : s.fromHole < 0) (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax)
    (hhome : s.onBench = false) :=
  parked_peg_ctx h.toCore (moveHeadroom_of_cons h) (slideHeadroom_of_cons h)
    hF hm hT hhome

noncomputable def parked_gap_mul_ofK {done rest : List Nat} {r : Nat} {b : Ecbs.Board}
    {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvK done (r :: rest) b s base)
    (hF : s.fromHole < 0) (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax)
    (hhome : s.onBench = false) :=
  parked_gap_mul h.toCore (moveHeadroom_of_cons h) (slideHeadroom_of_cons h)
    hF hm hT hhome

noncomputable def mul_of_shape_ofK {done rest : List Nat} {r : Nat} {b : Ecbs.Board}
    {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvK done (r :: rest) b s base)
    (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax) (hhome : s.onBench = false) :=
  mul_of_shape h.toCore (moveHeadroom_of_cons h) (slideHeadroom_of_cons h) hm hT hhome

/-- A live nocopy mul clears the second home. A different home, and the array it holds, stay. -/
theorem mulLive_keep (b : Ecbs.Board) (dst second first : Nat) (xs ys : List Nat)
    (bud : Budget b 0)
    (xs0 : List Nat)
    (hin : HomeIn b second)
    (hne : first ≠ second)
    (hFD : first < b.sudo_5Board_4held.size)
    (hFH : first < b.sudo_5Board_4home.size)
    (hHeld : b.sudo_5Board_4held[first] = true)
    (hArr : b.sudo_5Board_4home[first] = embed xs0) :
    CellKeep (mulNoLiveBoard b dst second xs ys bud hin) first xs0 := by
  let bM := mulNoLiveBoard b dst second xs ys bud hin
  have hHeldM := mul_live_held b dst second xs ys bud hin
  have hS := settle_held_eq b second ⟨hin.hH, hin.hD⟩ ys bud.n bud.moves bud.slides bud.peak
  have hHomeM := mul_live_home b dst second xs ys bud hin
  have heldLt : first < bM.sudo_5Board_4held.size := by
    have hsz : bM.sudo_5Board_4held.size = b.sudo_5Board_4held.size := by
      rw [hHeldM]
      simp only [Array.size_set]
      rw [hS]
      simp only [Array.size_set]
    rw [hsz]
    exact hFD
  have held : bM.sudo_5Board_4held[first]'heldLt = true := by
    have h1 := idx_get hHeldM first heldLt
    rw [h1, Array.getElem_set, if_neg (Ne.symm hne)]
    have hsz : first <
        (settleBoard b second hin.hH hin.hD ys bud.n bud.moves bud.slides bud.peak).sudo_5Board_4held.size := by
      rw [hS, Array.size_set]; exact hFD
    have h2 := idx_get hS first hsz
    rw [h2, Array.getElem_set, if_neg (Ne.symm hne)]
    exact hHeld
  have homeLt : first < bM.sudo_5Board_4home.size := by
    rw [hHomeM, Array.size_set]; exact hFH
  have arr : bM.sudo_5Board_4home[first]'homeLt = embed xs0 := by
    have h1 := idx_get hHomeM first homeLt
    rw [h1, Array.getElem_set, if_neg (Ne.symm hne)]
    exact hArr
  exact { heldLt, held, homeLt, arr }

theorem mul_live_aimed (b : Ecbs.Board) (dst second : Nat) (xs ys : List Nat)
    (bud : Budget b 0)
    (hin : HomeIn b second) :
    (mulNoLiveBoard b dst second xs ys bud hin).sudo_5Board_8bench_on =
        true ∧
      (mulNoLiveBoard b dst second xs ys bud hin).sudo_5Board_8bench_to =
        (dst : Int) := by
  unfold mulNoLiveBoard
  refine ⟨?_, ?_⟩
  · simpa using
      mul_no_on (settleBoard b second hin.hH hin.hD ys bud.n bud.moves bud.slides bud.peak) dst second xs (ys.take bud.n)
        bud.n bud.k (bud.moves + 2 * pegCount (ys.take bud.n)) bud.hole bud.bench
        (raisedPeak bud.peak (countHeld (b.sudo_5Board_4held.set ⟨second, hin.hD⟩ true) 7)) bud.peakS bud.cOps
        (settle_ops_lt b 0 second bud.hops ⟨hin.hH, hin.hD⟩ ys bud.n bud.moves bud.slides bud.peak)
        (settle_held_lt b second ⟨hin.hH, hin.hD⟩ ys bud.n bud.moves bud.slides bud.peak)
        (settle_home_lt b second ⟨hin.hH, hin.hD⟩ ys bud.n bud.moves bud.slides bud.peak)
  · simpa using
      mul_no_to (settleBoard b second hin.hH hin.hD ys bud.n bud.moves bud.slides bud.peak) dst second xs (ys.take bud.n)
        bud.n bud.k (bud.moves + 2 * pegCount (ys.take bud.n)) bud.hole bud.bench
        (raisedPeak bud.peak (countHeld (b.sudo_5Board_4held.set ⟨second, hin.hD⟩ true) 7)) bud.peakS bud.cOps
        (settle_ops_lt b 0 second bud.hops ⟨hin.hH, hin.hD⟩ ys bud.n bud.moves bud.slides bud.peak)
        (settle_held_lt b second ⟨hin.hH, hin.hD⟩ ys bud.n bud.moves bud.slides bud.peak)
        (settle_home_lt b second ⟨hin.hH, hin.hD⟩ ys bud.n bud.moves bud.slides bud.peak)

theorem mulMovesNo_bound (moves n k bench : Nat) (xs ys : List Nat)
    (_hn : n ≤ bench) :
    mulMovesNo (moves + 2 * pegCount (ys.take n)) xs (ys.take n) n k bench ≤
      moves + 2 * pegCount (ys.take n) + n * (n + 1) + 3 * (bench - n) := by
  let sch := school n xs (ys.take n) (List.replicate bench 0) false
  have hs := schoolMoves_bound xs (ys.take n) n
  have hsch : sch.length = bench := by
    simpa [sch, List.length_replicate] using
      school_length xs (ys.take n) (List.replicate bench 0) false n
  have hf : foldCharge n (n - k) sch ≤ 3 * (bench - n) := by
    have h := foldCharge_bound n (n - k) sch
    rw [hsch] at h
    exact h
  have hgoal : mulMovesNo (moves + 2 * pegCount (ys.take n)) xs (ys.take n) n k bench =
      moves + 2 * pegCount (ys.take n) + schoolMoves xs (ys.take n) n n +
        foldCharge n (n - k) sch := by
    simp [mulMovesNo, sch]
  rw [hgoal]
  have h1 : moves + 2 * pegCount (ys.take n) + schoolMoves xs (ys.take n) n n ≤
      moves + 2 * pegCount (ys.take n) + n * (n + 1) :=
    Nat.add_le_add_left hs _
  exact Nat.le_trans (Nat.add_le_add_left hf _) (Nat.add_le_add h1 (Nat.le_refl _))

theorem mul_live_hole (b : Ecbs.Board) (dst second : Nat) (xs ys : List Nat)
    (bud : Budget b 0)
    (hin : HomeIn b second) :
    (mulNoLiveBoard b dst second xs ys bud hin).sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      Int.ofNat (raisedHole bud.hole (topIdx
        (school bud.n xs (ys.take bud.n) (List.replicate bud.bench 0) false))) := by
  unfold mulNoLiveBoard mulNoOffBoard
  rfl

/-- The gap mul leaves home 5 held. `clear` of that home is the named clear board.
    Its move counter stays inside the climb's move budget: one `mulCharge` has
    been spent and the clear adds at most `n`, both of which sit in `rungCharge`. -/
theorem clear_after_gap_mul {done rest : List Nat} {r : Nat} {b : Ecbs.Board}
    {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvK done (r :: rest) b s base)
    (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax)
    (hhome : s.onBench = false) :
    ∃ (bLoop bMul bClear : Ecbs.Board),
      Ecbs.mul bLoop ((5 : Nat) : Int) ((5 : Nat) : Int) ((6 : Nat) : Int)
          false false false = .ok bMul ∧
      Ecbs.clear bMul ((5 : Nat) : Int) = .ok bClear ∧
      bClear.sudo_5Board_5bench =
        embed (fieldMul s.n s.k s.benchlen s.gap
          (cubeTimes s.n s.k s.benchlen s.gap s.tally) ++
          List.replicate (s.benchlen - s.n) 0) := by
  obtain ⟨c, bLoop, ys, moves, slides, hole, peak, peakS, cMul, hH, hD, hops,
      _hcopy, _hsrc, hg, hmEq, hn, hkN, hbch, _hpeg, hysEq, hGap, _hX,
      _hOp, _hRow, _htier, _hmk, _h7, _hop0, _hOpsLe,       _hctrl0, _hhigh0,       _hcontrol, _hlen0, _hmax0, _ht0, hmul, _hrow0, _hmvB, _hslB, _hhoB, _hpkB, _hpsB,
      ⟨mvE, hmvE, hmovRel⟩, ⟨_, _, _⟩, _hmulW⟩ :=
    mul_of_shape_ofK h hm hT hhome
  obtain ⟨mvAbs, hmvAbs, hmvAbsLe⟩ := h.moves_loose
  have hmvEeq : mvE = mvAbs := ofNat_inj_nat (hmvE.symm.trans hmvAbs)
  have hMov : moves ≤ base.moves0 + done.length * rungCharge base.n base.bench base.mMax +
      base.n + s.tally * pegCharge base.n base.bench := by
    have hloose : moves ≤ mvE + base.n + s.tally * pegCharge base.n base.bench := by
      omega
    have hrel := hloose
    rw [hmvEeq] at hrel
    have hflat : mvAbs + base.n + s.tally * pegCharge base.n base.bench =
        mvAbs + (base.n + s.tally * pegCharge base.n base.bench) := by
      rw [← Nat.add_assoc]
    rw [hflat] at hrel
    have hstep := Nat.add_le_add_right hmvAbsLe
      (base.n + s.tally * pegCharge base.n base.bench)
    have hright := (Nat.add_assoc
      (base.moves0 + done.length * rungCharge base.n base.bench base.mMax)
      base.n (s.tally * pegCharge base.n base.bench)).symm
    exact Nat.le_trans (Nat.le_trans hrel hstep) (Nat.le_of_eq hright)
  let bMul := mulNoLiveBoard bLoop 5 6 c.g ys ⟨c.n, c.k, moves, slides, hole, c.bench, peak, peakS, cMul, hops⟩ ⟨hH, hD⟩
  have hKeep := mulLive_keep bLoop 5 6 5 c.g ys ⟨c.n, c.k, moves, slides, hole, c.bench, peak, peakS, cMul, hops⟩ c.g ⟨hH, hD⟩ (by decide) hGap.heldLt hGap.homeLt hGap.held hGap.arr
  let mvC := mulMovesNo (moves + 2 * pegCount (ys.take c.n)) c.g (ys.take c.n)
    c.n c.k c.bench
  have hmvC : bMul.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mvC := by
    simpa [bMul, mvC] using
      mul_live_moves bLoop 5 6 c.g ys ⟨c.n, c.k, moves, slides, hole, c.bench, peak, peakS, cMul, hops⟩ ⟨hH, hD⟩
  have hlenG : c.g.length = c.n := c.hlenx
  have hfitN : FitsLen c.g.length := by rw [hlenG]; exact c.hf
  have hpegN : pegCount c.g ≤ c.n := by rw [← hlenG]; exact pegCount_le c.g
  have hmvC_le : mvC ≤ moves + mulCharge c.n c.bench := by
    have hstep := mulMovesNo_bound moves c.n c.k c.bench c.g ys c.n_le
    have hrest : 2 * pegCount (ys.take c.n) + c.n * (c.n + 1) + 3 * (c.bench - c.n) ≤
        mulCharge c.n c.bench := by
      unfold mulCharge
      have hp := pegCount_take_le ys c.n
      omega
    omega
  have hk : done.length + 1 ≤ base.R := by
    have hlen := h.kLe
    rw [List.length_append, List.length_cons] at hlen
    omega
  have hbudget : mvC + pegCount c.g ≤
      base.moves0 + base.R * rungCharge base.n base.bench base.mMax := by
    have hmulC : mulCharge c.n c.bench = mulCharge base.n base.bench := by
      rw [hn, hbch, h.hn, h.hbench]
    have hcn : c.n = base.n := by rw [hn, h.hn]
    have h1 : mvC + pegCount c.g ≤ moves + mulCharge base.n base.bench + base.n := by
      have h := Nat.add_le_add hmvC_le hpegN
      rw [hmulC, hcn] at h
      exact h
    have h2 : moves + mulCharge base.n base.bench + base.n ≤
        base.moves0 + done.length * rungCharge base.n base.bench base.mMax +
          (base.n + s.tally * pegCharge base.n base.bench) +
          (mulCharge base.n base.bench + base.n) := by
      have hmov := hMov
      have hadd := Nat.add_le_add_right hmov (mulCharge base.n base.bench + base.n)
      simpa [Nat.add_assoc] using hadd
    have hpiece : base.n + s.tally * pegCharge base.n base.bench +
        (mulCharge base.n base.bench + base.n) ≤
        rungCharge base.n base.bench base.mMax := by
      unfold rungCharge
      have hpeg : s.tally * pegCharge base.n base.bench ≤
          (base.mMax + 1) * pegCharge base.n base.bench :=
        Nat.mul_le_mul_right _ (Nat.le_succ_of_le hT)
      have hnn : base.n + base.n = 2 * base.n := by rw [Nat.two_mul]
      have htwo : mulCharge base.n base.bench + mulCharge base.n base.bench =
          2 * mulCharge base.n base.bench := by rw [Nat.two_mul]
      omega
    have h3 : base.moves0 + done.length * rungCharge base.n base.bench base.mMax +
        (base.n + s.tally * pegCharge base.n base.bench) +
        (mulCharge base.n base.bench + base.n) ≤
        base.moves0 + done.length * rungCharge base.n base.bench base.mMax +
          rungCharge base.n base.bench base.mMax := by
      have h := Nat.add_le_add_left hpiece
        (base.moves0 + done.length * rungCharge base.n base.bench base.mMax)
      simpa [Nat.add_assoc] using h
    have hsucc : base.moves0 + done.length * rungCharge base.n base.bench base.mMax +
        rungCharge base.n base.bench base.mMax =
        base.moves0 + (done.length + 1) * rungCharge base.n base.bench base.mMax := by
      rw [Nat.add_assoc, ← Nat.succ_mul]
    have hR : base.moves0 + (done.length + 1) * rungCharge base.n base.bench base.mMax ≤
        base.moves0 + base.R * rungCharge base.n base.bench base.mMax :=
      Nat.add_le_add_left (Nat.mul_le_mul_right _ hk) _
    exact Nat.le_trans h1 (Nat.le_trans h2 (Nat.le_trans h3
      (Nat.le_trans (Nat.le_of_eq hsucc) hR)))
  have hfitC : FitsLen (mvC + pegCount c.g) := FitsLen.of_le base.fitM hbudget
  have hclear := clear_held_refines bMul 5 c.g mvC hKeep.homeLt hKeep.heldLt
    hKeep.held hKeep.arr hmvC hfitN hfitC
  have hpre : ys.take c.n = cubeTimes c.n c.k c.bench c.g c.m := by
    rw [hysEq]
    exact cubeBenchIter_prefix c.n c.k c.bench c.g c.hlenx c.m
  have hgapB : bMul.sudo_5Board_5bench =
      embed (fieldMul c.n c.k c.bench c.g (cubeTimes c.n c.k c.bench c.g c.m) ++
        List.replicate (c.bench - c.n) 0) := by
    have hraw := mul_live_bench_gap bLoop 5 6 c.g ys ⟨c.n, c.k, moves, slides, hole, c.bench, peak, peakS, cMul, hops⟩ ⟨hH, hD⟩ c.hn0 c.gap_pos c.n_le
    simpa [bMul, hpre] using hraw
  rw [hn, hkN, hbch, hg, hmEq] at hgapB
  refine ⟨bLoop, bMul, _, hmul, hclear, ?_⟩
  · show bMul.sudo_5Board_5bench =
      embed (fieldMul s.n s.k s.benchlen s.gap
        (cubeTimes s.n s.k s.benchlen s.gap s.tally) ++
        List.replicate (s.benchlen - s.n) 0)
    exact hgapB

/-- Moves through the red mul: the tight pre-mul bound, one `mulCharge`, the
    clear's `n`, one `pegCharge`, and the red `mulCharge`. That is one
    `rungCharge` on top of the rungs already run. -/
private theorem redMulBudget (moves0 doneLen n bench mMax tally moves mvC pegG pegL : Nat)
    (hT : tally ≤ mMax)
    (hMov : moves ≤ moves0 + doneLen * rungCharge n bench mMax + n + tally * pegCharge n bench)
    (hmv : mvC ≤ moves + mulCharge n bench) (hpeg : pegG ≤ n)
    (hcube : 2 * pegL + 2 * n + 3 * (bench - n) ≤ pegCharge n bench) :
    mvC + pegG + 2 * pegL + 2 * n + 3 * (bench - n) + mulCharge n bench ≤
      moves0 + (doneLen + 1) * rungCharge n bench mMax := by
  have hclear : mvC + pegG ≤ moves + mulCharge n bench + n := by omega
  have hU : mvC + pegG + 2 * pegL + 2 * n + 3 * (bench - n) ≤
      moves + mulCharge n bench + n + pegCharge n bench := by omega
  have hWith : mvC + pegG + 2 * pegL + 2 * n + 3 * (bench - n) + mulCharge n bench ≤
      moves + mulCharge n bench + n + pegCharge n bench + mulCharge n bench := by omega
  have hmov' : moves + mulCharge n bench + n + pegCharge n bench + mulCharge n bench ≤
      moves0 + doneLen * rungCharge n bench mMax +
        (n + tally * pegCharge n bench + mulCharge n bench + n + pegCharge n bench +
          mulCharge n bench) := by omega
  have hpiece : n + tally * pegCharge n bench + mulCharge n bench + n + pegCharge n bench +
      mulCharge n bench ≤ rungCharge n bench mMax := by
    have hred := charge_final_red n bench mMax
    have hmul := Nat.mul_le_mul_right (pegCharge n bench) hT
    omega
  have hsucc : moves0 + doneLen * rungCharge n bench mMax + rungCharge n bench mMax =
      moves0 + (doneLen + 1) * rungCharge n bench mMax := by
    rw [Nat.add_assoc, ← Nat.succ_mul]
  have hjoin : mvC + pegG + 2 * pegL + 2 * n + 3 * (bench - n) + mulCharge n bench ≤
      moves0 + doneLen * rungCharge n bench mMax + rungCharge n bench mMax := by
    exact Nat.le_trans hWith (Nat.le_trans hmov' (Nat.add_le_add_left hpiece _))
  exact Nat.le_trans hjoin (Nat.le_of_eq hsucc)

/-- Slides through the red mul: the peg loop, then one `2 · n` each for the gap
    mul, the red cube, and the red mul. -/
private theorem redSlideBudget (slides0 doneLen n mMax tally slides pegY pegL pegZ : Nat)
    (hT : tally ≤ mMax)
    (hS : slides ≤ slides0 + doneLen * rungSlideCharge n mMax + tally * (2 * n))
    (hY : 2 * pegY ≤ 2 * n) (hL : 2 * pegL ≤ 2 * n) (hZ : 2 * pegZ ≤ 2 * n) :
    slides + 2 * pegY + 2 * pegL + 2 * pegZ ≤
      slides0 + (doneLen + 1) * rungSlideCharge n mMax := by
  have hsum : slides + 2 * pegY + 2 * pegL + 2 * pegZ ≤
      slides0 + doneLen * rungSlideCharge n mMax + tally * (2 * n) + 2 * n + 2 * n + 2 * n := by
    omega
  have hpiece : tally * (2 * n) + 2 * n + 2 * n + 2 * n ≤ rungSlideCharge n mMax := by
    unfold rungSlideCharge
    have ht : tally + 3 ≤ mMax + 3 := by omega
    have hsplit : (tally + 3) * (2 * n) = tally * (2 * n) + 3 * (2 * n) := by
      rw [Nat.add_mul]
    have h3 : 3 * (2 * n) = 2 * n + 2 * n + 2 * n := by omega
    have hmul := Nat.mul_le_mul_right (2 * n) ht
    omega
  have hsum' : slides + 2 * pegY + 2 * pegL + 2 * pegZ ≤
      slides0 + doneLen * rungSlideCharge n mMax +
        (tally * (2 * n) + 2 * n + 2 * n + 2 * n) := by
    simpa [Nat.add_assoc] using hsum
  have hjoin : slides + 2 * pegY + 2 * pegL + 2 * pegZ ≤
      slides0 + doneLen * rungSlideCharge n mMax + rungSlideCharge n mMax := by
    exact Nat.le_trans hsum' (Nat.add_le_add_left hpiece _)
  have hsucc : slides0 + doneLen * rungSlideCharge n mMax + rungSlideCharge n mMax =
      slides0 + (doneLen + 1) * rungSlideCharge n mMax := by
    rw [Nat.add_assoc, ← Nat.succ_mul]
  exact Nat.le_trans hjoin (Nat.le_of_eq hsucc)

private theorem replicate_trits_local (k : Nat) : allTritList (List.replicate k 0) := by
  intro x hx
  simp [List.mem_replicate] at hx
  rcases hx with ⟨_, rfl⟩
  decide

/-- `clear` writes one home. A different home, and the array it holds, stay. -/
theorem clearCell_keep (b : Ecbs.Board) (home first : Nat) (xs : List Nat)
    (moves : Nat) (xs0 : List Nat)
    (hin : HomeIn b home)
    (hne : home ≠ first) (hk : CellKeep b first xs0) :
    CellKeep (clearHeldBoard b home xs moves hin.hH hin.hD) first xs0 := by
  let bC := clearHeldBoard b home xs moves hin.hH hin.hD
  have hHeldEq : bC.sudo_5Board_4held = b.sudo_5Board_4held.set ⟨home, hin.hD⟩ false := by
    simp [bC, clearHeldBoard]
  have hHomeEq : bC.sudo_5Board_4home = b.sudo_5Board_4home.set ⟨home, hin.hH⟩ #[] := by
    simp [bC, clearHeldBoard]
  have heldLt : first < bC.sudo_5Board_4held.size := by
    rw [hHeldEq, Array.size_set]; exact hk.heldLt
  have held : bC.sudo_5Board_4held[first]'heldLt = true := by
    rw [idx_get hHeldEq first heldLt, Array.getElem_set, if_neg hne]
    exact hk.held
  have homeLt : first < bC.sudo_5Board_4home.size := by
    rw [hHomeEq, Array.size_set]; exact hk.homeLt
  have arr : bC.sudo_5Board_4home[first]'homeLt = embed xs0 := by
    rw [idx_get hHomeEq first homeLt, Array.getElem_set, if_neg hne]
    exact hk.arr
  exact { heldLt, held, homeLt, arr }

/-- A live cube clears `src`. A different home, and the array it holds, stay. -/
theorem cubeLive_keep (b : Ecbs.Board) (dst src first : Nat) (xs : List Nat)
    (bud : Budget b 1)
    (xs0 : List Nat)
    (hin : HomeIn b src)
    (hne : first ≠ src)
    (hFD : first < b.sudo_5Board_4held.size)
    (hFH : first < b.sudo_5Board_4home.size)
    (hHeld : b.sudo_5Board_4held[first] = true)
    (hArr : b.sudo_5Board_4home[first] = embed xs0) :
    CellKeep (cubeLiveBoard b dst src xs bud hin)
      first xs0 := by
  let bC := cubeLiveBoard b dst src xs bud hin
  have hHeldC := cube_live_held b dst src xs bud hin
  have hS := settle_held_eq b src ⟨hin.hH, hin.hD⟩ xs bud.n bud.moves bud.slides bud.peak
  have hHomeC := cube_live_home b dst src xs bud hin
  have heldLt : first < bC.sudo_5Board_4held.size := by
    have hsz : bC.sudo_5Board_4held.size = b.sudo_5Board_4held.size := by
      rw [hHeldC]
      simp only [Array.size_set]
      rw [hS]
      simp only [Array.size_set]
    rw [hsz]
    exact hFD
  have held : bC.sudo_5Board_4held[first]'heldLt = true := by
    have h1 := idx_get hHeldC first heldLt
    rw [h1, Array.getElem_set, if_neg (Ne.symm hne)]
    have hsz : first <
        (settleBoard b src hin.hH hin.hD xs bud.n bud.moves bud.slides bud.peak).sudo_5Board_4held.size := by
      rw [hS, Array.size_set]; exact hFD
    have h2 := idx_get hS first hsz
    rw [h2, Array.getElem_set, if_neg (Ne.symm hne)]
    exact hHeld
  have homeLt : first < bC.sudo_5Board_4home.size := by
    rw [hHomeC, Array.size_set]; exact hFH
  have arr : bC.sudo_5Board_4home[first]'homeLt = embed xs0 := by
    have h1 := idx_get hHomeC first homeLt
    rw [h1, Array.getElem_set, if_neg (Ne.symm hne)]
    exact hArr
  exact { heldLt, held, homeLt, arr }

private theorem pegStep_tmax (bC : Ecbs.Board) (t0 j : Nat)
    (hrow : t0 + j < bC.sudo_5Board_3row.size) (ctrl : Nat) :
    (pegStep bC t0 j hrow ctrl).sudo_5Board_4cost.sudo_5Costs_9tally_max =
      bC.sudo_5Board_4cost.sudo_5Costs_9tally_max := rfl

private theorem cubeOff_tmax (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (n k moves hole bench peak peakS cOps : Nat)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hF : src < b.sudo_5Board_4held.size) (hHome : src < b.sudo_5Board_4home.size) :
    (cubeOffBoard b dst src xs n k moves hole bench peak peakS cOps hops hF hHome).sudo_5Board_4cost.sudo_5Costs_9tally_max =
      b.sudo_5Board_4cost.sudo_5Costs_9tally_max := rfl

private theorem settle_tmax (b : Ecbs.Board) (home : Nat)
    (hin : HomeIn b home)
    (xs : List Nat) (n moves slides peak : Nat) :
    (settleBoard b home hin.hH hin.hD xs n moves slides peak).sudo_5Board_4cost.sudo_5Costs_9tally_max =
      b.sudo_5Board_4cost.sudo_5Costs_9tally_max := by
  unfold settleBoard
  split <;> rfl

theorem cubeLive_tmax (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (bud : Budget b 1)
    (hin : HomeIn b src) :
    (cubeLiveBoard b dst src xs bud hin).sudo_5Board_4cost.sudo_5Costs_9tally_max =
      b.sudo_5Board_4cost.sudo_5Costs_9tally_max := by
  unfold cubeLiveBoard
  rw [cubeOff_tmax, settle_tmax b src hin xs bud.n bud.moves bud.slides bud.peak]

theorem pegPack_tmax (c : PegCtx) (i : Nat) (h0 : 0 < i) (hle : i ≤ c.m) :
    (pegPack c i h0 hle).b.sudo_5Board_4cost.sudo_5Costs_9tally_max =
      c.b0.sudo_5Board_4cost.sudo_5Costs_9tally_max := by
  match i with
  | 0 => exact absurd h0 (Nat.not_lt_zero 0)
  | 1 =>
    simp only [pegPack, pegBoard, pegFromOff, hle, dite_true]
    unfold offPeg
    rw [pegStep_tmax, cubeOff_tmax]
  | n + 2 =>
    have hle1 : n + 1 ≤ c.m := Nat.le_of_succ_le hle
    have h0' : 0 < n + 1 := Nat.succ_pos n
    have ih := pegPack_tmax c (n + 1) h0' hle1
    simp only [pegPack, pegBoard, pegNext, hle, dite_true]
    unfold livePegBoard
    let d := pegPack c (n + 1) h0' hle1
    rw [pegStep_tmax, cubeLive_tmax d.b c.src c.src d.xs
        ⟨c.n, c.k, d.moves, d.slides, d.hole, c.bench, d.peak, d.peakS, d.cOps, d.hops⟩
        ⟨d.hH, d.hD⟩]
    exact ih

private theorem place_tmax_local (b : Ecbs.Board) (home : Nat)
    (hin : HomeIn b home)
    (xs : List Nat) (moves peak : Nat) :
    (placeBoard b home hin.hH hin.hD xs moves peak).sudo_5Board_4cost.sudo_5Costs_9tally_max =
      b.sudo_5Board_4cost.sudo_5Costs_9tally_max := by
  unfold placeBoard
  dsimp only
  split <;> rfl

theorem mulLive_tmax (b : Ecbs.Board) (dst second : Nat) (xs ys : List Nat)
    (bud : Budget b 0)
    (hin : HomeIn b second) :
    (mulNoLiveBoard b dst second xs ys bud hin).sudo_5Board_4cost.sudo_5Costs_9tally_max =
      b.sudo_5Board_4cost.sudo_5Costs_9tally_max := by
  unfold mulNoLiveBoard mulNoOffBoard
  rw [settle_tmax b second hin ys bud.n bud.moves bud.slides bud.peak]

theorem clear_tmax (b : Ecbs.Board) (home : Nat) (xs : List Nat) (moves : Nat)
    (hin : HomeIn b home) :
    (clearHeldBoard b home xs moves hin.hH hin.hD).sudo_5Board_4cost.sudo_5Costs_9tally_max =
      b.sudo_5Board_4cost.sudo_5Costs_9tally_max := rfl

end EcbsLink2.Link2
