/-
  The control row below the tally, with at most one rung parked.
  A rung puts that colour in the park hole and clears its own hole. Unpark
  puts it back. `tally_clear` then empties the tally. The painted ladder is
  what remains. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.Invert

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- Below the tally origin, the row is the painted ladder, except the parked
    hole is empty and the park hole holds that hole's painted colour. -/
structure RowHome (row painted : List Nat) (parkAt : Nat) (fromHole : Int) (t0 : Nat) : Prop where
  len : row.length = painted.length
  parkLt : parkAt < painted.length
  fromLt : 0 ≤ fromHole → fromHole.toNat < painted.length
  below : ∀ j (hj : j < t0) (hr : j < row.length),
    row[j]'hr =
      if hF : 0 ≤ fromHole then
        if j = fromHole.toNat then 0
        else if j = parkAt then painted[fromHole.toNat]'(fromLt hF)
        else painted[j]'(by have := hj; have := hr; omega)
      else painted[j]'(by have := hj; have := hr; omega)

theorem paintZero_before (xs : List Nat) (start k j : Nat)
    (hj : j < start) (hlen : j < xs.length) :
    (paintZero xs start k)[j]'(by rw [paintZero_length]; exact hlen) = xs[j] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hne : start + k ≠ j := Nat.ne_of_gt (Nat.lt_of_lt_of_le hj (Nat.le_add_right _ _))
    simp [paintZero, List.getElem_set, hne, ih]

theorem paintZero_hi (xs : List Nat) (start k j : Nat)
    (hk : start + k ≤ j) (hj : j < xs.length) :
    (paintZero xs start k)[j]'(by rw [paintZero_length]; exact hj) = xs[j] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hne : start + k ≠ j := by omega
    simp [paintZero, List.getElem_set, hne, ih (by omega)]

theorem paintZero_lo (xs : List Nat) (start k j : Nat)
    (hj : j < k) (hk : start + k ≤ xs.length) :
    (paintZero xs start k)[start + j]'(by
      rw [paintZero_length]
      exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj start) hk) = 0 := by
  induction k generalizing j with
  | zero => omega
  | succ k ih =>
    simp only [paintZero]
    by_cases hlast : j = k
    · subst hlast
      simp [List.getElem_set]
    · have hne : start + k ≠ start + j := by omega
      simp [List.getElem_set, hne]
      exact ih j (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hj) hlast) (Nat.le_of_succ_le hk)

theorem paintOnes_before (xs : List Nat) (start k j : Nat)
    (hj : j < start) (hlen : j < xs.length) :
    (paintOnes xs start k)[j]'(by rw [paintOnes_length]; exact hlen) = xs[j] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hne : start + k ≠ j := Nat.ne_of_gt (Nat.lt_of_lt_of_le hj (Nat.le_add_right _ _))
    simp [paintOnes, List.getElem_set, hne, ih]

/-- The cell `afterPark` leaves. The hole write wins, then the park write,
    then the restored source. -/
theorem afterPark_cell (row : List Nat) (fromHole : Int) (park hole colour j : Nat)
    (hp : park < row.length) (_hh : hole < row.length) (hne : hole ≠ park)
    (hfrom : fromHole < 0 ∨ fromHole.toNat < row.length)
    (hfromNe : 0 ≤ fromHole → fromHole.toNat ≠ hole)
    (hfromPark : 0 ≤ fromHole → fromHole.toNat ≠ park)
    (hj : j < row.length) :
    (afterPark row fromHole park hole colour)[j]'(by rw [afterPark_length]; exact hj) =
      if j = hole then 0
      else if j = park then colour
      else if _hF : 0 ≤ fromHole then
        if j = fromHole.toNat then row[park]'hp
        else row[j]
      else row[j] := by
  unfold afterPark
  by_cases hneg : fromHole < 0
  · have hF : ¬ 0 ≤ fromHole := by omega
    simp only [hneg, ite_true]
    by_cases hjh : j = hole
    · simp [hjh, List.getElem_set, hne, hne.symm]
    · by_cases hjp : j = park
      · subst hjp
        simp [List.getElem_set, hne, hne.symm, hF, hjh]
      · have hneH : hole ≠ j := fun h => hjh h.symm
        have hnePk : park ≠ j := fun h => hjp h.symm
        simp [List.getElem_set, hneH, hnePk, hF]
        rw [if_neg hjh, if_neg hjp]
  · have hF : 0 ≤ fromHole := by omega
    have hsrc : fromHole.toNat < row.length := by
      cases hfrom with
      | inl h => exact absurd h hneg
      | inr h => exact h
    have hneS : fromHole.toNat ≠ hole := hfromNe hF
    have hneP : fromHole.toNat ≠ park := hfromPark hF
    simp only [hneg, ite_false]
    have hget : row.getD park 0 = row[park]'hp := by simp [List.getD, hp]
    by_cases hjh : j = hole
    · simp [hjh, List.getElem_set, hne, hne.symm, hneS]
    · by_cases hjp : j = park
      · subst hjp
        simp [List.getElem_set, hne, hne.symm, hneP, hget, hF, hjh]
      · by_cases hjs : j = fromHole.toNat
        · have hneH : hole ≠ fromHole.toNat := hneS.symm
          simp [List.getElem_set, hjs, hneH, hneP, hget, hF, hjh, hneS]
          rw [if_neg (fun h => hneP h.symm)]
          simpa [List.getD, hp] using hget
        · have h1 : hole ≠ j := fun h => hjh h.symm
          have h2 : park ≠ j := fun h => hjp h.symm
          have h3 : fromHole.toNat ≠ j := fun h => hjs h.symm
          simp [List.getElem_set, hF, hjh, hjp, hjs, h1, h2, h3]

theorem rowHome_length (row painted : List Nat) (parkAt : Nat) (fromHole : Int) (t0 : Nat)
    (h : RowHome row painted parkAt fromHole t0) :
    row.length = painted.length := h.len

/-- Parking `hole` preserves the agreement. `colour` is that hole's painted peg. -/
theorem rowHome_park (row painted : List Nat) (parkAt hole colour : Nat)
    (fromHole : Int) (t0 : Nat)
    (h : RowHome row painted parkAt fromHole t0)
    (hpark : parkAt < t0) (hne : hole ≠ parkAt)
    (hfromNe : 0 ≤ fromHole → fromHole.toNat ≠ hole)
    (hfromPark : 0 ≤ fromHole → fromHole.toNat ≠ parkAt)
    (hholeP : hole < painted.length)
    (hcol : colour = painted[hole]'hholeP) :
    RowHome (afterPark row fromHole parkAt hole colour) painted parkAt (hole : Int) t0 := by
  have hhlen : hole < painted.length := hholeP
  have hcol' : colour = painted[hole]'hhlen := hcol
  refine
    { len := by rw [afterPark_length, h.len]
      parkLt := h.parkLt
      fromLt := fun _ => hhlen
      below := ?_ }
  intro j hj hr
  have hrow : j < row.length := by rw [afterPark_length] at hr; exact hr
  have hfrom : fromHole < 0 ∨ fromHole.toNat < row.length := by
    by_cases hF : 0 ≤ fromHole
    · exact Or.inr (by rw [h.len]; exact h.fromLt hF)
    · exact Or.inl (by omega)
  have hcell := afterPark_cell row fromHole parkAt hole colour j
    (by rw [h.len]; exact h.parkLt) (by rw [h.len]; exact hhlen) hne hfrom hfromNe hfromPark hrow
  rw [hcell]
  have hold := h.below j hj hrow
  have hpos : 0 ≤ (hole : Int) := Int.ofNat_nonneg hole
  have hto : (hole : Int).toNat = hole := rfl
  by_cases hjh : j = hole
  · simp [hjh, hpos, hto]
  · by_cases hjp : j = parkAt
    · simp [hjh, hjp, hpos, hto, hcol']
    · by_cases hF : 0 ≤ fromHole
      · by_cases hjs : j = fromHole.toNat
        · have hneS : fromHole.toNat ≠ hole := hfromNe hF
          have hneP : fromHole.toNat ≠ parkAt := hfromPark hF
          have hneP' : parkAt ≠ fromHole.toNat := fun h => hneP h.symm
          simp [hjh, hjp, hF, hjs, hpos, hto, hneS, hneP, hneP', hcol']
          have hparkCell := h.below parkAt hpark (by rw [h.len]; exact h.parkLt)
          simp [hF, hneP'] at hparkCell
          exact hparkCell
        · simp [hjh, hjp, hF, hjs, hpos, hto, hold]
      · simp [hjh, hjp, hF, hpos, hto, hold]

/-- Tally writes sit at the origin and after it, so the parked agreement stays. -/
theorem afterTally_before (row : List Nat) (t0 tally colour j : Nat) (last : Bool)
    (hj0 : j < t0) (hj : j < row.length) :
    (afterTally row t0 tally colour last)[j]'(by rw [afterTally_length]; exact hj) = row[j] := by
  unfold afterTally
  have hred := paintRed_get_before row t0 tally j hj0 hj
  have hlenR : j < (paintRed row t0 tally).length := by rw [paintRed_length]; exact hj
  have h1 := paintOnes_before (paintRed row t0 tally) t0 tally j hj0 hlenR
  have hlen1 : j < (paintOnes (paintRed row t0 tally) t0 tally).length := by
    rw [paintOnes_length, paintRed_length]; exact hj
  have hpre1 : j < t0 + tally := by omega
  have h2 := paintOnes_before (paintOnes (paintRed row t0 tally) t0 tally)
    (t0 + tally) tally j hpre1 hlen1
  by_cases hL : last
  · simp [hL, hred]
  · by_cases hR : colour = 2
    · have hne : t0 + 2 * tally ≠ j := by omega
      simp [hL, hR, List.getElem_set, hne, h2]
      exact h1.trans hred
    · simp [hL, hR, h2]
      exact h1.trans hred

theorem rowHome_tally (row painted : List Nat) (parkAt : Nat) (fromHole : Int)
    (t0 tally colour : Nat) (last : Bool)
    (h : RowHome row painted parkAt fromHole t0) :
    RowHome (afterTally row t0 tally colour last) painted parkAt fromHole t0 := by
  refine
    { len := by rw [afterTally_length, h.len]
      parkLt := h.parkLt
      fromLt := h.fromLt
      below := ?_ }
  intro j hj hr
  have hrow : j < row.length := by rw [afterTally_length] at hr; exact hr
  rw [afterTally_before row t0 tally colour j last hj hrow]
  exact h.below j hj hrow

/-- A rung: park, then the tally. The agreement below the origin stays,
    now parked at `hole`. -/
theorem rowHome_rung (row painted : List Nat) (parkAt hole colour : Nat)
    (fromHole : Int) (t0 tally : Nat) (last : Bool)
    (h : RowHome row painted parkAt fromHole t0)
    (hpark : parkAt < t0) (hne : hole ≠ parkAt)
    (hfromNe : 0 ≤ fromHole → fromHole.toNat ≠ hole)
    (hfromPark : 0 ≤ fromHole → fromHole.toNat ≠ parkAt)
    (hholeP : hole < painted.length)
    (hcol : colour = painted[hole]'hholeP) :
    RowHome (rungRow row fromHole parkAt hole t0 tally colour last)
      painted parkAt (hole : Int) t0 := by
  unfold rungRow
  exact rowHome_tally _ _ _ _ _ _ _ _
    (rowHome_park row painted parkAt hole colour fromHole t0 h hpark hne
      hfromNe hfromPark hholeP hcol)

/-- Puts the parked colour back and clears the park hole. -/
def unparkList (row : List Nat) (fromHole : Int) (park : Nat) : List Nat :=
  if fromHole < 0 then row
  else (row.set fromHole.toNat (row.getD park 0)).set park 0

theorem unparkList_length (row : List Nat) (fromHole : Int) (park : Nat) :
    (unparkList row fromHole park).length = row.length := by
  unfold unparkList
  by_cases h : fromHole < 0
  · simp [h]
  · simp [h, List.length_set]

theorem rowHome_unpark (row painted : List Nat) (parkAt : Nat) (fromHole : Int) (t0 : Nat)
    (h : RowHome row painted parkAt fromHole t0)
    (hpark : parkAt < t0)
    (hfrom : 0 ≤ fromHole → fromHole.toNat < t0)
    (hfromPark : 0 ≤ fromHole → fromHole.toNat ≠ parkAt)
    (hpark0 : painted[parkAt]'h.parkLt = 0) :
    RowHome (unparkList row fromHole parkAt) painted parkAt (-1) t0 := by
  refine
    { len := by rw [unparkList_length, h.len]
      parkLt := h.parkLt
      fromLt := fun hle => absurd hle (by decide)
      below := ?_ }
  intro j hj hr
  have hrow : j < row.length := by rw [unparkList_length] at hr; exact hr
  unfold unparkList
  by_cases hneg : fromHole < 0
  · simp only [hneg, ite_true]
    have hold := h.below j hj hrow
    have hF : ¬ 0 ≤ fromHole := by omega
    simpa [hF] using hold
  · have hF : 0 ≤ fromHole := by omega
    have hsrc : fromHole.toNat < row.length := by rw [h.len]; exact h.fromLt hF
    have hsrcT : fromHole.toNat < t0 := hfrom hF
    simp only [hneg, ite_false]
    have hget : row.getD parkAt 0 = row[parkAt]'(by rw [h.len]; exact h.parkLt) := by
      simp [List.getD, show parkAt < row.length by rw [h.len]; exact h.parkLt]
    by_cases hjs : j = fromHole.toNat
    · have hneP : fromHole.toNat ≠ parkAt := hfromPark hF
      have hneP' : parkAt ≠ fromHole.toNat := fun h => hneP h.symm
      simp [hjs, List.getElem_set, hneP, hneP', hget]
      have hold := h.below parkAt hpark (by rw [h.len]; exact h.parkLt)
      have hold' : row[parkAt]'(by rw [h.len]; exact h.parkLt) =
          painted[fromHole.toNat]'(h.fromLt hF) := by
        simpa [hF, hneP'] using hold
      have hp' : parkAt < row.length := by rw [h.len]; exact h.parkLt
      simp [List.getElem?_eq_getElem, hp', hget]
      exact hold'
    · by_cases hjp : j = parkAt
      · simp [hjs, hjp, List.getElem_set, hpark0]
      · have hneS : fromHole.toNat ≠ j := fun h => hjs h.symm
        have hnePk : parkAt ≠ j := fun h => hjp h.symm
        simp [List.getElem_set, hneS, hnePk]
        have hold := h.below j hj hrow
        simp [hF, hjs, hjp] at hold
        exact hold

/-- Unpark, then empty the tally. Holes at and after the origin are blank on
    the painted row, and holes at and after the final tally are already blank,
    so the result is that painted row. -/
theorem rowHome_clear (row painted : List Nat) (parkAt : Nat) (fromHole : Int)
    (t0 m : Nat)
    (h : RowHome row painted parkAt fromHole t0)
    (hpark : parkAt < t0)
    (hfrom : 0 ≤ fromHole → fromHole.toNat < t0)
    (hfromPark : 0 ≤ fromHole → fromHole.toNat ≠ parkAt)
    (hpark0 : painted[parkAt]'h.parkLt = 0)
    (hzero : ∀ j (_hj : t0 ≤ j) (hp : j < painted.length), painted[j]'hp = 0)
    (hpast : ∀ j (_hj : t0 + m ≤ j) (hr : j < row.length), row[j]'hr = 0)
    (hroom : t0 + m ≤ row.length) :
    paintZero (unparkList row fromHole parkAt) t0 m = painted := by
  have hun := rowHome_unpark row painted parkAt fromHole t0 h hpark hfrom hfromPark hpark0
  apply List.ext_get
  · rw [paintZero_length, unparkList_length, h.len]
  · intro j hj1 hj2
    rw [List.get_eq_getElem, List.get_eq_getElem]
    have hju : j < (unparkList row fromHole parkAt).length := by
      rw [paintZero_length] at hj1
      exact hj1
    by_cases hlo : j < t0
    · rw [paintZero_before (unparkList row fromHole parkAt) t0 m j hlo hju]
      have hbelow := hun.below j hlo hju
      simpa using hbelow
    · have hge : t0 ≤ j := by omega
      have hp : j < painted.length := hj2
      rw [hzero j hge hp]
      by_cases hin : j < t0 + m
      · have hoff : j - t0 < m := by omega
        have hidx : t0 + (j - t0) = j := by omega
        have hget := paintZero_lo (unparkList row fromHole parkAt) t0 m (j - t0) hoff
          (by rw [unparkList_length]; exact hroom)
        simpa [hidx] using hget
      · have hge2 : t0 + m ≤ j := by omega
        rw [paintZero_hi _ _ _ _ hge2 hju]
        have hrow : j < row.length := by rw [unparkList_length] at hju; exact hju
        have hz := hpast j hge2 hrow
        unfold unparkList
        by_cases hneg : fromHole < 0
        · simpa [hneg] using hz
        · have hF : 0 ≤ fromHole := by omega
          have hsrc : fromHole.toNat < t0 := hfrom hF
          have hneS : fromHole.toNat ≠ j := by omega
          have hneP : parkAt ≠ j := by omega
          simp [hneg, List.getElem_set, hneS, hneP, hz]

end EcbsLink2.Link2
