/-
  The board `invert` starts from: `new_board`, `put` into home `bottom`, the
  `op_inv` bump, `copy_band` into the gap, and `tally_start`. That board is the
  climb entry (`onBench = false`, tally length 1).
-/
import EcbsLink2.Link2.AfterClimb

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

theorem rowGet_idx {α : Type} {xs : List α} {i j : Nat} (h : i = j) (hi : i < xs.length) :
    xs[i] = xs[j]'(h ▸ hi) := by
  subst h
  rfl

theorem list_get_eq {xs ys : List Nat} (h : xs = ys) (i : Nat) (hi : i < xs.length) :
    xs[i] = ys[i]'(h ▸ hi) := by
  subst h
  rfl

theorem paintRow_cons (row : List Nat) (i c : Nat) (cs : List Nat) :
    paint row i (c :: cs) = paint (row.set i c) (i + 1) cs := rfl

theorem paintRow_length (row : List Nat) (i : Nat) (cols : List Nat) :
    (paint row i cols).length = row.length := by
  induction cols generalizing row i with
  | nil => rfl
  | cons c cs ih => simp only [paintRow_cons, ih, List.length_set]

theorem paintRow_lo (row : List Nat) (i : Nat) (cols : List Nat) (j : Nat)
    (hj : j < i) (hj' : j < row.length) :
    (paint row i cols)[j]'(by rw [paintRow_length]; exact hj') = row[j] := by
  induction cols generalizing row i with
  | nil => rfl
  | cons c cs ih =>
    simp only [paintRow_cons]
    have hne : i ≠ j := by omega
    have hj1 : j < i + 1 := by omega
    have hj2 : j < (row.set i c).length := by rw [List.length_set]; exact hj'
    rw [ih _ _ hj1 hj2, List.getElem_set, if_neg hne]

theorem paintRow_hi (row : List Nat) (i : Nat) (cols : List Nat) (j : Nat)
    (hj : i + cols.length ≤ j) (hj' : j < row.length) :
    (paint row i cols)[j]'(by rw [paintRow_length]; exact hj') = row[j] := by
  induction cols generalizing row i with
  | nil => rfl
  | cons c cs ih =>
    simp only [paintRow_cons]
    have hj1 : i + 1 + cs.length ≤ j := by
      simp [List.length_cons] at hj
      omega
    have hne : i ≠ j := by omega
    have hj2 : j < (row.set i c).length := by rw [List.length_set]; exact hj'
    rw [ih _ _ hj1 hj2, List.getElem_set, if_neg hne]

theorem paintRow_at (row : List Nat) (start : Nat) (cols : List Nat)
    (h : start + cols.length ≤ row.length) (k : Nat) (hk : k < cols.length) :
    (paint row start cols)[start + k]'(by rw [paintRow_length]; omega) = cols[k] := by
  induction cols generalizing row start k with
  | nil => cases hk
  | cons c cs ih =>
    simp only [paintRow_cons]
    by_cases hk0 : k = 0
    · subst hk0
      simp only [Nat.add_zero]
      have hlen : start < (row.set start c).length := by rw [List.length_set]; omega
      rw [paintRow_lo (row.set start c) (start + 1) cs start (by omega) hlen,
        List.getElem_set_self]
      simp
    · have hlenCs : (c :: cs).length = cs.length + 1 := by simp
      have hk' : k - 1 < cs.length := by omega
      have hrest : start + 1 + cs.length ≤ (row.set start c).length := by
        rw [List.length_set]
        omega
      have ih' := ih (row.set start c) (start + 1) hrest (k - 1) hk'
      have hcons : (c :: cs)[(k - 1) + 1]'(by omega) = cs[k - 1] := by
        simp [List.getElem_cons_succ]
      have hget : (c :: cs)[k]'(by omega) = cs[k - 1] := by
        have hidx : (k - 1) + 1 = k := by omega
        exact (rowGet_idx hidx (by omega)).symm.trans hcons
      have hpi : start + 1 + (k - 1) <
          (paint (row.set start c) (start + 1) cs).length := by
        rw [paintRow_length, List.length_set]; omega
      have hidx : start + 1 + (k - 1) = start + k := by omega
      rw [← rowGet_idx hidx hpi, ih', hget]

theorem prefixes_le (tally room : Nat) (rs : List Nat)
    (h : tallyPrefixesLe tally room rs = true) : tally ≤ room := by
  cases rs with
  | nil => simpa [tallyPrefixesLe] using h
  | cons r rs =>
    have h' : tally ≤ room ∧ tallyPrefixesLe (tallyAfter tally r rs.isEmpty) room rs = true := by
      simpa [tallyPrefixesLe] using h
    exact h'.1

theorem tallyPrefixesLe_final (tally room : Nat) (rs : List Nat)
    (h : tallyPrefixesLe tally room rs = true) : climbTally tally rs ≤ room := by
  induction rs generalizing tally with
  | nil => simpa [climbTally, tallyPrefixesLe] using h
  | cons r rs ih =>
    have h' : tally ≤ room ∧
        tallyPrefixesLe (tallyAfter tally r rs.isEmpty) room rs = true := by
      simpa [tallyPrefixesLe] using h
    exact ih _ h'.2

theorem rungColour_ne (c : Nat) : rungColour c ≠ 0 := by
  unfold rungColour
  by_cases h : c % 2 = 1 <;> simp [h]

theorem rung_ne_zero (c k : Nat) (hk : k < (rungList c).length) :
    (rungList c)[k] ≠ 0 := by
  induction c using Nat.strongRecOn generalizing k with
  | ind c ih =>
    by_cases hc : c ≤ 1
    · rw [rungList_le hc] at hk
      cases hk
    · have hgt : 1 < c := by omega
      have hrs := rungList_gt hgt
      have hget := list_get_eq hrs k hk
      rw [hget]
      cases k with
      | zero =>
        simp [rungColour_ne]
      | succ k =>
        have hk' : k < (rungList (c / 2)).length := by
          have hlen : (rungList c).length = (rungList (c / 2)).length + 1 := by
            simp [hrs, List.length_cons]
          omega
        have htail : (rungColour c :: rungList (c / 2))[k + 1]'(hrs ▸ hk) =
            (rungList (c / 2))[k] := by
          simp [List.getElem_cons_succ]
        rw [htail]
        exact ih (c / 2) (Nat.div_lt_self (by omega) (by decide)) k hk'

theorem built_held_blank (t : Spec.Tier) :
    (builtBoard t).sudo_5Board_4held = Array.mkArray 8 false := by
  simp [builtBoard, midBoard, placed, blankOf]
  apply Array.ext
  · simp [Array.size_set, Array.size_mkArray]
  · intro i h1 h2
    simp [Array.getElem_set, Array.getElem_mkArray]

theorem built_home_blank (t : Spec.Tier) :
    (builtBoard t).sudo_5Board_4home = Array.mkArray 8 (#[] : Array Int) := by
  simp [builtBoard, midBoard, placed, blankOf]
  apply Array.ext
  · simp [Array.size_set, Array.size_mkArray]
  · intro i h1 h2
    rw [Array.getElem_set]
    split
    · simp [Array.getElem_mkArray]
    · next hne =>
      rw [Array.getElem_set]
      split
      · next heq => exact absurd heq hne
      · simp [Array.getElem_mkArray]

theorem built_ops_blank (t : Spec.Tier) :
    (builtBoard t).sudo_5Board_4cost.sudo_5Costs_3ops = Array.mkArray 5 0 := by
  simp [builtBoard, midBoard, placed, blankOf]

theorem built_moves0 (t : Spec.Tier) :
    (builtBoard t).sudo_5Board_4cost.sudo_5Costs_5moves = 0 := by
  simp [builtBoard, midBoard, placed, blankOf]

theorem built_peak1 (t : Spec.Tier) :
    (builtBoard t).sudo_5Board_4cost.sudo_5Costs_4peak = 1 := by
  simp [builtBoard, midBoard, placed, blankOf]

theorem built_tier (t : Spec.Tier) :
    (builtBoard t).sudo_5Board_1t = embTier t := by
  simp [builtBoard, midBoard, placed, blankOf]

theorem home2_lt (t : Spec.Tier) : 2 < (builtBoard t).sudo_5Board_4home.size := by
  rw [built_home_blank]; simp [Array.size_mkArray]

theorem held2_lt (t : Spec.Tier) : 2 < (builtBoard t).sudo_5Board_4held.size := by
  rw [built_held_blank]; simp [Array.size_mkArray]

theorem held7_le (t : Spec.Tier) : 7 ≤ (builtBoard t).sudo_5Board_4held.size := by
  rw [built_held_blank]; simp [Array.size_mkArray]

theorem held2_empty (t : Spec.Tier) :
    (builtBoard t).sudo_5Board_4held[2]'(held2_lt t) = false := by
  have hb : 2 < (Array.mkArray 8 false).size := by simp [Array.size_mkArray]
  exact cell_eq_of (built_held_blank t) (hb := hb) (by simp [Array.getElem_mkArray])

theorem countHeld_bottom :
    countHeld ((Array.mkArray 8 false).set ⟨2, by simp [Array.size_mkArray]⟩ true) 7 = 1 := by
  decide

theorem countHeld_gap :
    countHeld (((Array.mkArray 8 false).set ⟨2, by simp [Array.size_mkArray]⟩ true).set
      ⟨5, by simp [Array.size_set, Array.size_mkArray]⟩ true) 7 = 2 := by
  decide

/-- `put` of the input into home `bottom` on a fresh board. Peak stays 1. -/
theorem put_bottom (t : Spec.Tier) (h : BoardOk t) (xs : List Nat)
    (hx : xs.length = t.n) :
    Ecbs.put (builtBoard t) Ecbs.bottom (embed xs) =
      .ok (placeBoard (builtBoard t) 2 (home2_lt t) (held2_lt t) xs 0 1) := by
  have hfn : FitsLen t.n := FitsLen.of_le (fits_of h.fits_n) (by omega)
  have hpeg : FitsLen (0 + pegCount xs) := by
    apply FitsLen.of_le hfn
    have hle := pegCount_le xs
    rw [hx] at hle
    omega
  rw [show Ecbs.bottom = ((2 : Nat) : Int) from rfl]
  exact put_refines (builtBoard t) 2 xs 0 1 (home2_lt t) (held2_lt t) (held7_le t)
    (held2_empty t)
    (by rw [built_tier]; simp [embTier, hx, ofNat_eq_natCast])
    (by rw [hx]; exact hfn)
    (by rw [built_moves0]; rfl)
    (by rw [built_peak1]; rfl)
    hpeg

theorem place_bottom_eq (t : Spec.Tier) (xs : List Nat) :
    placeBoard (builtBoard t) 2 (home2_lt t) (held2_lt t) xs 0 1 =
      { builtBoard t with
        sudo_5Board_4home :=
          (builtBoard t).sudo_5Board_4home.set ⟨2, home2_lt t⟩ (embed xs)
        sudo_5Board_4held :=
          (builtBoard t).sudo_5Board_4held.set ⟨2, held2_lt t⟩ true
        sudo_5Board_4cost := { (builtBoard t).sudo_5Board_4cost with
          sudo_5Costs_5moves := Int.ofNat (pegCount xs) } } := by
  unfold placeBoard
  dsimp only
  have hocc : countHeld
      ((builtBoard t).sudo_5Board_4held.set ⟨2, held2_lt t⟩ true) 7 = 1 := by
    have hs := Array.set_congr_arr (built_held_blank t) (held2_lt t) true
    have hfin :
        (⟨2, built_held_blank t ▸ held2_lt t⟩ : Fin (Array.mkArray 8 false).size) =
          ⟨2, by simp [Array.size_mkArray]⟩ := Fin.ext rfl
    rw [hs, hfin, countHeld_bottom]
  rw [hocc]
  simp [Nat.zero_add, show ¬ ((1 : Nat) < 1) from by decide]

/-- The fresh board with the input in home `bottom`. -/
def bottomBoard (t : Spec.Tier) (xs : List Nat) : Ecbs.Board :=
  { builtBoard t with
    sudo_5Board_4home :=
      (builtBoard t).sudo_5Board_4home.set ⟨2, home2_lt t⟩ (embed xs)
    sudo_5Board_4held :=
      (builtBoard t).sudo_5Board_4held.set ⟨2, held2_lt t⟩ true
    sudo_5Board_4cost := { (builtBoard t).sudo_5Board_4cost with
      sudo_5Costs_5moves := Int.ofNat (pegCount xs) } }

theorem put_bottom_board (t : Spec.Tier) (h : BoardOk t) (xs : List Nat)
    (hx : xs.length = t.n) :
    Ecbs.put (builtBoard t) Ecbs.bottom (embed xs) = .ok (bottomBoard t xs) := by
  rw [put_bottom t h xs hx, place_bottom_eq]
  rfl

theorem bottom_ops (t : Spec.Tier) (xs : List Nat) :
    (bottomBoard t xs).sudo_5Board_4cost.sudo_5Costs_3ops = Array.mkArray 5 0 := by
  simp [bottomBoard, built_ops_blank]

theorem bottom_ops2 (t : Spec.Tier) (xs : List Nat) :
    2 < (bottomBoard t xs).sudo_5Board_4cost.sudo_5Costs_3ops.size := by
  rw [bottom_ops]; simp [Array.size_mkArray]

theorem bottom_ops_zero (t : Spec.Tier) (xs : List Nat) :
    (bottomBoard t xs).sudo_5Board_4cost.sudo_5Costs_3ops[2]'(bottom_ops2 t xs) =
      Int.ofNat 0 := by
  have hb : 2 < (Array.mkArray 5 0).size := by simp [Array.size_mkArray]
  exact cell_eq_of (bottom_ops t xs) (hb := hb)
    (by simp [Array.getElem_mkArray, ofNat_eq_natCast])

/-- The `op_inv` cell, then whatever follows. -/
theorem bump_cont {β : Type} (b : Ecbs.Board) (c : Nat)
    (hops : 2 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_3ops[2] = Int.ofNat c)
    (hfit : FitsLen (c + 1))
    (k : Ecbs.Board → Except SudoRt.Trap β) :
    (SudoRt.atL b.sudo_5Board_4cost.sudo_5Costs_3ops Ecbs.op_inv >>= fun t1 =>
      SudoRt.addI t1 (1 : Int) >>= fun t2 =>
      SudoRt.putL b.sudo_5Board_4cost.sudo_5Costs_3ops Ecbs.op_inv t2 >>= fun t3 =>
      k { b with sudo_5Board_4cost :=
        { b.sudo_5Board_4cost with sudo_5Costs_3ops := t3 } }) =
      k (bumpOp b 2 c hops) := by
  have hop : Ecbs.op_inv = Int.ofNat 2 := rfl
  rw [hop, atL_ofNat _ 2 hops, hc, ok_bind, addI_ofNat_one c hfit, ok_bind,
    putL_ofNat _ 2 (Int.ofNat (c + 1)) hops, ok_bind]
  rfl

theorem bottom_home5 (t : Spec.Tier) (xs : List Nat) :
    5 < (bottomBoard t xs).sudo_5Board_4home.size := by
  simp [bottomBoard, Array.size_set]
  rw [built_home_blank]
  simp [Array.size_mkArray]

theorem bottom_held5 (t : Spec.Tier) (xs : List Nat) :
    5 < (bottomBoard t xs).sudo_5Board_4held.size := by
  simp [bottomBoard, Array.size_set]
  rw [built_held_blank]
  simp [Array.size_mkArray]

theorem bottom_held2 (t : Spec.Tier) (xs : List Nat) :
    2 < (bottomBoard t xs).sudo_5Board_4held.size := by
  simp [bottomBoard, Array.size_set]
  rw [built_held_blank]
  simp [Array.size_mkArray]

theorem bottom_home2 (t : Spec.Tier) (xs : List Nat) :
    2 < (bottomBoard t xs).sudo_5Board_4home.size := by
  simp [bottomBoard, Array.size_set]
  rw [built_home_blank]
  simp [Array.size_mkArray]

theorem bottom_held7 (t : Spec.Tier) (xs : List Nat) :
    7 ≤ (bottomBoard t xs).sudo_5Board_4held.size := by
  simp [bottomBoard, Array.size_set]
  rw [built_held_blank]
  decide

theorem bottom_src_held (t : Spec.Tier) (xs : List Nat) :
    (bottomBoard t xs).sudo_5Board_4held[2]'(bottom_held2 t xs) = true := by
  have hsz : 2 < ((builtBoard t).sudo_5Board_4held.set ⟨2, held2_lt t⟩ true).size := by
    rw [Array.size_set]; exact held2_lt t
  have hget := Array.getElem_set_eq (builtBoard t).sudo_5Board_4held ⟨2, held2_lt t⟩ true
    rfl hsz
  have hfin : (⟨2, bottom_held2 t xs⟩ : Fin (bottomBoard t xs).sudo_5Board_4held.size) =
      ⟨2, hsz⟩ := by
    simp [bottomBoard, Fin.ext_iff]
  simp [bottomBoard, hfin, hget]

theorem bottom_src_arr (t : Spec.Tier) (xs : List Nat) :
    (bottomBoard t xs).sudo_5Board_4home[2]'(bottom_home2 t xs) = embed xs := by
  have hsz : 2 < ((builtBoard t).sudo_5Board_4home.set ⟨2, home2_lt t⟩ (embed xs)).size := by
    rw [Array.size_set]; exact home2_lt t
  have hget := Array.getElem_set_eq (builtBoard t).sudo_5Board_4home ⟨2, home2_lt t⟩ (embed xs)
    rfl hsz
  have hfin : (⟨2, bottom_home2 t xs⟩ : Fin (bottomBoard t xs).sudo_5Board_4home.size) =
      ⟨2, hsz⟩ := by
    simp [bottomBoard, Fin.ext_iff]
  simp [bottomBoard, hfin, hget]

theorem bottom_dst_empty (t : Spec.Tier) (xs : List Nat) :
    (bottomBoard t xs).sudo_5Board_4held[5]'(bottom_held5 t xs) = false := by
  have hne : (2 : Nat) ≠ 5 := by decide
  have hset : 5 < ((builtBoard t).sudo_5Board_4held.set ⟨2, held2_lt t⟩ true).size := by
    rw [Array.size_set, built_held_blank]; simp [Array.size_mkArray]
  have hget := Array.getElem_set_ne (builtBoard t).sudo_5Board_4held ⟨2, held2_lt t⟩ true
    hset hne
  have hb : 5 < (Array.mkArray 8 false).size := by simp [Array.size_mkArray]
  have hblank : (builtBoard t).sudo_5Board_4held[5]'(Array.size_set _ _ _ ▸ hset) = false :=
    cell_eq_of (built_held_blank t) (hb := hb) (by simp [Array.getElem_mkArray])
  have hfin : (⟨5, bottom_held5 t xs⟩ : Fin (bottomBoard t xs).sudo_5Board_4held.size) =
      ⟨5, hset⟩ := Fin.ext rfl
  simp [bottomBoard, hfin, hget, hblank]

theorem bottom_moves (t : Spec.Tier) (xs : List Nat) :
    (bottomBoard t xs).sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat (pegCount xs) := by
  simp [bottomBoard]

theorem bottom_peak (t : Spec.Tier) (xs : List Nat) :
    (bottomBoard t xs).sudo_5Board_4cost.sudo_5Costs_4peak = 1 := by
  simp [bottomBoard, built_peak1]

theorem bottom_n (t : Spec.Tier) (xs : List Nat) :
    (bottomBoard t xs).sudo_5Board_1t.sudo_4Tier_1n = Int.ofNat t.n := by
  simp [bottomBoard, built_tier, embTier]

/-- `op_inv` bumped on the board that holds the input. -/
def bumpedBoard (t : Spec.Tier) (xs : List Nat) : Ecbs.Board :=
  bumpOp (bottomBoard t xs) 2 0 (bottom_ops2 t xs)

theorem bump_bottom (t : Spec.Tier) (xs : List Nat) :
    (do
      let ix := Ecbs.op_inv
      let t1 ← SudoRt.atL (bottomBoard t xs).sudo_5Board_4cost.sudo_5Costs_3ops ix
      let t2 ← SudoRt.addI t1 (1 : Int)
      let t3 ← SudoRt.putL (bottomBoard t xs).sudo_5Board_4cost.sudo_5Costs_3ops ix t2
      pure ({ bottomBoard t xs with sudo_5Board_4cost :=
        { (bottomBoard t xs).sudo_5Board_4cost with sudo_5Costs_3ops := t3 } })) =
      .ok (bumpedBoard t xs) := by
  simpa [bumpedBoard] using
    bump_cont (bottomBoard t xs) 0 (bottom_ops2 t xs) (bottom_ops_zero t xs)
      (by unfold FitsLen i64MaxNat; decide) pure

theorem bumped_home5 (t : Spec.Tier) (xs : List Nat) :
    5 < (bumpedBoard t xs).sudo_5Board_4home.size := by
  simpa [bumpedBoard, bumpOp] using bottom_home5 t xs

theorem bumped_held5 (t : Spec.Tier) (xs : List Nat) :
    5 < (bumpedBoard t xs).sudo_5Board_4held.size := by
  simpa [bumpedBoard, bumpOp] using bottom_held5 t xs

theorem bumped_held2 (t : Spec.Tier) (xs : List Nat) :
    2 < (bumpedBoard t xs).sudo_5Board_4held.size := by
  simpa [bumpedBoard, bumpOp] using bottom_held2 t xs

theorem bumped_home2 (t : Spec.Tier) (xs : List Nat) :
    2 < (bumpedBoard t xs).sudo_5Board_4home.size := by
  simpa [bumpedBoard, bumpOp] using bottom_home2 t xs

theorem bumped_held7 (t : Spec.Tier) (xs : List Nat) :
    7 ≤ (bumpedBoard t xs).sudo_5Board_4held.size := by
  simpa [bumpedBoard, bumpOp] using bottom_held7 t xs

theorem bumped_src_held (t : Spec.Tier) (xs : List Nat) :
    (bumpedBoard t xs).sudo_5Board_4held[2]'(bumped_held2 t xs) = true := by
  exact cell_eq_of (by simp [bumpedBoard, bumpOp] : (bumpedBoard t xs).sudo_5Board_4held =
    (bottomBoard t xs).sudo_5Board_4held) (bottom_src_held t xs)

theorem bumped_src_arr (t : Spec.Tier) (xs : List Nat) :
    (bumpedBoard t xs).sudo_5Board_4home[2]'(bumped_home2 t xs) = embed xs := by
  exact cell_eq_of (by simp [bumpedBoard, bumpOp] : (bumpedBoard t xs).sudo_5Board_4home =
    (bottomBoard t xs).sudo_5Board_4home) (bottom_src_arr t xs)

theorem bumped_dst_empty (t : Spec.Tier) (xs : List Nat) :
    (bumpedBoard t xs).sudo_5Board_4held[5]'(bumped_held5 t xs) = false := by
  exact cell_eq_of (by simp [bumpedBoard, bumpOp] : (bumpedBoard t xs).sudo_5Board_4held =
    (bottomBoard t xs).sudo_5Board_4held) (bottom_dst_empty t xs)

theorem bumped_moves (t : Spec.Tier) (xs : List Nat) :
    (bumpedBoard t xs).sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat (pegCount xs) := by
  simp [bumpedBoard, bumpOp, bottom_moves]

theorem bumped_peak (t : Spec.Tier) (xs : List Nat) :
    (bumpedBoard t xs).sudo_5Board_4cost.sudo_5Costs_4peak = 1 := by
  simp [bumpedBoard, bumpOp, bottom_peak]

theorem bumped_n (t : Spec.Tier) (xs : List Nat) :
    (bumpedBoard t xs).sudo_5Board_1t.sudo_4Tier_1n = Int.ofNat t.n := by
  simp [bumpedBoard, bumpOp, bottom_n]

theorem gap_count (t : Spec.Tier) (xs : List Nat) :
    countHeld ((bumpedBoard t xs).sudo_5Board_4held.set ⟨5, bumped_held5 t xs⟩ true) 7 = 2 := by
  have hblank := built_held_blank t
  have hset2 := Array.set_congr_arr hblank (held2_lt t) true
  have hfin2 :
      (⟨2, hblank ▸ held2_lt t⟩ : Fin (Array.mkArray 8 false).size) =
        ⟨2, by simp [Array.size_mkArray]⟩ := Fin.ext rfl
  have hbot : (bottomBoard t xs).sudo_5Board_4held =
      (Array.mkArray 8 false).set ⟨2, by simp [Array.size_mkArray]⟩ true := by
    rw [show (bottomBoard t xs).sudo_5Board_4held =
      (builtBoard t).sudo_5Board_4held.set ⟨2, held2_lt t⟩ true from rfl, hset2, hfin2]
  have hbump : (bumpedBoard t xs).sudo_5Board_4held = (bottomBoard t xs).sudo_5Board_4held := by
    simp [bumpedBoard, bumpOp]
  have h5 := Array.set_congr_arr (hbump.trans hbot) (bumped_held5 t xs) true
  have hfin5 :
      (⟨5, (hbump.trans hbot) ▸ bumped_held5 t xs⟩ :
        Fin ((Array.mkArray 8 false).set ⟨2, by simp [Array.size_mkArray]⟩ true).size) =
        ⟨5, by simp [Array.size_set, Array.size_mkArray]⟩ := Fin.ext rfl
  rw [h5, hfin5, countHeld_gap]

/-- Copying the input into the gap raises the peak from 1 to 2. -/
theorem place_gap_eq (t : Spec.Tier) (xs : List Nat) :
    placeBoard (bumpedBoard t xs) 5 (bumped_home5 t xs) (bumped_held5 t xs)
        xs (pegCount xs) 1 =
      { { bumpedBoard t xs with
          sudo_5Board_4home := (bumpedBoard t xs).sudo_5Board_4home.set
            ⟨5, bumped_home5 t xs⟩ (embed xs)
          sudo_5Board_4held := (bumpedBoard t xs).sudo_5Board_4held.set
            ⟨5, bumped_held5 t xs⟩ true
          sudo_5Board_4cost := { (bumpedBoard t xs).sudo_5Board_4cost with
            sudo_5Costs_5moves := Int.ofNat (pegCount xs + pegCount xs) } } with
        sudo_5Board_4cost :=
          { { bumpedBoard t xs with
              sudo_5Board_4home := (bumpedBoard t xs).sudo_5Board_4home.set
                ⟨5, bumped_home5 t xs⟩ (embed xs)
              sudo_5Board_4held := (bumpedBoard t xs).sudo_5Board_4held.set
                ⟨5, bumped_held5 t xs⟩ true
              sudo_5Board_4cost := { (bumpedBoard t xs).sudo_5Board_4cost with
                sudo_5Costs_5moves := Int.ofNat (pegCount xs + pegCount xs) } }.sudo_5Board_4cost with
            sudo_5Costs_4peak := Int.ofNat 2 } } := by
  unfold placeBoard
  dsimp only
  rw [gap_count t xs]
  simp [show (1 : Nat) < 2 from by decide]

theorem copy_gap (t : Spec.Tier) (h : BoardOk t) (xs : List Nat) (hx : xs.length = t.n) :
    Ecbs.copy_band (bumpedBoard t xs) Ecbs.gap ((2 : Nat) : Int) false =
      .ok (placeBoard (bumpedBoard t xs) 5 (bumped_home5 t xs) (bumped_held5 t xs)
        xs (pegCount xs) 1) := by
  rw [show Ecbs.gap = ((5 : Nat) : Int) from rfl]
  have hfn : FitsLen (2 * t.n) := FitsLen.of_le (fits_of h.fits_n) (by omega)
  have hfit : FitsLen (pegCount xs + pegCount xs) := by
    apply FitsLen.of_le hfn
    have hle := pegCount_le xs
    rw [hx] at hle
    omega
  exact copy_band_refines (bumpedBoard t xs) 5 2 xs (pegCount xs) 1
    (bumped_home5 t xs) (bumped_held5 t xs) (bumped_home2 t xs) (bumped_held2 t xs)
    (bumped_held7 t xs) (bumped_src_held t xs) (bumped_src_arr t xs) (bumped_dst_empty t xs)
    (by rw [bumped_n, hx, ofNat_eq_natCast])
    (by rw [hx]; exact FitsLen.of_le (fits_of h.fits_n) (by omega))
    (bumped_moves t xs)
    (by rw [bumped_peak]; rfl)
    hfit

/-- The board after the input sits in the gap. Peak is 2, moves are twice the peg count. -/
def gapBoard (t : Spec.Tier) (xs : List Nat) : Ecbs.Board :=
  let b0 := bumpedBoard t xs
  let b1 : Ecbs.Board :=
    { b0 with
      sudo_5Board_4home := b0.sudo_5Board_4home.set ⟨5, bumped_home5 t xs⟩ (embed xs)
      sudo_5Board_4held := b0.sudo_5Board_4held.set ⟨5, bumped_held5 t xs⟩ true
      sudo_5Board_4cost := { b0.sudo_5Board_4cost with
        sudo_5Costs_5moves := Int.ofNat (pegCount xs + pegCount xs) } }
  { b1 with sudo_5Board_4cost := { b1.sudo_5Board_4cost with
      sudo_5Costs_4peak := Int.ofNat 2 } }

theorem copy_gap_board (t : Spec.Tier) (h : BoardOk t) (xs : List Nat)
    (hx : xs.length = t.n) :
    Ecbs.copy_band (bumpedBoard t xs) Ecbs.gap ((2 : Nat) : Int) false =
      .ok (gapBoard t xs) := by
  rw [copy_gap t h xs hx, place_gap_eq]
  rfl

theorem gap_len0 (t : Spec.Tier) (xs : List Nat) :
    (gapBoard t xs).sudo_5Board_9tally_len = 0 := by
  simp [gapBoard, bumpedBoard, bumpOp, bottomBoard, builtBoard, midBoard, placed, blankOf]

theorem gap_tally0 (t : Spec.Tier) (xs : List Nat) :
    (gapBoard t xs).sudo_5Board_6tally0 = Int.ofNat (tallyOrigin t) := by
  simp [gapBoard, bumpedBoard, bumpOp, bottomBoard, builtBoard, midBoard, placed, blankOf,
    tallyOrigin, tierR]
  omega

theorem gap_ctrl (t : Spec.Tier) (xs : List Nat) :
    (gapBoard t xs).sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (tierR t) := by
  simp [gapBoard, bumpedBoard, bumpOp, bottomBoard, builtBoard, midBoard, placed, blankOf, tierR]

theorem gap_high (t : Spec.Tier) (xs : List Nat) (hR : 0 < tierR t) :
    (gapBoard t xs).sudo_5Board_4cost.sudo_5Costs_15control_highest =
      Int.ofNat (t.script + 2 + tierR t - 1) := by
  have hne : rungList (t.n - 1) ≠ [] := by
    intro he
    have : (rungList (t.n - 1)).length = 0 := by simp [he]
    unfold tierR at hR
    omega
  simp [gapBoard, bumpedBoard, bumpOp, bottomBoard, builtBoard, midBoard, placed, blankOf,
    if_neg hne, tierR]

theorem gap_row (t : Spec.Tier) (xs : List Nat) :
    (gapBoard t xs).sudo_5Board_3row =
      embed (paint (List.replicate t.control 0) (t.script + 2) (rungList (t.n - 1))) := by
  simp [gapBoard, bumpedBoard, bumpOp, bottomBoard, builtBoard, midBoard, placed, blankOf]

theorem gap_control (t : Spec.Tier) (xs : List Nat) :
    (gapBoard t xs).sudo_5Board_1t.sudo_4Tier_7control = Int.ofNat t.control := by
  simp [gapBoard, bumpedBoard, bumpOp, bottomBoard, builtBoard, midBoard, placed, blankOf, embTier]

theorem gap_tmax (t : Spec.Tier) (xs : List Nat) :
    (gapBoard t xs).sudo_5Board_4cost.sudo_5Costs_9tally_max = 0 := by
  simp [gapBoard, bumpedBoard, bumpOp, bottomBoard, builtBoard, midBoard, placed, blankOf]

theorem origin_lt (t : Spec.Tier) (sat : TierSat t) : tallyOrigin t < t.control := by
  have h1 := prefixes_le 1 (rowRoom t) (tierClimb t) sat.prefixes
  exact Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right h1) sat.room_fit

theorem gap_row_lt (t : Spec.Tier) (xs : List Nat) (sat : TierSat t) :
    tallyOrigin t < (gapBoard t xs).sudo_5Board_3row.size := by
  rw [gap_row, size_embed, paintRow_length, List.length_replicate]
  exact origin_lt t sat

/-- One white peg at the tally origin. The recorded high was the last ladder hole. -/
theorem tally_gap (t : Spec.Tier) (h : BoardOk t) (xs : List Nat) (sat : TierSat t)
    (hR : 0 < tierR t) :
    Ecbs.tally_start (gapBoard t xs) =
      .ok { gapBoard t xs with
        sudo_5Board_3row := (gapBoard t xs).sudo_5Board_3row.set
          ⟨tallyOrigin t, gap_row_lt t xs sat⟩ (1 : Int)
        sudo_5Board_9tally_len := 1
        sudo_5Board_4cost := { (gapBoard t xs).sudo_5Board_4cost with
          sudo_5Costs_15control_highest := ((tallyOrigin t : Nat) : Int)
          sudo_5Costs_4ctrl := Int.ofNat (tierR t + 1)
          sudo_5Costs_9tally_max := 1 } } := by
  have hhigh : t.script + 2 + tierR t - 1 < tallyOrigin t := by
    unfold tallyOrigin
    omega
  have hfit0 : FitsLen (tallyOrigin t) := by
    apply FitsLen.of_le (fits_of h.fits_control)
    have := origin_lt t sat
    omega
  have hfitC : FitsLen (tierR t + 1) := by
    apply FitsLen.of_le (fits_of h.fits_control)
    have hL := h.ladder
    unfold tierR at *
    omega
  have hrun := tally_start_raise (gapBoard t xs) (tallyOrigin t)
      (t.script + 2 + tierR t - 1) t.control (tierR t) 0
    (gap_len0 t xs) (gap_tally0 t xs) (gap_row_lt t xs sat) (gap_control t xs)
    (origin_lt t sat)
    (by rw [gap_high t xs hR, ofNat_eq_natCast]) hhigh hfit0
    (by rw [gap_ctrl t xs, ofNat_eq_natCast]) hfitC
    (by rw [gap_tmax t xs]; rfl) (by decide)
  simpa [ofNat_eq_natCast] using hrun

/-- After the `op_inv` bump, `invert` copies home `bottom` into the gap and continues. -/
theorem invert_copy_head (t : Spec.Tier) (xs : List Nat) :
    ∃ k, Ecbs.invert (bottomBoard t xs) ((2 : Nat) : Int) =
      Ecbs.copy_band (bumpedBoard t xs) Ecbs.gap ((2 : Nat) : Int) false >>= k := by
  apply Exists.intro
  unfold Ecbs.invert
  dsimp only
  rw [show Ecbs.op_inv = Int.ofNat 2 from rfl]
  rw [atL_ofNat _ 2 (bottom_ops2 t xs), bottom_ops_zero t xs, ok_bind]
  rw [addI_ofNat_one 0 (by unfold FitsLen i64MaxNat; decide), ok_bind]
  rw [putL_ofNat _ 2 (Int.ofNat 1) (bottom_ops2 t xs), ok_bind]
  conv =>
    lhs
    pattern (Ecbs.copy_band _ Ecbs.gap _ false)
    change Ecbs.copy_band (bumpedBoard t xs) Ecbs.gap ((2 : Nat) : Int) false

/-- After the bump and the copy into the gap, `invert` starts the tally and continues. -/
theorem invert_tally_head (t : Spec.Tier) (h : BoardOk t) (xs : List Nat)
    (hx : xs.length = t.n) :
    ∃ k, Ecbs.invert (bottomBoard t xs) ((2 : Nat) : Int) =
      Ecbs.tally_start (gapBoard t xs) >>= k := by
  apply Exists.intro
  unfold Ecbs.invert
  dsimp only
  rw [show Ecbs.op_inv = Int.ofNat 2 from rfl]
  rw [atL_ofNat _ 2 (bottom_ops2 t xs), bottom_ops_zero t xs, ok_bind]
  rw [addI_ofNat_one 0 (by unfold FitsLen i64MaxNat; decide), ok_bind]
  rw [putL_ofNat _ 2 (Int.ofNat 1) (bottom_ops2 t xs), ok_bind]
  conv =>
    lhs
    pattern (Ecbs.copy_band _ Ecbs.gap _ false)
    change Ecbs.copy_band (bumpedBoard t xs) Ecbs.gap ((2 : Nat) : Int) false
  rw [copy_gap_board t h xs hx, ok_bind]

end EcbsLink2.Link2
