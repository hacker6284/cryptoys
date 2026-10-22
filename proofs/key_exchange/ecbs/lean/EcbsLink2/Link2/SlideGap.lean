/-
  A later rung starts with the gap on the bench. `slideGap` is the emitted
  `settle`: that bench moves into home 5 and the bench goes off. Park and copy
  only touch the row, the control counter, the parked hole, the rung index, and
  the spare. They commute with that settle. The white scan between copy and the
  first cube reads the tally row, not home 5 and not the bench.
-/
import EcbsLink2.Link2.GapAt

namespace EcbsLink2.Link2

open MegaDreifach.Link2

/-- The emitted slide of the gap bench into its home. -/
def slideGap (b : Ecbs.Board) : Except SudoRt.Trap Ecbs.Board :=
  Ecbs.settle b

/-- Raising the peak at a smaller held-count, then at a larger one, is the same
    as raising it only at the larger count. -/
theorem raisedPeak_absorb (peak a b : Nat) (hab : a ≤ b) :
    raisedPeak (raisedPeak peak a) b = raisedPeak peak b := by
  unfold raisedPeak
  by_cases hpa : peak < a
  · simp only [hpa, ite_true]
    by_cases hab' : a < b
    · have hpb : peak < b := Nat.lt_of_lt_of_le hpa (Nat.le_of_lt hab')
      simp [hab', hpb]
    · have heq : a = b := Nat.le_antisymm hab (Nat.not_lt.mp hab')
      have hpb : peak < b := by rw [← heq]; exact hpa
      simp [hab', heq, hpb]
  · simp only [hpa, ite_false]

theorem settleBoard_row (b : Ecbs.Board) (home : Nat)
    (hin : HomeIn b home)
    (xs : List Nat) (n moves slides peak : Nat) :
    (settleBoard b home hin.hH hin.hD xs n moves slides peak).sudo_5Board_3row =
      b.sudo_5Board_3row := by
  unfold settleBoard
  split <;> rfl

theorem settleBoard_ctrl (b : Ecbs.Board) (home : Nat)
    (hin : HomeIn b home)
    (xs : List Nat) (n moves slides peak : Nat) :
    (settleBoard b home hin.hH hin.hD xs n moves slides peak).sudo_5Board_4cost.sudo_5Costs_4ctrl =
      b.sudo_5Board_4cost.sudo_5Costs_4ctrl := by
  unfold settleBoard
  split <;> rfl

theorem settleBoard_from (b : Ecbs.Board) (home : Nat)
    (hin : HomeIn b home)
    (xs : List Nat) (n moves slides peak : Nat) :
    (settleBoard b home hin.hH hin.hD xs n moves slides peak).sudo_5Board_11parked_from =
      b.sudo_5Board_11parked_from := by
  unfold settleBoard
  split <;> rfl

theorem settleBoard_ridx (b : Ecbs.Board) (home : Nat)
    (hin : HomeIn b home)
    (xs : List Nat) (n moves slides peak : Nat) :
    (settleBoard b home hin.hH hin.hD xs n moves slides peak).sudo_5Board_8rung_idx =
      b.sudo_5Board_8rung_idx := by
  unfold settleBoard
  split <;> rfl

theorem parkKeep_home (b : Ecbs.Board) (hole park rung i ctrl : Nat)
    (hRowP : park < b.sudo_5Board_3row.size) (hRowH : hole < b.sudo_5Board_3row.size) :
    (parkKeepBoard b hole park rung i ctrl hRowP hRowH).sudo_5Board_4home =
      b.sudo_5Board_4home := by
  simp [parkKeepBoard]

theorem parkKeep_held (b : Ecbs.Board) (hole park rung i ctrl : Nat)
    (hRowP : park < b.sudo_5Board_3row.size) (hRowH : hole < b.sudo_5Board_3row.size) :
    (parkKeepBoard b hole park rung i ctrl hRowP hRowH).sudo_5Board_4held =
      b.sudo_5Board_4held := by
  simp [parkKeepBoard]

theorem parkKeep_on (b : Ecbs.Board) (hole park rung i ctrl : Nat)
    (hRowP : park < b.sudo_5Board_3row.size) (hRowH : hole < b.sudo_5Board_3row.size) :
    (parkKeepBoard b hole park rung i ctrl hRowP hRowH).sudo_5Board_8bench_on =
      b.sudo_5Board_8bench_on := by
  simp [parkKeepBoard]

theorem parkKeep_bench (b : Ecbs.Board) (hole park rung i ctrl : Nat)
    (hRowP : park < b.sudo_5Board_3row.size) (hRowH : hole < b.sudo_5Board_3row.size) :
    (parkKeepBoard b hole park rung i ctrl hRowP hRowH).sudo_5Board_5bench =
      b.sudo_5Board_5bench := by
  simp [parkKeepBoard]

theorem parkKeep_moves (b : Ecbs.Board) (hole park rung i ctrl : Nat)
    (hRowP : park < b.sudo_5Board_3row.size) (hRowH : hole < b.sudo_5Board_3row.size) :
    (parkKeepBoard b hole park rung i ctrl hRowP hRowH).sudo_5Board_4cost.sudo_5Costs_5moves =
      b.sudo_5Board_4cost.sudo_5Costs_5moves := by
  simp [parkKeepBoard]

theorem parkKeep_slides (b : Ecbs.Board) (hole park rung i ctrl : Nat)
    (hRowP : park < b.sudo_5Board_3row.size) (hRowH : hole < b.sudo_5Board_3row.size) :
    (parkKeepBoard b hole park rung i ctrl hRowP hRowH).sudo_5Board_4cost.sudo_5Costs_6slides =
      b.sudo_5Board_4cost.sudo_5Costs_6slides := by
  simp [parkKeepBoard]

theorem parkKeep_peak (b : Ecbs.Board) (hole park rung i ctrl : Nat)
    (hRowP : park < b.sudo_5Board_3row.size) (hRowH : hole < b.sudo_5Board_3row.size) :
    (parkKeepBoard b hole park rung i ctrl hRowP hRowH).sudo_5Board_4cost.sudo_5Costs_4peak =
      b.sudo_5Board_4cost.sudo_5Costs_4peak := by
  simp [parkKeepBoard]

theorem settleBoard_pos (b : Ecbs.Board) (home : Nat)
    (hin : HomeIn b home)
    (xs : List Nat) (n moves slides peak : Nat)
    (hpk : peak < countHeld (b.sudo_5Board_4held.set ⟨home, hin.hD⟩ true) 7) :
    settleBoard b home hin.hH hin.hD xs n moves slides peak =
      { b with
        sudo_5Board_4home := b.sudo_5Board_4home.set ⟨home, hin.hH⟩ (embed (xs.take n))
        sudo_5Board_4held := b.sudo_5Board_4held.set ⟨home, hin.hD⟩ true
        sudo_5Board_8bench_on := false
        sudo_5Board_4cost := { b.sudo_5Board_4cost with
          sudo_5Costs_5moves := Int.ofNat (moves + 2 * pegCount (xs.take n))
          sudo_5Costs_6slides := Int.ofNat (slides + 2 * pegCount (xs.take n))
          sudo_5Costs_4peak := Int.ofNat (countHeld (b.sudo_5Board_4held.set ⟨home, hin.hD⟩ true) 7) } } := by
  unfold settleBoard
  simp [hpk]

theorem settleBoard_neg (b : Ecbs.Board) (home : Nat)
    (hin : HomeIn b home)
    (xs : List Nat) (n moves slides peak : Nat)
    (hpk : ¬ peak < countHeld (b.sudo_5Board_4held.set ⟨home, hin.hD⟩ true) 7) :
    settleBoard b home hin.hH hin.hD xs n moves slides peak =
      { b with
        sudo_5Board_4home := b.sudo_5Board_4home.set ⟨home, hin.hH⟩ (embed (xs.take n))
        sudo_5Board_4held := b.sudo_5Board_4held.set ⟨home, hin.hD⟩ true
        sudo_5Board_8bench_on := false
        sudo_5Board_4cost := { b.sudo_5Board_4cost with
          sudo_5Costs_5moves := Int.ofNat (moves + 2 * pegCount (xs.take n))
          sudo_5Costs_6slides := Int.ofNat (slides + 2 * pegCount (xs.take n)) } } := by
  unfold settleBoard
  simp [hpk]

/-- Keep-park of a board whose gap bench has already been slid home. The row
    proof is the original one: sliding does not change the row. -/
theorem parkKeep_settled_pos
    (b : Ecbs.Board) (hole park rung i ctrl home : Nat)
    (hRowP : park < b.sudo_5Board_3row.size)
    (hRowH : hole < b.sudo_5Board_3row.size)
    (hH : home < b.sudo_5Board_4home.size)
    (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (n moves slides peak : Nat)
    (_hpk : peak < countHeld (b.sudo_5Board_4held.set ⟨home, hD⟩ true) 7) :
    parkKeepBoard
        ({ b with
          sudo_5Board_4home := b.sudo_5Board_4home.set ⟨home, hH⟩ (embed (xs.take n))
          sudo_5Board_4held := b.sudo_5Board_4held.set ⟨home, hD⟩ true
          sudo_5Board_8bench_on := false
          sudo_5Board_4cost := { b.sudo_5Board_4cost with
            sudo_5Costs_5moves := Int.ofNat (moves + 2 * pegCount (xs.take n))
            sudo_5Costs_6slides := Int.ofNat (slides + 2 * pegCount (xs.take n))
            sudo_5Costs_4peak :=
              Int.ofNat (countHeld (b.sudo_5Board_4held.set ⟨home, hD⟩ true) 7) } })
        hole park rung i ctrl hRowP hRowH =
      { parkKeepBoard b hole park rung i ctrl hRowP hRowH with
        sudo_5Board_4home := b.sudo_5Board_4home.set ⟨home, hH⟩ (embed (xs.take n))
        sudo_5Board_4held := b.sudo_5Board_4held.set ⟨home, hD⟩ true
        sudo_5Board_8bench_on := false
        sudo_5Board_4cost :=
          { (parkKeepBoard b hole park rung i ctrl hRowP hRowH).sudo_5Board_4cost with
            sudo_5Costs_5moves := Int.ofNat (moves + 2 * pegCount (xs.take n))
            sudo_5Costs_6slides := Int.ofNat (slides + 2 * pegCount (xs.take n))
            sudo_5Costs_4peak :=
              Int.ofNat (countHeld (b.sudo_5Board_4held.set ⟨home, hD⟩ true) 7) } } := by
  unfold parkKeepBoard
  simp [ofNat_eq_natCast]

/-- A settle into home 5 adds at most `2 · n` moves and `2 · n` slides, leaves
    ops alone, and does not push the peak above `max(peak, 7)`. -/
theorem settle_cost_room (n : Nat) (pegs : Nat) (hpegs : pegs ≤ n) :
    2 * pegs ≤ 2 * n := by
  omega

theorem settle_peak_le (peak occ : Nat) (hocc : occ ≤ 7) :
    (if peak < occ then occ else peak) ≤ max peak 7 := by
  by_cases h : peak < occ
  · simp only [h, ite_true]
    exact Nat.le_trans hocc (Nat.le_max_right _ _)
  · simp only [h, ite_false]
    exact Nat.le_max_left _ _

theorem charge_white_settle (n bench m : Nat) :
    2 * n + (n + m * pegCharge n bench + mulCharge n bench + n) ≤
      rungCharge n bench m := by
  let W := n + m * pegCharge n bench + mulCharge n bench + n
  have hpeg : 2 * n ≤ pegCharge n bench := by
    unfold pegCharge
    exact Nat.le_trans (by omega : 2 * n ≤ 4 * n) (Nat.le_add_right _ _)
  have hslack : 2 * n + W ≤ W + pegCharge n bench := by
    dsimp only [W]
    omega
  have hmore : W + pegCharge n bench ≤ rungCharge n bench m := by
    unfold rungCharge
    dsimp only [W]
    have hsplit : m * pegCharge n bench + pegCharge n bench =
        (m + 1) * pegCharge n bench := by
      rw [← Nat.succ_mul]
    have hre : n + m * pegCharge n bench + mulCharge n bench + n + pegCharge n bench =
        2 * n + (m * pegCharge n bench + pegCharge n bench) + mulCharge n bench := by
      omega
    rw [hre, hsplit]
    have hm : mulCharge n bench ≤ mulCharge n bench + mulCharge n bench :=
      Nat.le_add_right _ _
    have h2 : mulCharge n bench + mulCharge n bench = 2 * mulCharge n bench := by
      rw [Nat.two_mul]
    omega
  exact Nat.le_trans hslack hmore

theorem charge_red_settle (n bench m : Nat) :
    2 * n + (n + m * pegCharge n bench + mulCharge n bench + n +
        (2 * n + 3 * (bench - n)) + mulCharge n bench) ≤
      rungCharge n bench m := by
  unfold rungCharge pegCharge
  have hmul : (m + 1) * (4 * n + 3 * (bench - n)) =
      m * (4 * n + 3 * (bench - n)) + (4 * n + 3 * (bench - n)) := by
    rw [Nat.succ_mul]
  have htwo : mulCharge n bench + mulCharge n bench = 2 * mulCharge n bench := by
    rw [Nat.two_mul]
  have h4 : 4 * n = 2 * n + (2 * n) := by omega
  omega

/-- Keep-park of a board whose gap bench has already been slid home, when the
    peak does not rise. -/
theorem parkKeep_settled_neg
    (b : Ecbs.Board) (hole park rung i ctrl home : Nat)
    (hRowP : park < b.sudo_5Board_3row.size)
    (hRowH : hole < b.sudo_5Board_3row.size)
    (hH : home < b.sudo_5Board_4home.size)
    (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (n moves slides peak : Nat)
    (_hpk : ¬ peak < countHeld (b.sudo_5Board_4held.set ⟨home, hD⟩ true) 7) :
    parkKeepBoard
        ({ b with
          sudo_5Board_4home := b.sudo_5Board_4home.set ⟨home, hH⟩ (embed (xs.take n))
          sudo_5Board_4held := b.sudo_5Board_4held.set ⟨home, hD⟩ true
          sudo_5Board_8bench_on := false
          sudo_5Board_4cost := { b.sudo_5Board_4cost with
            sudo_5Costs_5moves := Int.ofNat (moves + 2 * pegCount (xs.take n))
            sudo_5Costs_6slides := Int.ofNat (slides + 2 * pegCount (xs.take n)) } })
        hole park rung i ctrl hRowP hRowH =
      { parkKeepBoard b hole park rung i ctrl hRowP hRowH with
        sudo_5Board_4home := b.sudo_5Board_4home.set ⟨home, hH⟩ (embed (xs.take n))
        sudo_5Board_4held := b.sudo_5Board_4held.set ⟨home, hD⟩ true
        sudo_5Board_8bench_on := false
        sudo_5Board_4cost :=
          { (parkKeepBoard b hole park rung i ctrl hRowP hRowH).sudo_5Board_4cost with
            sudo_5Costs_5moves := Int.ofNat (moves + 2 * pegCount (xs.take n))
            sudo_5Costs_6slides := Int.ofNat (slides + 2 * pegCount (xs.take n)) } } := by
  unfold parkKeepBoard
  simp [ofNat_eq_natCast]

theorem getD_set_self (a : Array Bool) (i : Nat) (hi : i < a.size) (v : Bool) :
    (a.set ⟨i, hi⟩ v).getD i false = v := by
  simp [Array.getD, Array.getElem_set, Array.size_set, hi]

theorem getD_set_ne (a : Array Bool) (i j : Nat) (hi : i < a.size) (v : Bool)
    (hne : j ≠ i) :
    (a.set ⟨i, hi⟩ v).getD j false = a.getD j false := by
  unfold Array.getD
  simp only [Array.size_set]
  by_cases hj : j < a.size
  · simp [hj, Array.getElem_set, Ne.symm hne]
  · simp [hj]

/-- Setting one more held flag does not lower the count of the first `k` homes. -/
theorem countHeld_set_ge (held : Array Bool) (i : Nat) (hi : i < held.size) (k : Nat) :
    countHeld held k ≤ countHeld (held.set ⟨i, hi⟩ true) k := by
  induction k with
  | zero =>
    unfold countHeld
    omega
  | succ k ih =>
    unfold countHeld
    by_cases hk : k = i
    · have hself : (held.set ⟨i, hi⟩ true).getD k false = true := by
        rw [hk]
        exact getD_set_self held i hi true
      simp only [hself, ite_true]
      have hbit : (if held.getD k false then 1 else 0) ≤ 1 := by split <;> decide
      omega
    · have hne : (held.set ⟨i, hi⟩ true).getD k false = held.getD k false :=
        getD_set_ne held i k hi true hk
      simp only [hne]
      omega

theorem array_set_comm {α : Type} (a : Array α) (i j : Nat)
    (hi : i < a.size) (hj : j < a.size) (v w : α) (hne : i ≠ j) :
    (a.set ⟨i, hi⟩ v).set ⟨j, by rw [Array.size_set]; exact hj⟩ w =
      (a.set ⟨j, hj⟩ w).set ⟨i, by rw [Array.size_set]; exact hi⟩ v := by
  apply Array.ext
  · simp [Array.size_set]
  · intro k hk1 hk2
    by_cases hki : k = i
    · subst hki
      simp [Array.getElem_set, hne.symm]
    · by_cases hkj : k = j
      · subst hkj
        simp [Array.getElem_set, hne]
      · have hki' : i ≠ k := Ne.symm hki
        have hkj' : j ≠ k := Ne.symm hkj
        simp [Array.getElem_set, hki', hkj']

/-- `cubeMoves` adds its incoming counter unchanged. -/
theorem cubeMoves_add (moves d : Nat) (xs : List Nat) (n k bench : Nat) :
    cubeMoves (moves + d) xs n k bench = cubeMoves moves xs n k bench + d := by
  unfold cubeMoves
  dsimp only
  omega

/-- A settle of at most `2 · n`, paid inside a loop that was already one settle
    short, is absorbed by that slack. -/
theorem settle_absorbed (mv pegs settle loop m n bench : Nat)
    (hpegs : pegs ≤ n) (hset : settle ≤ 2 * n)
    (hloop : loop + 2 * n ≤ mv + settle + pegs + m * pegCharge n bench) :
    loop ≤ mv + n + m * pegCharge n bench := by
  omega

theorem array_set_irrel {α : Type} (a : Array α) (i : Nat) (h h' : i < a.size) (v : α) :
    a.set ⟨i, h⟩ v = a.set ⟨i, h'⟩ v := by
  have : (⟨i, h⟩ : Fin a.size) = ⟨i, h'⟩ := Fin.ext rfl
  simp [this]

theorem get_proof_irrel {α : Type} (a : Array α) (i : Nat) (h h' : i < a.size) :
    a[i]'h = a[i]'h' :=
  congrArg (fun p : i < a.size => a[i]'p) (proof_irrel h h')

theorem countHeld_congr (a b : Array Bool) (h : a = b) (k : Nat) :
    countHeld a k = countHeld b k := by
  rw [h]

theorem countHeld_of_eq (a c : Array Bool) (h : a = c) (i : Nat) (ha : i < a.size) (k : Nat) :
    countHeld (a.set ⟨i, ha⟩ true) k =
      countHeld (c.set ⟨i, h ▸ ha⟩ true) k := by
  subst h
  rfl

theorem array_set_of_eq {α : Type} (a c : Array α) (h : a = c) (i : Nat) (ha : i < a.size) (v : α) :
    a.set ⟨i, ha⟩ v = c.set ⟨i, h ▸ ha⟩ v := by
  subst h
  rfl

theorem raised_both (peak c1 c2 both : Nat) (h1 : c1 ≤ both) (h2 : c2 ≤ both) :
    raisedPeak (raisedPeak peak c1) both = raisedPeak (raisedPeak peak c2) both := by
  rw [raisedPeak_absorb peak c1 both h1, raisedPeak_absorb peak c2 both h2]

theorem place_moves_out (b : Ecbs.Board) (home : Nat)
    (hin : HomeIn b home)
    (xs : List Nat) (moves peak : Nat) :
    (placeBoard b home hin.hH hin.hD xs moves peak).sudo_5Board_4cost.sudo_5Costs_5moves =
      Int.ofNat (moves + pegCount xs) := by
  unfold placeBoard
  dsimp only
  split <;> rfl

theorem place_slides_out (b : Ecbs.Board) (home : Nat)
    (hin : HomeIn b home)
    (xs : List Nat) (moves peak : Nat) :
    (placeBoard b home hin.hH hin.hD xs moves peak).sudo_5Board_4cost.sudo_5Costs_6slides =
      b.sudo_5Board_4cost.sudo_5Costs_6slides := by
  unfold placeBoard
  dsimp only
  split <;> rfl

theorem place_on_out (b : Ecbs.Board) (home : Nat)
    (hin : HomeIn b home)
    (xs : List Nat) (moves peak : Nat) :
    (placeBoard b home hin.hH hin.hD xs moves peak).sudo_5Board_8bench_on =
      b.sudo_5Board_8bench_on := by
  unfold placeBoard
  dsimp only
  split <;> rfl

theorem place_row_out (b : Ecbs.Board) (home : Nat)
    (hin : HomeIn b home)
    (xs : List Nat) (moves peak : Nat) :
    (placeBoard b home hin.hH hin.hD xs moves peak).sudo_5Board_3row = b.sudo_5Board_3row := by
  unfold placeBoard
  dsimp only
  split <;> rfl

theorem place_peak_out (b : Ecbs.Board) (home : Nat)
    (hin : HomeIn b home)
    (xs : List Nat) (moves peak : Nat)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak) :
    (placeBoard b home hin.hH hin.hD xs moves peak).sudo_5Board_4cost.sudo_5Costs_4peak =
      Int.ofNat (raisedPeak peak (countHeld (b.sudo_5Board_4held.set ⟨home, hin.hD⟩ true) 7)) := by
  unfold placeBoard raisedPeak
  dsimp only
  split
  · next hlt =>
      simp [hlt, ofNat_eq_natCast]
  · next hnk =>
      simp [hnk, hpeak]

theorem settle_row_out (b : Ecbs.Board) (home : Nat)
    (hin : HomeIn b home)
    (xs : List Nat) (n moves slides peak : Nat) :
    (settleBoard b home hin.hH hin.hD xs n moves slides peak).sudo_5Board_3row =
      b.sudo_5Board_3row := by
  by_cases hpk : peak < countHeld (b.sudo_5Board_4held.set ⟨home, hin.hD⟩ true) 7
  · rw [settle_peak b home ⟨hin.hH, hin.hD⟩ xs n moves slides peak hpk]
  · rw [settle_keep b home ⟨hin.hH, hin.hD⟩ xs n moves slides peak hpk]

/-- The bench list `gap.take n ++` zeros, cut back to `n`, is the gap. -/
theorem gap_slide_take (gap : List Nat) (n bench : Nat) (hlen : gap.length = n) :
    ((gap.take n ++ List.replicate (bench - n) 0).take n) = gap := by
  have hpre : (gap.take n).length = n := by
    rw [List.length_take, hlen, Nat.min_eq_left (Nat.le_refl _)]
  have hleft := List.take_left (gap.take n) (List.replicate (bench - n) 0)
  rw [hpre] at hleft
  rw [hleft, ← hlen, List.take_length]

theorem place_home_out (b : Ecbs.Board) (home : Nat)
    (hin : HomeIn b home)
    (xs : List Nat) (moves peak : Nat) :
    (placeBoard b home hin.hH hin.hD xs moves peak).sudo_5Board_4home =
      b.sudo_5Board_4home.set ⟨home, hin.hH⟩ (embed xs) := by
  unfold placeBoard
  dsimp only
  split <;> rfl

theorem place_held_out (b : Ecbs.Board) (home : Nat)
    (hin : HomeIn b home)
    (xs : List Nat) (moves peak : Nat) :
    (placeBoard b home hin.hH hin.hD xs moves peak).sudo_5Board_4held =
      b.sudo_5Board_4held.set ⟨home, hin.hD⟩ true := by
  unfold placeBoard
  dsimp only
  split <;> rfl

theorem place_size_home (b : Ecbs.Board) (home : Nat)
    (hin : HomeIn b home)
    (xs : List Nat) (moves peak : Nat) :
    (placeBoard b home hin.hH hin.hD xs moves peak).sudo_5Board_4home.size =
      b.sudo_5Board_4home.size := by
  rw [place_home_out b home hin xs moves peak, Array.size_set]

theorem place_size_held (b : Ecbs.Board) (home : Nat)
    (hin : HomeIn b home)
    (xs : List Nat) (moves peak : Nat) :
    (placeBoard b home hin.hH hin.hD xs moves peak).sudo_5Board_4held.size =
      b.sudo_5Board_4held.size := by
  rw [place_held_out b home hin xs moves peak, Array.size_set]

/-- Fields `place` does not write. -/
theorem place_rest (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat) :
    (placeBoard b home hH hD xs moves peak).sudo_5Board_1t = b.sudo_5Board_1t ∧
    (placeBoard b home hH hD xs moves peak).sudo_5Board_8bench_to =
      b.sudo_5Board_8bench_to ∧
    (placeBoard b home hH hD xs moves peak).sudo_5Board_5bench = b.sudo_5Board_5bench ∧
    (placeBoard b home hH hD xs moves peak).sudo_5Board_5phase = b.sudo_5Board_5phase ∧
    (placeBoard b home hH hD xs moves peak).sudo_5Board_8phase_m0 =
      b.sudo_5Board_8phase_m0 ∧
    (placeBoard b home hH hD xs moves peak).sudo_5Board_8phase_pk =
      b.sudo_5Board_8phase_pk ∧
    (placeBoard b home hH hD xs moves peak).sudo_5Board_10phase_hole =
      b.sudo_5Board_10phase_hole ∧
    (placeBoard b home hH hD xs moves peak).sudo_5Board_12calling_hole =
      b.sudo_5Board_12calling_hole ∧
    (placeBoard b home hH hD xs moves peak).sudo_5Board_7ladder0 =
      b.sudo_5Board_7ladder0 ∧
    (placeBoard b home hH hD xs moves peak).sudo_5Board_6nrungs = b.sudo_5Board_6nrungs ∧
    (placeBoard b home hH hD xs moves peak).sudo_5Board_9park_hole =
      b.sudo_5Board_9park_hole ∧
    (placeBoard b home hH hD xs moves peak).sudo_5Board_6tally0 = b.sudo_5Board_6tally0 ∧
    (placeBoard b home hH hD xs moves peak).sudo_5Board_6marker = b.sudo_5Board_6marker ∧
    (placeBoard b home hH hD xs moves peak).sudo_5Board_11parked_from =
      b.sudo_5Board_11parked_from ∧
    (placeBoard b home hH hD xs moves peak).sudo_5Board_9tally_len =
      b.sudo_5Board_9tally_len ∧
    (placeBoard b home hH hD xs moves peak).sudo_5Board_9marker_on =
      b.sudo_5Board_9marker_on ∧
    (placeBoard b home hH hD xs moves peak).sudo_5Board_8rung_idx =
      b.sudo_5Board_8rung_idx ∧
    (placeBoard b home hH hD xs moves peak).sudo_5Board_6ladder = b.sudo_5Board_6ladder ∧
    (placeBoard b home hH hD xs moves peak).sudo_5Board_3log = b.sudo_5Board_3log ∧
    (placeBoard b home hH hD xs moves peak).sudo_5Board_4cost.sudo_5Costs_4ctrl =
      b.sudo_5Board_4cost.sudo_5Costs_4ctrl ∧
    (placeBoard b home hH hD xs moves peak).sudo_5Board_4cost.sudo_5Costs_5calls =
      b.sudo_5Board_4cost.sudo_5Costs_5calls ∧
    (placeBoard b home hH hD xs moves peak).sudo_5Board_4cost.sudo_5Costs_13stale_cleared =
      b.sudo_5Board_4cost.sudo_5Costs_13stale_cleared ∧
    (placeBoard b home hH hD xs moves peak).sudo_5Board_4cost.sudo_5Costs_14key_grid_moves =
      b.sudo_5Board_4cost.sudo_5Costs_14key_grid_moves ∧
    (placeBoard b home hH hD xs moves peak).sudo_5Board_4cost.sudo_5Costs_12ladder_moves =
      b.sudo_5Board_4cost.sudo_5Costs_12ladder_moves ∧
    (placeBoard b home hH hD xs moves peak).sudo_5Board_4cost.sudo_5Costs_11peak_strict =
      b.sudo_5Board_4cost.sudo_5Costs_11peak_strict ∧
    (placeBoard b home hH hD xs moves peak).sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole ∧
    (placeBoard b home hH hD xs moves peak).sudo_5Board_4cost.sudo_5Costs_15control_highest =
      b.sudo_5Board_4cost.sudo_5Costs_15control_highest ∧
    (placeBoard b home hH hD xs moves peak).sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
      b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max ∧
    (placeBoard b home hH hD xs moves peak).sudo_5Board_4cost.sudo_5Costs_9tally_max =
      b.sudo_5Board_4cost.sudo_5Costs_9tally_max ∧
    (placeBoard b home hH hD xs moves peak).sudo_5Board_4cost.sudo_5Costs_14moves_by_phase =
      b.sudo_5Board_4cost.sudo_5Costs_14moves_by_phase ∧
    (placeBoard b home hH hD xs moves peak).sudo_5Board_4cost.sudo_5Costs_13peak_by_phase =
      b.sudo_5Board_4cost.sudo_5Costs_13peak_by_phase ∧
    (placeBoard b home hH hD xs moves peak).sudo_5Board_4cost.sudo_5Costs_3ops =
      b.sudo_5Board_4cost.sudo_5Costs_3ops := by
  unfold placeBoard
  dsimp only
  split <;>
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Fields `settle` does not write. -/
theorem settle_rest (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (n moves slides peak : Nat) :
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_1t = b.sudo_5Board_1t ∧
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_8bench_to =
      b.sudo_5Board_8bench_to ∧
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_5bench =
      b.sudo_5Board_5bench ∧
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_5phase =
      b.sudo_5Board_5phase ∧
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_8phase_m0 =
      b.sudo_5Board_8phase_m0 ∧
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_8phase_pk =
      b.sudo_5Board_8phase_pk ∧
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_10phase_hole =
      b.sudo_5Board_10phase_hole ∧
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_12calling_hole =
      b.sudo_5Board_12calling_hole ∧
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_7ladder0 =
      b.sudo_5Board_7ladder0 ∧
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_6nrungs =
      b.sudo_5Board_6nrungs ∧
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_9park_hole =
      b.sudo_5Board_9park_hole ∧
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_6tally0 =
      b.sudo_5Board_6tally0 ∧
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_6marker =
      b.sudo_5Board_6marker ∧
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_11parked_from =
      b.sudo_5Board_11parked_from ∧
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_9tally_len =
      b.sudo_5Board_9tally_len ∧
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_9marker_on =
      b.sudo_5Board_9marker_on ∧
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_8rung_idx =
      b.sudo_5Board_8rung_idx ∧
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_6ladder =
      b.sudo_5Board_6ladder ∧
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_3log =
      b.sudo_5Board_3log ∧
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_4cost.sudo_5Costs_4ctrl =
      b.sudo_5Board_4cost.sudo_5Costs_4ctrl ∧
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_4cost.sudo_5Costs_5calls =
      b.sudo_5Board_4cost.sudo_5Costs_5calls ∧
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_4cost.sudo_5Costs_13stale_cleared =
      b.sudo_5Board_4cost.sudo_5Costs_13stale_cleared ∧
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_4cost.sudo_5Costs_14key_grid_moves =
      b.sudo_5Board_4cost.sudo_5Costs_14key_grid_moves ∧
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_4cost.sudo_5Costs_12ladder_moves =
      b.sudo_5Board_4cost.sudo_5Costs_12ladder_moves ∧
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_4cost.sudo_5Costs_11peak_strict =
      b.sudo_5Board_4cost.sudo_5Costs_11peak_strict ∧
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole ∧
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_4cost.sudo_5Costs_15control_highest =
      b.sudo_5Board_4cost.sudo_5Costs_15control_highest ∧
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
      b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max ∧
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_4cost.sudo_5Costs_9tally_max =
      b.sudo_5Board_4cost.sudo_5Costs_9tally_max ∧
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_4cost.sudo_5Costs_14moves_by_phase =
      b.sudo_5Board_4cost.sudo_5Costs_14moves_by_phase ∧
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_4cost.sudo_5Costs_13peak_by_phase =
      b.sudo_5Board_4cost.sudo_5Costs_13peak_by_phase ∧
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_4cost.sudo_5Costs_3ops =
      b.sudo_5Board_4cost.sudo_5Costs_3ops := by
  by_cases hpk : peak < countHeld (b.sudo_5Board_4held.set ⟨home, hD⟩ true) 7
  · rw [settle_peak b home ⟨hH, hD⟩ xs n moves slides peak hpk]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rw [settle_keep b home ⟨hH, hD⟩ xs n moves slides peak hpk]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `place` at `dst` and `settle` at a different `home` write disjoint homes.
    Moves add, slides are only the settle's, and the peak is the raise against
    both held flags in either order. -/
theorem place_settle_comm (b : Ecbs.Board) (home dst : Nat)
    (hin : HomeIn b home)
    (hHd : dst < b.sudo_5Board_4home.size) (hDd : dst < b.sudo_5Board_4held.size)
    (hne : home ≠ dst)
    (xs g : List Nat) (n moves slides peak : Nat)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak) :
    let bS := settleBoard b home hin.hH hin.hD xs n moves slides peak
    let c5 := countHeld (b.sudo_5Board_4held.set ⟨home, hin.hD⟩ true) 7
    let pkS := raisedPeak peak c5
    let hHdS : dst < bS.sudo_5Board_4home.size := by
      rw [settle_home_eq b home ⟨hin.hH, hin.hD⟩ xs n moves slides peak, Array.size_set]; exact hHd
    let hDdS : dst < bS.sudo_5Board_4held.size := by
      rw [settle_held_eq b home ⟨hin.hH, hin.hD⟩ xs n moves slides peak, Array.size_set]; exact hDd
    let bP := placeBoard b dst hHd hDd g moves peak
    let c6 := countHeld (b.sudo_5Board_4held.set ⟨dst, hDd⟩ true) 7
    let pkP := raisedPeak peak c6
    let hHS : home < bP.sudo_5Board_4home.size := by
      rw [place_size_home b dst ⟨hHd, hDd⟩ g moves peak]; exact hin.hH
    let hDS : home < bP.sudo_5Board_4held.size := by
      rw [place_size_held b dst ⟨hHd, hDd⟩ g moves peak]; exact hin.hD
    placeBoard bS dst hHdS hDdS g (moves + 2 * pegCount (xs.take n)) pkS =
      settleBoard bP home hHS hDS xs n (moves + pegCount g) slides pkP := by
  intro bS c5 pkS hHdS hDdS bP c6 pkP hHS hDS
  let both :=
    countHeld ((b.sudo_5Board_4held.set ⟨home, hin.hD⟩ true).set
      ⟨dst, by rw [Array.size_set]; exact hDd⟩ true) 7
  have hc5 : c5 ≤ both := by
    simpa [c5, both] using
      countHeld_set_ge (b.sudo_5Board_4held.set ⟨home, hin.hD⟩ true)
        dst (by rw [Array.size_set]; exact hDd) 7
  have hc6 : c6 ≤ both := by
    have hcomm := array_set_comm b.sudo_5Board_4held dst home hDd hin.hD true true hne.symm
    have hle := countHeld_set_ge (b.sudo_5Board_4held.set ⟨dst, hDd⟩ true)
      home (by rw [Array.size_set]; exact hin.hD) 7
    have hEq := countHeld_congr _ _ hcomm 7
    simpa [c6, both] using Nat.le_trans hle (Nat.le_of_eq hEq)
  rcases place_rest bS dst hHdS hDdS g (moves + 2 * pegCount (xs.take n)) pkS with
    ⟨PS_t, PS_to, PS_bench, PS_phase, PS_m0, PS_pk, PS_ph, PS_call, PS_l0, PS_nr,
      PS_park, PS_t0, PS_marker, PS_from, PS_len, PS_mon, PS_ridx, PS_lad, PS_log,
      PS_ctrl, PS_calls, PS_stale, PS_key, PS_ladM, PS_strict, PS_hole, PS_high,
      PS_mark, PS_tmax, PS_mbp, PS_pbp, PS_ops⟩
  rcases settle_rest b home hin.hH hin.hD xs n moves slides peak with
    ⟨SB_t, SB_to, SB_bench, SB_phase, SB_m0, SB_pk, SB_ph, SB_call, SB_l0, SB_nr,
      SB_park, SB_t0, SB_marker, SB_from, SB_len, SB_mon, SB_ridx, SB_lad, SB_log,
      SB_ctrl, SB_calls, SB_stale, SB_key, SB_ladM, SB_strict, SB_hole, SB_high,
      SB_mark, SB_tmax, SB_mbp, SB_pbp, SB_ops⟩
  rcases place_rest b dst hHd hDd g moves peak with
    ⟨PB_t, PB_to, PB_bench, PB_phase, PB_m0, PB_pk, PB_ph, PB_call, PB_l0, PB_nr,
      PB_park, PB_t0, PB_marker, PB_from, PB_len, PB_mon, PB_ridx, PB_lad, PB_log,
      PB_ctrl, PB_calls, PB_stale, PB_key, PB_ladM, PB_strict, PB_hole, PB_high,
      PB_mark, PB_tmax, PB_mbp, PB_pbp, PB_ops⟩
  rcases settle_rest bP home hHS hDS xs n (moves + pegCount g) slides pkP with
    ⟨SP_t, SP_to, SP_bench, SP_phase, SP_m0, SP_pk, SP_ph, SP_call, SP_l0, SP_nr,
      SP_park, SP_t0, SP_marker, SP_from, SP_len, SP_mon, SP_ridx, SP_lad, SP_log,
      SP_ctrl, SP_calls, SP_stale, SP_key, SP_ladM, SP_strict, SP_hole, SP_high,
      SP_mark, SP_tmax, SP_mbp, SP_pbp, SP_ops⟩
  have chain {α : Type} {a b c d e : α} (h1 : a = b) (h2 : b = c) (h3 : d = c) (h4 : e = d) :
      a = e := by rw [h1, h2, ← h3, ← h4]
  apply board_ext
  case hhome =>
    have hL := place_home_out bS dst ⟨hHdS, hDdS⟩ g (moves + 2 * pegCount (xs.take n)) pkS
    have hB : bS.sudo_5Board_4home =
        b.sudo_5Board_4home.set ⟨home, hin.hH⟩ (embed (xs.take n)) :=
      settle_home_eq b home ⟨hin.hH, hin.hD⟩ xs n moves slides peak
    have h1 := array_set_of_eq bS.sudo_5Board_4home _ hB dst hHdS (embed g)
    have h2 := array_set_irrel (b.sudo_5Board_4home.set ⟨home, hin.hH⟩ (embed (xs.take n))) dst
      (hB ▸ hHdS) (by rw [Array.size_set]; exact hHd) (embed g)
    have h3 := array_set_comm b.sudo_5Board_4home home dst hin.hH hHd
      (embed (xs.take n)) (embed g) hne
    have hP : bP.sudo_5Board_4home = b.sudo_5Board_4home.set ⟨dst, hHd⟩ (embed g) :=
      place_home_out b dst ⟨hHd, hDd⟩ g moves peak
    have hS := settle_home_eq bP home ⟨hHS, hDS⟩ xs n (moves + pegCount g) slides pkP
    have h4 := array_set_of_eq bP.sudo_5Board_4home _ hP home hHS (embed (xs.take n))
    have h5 := array_set_irrel (b.sudo_5Board_4home.set ⟨dst, hHd⟩ (embed g)) home
      (hP ▸ hHS) (by rw [Array.size_set]; exact hin.hH) (embed (xs.take n))
    rw [hL]
    exact ((h1.trans h2).trans h3).trans (h5.symm.trans (h4.symm.trans hS.symm))
  case hheld =>
    have hL := place_held_out bS dst ⟨hHdS, hDdS⟩ g (moves + 2 * pegCount (xs.take n)) pkS
    have hB : bS.sudo_5Board_4held = b.sudo_5Board_4held.set ⟨home, hin.hD⟩ true :=
      settle_held_eq b home ⟨hin.hH, hin.hD⟩ xs n moves slides peak
    have h1 := array_set_of_eq bS.sudo_5Board_4held _ hB dst hDdS true
    have h2 := array_set_irrel (b.sudo_5Board_4held.set ⟨home, hin.hD⟩ true) dst
      (hB ▸ hDdS) (by rw [Array.size_set]; exact hDd) true
    have h3 := array_set_comm b.sudo_5Board_4held home dst hin.hD hDd true true hne
    have hP : bP.sudo_5Board_4held = b.sudo_5Board_4held.set ⟨dst, hDd⟩ true :=
      place_held_out b dst ⟨hHd, hDd⟩ g moves peak
    have hS := settle_held_eq bP home ⟨hHS, hDS⟩ xs n (moves + pegCount g) slides pkP
    have h4 := array_set_of_eq bP.sudo_5Board_4held _ hP home hDS true
    have h5 := array_set_irrel (b.sudo_5Board_4held.set ⟨dst, hDd⟩ true) home
      (hP ▸ hDS) (by rw [Array.size_set]; exact hin.hD) true
    rw [hL]
    exact ((h1.trans h2).trans h3).trans (h5.symm.trans (h4.symm.trans hS.symm))
  case hon =>
    rw [place_on_out bS dst ⟨hHdS, hDdS⟩ g (moves + 2 * pegCount (xs.take n)) pkS,
      settle_bench_off b home ⟨hin.hH, hin.hD⟩ xs n moves slides peak,
      settle_bench_off bP home ⟨hHS, hDS⟩ xs n (moves + pegCount g) slides pkP]
  case ht => exact chain PS_t SB_t PB_t SP_t
  case hto => exact chain PS_to SB_to PB_to SP_to
  case hbench => exact chain PS_bench SB_bench PB_bench SP_bench
  case hphase => exact chain PS_phase SB_phase PB_phase SP_phase
  case hm0 => exact chain PS_m0 SB_m0 PB_m0 SP_m0
  case hpk => exact chain PS_pk SB_pk PB_pk SP_pk
  case hrow =>
    exact chain (place_row_out bS dst ⟨hHdS, hDdS⟩ g (moves + 2 * pegCount (xs.take n)) pkS)
      (settle_row_out b home ⟨hin.hH, hin.hD⟩ xs n moves slides peak)
      (place_row_out b dst ⟨hHd, hDd⟩ g moves peak)
      (settle_row_out bP home ⟨hHS, hDS⟩ xs n (moves + pegCount g) slides pkP)
  case hph => exact chain PS_ph SB_ph PB_ph SP_ph
  case hcall => exact chain PS_call SB_call PB_call SP_call
  case hl0 => exact chain PS_l0 SB_l0 PB_l0 SP_l0
  case hnr => exact chain PS_nr SB_nr PB_nr SP_nr
  case hpark => exact chain PS_park SB_park PB_park SP_park
  case ht0 => exact chain PS_t0 SB_t0 PB_t0 SP_t0
  case hmarker => exact chain PS_marker SB_marker PB_marker SP_marker
  case hfrom => exact chain PS_from SB_from PB_from SP_from
  case hlen => exact chain PS_len SB_len PB_len SP_len
  case hmon => exact chain PS_mon SB_mon PB_mon SP_mon
  case hridx => exact chain PS_ridx SB_ridx PB_ridx SP_ridx
  case hlad => exact chain PS_lad SB_lad PB_lad SP_lad
  case hlog => exact chain PS_log SB_log PB_log SP_log
  case hcost =>
    apply cost_ext
    case hmoves =>
      have hL := place_moves_out bS dst ⟨hHdS, hDdS⟩ g (moves + 2 * pegCount (xs.take n)) pkS
      have hR := settle_moves_eq bP home ⟨hHS, hDS⟩ xs n (moves + pegCount g) slides pkP
      rw [hL, hR]
      apply congrArg
      omega
    case hslides =>
      have hL := place_slides_out bS dst ⟨hHdS, hDdS⟩ g (moves + 2 * pegCount (xs.take n)) pkS
      have hS := settle_slides_eq b home ⟨hin.hH, hin.hD⟩ xs n moves slides peak
      have hR := settle_slides_eq bP home ⟨hHS, hDS⟩ xs n (moves + pegCount g) slides pkP
      rw [hL, hS, hR]
    case hpeak =>
      have hpkS : bS.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pkS := by
        simpa [pkS, c5, raisedPeak] using
          settle_peak_eq b home ⟨hin.hH, hin.hD⟩ xs n moves slides peak hpeak
      have hpkP : bP.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pkP := by
        simpa [pkP, c6, raisedPeak] using
          place_peak_out b dst ⟨hHd, hDd⟩ g moves peak hpeak
      rw [place_peak_out bS dst ⟨hHdS, hDdS⟩ g _ pkS hpkS,
        settle_peak_eq bP home ⟨hHS, hDS⟩ xs n (moves + pegCount g) slides pkP hpkP]
      have hcountS :
          countHeld (bS.sudo_5Board_4held.set ⟨dst, hDdS⟩ true) 7 = both := by
        have hh : bS.sudo_5Board_4held =
            b.sudo_5Board_4held.set ⟨home, hin.hD⟩ true :=
          settle_held_eq b home ⟨hin.hH, hin.hD⟩ xs n moves slides peak
        have h1 := countHeld_of_eq bS.sudo_5Board_4held _ hh dst hDdS 7
        refine h1.trans ?_
        apply countHeld_congr
        exact array_set_irrel _ dst (hh ▸ hDdS) (by rw [Array.size_set]; exact hDd) true
      have hcountP :
          countHeld (bP.sudo_5Board_4held.set ⟨home, hDS⟩ true) 7 = both := by
        have hh : bP.sudo_5Board_4held =
            b.sudo_5Board_4held.set ⟨dst, hDd⟩ true :=
          place_held_out b dst ⟨hHd, hDd⟩ g moves peak
        have h1 := countHeld_of_eq bP.sudo_5Board_4held _ hh home hDS 7
        have hleft := array_set_irrel (b.sudo_5Board_4held.set ⟨dst, hDd⟩ true) home
          (hh ▸ hDS) (by rw [Array.size_set]; exact hin.hD) true
        have hswap := array_set_comm b.sudo_5Board_4held dst home hDd hin.hD true true hne.symm
        exact (h1.trans (countHeld_congr _ _ hleft 7)).trans (countHeld_congr _ _ hswap 7)
      rw [hcountS, hcountP]
      apply congrArg Int.ofNat
      simpa [pkS, pkP, raisedPeak] using raised_both peak c5 c6 both hc5 hc6
    case hctrl => exact chain PS_ctrl SB_ctrl PB_ctrl SP_ctrl
    case hcalls => exact chain PS_calls SB_calls PB_calls SP_calls
    case hstale => exact chain PS_stale SB_stale PB_stale SP_stale
    case hkey => exact chain PS_key SB_key PB_key SP_key
    case hlad => exact chain PS_ladM SB_ladM PB_ladM SP_ladM
    case hstrict => exact chain PS_strict SB_strict PB_strict SP_strict
    case hhole => exact chain PS_hole SB_hole PB_hole SP_hole
    case hhigh => exact chain PS_high SB_high PB_high SP_high
    case hmark => exact chain PS_mark SB_mark PB_mark SP_mark
    case htally => exact chain PS_tmax SB_tmax PB_tmax SP_tmax
    case hmbp => exact chain PS_mbp SB_mbp PB_mbp SP_mbp
    case hpbp => exact chain PS_pbp SB_pbp PB_pbp SP_pbp
    case hops => exact chain PS_ops SB_ops PB_ops SP_ops

/-- After the gap has been slid home, `ClimbInv` holds for the same model with
    the bench flag off. Cost counters are not part of `ClimbInv`. -/
theorem climbInv_settled (b : Ecbs.Board) (s : ClimbModel)
    (h : ClimbInv b s) (_hon : s.onBench = true)
    (xs : List Nat) (moves slides peak : Nat)
    (_hxs : b.sudo_5Board_5bench = embed xs)
    (hgap : xs = s.gap.take s.n ++ List.replicate (s.benchlen - s.n) 0)
    (hlen : s.gap.length = s.n)
    (_hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (_hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (_hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak) :
    ClimbInv (settleBoard b 5 h.hG h.hGs xs s.n moves slides peak)
      { s with onBench := false } := by
  rcases settle_rest b 5 h.hG h.hGs xs s.n moves slides peak with
    ⟨_, _, _, _, _, _, _, _, _, _, S_park, _, _, S_from, S_len, _, S_ridx, _, _,
      _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  refine
    { hG := ?_
      hGs := ?_
      marker := ?_
      len := ?_
      ctrl := ?_
      high := ?_
      t0 := ?_
      row := ?_
      park := ?_
      fromP := ?_
      ridx := ?_
      gapHome := ?_
      gapBench := ?_ }
  · rw [settle_home_eq b 5 ⟨h.hG, h.hGs⟩ xs s.n moves slides peak, Array.size_set]; exact h.hG
  · rw [settle_held_eq b 5 ⟨h.hG, h.hGs⟩ xs s.n moves slides peak, Array.size_set]; exact h.hGs
  · rw [settle_marker_eq b 5 ⟨h.hG, h.hGs⟩ xs s.n moves slides peak]; exact h.marker
  · exact S_len.trans h.len
  · rw [settle_ctrl_eq b 5 ⟨h.hG, h.hGs⟩ xs s.n moves slides peak]; exact h.ctrl
  · rw [settle_high_eq b 5 ⟨h.hG, h.hGs⟩ xs s.n moves slides peak]; exact h.high
  · rw [settle_tally_eq b 5 ⟨h.hG, h.hGs⟩ xs s.n moves slides peak]; exact h.t0
  · rw [settle_row_out b 5 ⟨h.hG, h.hGs⟩ xs s.n moves slides peak]; exact h.row
  · exact S_park.trans h.park
  · exact S_from.trans h.fromP
  · exact S_ridx.trans h.ridx
  · intro _
    refine ⟨?_, ?_⟩
    · have hh := settle_held_eq b 5 ⟨h.hG, h.hGs⟩ xs s.n moves slides peak
      have hsz := settle_held_lt b 5 ⟨h.hG, h.hGs⟩ xs s.n moves slides peak
      rw [idx_get hh 5 hsz]
      simp [Array.getElem_set]
    · have hh := settle_home_eq b 5 ⟨h.hG, h.hGs⟩ xs s.n moves slides peak
      have hsz := settle_home_lt b 5 ⟨h.hG, h.hGs⟩ xs s.n moves slides peak
      rw [idx_get hh 5 hsz]
      simp [Array.getElem_set, hgap, gap_slide_take s.gap s.n s.benchlen hlen]
  · intro hOn
    simp at hOn

/-- `settle` does not write `tally_max`. -/
theorem settle_tmax_eq (b : Ecbs.Board) (home : Nat)
    (hin : HomeIn b home)
    (xs : List Nat) (n moves slides peak : Nat) :
    (settleBoard b home hin.hH hin.hD xs n moves slides peak).sudo_5Board_4cost.sudo_5Costs_9tally_max =
      b.sudo_5Board_4cost.sudo_5Costs_9tally_max := by
  by_cases hpk : peak < countHeld (b.sudo_5Board_4held.set ⟨home, hin.hD⟩ true) 7
  · rw [settle_peak b home ⟨hin.hH, hin.hD⟩ xs n moves slides peak hpk]
  · rw [settle_keep b home ⟨hin.hH, hin.hD⟩ xs n moves slides peak hpk]

/-- The park read survives a slide into home 5. It reads the row, the control
    counter, the parked hole, and the rung index. `settle` writes none of them.
    `climb_holes` reads only `ladder0` and `nrungs`, which the slide also leaves. -/
theorem parkRead_slideGap {b : Ecbs.Board} {s : ClimbModel} {rest : List Nat}
    {base : ClimbBudget} (h : ParkRead b s rest base)
    (xs : List Nat) (n moves slides peak : Nat)
    (h5H : 5 < b.sudo_5Board_4home.size) (h5D : 5 < b.sudo_5Board_4held.size) :
    ParkRead (settleBoard b 5 h5H h5D xs n moves slides peak)
      { s with onBench := false } rest base := by
  let bS := settleBoard b 5 h5H h5D xs n moves slides peak
  obtain ⟨_, _, _, _, _, _, _, _, hl0, hnr, _⟩ :=
    settle_rest b 5 h5H h5D xs n moves slides peak
  have hclimb : Ecbs.climb_holes bS = Ecbs.climb_holes b := by
    unfold Ecbs.climb_holes
    rw [hl0, hnr]
  refine
    { ladder0B := hl0.trans h.ladder0B
      nrungsB := hnr.trans h.nrungsB
      climbH := hclimb.trans h.climbH
      holeLt := h.holeLt
      parkLt := h.parkLt
      parkNe := h.parkNe
      parkLe := h.parkLe
      parkIn := h.parkIn
      parkCell := h.parkCell
      fromIdle := h.fromIdle
      fromNat := h.fromNat
      srcOk := h.srcOk
      parkHeld := h.parkHeld
      nextRung := h.nextRung
      ladderTail := h.ladderTail
      fit2 := h.fit2
      fit4 := h.fit4
      fitI := h.fitI
      l0pos := h.l0pos
      fitL0 := h.fitL0
      fitLR := h.fitLR }

/-- The peg read survives a slide into home 5. Ops, the strict peak, and the
    recorded bench hole are not among the counters `settle` writes. The gap's
    trits are the model's, not a home-5 read. -/
theorem pegRead_slideGap {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : PegRead b s base)
    (xs : List Nat) (n moves slides peak : Nat)
    (h5H : 5 < b.sudo_5Board_4home.size) (h5D : 5 < b.sudo_5Board_4held.size) :
    PegRead (settleBoard b 5 h5H h5D xs n moves slides peak)
      { s with onBench := false } base := by
  let bS := settleBoard b 5 h5H h5D xs n moves slides peak
  have hopsEq := settle_ops b 5 ⟨h5H, h5D⟩ xs n moves slides peak
  have hstrict := settle_strict_eq b 5 ⟨h5H, h5D⟩ xs n moves slides peak
  have hhole := settle_hole_eq b 5 ⟨h5H, h5D⟩ xs n moves slides peak
  obtain ⟨c, hc⟩ := h.cOps
  obtain ⟨p, hp⟩ := h.peakS
  obtain ⟨hn, hh⟩ := h.holeM
  refine
    { opsGt := by rw [hopsEq]; exact h.opsGt
      cOps := ⟨c, by
        have hsz : 1 < bS.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
          rw [hopsEq]; exact h.opsGt
        exact (idx_get hopsEq 1 hsz).trans hc⟩
      peakS := ⟨p, hstrict.trans hp⟩
      holeM := ⟨hn, hhole.trans hh⟩
      trits := h.trits
      top := h.top
      fitRow := h.fitRow
      fitTall := h.fitTall
      fitCtrl := h.fitCtrl
      n_pos := h.n_pos
      span := h.span
      small := h.small
      n_small := h.n_small
      fitN := h.fitN
      fitBn := h.fitBn
      fit3 := h.fit3 }

/-- `ClimbShape` after `slideGap`. `settle` writes home 5's array and held flag,
    turns the bench off, and updates the move, slide, and peak counters. The
    park read and the peg read do not use those fields. Home 5 being clear is
    the bench-on obligation; after the slide the model is bench-off, so that
    obligation is gone, and the bench-off obligation is the flag `settle` writes. -/
theorem climbShape_slideGap {b : Ecbs.Board} {s : ClimbModel} {rest : List Nat}
    {base : ClimbBudget} (h : ClimbShape b s rest base) (_hon : s.onBench = true)
    (xs : List Nat) (moves slides peak : Nat) :
    let h5H := Nat.lt_trans (by decide : (5 : Nat) < 6) h.spareH
    let h5D := Nat.lt_of_lt_of_le (by decide : (5 : Nat) < 7) h.h7
    ClimbShape (settleBoard b 5 h5H h5D xs s.n moves slides peak)
      { s with onBench := false } rest base := by
  intro h5H h5D
  let bS := settleBoard b 5 h5H h5D xs s.n moves slides peak
  let s' : ClimbModel := { s with onBench := false }
  have hHeld := settle_held_eq b 5 ⟨h5H, h5D⟩ xs s.n moves slides peak
  have hHome := settle_home_eq b 5 ⟨h5H, h5D⟩ xs s.n moves slides peak
  have htier := settle_tier_eq b 5 ⟨h5H, h5D⟩ xs s.n moves slides peak
  have h6 : 6 < bS.sudo_5Board_4held.size := by
    rw [hHeld, Array.size_set]; exact h.spareD
  have h6H : 6 < bS.sudo_5Board_4home.size := by
    rw [hHome, Array.size_set]; exact h.spareH
  have hxD : base.xHome < bS.sudo_5Board_4held.size := by
    rw [hHeld, Array.size_set]; exact h.xD
  have hxH : base.xHome < bS.sudo_5Board_4home.size := by
    rw [hHome, Array.size_set]; exact h.xH
  refine
    { spareH := h6H
      spareD := h6
      spareE := by
        rw [idx_get hHeld 6 h6, Array.getElem_set, if_neg (by decide : (5 : Nat) ≠ 6)]
        exact h.spareE
      h7 := by rw [hHeld, Array.size_set]; exact h.h7
      gapClear := by
        intro hOn
        simp at hOn
      offWhenHome := by
        intro _
        exact settle_bench_off b 5 ⟨h5H, h5D⟩ xs s.n moves slides peak
      xD := hxD
      xH := hxH
      xHeld := by
        rw [idx_get hHeld base.xHome hxD, Array.getElem_set, if_neg (Ne.symm h.xNe5)]
        exact h.xHeld
      xArr := by
        rw [idx_get hHome base.xHome hxH, Array.getElem_set, if_neg (Ne.symm h.xNe5)]
        exact h.xArr
      xNe5 := h.xNe5
      xNe6 := h.xNe6
      gapLen := h.gapLen
      seg := h.seg
      tierN := by rw [htier]; exact h.tierN
      tierK := by rw [htier]; exact h.tierK
      tierB := by rw [htier]; exact h.tierB
      tierW := by rw [htier]; exact h.tierW
      tierH := by rw [htier]; exact h.tierH
      tierR := by rw [htier]; exact h.tierR
      tierCg := by rw [htier]; exact h.tierCg
      tierC := by rw [htier]; exact h.tierC
      rowLen := h.rowLen
      w0 := h.w0
      h0 := h.h0
      r0 := h.r0
      rlt := h.rlt
      n_eq := h.n_eq
      k_le := h.k_le
      gap_eq := h.gap_eq
      side := side_settle h.side 5 ⟨h5H, h5D⟩ xs s.n moves slides peak
        (by decide) (by decide) (by decide) (by decide)
      quiet := quiet_settle h.quiet 5 ⟨h5H, h5D⟩ xs s.n moves slides peak
      park := parkRead_slideGap h.park xs s.n moves slides peak h5H h5D
      peg := pegRead_slideGap h.peg xs s.n moves slides peak h5H h5D }

/-- The core invariant on the slid board. Moves and slides are not fields of
    the core. Ops are copied. The peak stays `max(previous, 7)`. -/
theorem climbCore_slideGap {done rest : List Nat} {b : Ecbs.Board}
    {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvKCore done rest b s base) (hon : s.onBench = true)
    (xs : List Nat) (moves slides peak : Nat)
    (hmv : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hsl : b.sudo_5Board_4cost.sudo_5Costs_6slides = (slides : Int))
    (hpk : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hxs : b.sudo_5Board_5bench = embed xs)
    (hgap : xs = s.gap.take s.n ++ List.replicate (s.benchlen - s.n) 0) :
    let h5H := Nat.lt_trans (by decide : (5 : Nat) < 6) h.shape.spareH
    let h5D := Nat.lt_of_lt_of_le (by decide : (5 : Nat) < 7) h.shape.h7
    ClimbInvKCore done rest (settleBoard b 5 h5H h5D xs s.n moves slides peak)
      { s with onBench := false } base := by
  intro h5H h5D
  let bS := settleBoard b 5 h5H h5D xs s.n moves slides peak
  have hshape : ClimbShape bS { s with onBench := false } rest base :=
    climbShape_slideGap h.shape hon xs moves slides peak
  have hmvI : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves := by
    rw [hmv, ofNat_eq_natCast]
  have hslI : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides := by
    rw [hsl, ofNat_eq_natCast]
  have hpkI : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak := by
    rw [hpk, ofNat_eq_natCast]
  have hinv0 := climbInv_settled b s h.inv hon xs moves slides peak hxs hgap h.shape.gapLen
    hmvI hslI hpkI
  have hboard :=
    settleBoard_irrel b 5 h.inv.hG h5H h.inv.hGs h5D xs s.n moves slides peak
  have hinv : ClimbInv bS { s with onBench := false } := by
    rw [hboard] at hinv0
    simpa [bS] using hinv0
  obtain ⟨pk0, hpk0, hpkLe⟩ := h.peak
  have hpkN : peak = pk0 := ofNat_inj_nat (hpk.symm.trans hpk0)
  let occ := countHeld (b.sudo_5Board_4held.set ⟨5, h5D⟩ true) 7
  have hpeakS := settle_peak_eq b 5 ⟨h5H, h5D⟩ xs s.n moves slides peak hpkI
  refine
    { inv := hinv
      idx := h.idx
      hn := h.hn
      hbench := h.hbench
      htally0 := h.htally0
      kLe := h.kLe
      shape := hshape
      ops := by
        intro i hi
        have hi0 : i < b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
          rw [← settle_ops b 5 ⟨h5H, h5D⟩ xs s.n moves slides peak]; exact hi
        obtain ⟨c, hc, hle⟩ := h.ops i hi0
        refine ⟨c, ?_, hle⟩
        have hopsEq := settle_ops b 5 ⟨h5H, h5D⟩ xs s.n moves slides peak
        exact (idx_get hopsEq i hi).trans hc
      peak := by
        let pk' := if peak < occ then occ else peak
        have hocc : occ ≤ 7 := countHeld_seven _
        have hle := settle_peak_le peak occ hocc
        refine ⟨pk', hpeakS, ?_⟩
        have hpk' : pk' ≤ max pk0 7 := by
          simpa [pk', hpkN] using hle
        exact peak_carry base.peak0 pk0 pk' hpkLe hpk'
      strictLe := by
        obtain ⟨ps, hps, hle⟩ := h.strictLe
        refine ⟨ps, ?_, hle⟩
        rw [settle_strict_eq b 5 ⟨h5H, h5D⟩ xs s.n moves slides peak]
        exact hps
      holeLe := by
        obtain ⟨ho, hho, hle⟩ := h.holeLe
        refine ⟨ho, ?_, hle⟩
        rw [settle_hole_eq b 5 ⟨h5H, h5D⟩ xs s.n moves slides peak]
        exact hho
      highTop := h.highTop
      parkBelow := h.parkBelow
      holeBelow := h.holeBelow
      fromBelow := h.fromBelow
      finalLe := h.finalLe
      tailFit := h.tailFit
      tailZero := h.tailZero
      openRoom := h.openRoom
      openZero := h.openZero
      tmaxLt := by
        obtain ⟨tmax, ht⟩ := h.tmaxLt
        refine ⟨tmax, ?_⟩
        rw [settle_tmax_eq b 5 ⟨h5H, h5D⟩ xs s.n moves slides peak, ht]
      ctrlLe := h.ctrlLe
      srcAbove := h.srcAbove
      parkEq := h.parkEq
      origin := h.origin
      fromNePark := h.fromNePark
      rowHome := h.rowHome
      blankTail := h.blankTail }

/-- The padded bench list has length `bench` once `n ≤ bench`. -/
theorem bench_pad_len (gap : List Nat) (n bench : Nat)
    (hlen : gap.length = n) (hnle : n ≤ bench) :
    (gap.take n ++ List.replicate (bench - n) 0).length = bench := by
  simp only [List.length_append, List.length_take, List.length_replicate, hlen,
    Nat.min_eq_left (Nat.le_refl n)]
  omega

/-- Entries at or past `n` in that pad are zero. -/
theorem bench_pad_zero (gap : List Nat) (n bench : Nat)
    (hlen : gap.length = n) (_hnle : n ≤ bench) :
    let xs := gap.take n ++ List.replicate (bench - n) 0
    ∀ i, n ≤ i → ∀ hi : i < xs.length, xs[i] = 0 := by
  intro xs i hi hix
  have hpre : (gap.take n).length = n := by
    rw [List.length_take, hlen, Nat.min_eq_left (Nat.le_refl _)]
  have hge : (gap.take n).length ≤ i := by
    rw [hpre]
    exact hi
  rw [List.getElem_append_right hge, List.getElem_replicate]

/-- `slideGap` is the emitted `settle` of a bench-on gap. The slid value is the
    bench prefix, and the move and slide fits are the tight headroom on
    `mv + 2 · pegs`. -/
theorem slideGap_run
    {done rest : List Nat} {r : Nat} {b : Ecbs.Board} {s : ClimbModel}
    {base : ClimbBudget}
    (h : ClimbInvK done (r :: rest) b s base) (hon : s.onBench = true) :
    let xs := s.gap.take s.n ++ List.replicate (s.benchlen - s.n) 0
    ∃ (moves slides peak : Nat),
      let h5H := Nat.lt_trans (by decide : (5 : Nat) < 6) h.shape.spareH
      let h5D := Nat.lt_of_lt_of_le (by decide : (5 : Nat) < 7) h.shape.h7
      b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int) ∧
      b.sudo_5Board_4cost.sudo_5Costs_6slides = (slides : Int) ∧
      b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int) ∧
      b.sudo_5Board_5bench = embed xs ∧
      slideGap b = .ok (settleBoard b 5 h5H h5D xs s.n moves slides peak) := by
  intro xs
  obtain ⟨moves, hmv, hmvLe⟩ := h.moves
  obtain ⟨slides, hsl, hslLe⟩ := h.slides
  have hmvRes : moves + 2 * base.n ≤
      base.moves0 + done.length * rungCharge base.n base.bench base.mMax := by
    simpa [hon] using hmvLe
  have hslRes : slides + 2 * base.n ≤
      base.slides0 + done.length * rungSlideCharge base.n base.mMax := by
    simpa [hon] using hslLe
  obtain ⟨peak, hpk, _hpkLe⟩ := h.peak
  refine ⟨moves, slides, peak, ?_⟩
  intro h5H h5D
  have hg := h.inv.gapBench hon
  have hxs : b.sudo_5Board_5bench = embed xs := by
    simpa [xs] using hg.2.2.1
  have hnleB : s.n ≤ s.benchlen := by
    have hsp := h.shape.peg.span
    omega
  have hlenX : xs.length = s.benchlen :=
    bench_pad_len s.gap s.n s.benchlen h.shape.gapLen hnleB
  have hpos : 0 < xs.length := by
    rw [hlenX]
    exact Nat.lt_of_lt_of_le h.shape.peg.n_pos hnleB
  have hnle : s.n ≤ xs.length := by
    rw [hlenX]
    exact hnleB
  have hzero : ∀ i, s.n ≤ i → ∀ hi : i < xs.length, xs[i] = 0 :=
    bench_pad_zero s.gap s.n s.benchlen h.shape.gapLen hnleB
  have hmvI : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves := by
    rw [hmv, ofNat_eq_natCast]
  have hslI : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides := by
    rw [hsl, ofNat_eq_natCast]
  have hpkI : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak := by
    rw [hpk, ofNat_eq_natCast]
  have hpegs : pegCount (xs.take s.n) ≤ base.n := by
    rw [← h.hn]
    exact pegCount_take_le xs s.n
  have hk : done.length + 1 ≤ base.R := by
    have hlen := h.kLe
    simp [List.length_append, List.length_cons] at hlen
    omega
  have hroomM := bench_headroom_of base.moves0 base.R done.length base.n base.bench
    base.mMax moves (pegCount (xs.take s.n)) hk hmvRes hpegs base.fitM
  have hroomS := bench_slide_headroom_of base.slides0 base.R done.length base.n
    base.mMax slides (pegCount (xs.take s.n)) hk hslRes hpegs base.fitS
  have hfitM : FitsLen (moves + 2 * pegCount (xs.take s.n)) :=
    FitsLen.of_le hroomM (Nat.le_add_right _ _)
  have hfitS : FitsLen (slides + 2 * pegCount (xs.take s.n)) :=
    FitsLen.of_le hroomS (Nat.le_add_right _ _)
  have hpegF : FitsLen (2 * pegCount (xs.take s.n)) :=
    FitsLen.of_le hfitM (Nat.le_add_left _ _)
  have hempty : b.sudo_5Board_4held[5]'h5D = false := by
    have hclear := h.shape.gapClear hon
    exact (get_proof_irrel b.sudo_5Board_4held 5 h5D
      (Nat.lt_of_lt_of_le (by decide : (5 : Nat) < 7) h.shape.h7)).trans hclear
  have hrun := settle_refines b 5 xs s.n moves slides peak h5H h5D h.shape.h7
    hg.1 hg.2.1 hempty hxs h.shape.tierN hpos hnle hzero h.shape.peg.fitN
    (by rw [hlenX]; exact h.shape.peg.fitBn) hmvI hslI hpkI hpegF hfitM hfitS
  exact ⟨hmv, hsl, hpk, hxs, by simpa [slideGap] using hrun⟩

/-- Rewriting the board under `parkKeep` rewrites the row-size proofs with it. -/
theorem parkKeep_cast
    {b1 b2 : Ecbs.Board} (h : b1 = b2) (hole park rung i ctrl : Nat)
    (hRowP : park < b1.sudo_5Board_3row.size)
    (hRowH : hole < b1.sudo_5Board_3row.size) :
    parkKeepBoard b1 hole park rung i ctrl hRowP hRowH =
      parkKeepBoard b2 hole park rung i ctrl (h ▸ hRowP) (h ▸ hRowH) := by
  subst h
  rfl

/-- `parkKeep` and `settle` write different fields, so they commute. The row
    proofs on the slid board are the original ones, transported along
    `settleBoard_row`. -/
theorem parkKeep_settle_comm
    (b : Ecbs.Board) (hole park rung i ctrl home : Nat)
    (hRowP : park < b.sudo_5Board_3row.size)
    (hRowH : hole < b.sudo_5Board_3row.size)
    (hH : home < b.sudo_5Board_4home.size)
    (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (n moves slides peak : Nat) :
    parkKeepBoard (settleBoard b home hH hD xs n moves slides peak)
        hole park rung i ctrl
        (settleBoard_row b home ⟨hH, hD⟩ xs n moves slides peak ▸ hRowP)
        (settleBoard_row b home ⟨hH, hD⟩ xs n moves slides peak ▸ hRowH) =
      settleBoard (parkKeepBoard b hole park rung i ctrl hRowP hRowH)
        home
        (parkKeep_home b hole park rung i ctrl hRowP hRowH ▸ hH)
        (parkKeep_held b hole park rung i ctrl hRowP hRowH ▸ hD)
        xs n moves slides peak := by
  let bK := parkKeepBoard b hole park rung i ctrl hRowP hRowH
  let hHK : home < bK.sudo_5Board_4home.size :=
    parkKeep_home b hole park rung i ctrl hRowP hRowH ▸ hH
  let hDK : home < bK.sudo_5Board_4held.size :=
    parkKeep_held b hole park rung i ctrl hRowP hRowH ▸ hD
  by_cases hpk : peak < countHeld (b.sudo_5Board_4held.set ⟨home, hD⟩ true) 7
  · have hheld : bK.sudo_5Board_4held = b.sudo_5Board_4held :=
      parkKeep_held b hole park rung i ctrl hRowP hRowH
    have hset := (array_set_of_eq bK.sudo_5Board_4held b.sudo_5Board_4held hheld
      home hDK true).trans (array_set_irrel b.sudo_5Board_4held home (hheld ▸ hDK) hD true)
    have hpkK : peak < countHeld (bK.sudo_5Board_4held.set ⟨home, hDK⟩ true) 7 := by
      rw [countHeld_congr _ _ hset 7]
      exact hpk
    have hS := settleBoard_pos b home ⟨hH, hD⟩ xs n moves slides peak hpk
    have hrow := settleBoard_row b home ⟨hH, hD⟩ xs n moves slides peak
    have hL : parkKeepBoard (settleBoard b home hH hD xs n moves slides peak)
        hole park rung i ctrl (hrow ▸ hRowP) (hrow ▸ hRowH) =
        parkKeepBoard ({ b with
          sudo_5Board_4home := b.sudo_5Board_4home.set ⟨home, hH⟩ (embed (xs.take n))
          sudo_5Board_4held := b.sudo_5Board_4held.set ⟨home, hD⟩ true
          sudo_5Board_8bench_on := false
          sudo_5Board_4cost := { b.sudo_5Board_4cost with
            sudo_5Costs_5moves := Int.ofNat (moves + 2 * pegCount (xs.take n))
            sudo_5Costs_6slides := Int.ofNat (slides + 2 * pegCount (xs.take n))
            sudo_5Costs_4peak :=
              Int.ofNat (countHeld (b.sudo_5Board_4held.set ⟨home, hD⟩ true) 7) } })
          hole park rung i ctrl hRowP hRowH := by
      rw [parkKeep_cast hS hole park rung i ctrl (hrow ▸ hRowP) (hrow ▸ hRowH)]
    rw [hL, parkKeep_settled_pos b hole park rung i ctrl home hRowP hRowH hH hD
      xs n moves slides peak hpk]
    rw [settleBoard_pos bK home ⟨hHK, hDK⟩ xs n moves slides peak hpkK]
    apply board_ext
    · simp [bK, parkKeepBoard]
    · simp [bK, parkKeepBoard]
    · simp [bK, parkKeepBoard]
    · simp [bK, parkKeepBoard]
    · simp [bK, parkKeepBoard]
    · simp [bK, parkKeepBoard]
    · apply cost_ext <;> first
        | exact congrArg Int.ofNat (countHeld_congr _ _ hset 7)
        | simp [bK, parkKeepBoard, ofNat_eq_natCast]
    · simp [bK, parkKeepBoard]
    · simp [bK, parkKeepBoard]
    · simp [bK, parkKeepBoard]
    · simp [bK, parkKeepBoard]
    · simp [bK, parkKeepBoard]
    · simp [bK, parkKeepBoard]
    · simp [bK, parkKeepBoard]
    · simp [bK, parkKeepBoard]
    · simp [bK, parkKeepBoard]
    · simp [bK, parkKeepBoard]
    · simp [bK, parkKeepBoard]
    · simp [bK, parkKeepBoard]
    · simp [bK, parkKeepBoard]
    · simp [bK, parkKeepBoard]
    · simp [bK, parkKeepBoard]
    · simp [bK, parkKeepBoard]
    · simp [bK, parkKeepBoard]
  · have hheld : bK.sudo_5Board_4held = b.sudo_5Board_4held :=
      parkKeep_held b hole park rung i ctrl hRowP hRowH
    have hset := (array_set_of_eq bK.sudo_5Board_4held b.sudo_5Board_4held hheld
      home hDK true).trans (array_set_irrel b.sudo_5Board_4held home (hheld ▸ hDK) hD true)
    have hpkK : ¬ peak < countHeld (bK.sudo_5Board_4held.set ⟨home, hDK⟩ true) 7 := by
      rw [countHeld_congr _ _ hset 7]
      exact hpk
    have hS := settleBoard_neg b home ⟨hH, hD⟩ xs n moves slides peak hpk
    have hrow := settleBoard_row b home ⟨hH, hD⟩ xs n moves slides peak
    have hL : parkKeepBoard (settleBoard b home hH hD xs n moves slides peak)
        hole park rung i ctrl (hrow ▸ hRowP) (hrow ▸ hRowH) =
        parkKeepBoard ({ b with
          sudo_5Board_4home := b.sudo_5Board_4home.set ⟨home, hH⟩ (embed (xs.take n))
          sudo_5Board_4held := b.sudo_5Board_4held.set ⟨home, hD⟩ true
          sudo_5Board_8bench_on := false
          sudo_5Board_4cost := { b.sudo_5Board_4cost with
            sudo_5Costs_5moves := Int.ofNat (moves + 2 * pegCount (xs.take n))
            sudo_5Costs_6slides := Int.ofNat (slides + 2 * pegCount (xs.take n)) } })
          hole park rung i ctrl hRowP hRowH := by
      rw [parkKeep_cast hS hole park rung i ctrl (hrow ▸ hRowP) (hrow ▸ hRowH)]
    rw [hL, parkKeep_settled_neg b hole park rung i ctrl home hRowP hRowH hH hD
      xs n moves slides peak hpk]
    rw [settleBoard_neg bK home ⟨hHK, hDK⟩ xs n moves slides peak hpkK]
    apply board_ext
    · simp [bK, parkKeepBoard]
    · simp [bK, parkKeepBoard]
    · simp [bK, parkKeepBoard]
    · simp [bK, parkKeepBoard]
    · simp [bK, parkKeepBoard]
    · simp [bK, parkKeepBoard]
    · apply cost_ext <;> simp [bK, parkKeepBoard, ofNat_eq_natCast]
    · simp [bK, parkKeepBoard]
    · simp [bK, parkKeepBoard]
    · simp [bK, parkKeepBoard]
    · simp [bK, parkKeepBoard]
    · simp [bK, parkKeepBoard]
    · simp [bK, parkKeepBoard]
    · simp [bK, parkKeepBoard]
    · simp [bK, parkKeepBoard]
    · simp [bK, parkKeepBoard]
    · simp [bK, parkKeepBoard]
    · simp [bK, parkKeepBoard]
    · simp [bK, parkKeepBoard]
    · simp [bK, parkKeepBoard]
    · simp [bK, parkKeepBoard]
    · simp [bK, parkKeepBoard]
    · simp [bK, parkKeepBoard]
    · simp [bK, parkKeepBoard]

/-- `unpark` writes the control row, `parked_from`, and the control counter.
    It does not read the home array or the bench, so it commutes with `settle`. -/
theorem unparked_home (b : Ecbs.Board) (src park prev ctrl : Nat)
    (hRowS : src < b.sudo_5Board_3row.size) (hRowP : park < b.sudo_5Board_3row.size) :
    (unparkedBoard b src park prev ctrl hRowS hRowP).sudo_5Board_4home =
      b.sudo_5Board_4home := by
  simp [unparkedBoard]

theorem unparked_held (b : Ecbs.Board) (src park prev ctrl : Nat)
    (hRowS : src < b.sudo_5Board_3row.size) (hRowP : park < b.sudo_5Board_3row.size) :
    (unparkedBoard b src park prev ctrl hRowS hRowP).sudo_5Board_4held =
      b.sudo_5Board_4held := by
  simp [unparkedBoard]

theorem unparked_cast
    {b1 b2 : Ecbs.Board} (h : b1 = b2) (src park prev ctrl : Nat)
    (hRowS : src < b1.sudo_5Board_3row.size) (hRowP : park < b1.sudo_5Board_3row.size) :
    unparkedBoard b1 src park prev ctrl hRowS hRowP =
      unparkedBoard b2 src park prev ctrl (h ▸ hRowS) (h ▸ hRowP) := by
  subst h
  rfl

theorem unparked_settled_pos
    (b : Ecbs.Board) (src park prev ctrl home : Nat)
    (hRowS : src < b.sudo_5Board_3row.size) (hRowP : park < b.sudo_5Board_3row.size)
    (hin : HomeIn b home)
    (xs : List Nat) (n moves slides peak : Nat)
    (_hpk : peak < countHeld (b.sudo_5Board_4held.set ⟨home, hin.hD⟩ true) 7) :
    unparkedBoard
        ({ b with
          sudo_5Board_4home := b.sudo_5Board_4home.set ⟨home, hin.hH⟩ (embed (xs.take n))
          sudo_5Board_4held := b.sudo_5Board_4held.set ⟨home, hin.hD⟩ true
          sudo_5Board_8bench_on := false
          sudo_5Board_4cost := { b.sudo_5Board_4cost with
            sudo_5Costs_5moves := Int.ofNat (moves + 2 * pegCount (xs.take n))
            sudo_5Costs_6slides := Int.ofNat (slides + 2 * pegCount (xs.take n))
            sudo_5Costs_4peak :=
              Int.ofNat (countHeld (b.sudo_5Board_4held.set ⟨home, hin.hD⟩ true) 7) } })
        src park prev ctrl hRowS hRowP =
      { unparkedBoard b src park prev ctrl hRowS hRowP with
        sudo_5Board_4home := b.sudo_5Board_4home.set ⟨home, hin.hH⟩ (embed (xs.take n))
        sudo_5Board_4held := b.sudo_5Board_4held.set ⟨home, hin.hD⟩ true
        sudo_5Board_8bench_on := false
        sudo_5Board_4cost :=
          { (unparkedBoard b src park prev ctrl hRowS hRowP).sudo_5Board_4cost with
            sudo_5Costs_5moves := Int.ofNat (moves + 2 * pegCount (xs.take n))
            sudo_5Costs_6slides := Int.ofNat (slides + 2 * pegCount (xs.take n))
            sudo_5Costs_4peak :=
              Int.ofNat (countHeld (b.sudo_5Board_4held.set ⟨home, hin.hD⟩ true) 7) } } := by
  unfold unparkedBoard
  simp [ofNat_eq_natCast]

theorem unparked_settled_neg
    (b : Ecbs.Board) (src park prev ctrl home : Nat)
    (hRowS : src < b.sudo_5Board_3row.size) (hRowP : park < b.sudo_5Board_3row.size)
    (hin : HomeIn b home)
    (xs : List Nat) (n moves slides peak : Nat)
    (_hpk : ¬ peak < countHeld (b.sudo_5Board_4held.set ⟨home, hin.hD⟩ true) 7) :
    unparkedBoard
        ({ b with
          sudo_5Board_4home := b.sudo_5Board_4home.set ⟨home, hin.hH⟩ (embed (xs.take n))
          sudo_5Board_4held := b.sudo_5Board_4held.set ⟨home, hin.hD⟩ true
          sudo_5Board_8bench_on := false
          sudo_5Board_4cost := { b.sudo_5Board_4cost with
            sudo_5Costs_5moves := Int.ofNat (moves + 2 * pegCount (xs.take n))
            sudo_5Costs_6slides := Int.ofNat (slides + 2 * pegCount (xs.take n)) } })
        src park prev ctrl hRowS hRowP =
      { unparkedBoard b src park prev ctrl hRowS hRowP with
        sudo_5Board_4home := b.sudo_5Board_4home.set ⟨home, hin.hH⟩ (embed (xs.take n))
        sudo_5Board_4held := b.sudo_5Board_4held.set ⟨home, hin.hD⟩ true
        sudo_5Board_8bench_on := false
        sudo_5Board_4cost :=
          { (unparkedBoard b src park prev ctrl hRowS hRowP).sudo_5Board_4cost with
            sudo_5Costs_5moves := Int.ofNat (moves + 2 * pegCount (xs.take n))
            sudo_5Costs_6slides := Int.ofNat (slides + 2 * pegCount (xs.take n)) } } := by
  unfold unparkedBoard
  simp [ofNat_eq_natCast]

/-- The parked source is a control-row index strictly before the tally.
    `unpark` writes that row slot. `settle` writes home 5, a different array. -/
theorem unparked_settle_comm
    (b : Ecbs.Board) (src park prev ctrl home : Nat)
    (hRowS : src < b.sudo_5Board_3row.size) (hRowP : park < b.sudo_5Board_3row.size)
    (hin : HomeIn b home)
    (xs : List Nat) (n moves slides peak : Nat) :
    unparkedBoard (settleBoard b home hin.hH hin.hD xs n moves slides peak)
        src park prev ctrl
        (settleBoard_row b home ⟨hin.hH, hin.hD⟩ xs n moves slides peak ▸ hRowS)
        (settleBoard_row b home ⟨hin.hH, hin.hD⟩ xs n moves slides peak ▸ hRowP) =
      settleBoard (unparkedBoard b src park prev ctrl hRowS hRowP)
        home
        (unparked_home b src park prev ctrl hRowS hRowP ▸ hin.hH)
        (unparked_held b src park prev ctrl hRowS hRowP ▸ hin.hD)
        xs n moves slides peak := by
  let bU := unparkedBoard b src park prev ctrl hRowS hRowP
  let hHU : home < bU.sudo_5Board_4home.size :=
    unparked_home b src park prev ctrl hRowS hRowP ▸ hin.hH
  let hDU : home < bU.sudo_5Board_4held.size :=
    unparked_held b src park prev ctrl hRowS hRowP ▸ hin.hD
  by_cases hpk : peak < countHeld (b.sudo_5Board_4held.set ⟨home, hin.hD⟩ true) 7
  · have hheld : bU.sudo_5Board_4held = b.sudo_5Board_4held :=
      unparked_held b src park prev ctrl hRowS hRowP
    have hset := (array_set_of_eq bU.sudo_5Board_4held b.sudo_5Board_4held hheld
      home hDU true).trans (array_set_irrel b.sudo_5Board_4held home (hheld ▸ hDU) hin.hD true)
    have hpkU : peak < countHeld (bU.sudo_5Board_4held.set ⟨home, hDU⟩ true) 7 := by
      rw [countHeld_congr _ _ hset 7]
      exact hpk
    have hS := settleBoard_pos b home ⟨hin.hH, hin.hD⟩ xs n moves slides peak hpk
    have hrow := settleBoard_row b home ⟨hin.hH, hin.hD⟩ xs n moves slides peak
    have hL : unparkedBoard (settleBoard b home hin.hH hin.hD xs n moves slides peak)
        src park prev ctrl (hrow ▸ hRowS) (hrow ▸ hRowP) =
        unparkedBoard ({ b with
          sudo_5Board_4home := b.sudo_5Board_4home.set ⟨home, hin.hH⟩ (embed (xs.take n))
          sudo_5Board_4held := b.sudo_5Board_4held.set ⟨home, hin.hD⟩ true
          sudo_5Board_8bench_on := false
          sudo_5Board_4cost := { b.sudo_5Board_4cost with
            sudo_5Costs_5moves := Int.ofNat (moves + 2 * pegCount (xs.take n))
            sudo_5Costs_6slides := Int.ofNat (slides + 2 * pegCount (xs.take n))
            sudo_5Costs_4peak :=
              Int.ofNat (countHeld (b.sudo_5Board_4held.set ⟨home, hin.hD⟩ true) 7) } })
          src park prev ctrl hRowS hRowP := by
      rw [unparked_cast hS src park prev ctrl (hrow ▸ hRowS) (hrow ▸ hRowP)]
    rw [hL, unparked_settled_pos b src park prev ctrl home hRowS hRowP ⟨hin.hH, hin.hD⟩ xs n moves slides peak hpk]
    rw [settleBoard_pos bU home ⟨hHU, hDU⟩ xs n moves slides peak hpkU]
    apply board_ext
    · simp [bU, unparkedBoard]
    · simp [bU, unparkedBoard]
    · simp [bU, unparkedBoard]
    · simp [bU, unparkedBoard]
    · simp [bU, unparkedBoard]
    · simp [bU, unparkedBoard]
    · apply cost_ext <;> first
        | exact congrArg Int.ofNat (countHeld_congr _ _ hset 7)
        | simp [bU, unparkedBoard, ofNat_eq_natCast]
    · simp [bU, unparkedBoard]
    · simp [bU, unparkedBoard]
    · simp [bU, unparkedBoard]
    · simp [bU, unparkedBoard]
    · simp [bU, unparkedBoard]
    · simp [bU, unparkedBoard]
    · simp [bU, unparkedBoard]
    · simp [bU, unparkedBoard]
    · simp [bU, unparkedBoard]
    · simp [bU, unparkedBoard]
    · simp [bU, unparkedBoard]
    · simp [bU, unparkedBoard]
    · simp [bU, unparkedBoard]
    · simp [bU, unparkedBoard]
    · simp [bU, unparkedBoard]
    · simp [bU, unparkedBoard]
    · simp [bU, unparkedBoard]
  · have hheld : bU.sudo_5Board_4held = b.sudo_5Board_4held :=
      unparked_held b src park prev ctrl hRowS hRowP
    have hset := (array_set_of_eq bU.sudo_5Board_4held b.sudo_5Board_4held hheld
      home hDU true).trans (array_set_irrel b.sudo_5Board_4held home (hheld ▸ hDU) hin.hD true)
    have hpkU : ¬ peak < countHeld (bU.sudo_5Board_4held.set ⟨home, hDU⟩ true) 7 := by
      rw [countHeld_congr _ _ hset 7]
      exact hpk
    have hS := settleBoard_neg b home ⟨hin.hH, hin.hD⟩ xs n moves slides peak hpk
    have hrow := settleBoard_row b home ⟨hin.hH, hin.hD⟩ xs n moves slides peak
    have hL : unparkedBoard (settleBoard b home hin.hH hin.hD xs n moves slides peak)
        src park prev ctrl (hrow ▸ hRowS) (hrow ▸ hRowP) =
        unparkedBoard ({ b with
          sudo_5Board_4home := b.sudo_5Board_4home.set ⟨home, hin.hH⟩ (embed (xs.take n))
          sudo_5Board_4held := b.sudo_5Board_4held.set ⟨home, hin.hD⟩ true
          sudo_5Board_8bench_on := false
          sudo_5Board_4cost := { b.sudo_5Board_4cost with
            sudo_5Costs_5moves := Int.ofNat (moves + 2 * pegCount (xs.take n))
            sudo_5Costs_6slides := Int.ofNat (slides + 2 * pegCount (xs.take n)) } })
          src park prev ctrl hRowS hRowP := by
      rw [unparked_cast hS src park prev ctrl (hrow ▸ hRowS) (hrow ▸ hRowP)]
    rw [hL, unparked_settled_neg b src park prev ctrl home hRowS hRowP ⟨hin.hH, hin.hD⟩ xs n moves slides peak hpk]
    rw [settleBoard_neg bU home ⟨hHU, hDU⟩ xs n moves slides peak hpkU]
    apply board_ext
    · simp [bU, unparkedBoard]
    · simp [bU, unparkedBoard]
    · simp [bU, unparkedBoard]
    · simp [bU, unparkedBoard]
    · simp [bU, unparkedBoard]
    · simp [bU, unparkedBoard]
    · apply cost_ext <;> simp [bU, unparkedBoard, ofNat_eq_natCast]
    · simp [bU, unparkedBoard]
    · simp [bU, unparkedBoard]
    · simp [bU, unparkedBoard]
    · simp [bU, unparkedBoard]
    · simp [bU, unparkedBoard]
    · simp [bU, unparkedBoard]
    · simp [bU, unparkedBoard]
    · simp [bU, unparkedBoard]
    · simp [bU, unparkedBoard]
    · simp [bU, unparkedBoard]
    · simp [bU, unparkedBoard]
    · simp [bU, unparkedBoard]
    · simp [bU, unparkedBoard]
    · simp [bU, unparkedBoard]
    · simp [bU, unparkedBoard]
    · simp [bU, unparkedBoard]
    · simp [bU, unparkedBoard]

/-- A resume park is unpark, then the keep-park. `ctrl` on the keep is already
    two ahead. The source hole is a control-row index (`fromBelow`), and the
    keep writes that row, not home 5. -/
def parkResumeBoard (b : Ecbs.Board) (src hole park prev rung i ctrl : Nat)
    (hRowS : src < b.sudo_5Board_3row.size)
    (hRowP : park < b.sudo_5Board_3row.size)
    (hRowH : hole < b.sudo_5Board_3row.size) : Ecbs.Board :=
  parkKeepBoard (unparkedBoard b src park prev ctrl hRowS hRowP)
    hole park rung i (ctrl + 2)
    (by simp [unparkedBoard, Array.size_set]; exact hRowP)
    (by simp [unparkedBoard, Array.size_set]; exact hRowH)

theorem parkResume_cast
    {b1 b2 : Ecbs.Board} (h : b1 = b2) (src hole park prev rung i ctrl : Nat)
    (hRowS : src < b1.sudo_5Board_3row.size)
    (hRowP : park < b1.sudo_5Board_3row.size)
    (hRowH : hole < b1.sudo_5Board_3row.size) :
    parkResumeBoard b1 src hole park prev rung i ctrl hRowS hRowP hRowH =
      parkResumeBoard b2 src hole park prev rung i ctrl (h ▸ hRowS) (h ▸ hRowP) (h ▸ hRowH) := by
  subst h
  rfl

/-- Resume park commutes with `settle`. Unpark and the keep-park each commute
    with it, and the source hole is only used as a control-row index. -/
theorem parkResume_settle_comm
    (b : Ecbs.Board) (src hole park prev rung i ctrl home : Nat)
    (hRowS : src < b.sudo_5Board_3row.size)
    (hRowP : park < b.sudo_5Board_3row.size)
    (hRowH : hole < b.sudo_5Board_3row.size)
    (hH : home < b.sudo_5Board_4home.size)
    (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (n moves slides peak : Nat) :
    let hrow := settleBoard_row b home ⟨hH, hD⟩ xs n moves slides peak
    let bU := unparkedBoard b src park prev ctrl hRowS hRowP
    let hPU : park < bU.sudo_5Board_3row.size := by
      simp [bU, unparkedBoard, Array.size_set]; exact hRowP
    let hHU : hole < bU.sudo_5Board_3row.size := by
      simp [bU, unparkedBoard, Array.size_set]; exact hRowH
    let hHomeU : home < bU.sudo_5Board_4home.size :=
      unparked_home b src park prev ctrl hRowS hRowP ▸ hH
    let hHeldU : home < bU.sudo_5Board_4held.size :=
      unparked_held b src park prev ctrl hRowS hRowP ▸ hD
    parkResumeBoard (settleBoard b home hH hD xs n moves slides peak)
        src hole park prev rung i ctrl (hrow ▸ hRowS) (hrow ▸ hRowP) (hrow ▸ hRowH) =
      settleBoard (parkResumeBoard b src hole park prev rung i ctrl hRowS hRowP hRowH)
        home
        (parkKeep_home bU hole park rung i (ctrl + 2) hPU hHU ▸ hHomeU)
        (parkKeep_held bU hole park rung i (ctrl + 2) hPU hHU ▸ hHeldU)
        xs n moves slides peak := by
  intro hrow bU hPU hHU hHomeU hHeldU
  have hU := unparked_settle_comm b src park prev ctrl home hRowS hRowP ⟨hH, hD⟩ xs n moves slides peak
  unfold parkResumeBoard
  have hcast := parkKeep_cast hU hole park rung i (ctrl + 2)
    (by simp [unparkedBoard, Array.size_set]; exact (hrow ▸ hRowP))
    (by simp [unparkedBoard, Array.size_set]; exact (hrow ▸ hRowH))
  have hK := parkKeep_settle_comm bU hole park rung i (ctrl + 2) home
    hPU hHU hHomeU hHeldU xs n moves slides peak
  have hrowU := settleBoard_row bU home ⟨hHomeU, hHeldU⟩ xs n moves slides peak
  have hp : (hU ▸ (by simp [unparkedBoard, Array.size_set]; exact (hrow ▸ hRowP))) =
      (hrowU ▸ hPU) := Subsingleton.elim _ _
  have hh : (hU ▸ (by simp [unparkedBoard, Array.size_set]; exact (hrow ▸ hRowH))) =
      (hrowU ▸ hHU) := Subsingleton.elim _ _
  rw [hcast, hp, hh, hK]

end EcbsLink2.Link2
