/-
  Pieces of `invert`: `set_control`, then the ladder walk. Proof-only.
  Not a security claim.
-/
import EcbsLink2.Link2.Board

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- `set_control` writes `c` at a hole strictly above the recorded high. -/
theorem set_control_raise (b : Ecbs.Board) (i c high control : Nat)
    (hrow : i < b.sudo_5Board_3row.size)
    (hctrl : b.sudo_5Board_1t.sudo_4Tier_7control = (control : Int))
    (hic : i < control)
    (hhigh : b.sudo_5Board_4cost.sudo_5Costs_15control_highest = (high : Int))
    (hgt : high < i) :
    Ecbs.set_control b (i : Int) (c : Int) =
      .ok { b with
        sudo_5Board_3row := b.sudo_5Board_3row.set ⟨i, hrow⟩ (c : Int)
        sudo_5Board_4cost := { b.sudo_5Board_4cost with
          sudo_5Costs_15control_highest := (i : Int) } } := by
  unfold Ecbs.set_control
  have hge : decide ((i : Int) ≥ (0 : Int)) = true := by
    rw [decide_eq_true_eq]
    show (0 : Int) ≤ Int.ofNat i
    rw [ofNat_eq_natCast i]
    exact Int.ofNat_nonneg i
  simp only [hge, if_true, hctrl]
  have hlt : decide ((i : Int) < (control : Int)) = true := by
    rw [decide_eq_true_eq, ← ofNat_eq_natCast i, ← ofNat_eq_natCast control]
    exact (ofNat_lt_iff i control).mpr hic
  rw [hlt, pure_eq_ok, ok_bind, sudoAssert_true, ok_bind]
  rw [← ofNat_eq_natCast i, putL_ofNat _ i (c : Int) hrow, ok_bind]
  rw [hhigh]
  have hgtI : decide (Int.ofNat i > (high : Int)) = true := by
    rw [decide_eq_true_eq, ← ofNat_eq_natCast high]
    exact (ofNat_lt_iff high i).mpr hgt
  rw [hgtI, if_pos rfl, pure_eq_ok]

/-- `set_control` writes `c` at a hole that does not beat the recorded high. -/
theorem set_control_keep (b : Ecbs.Board) (i c high control : Nat)
    (hrow : i < b.sudo_5Board_3row.size)
    (hctrl : b.sudo_5Board_1t.sudo_4Tier_7control = (control : Int))
    (hic : i < control)
    (hhigh : b.sudo_5Board_4cost.sudo_5Costs_15control_highest = (high : Int))
    (hle : i ≤ high) :
    Ecbs.set_control b (i : Int) (c : Int) =
      .ok { b with
        sudo_5Board_3row := b.sudo_5Board_3row.set ⟨i, hrow⟩ (c : Int) } := by
  unfold Ecbs.set_control
  have hge : decide ((i : Int) ≥ (0 : Int)) = true := by
    rw [decide_eq_true_eq]
    show (0 : Int) ≤ Int.ofNat i
    rw [ofNat_eq_natCast i]
    exact Int.ofNat_nonneg i
  simp only [hge, if_true, hctrl]
  have hlt : decide ((i : Int) < (control : Int)) = true := by
    rw [decide_eq_true_eq, ← ofNat_eq_natCast i, ← ofNat_eq_natCast control]
    exact (ofNat_lt_iff i control).mpr hic
  rw [hlt, pure_eq_ok, ok_bind, sudoAssert_true, ok_bind]
  rw [← ofNat_eq_natCast i, putL_ofNat _ i (c : Int) hrow, ok_bind]
  rw [hhigh]
  have hngt : decide (Int.ofNat i > (high : Int)) = false := by
    rw [decide_eq_false_iff_not, ← ofNat_eq_natCast high]
    intro hgt
    exact Nat.not_lt.mpr hle ((ofNat_lt_iff high i).mp hgt)
  rw [hngt]
  simp only [Bool.false_eq_true, if_false, pure_eq_ok]

/-- `unpark` when nothing is parked. -/
theorem unpark_idle (b : Ecbs.Board)
    (h : b.sudo_5Board_11parked_from = -1) :
    Ecbs.unpark b = .ok b := by
  unfold Ecbs.unpark
  rw [h]
  have hlt : decide ((-1 : Int) < (0 : Int)) = true := by decide
  rw [hlt, if_pos rfl, pure_eq_ok]

private theorem beq_colour_ne_zero (c : Nat) (h : c ≠ 0) :
    SudoRt.SEq.beq (c : Int) (0 : Int) = false := by
  rw [sEq_int, ← ofNat_eq_natCast c, show (0 : Int) = Int.ofNat 0 from rfl,
    decide_eq_false_iff_not]
  intro h0
  exact h (Int.ofNat.inj h0)

private theorem beq_zero_zero :
    SudoRt.SEq.beq (0 : Int) (0 : Int) = true := by
  rw [sEq_int]
  exact decide_eq_true rfl

/-- `park` from an idle board. `hole` holds `colour ≠ 0`, the parking hole is empty,
    and the parking hole is strictly above the recorded high, so that high rises. -/
theorem park_refines (b : Ecbs.Board) (hole park colour high control ctrl : Nat)
    (hIdle : b.sudo_5Board_11parked_from = -1)
    (hParkF : b.sudo_5Board_9park_hole = (park : Int))
    (hRowH : hole < b.sudo_5Board_3row.size)
    (hRowP : park < b.sudo_5Board_3row.size)
    (hColour : b.sudo_5Board_3row[hole] = (colour : Int))
    (hZero : b.sudo_5Board_3row[park] = 0)
    (hCol : colour ≠ 0)
    (hCtrlN : b.sudo_5Board_1t.sudo_4Tier_7control = (control : Int))
    (hParkC : park < control)
    (hHigh : b.sudo_5Board_4cost.sudo_5Costs_15control_highest = (high : Int))
    (hGt : high < park)
    (hCtrl : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = (ctrl : Int))
    (hFit : FitsLen (ctrl + 2))
    (hne : hole ≠ park) :
    Ecbs.park b (hole : Int) =
      .ok ((colour : Int),
        { b with
          sudo_5Board_3row :=
            (b.sudo_5Board_3row.set ⟨park, hRowP⟩ (colour : Int)).set
              ⟨hole, by rw [Array.size_set]; exact hRowH⟩ (0 : Int)
          sudo_5Board_4cost := { b.sudo_5Board_4cost with
            sudo_5Costs_15control_highest := (park : Int)
            sudo_5Costs_4ctrl := Int.ofNat (ctrl + 2) }
          sudo_5Board_11parked_from := (hole : Int) }) := by
  unfold Ecbs.park
  rw [unpark_idle b hIdle, ok_bind]
  conv => zeta
  rw [← ofNat_eq_natCast hole]
  rw [atL_ofNat b.sudo_5Board_3row hole hRowH, hColour, ok_bind]
  rw [beq_colour_ne_zero colour hCol]
  simp only [Bool.not_false, if_true]
  rw [hParkF, ← ofNat_eq_natCast park, atL_ofNat _ park hRowP, hZero, ok_bind, beq_zero_zero]
  simp only [pure_eq_ok, ok_bind, sudoAssert_true]
  rw [ofNat_eq_natCast park]
  rw [set_control_raise b park colour high control hRowP hCtrlN hParkC hHigh hGt, ok_bind]
  have hRowH0 : hole < (b.sudo_5Board_3row.set ⟨park, hRowP⟩ (colour : Int)).size := by
    rw [Array.size_set]; exact hRowH
  rw [putL_ofNat _ hole (0 : Int) hRowH0, ok_bind]
  rw [hCtrl, ← ofNat_eq_natCast ctrl, show (2 : Int) = Int.ofNat 2 from rfl,
    addI_ofNat ctrl 2 hFit, ok_bind]
  have hRead :
      ((b.sudo_5Board_3row.set ⟨park, hRowP⟩ (colour : Int)).set
        ⟨hole, by rw [Array.size_set]; exact hRowH⟩ (0 : Int))[park]'
        (by simp [Array.size_set]; exact hRowP) = (colour : Int) := by
    simp [Array.getElem_set, hne]
  simp only [hParkF]
  rw [← ofNat_eq_natCast park]
  rw [atL_ofNat _ park (by simp [Array.size_set]; exact hRowP), hRead]
  rfl

/-- `unpark` puts the parked colour back and clears the parking hole. The restored
    hole does not beat the recorded high. -/
theorem unpark_back (b : Ecbs.Board) (src park colour high control ctrl : Nat)
    (hFrom : b.sudo_5Board_11parked_from = (src : Int))
    (hPark : b.sudo_5Board_9park_hole = (park : Int))
    (hRowS : src < b.sudo_5Board_3row.size)
    (hRowP : park < b.sudo_5Board_3row.size)
    (hColour : b.sudo_5Board_3row[park]'hRowP = (colour : Int))
    (hCtrlN : b.sudo_5Board_1t.sudo_4Tier_7control = (control : Int))
    (hSrcC : src < control)
    (hHigh : b.sudo_5Board_4cost.sudo_5Costs_15control_highest = (high : Int))
    (hLe : src ≤ high)
    (hCtrl : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = (ctrl : Int))
    (hFit : FitsLen (ctrl + 2)) :
    Ecbs.unpark b =
      .ok { b with
        sudo_5Board_3row :=
          (b.sudo_5Board_3row.set ⟨src, hRowS⟩ (colour : Int)).set
            ⟨park, by rw [Array.size_set]; exact hRowP⟩ (0 : Int)
        sudo_5Board_11parked_from := -1
        sudo_5Board_4cost := { b.sudo_5Board_4cost with
          sudo_5Costs_4ctrl := Int.ofNat (ctrl + 2) } } := by
  unfold Ecbs.unpark
  rw [hFrom]
  have hnot : decide ((src : Int) < (0 : Int)) = false := by
    rw [decide_eq_false_iff_not, ← ofNat_eq_natCast src]
    exact fun h => (Int.not_lt.mpr (Int.ofNat_nonneg src)) h
  simp only [hnot, Bool.false_eq_true, if_false]
  conv => zeta
  rw [hPark, ← ofNat_eq_natCast park, atL_ofNat _ park hRowP, hColour, ok_bind]
  rw [set_control_keep b src colour high control hRowS hCtrlN hSrcC hHigh hLe, ok_bind]
  dsimp only
  have hRowP0 : park < (b.sudo_5Board_3row.set ⟨src, hRowS⟩ (colour : Int)).size := by
    rw [Array.size_set]; exact hRowP
  rw [hPark, ← ofNat_eq_natCast park, putL_ofNat _ park (0 : Int) hRowP0, ok_bind]
  rw [negI_one, ok_bind]
  rw [hCtrl, ← ofNat_eq_natCast ctrl, show (2 : Int) = Int.ofNat 2 from rfl,
    addI_ofNat ctrl 2 hFit, ok_bind]
  rfl

/-- `park_rung` reads climb-hole `i`, parks the colour there, and checks it is `rung`. -/
theorem park_rung_refines (b : Ecbs.Board) (holes : List Nat)
    (i hole park rung high control ctrl : Nat)
    (hClimb : Ecbs.climb_holes b = .ok (embed holes))
    (hIdx : b.sudo_5Board_8rung_idx = (i : Int))
    (hAt : i < holes.length) (hHole : holes[i] = hole)
    (hIdle : b.sudo_5Board_11parked_from = -1)
    (hParkF : b.sudo_5Board_9park_hole = (park : Int))
    (hRowH : hole < b.sudo_5Board_3row.size)
    (hRowP : park < b.sudo_5Board_3row.size)
    (hColour : b.sudo_5Board_3row[hole] = (rung : Int))
    (hZero : b.sudo_5Board_3row[park] = 0)
    (hRung : rung ≠ 0)
    (hCtrlN : b.sudo_5Board_1t.sudo_4Tier_7control = (control : Int))
    (hParkC : park < control)
    (hHigh : b.sudo_5Board_4cost.sudo_5Costs_15control_highest = (high : Int))
    (hGt : high < park)
    (hCtrl : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = (ctrl : Int))
    (hFit : FitsLen (ctrl + 2))
    (hne : hole ≠ park)
    (hFitI : FitsLen (i + 1)) :
    Ecbs.park_rung b (rung : Int) =
      .ok { b with
        sudo_5Board_3row :=
          (b.sudo_5Board_3row.set ⟨park, hRowP⟩ (rung : Int)).set
            ⟨hole, by rw [Array.size_set]; exact hRowH⟩ (0 : Int)
        sudo_5Board_4cost := { b.sudo_5Board_4cost with
          sudo_5Costs_15control_highest := (park : Int)
          sudo_5Costs_4ctrl := Int.ofNat (ctrl + 2) }
        sudo_5Board_11parked_from := (hole : Int)
        sudo_5Board_8rung_idx := Int.ofNat (i + 1) } := by
  unfold Ecbs.park_rung
  rw [hClimb, ok_bind]
  conv => zeta
  rw [hIdx, ← ofNat_eq_natCast i, atL_embed holes i hAt, hHole, ok_bind]
  rw [ofNat_eq_natCast hole]
  rw [park_refines b hole park rung high control ctrl
      hIdle hParkF hRowH hRowP hColour hZero hRung
      hCtrlN hParkC hHigh hGt hCtrl hFit hne, ok_bind]
  dsimp only
  rw [sudoAssertEq_int rfl 305, ok_bind]
  rw [hIdx, ← ofNat_eq_natCast i, show (1 : Int) = Int.ofNat 1 from rfl,
    addI_ofNat i 1 hFitI, ok_bind, pure_eq_ok]

/-- `park` when the parking hole does not beat the recorded high, so that high stays.
    `invert` parks this way: `tally_start` has already written the tally hole, one past
    the parking hole. -/
theorem park_keep (b : Ecbs.Board) (hole park colour high control ctrl : Nat)
    (hIdle : b.sudo_5Board_11parked_from = -1)
    (hParkF : b.sudo_5Board_9park_hole = (park : Int))
    (hRowH : hole < b.sudo_5Board_3row.size)
    (hRowP : park < b.sudo_5Board_3row.size)
    (hColour : b.sudo_5Board_3row[hole] = (colour : Int))
    (hZero : b.sudo_5Board_3row[park] = 0)
    (hCol : colour ≠ 0)
    (hCtrlN : b.sudo_5Board_1t.sudo_4Tier_7control = (control : Int))
    (hParkC : park < control)
    (hHigh : b.sudo_5Board_4cost.sudo_5Costs_15control_highest = (high : Int))
    (hLe : park ≤ high)
    (hCtrl : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = (ctrl : Int))
    (hFit : FitsLen (ctrl + 2))
    (hne : hole ≠ park) :
    Ecbs.park b (hole : Int) =
      .ok ((colour : Int),
        { b with
          sudo_5Board_3row :=
            (b.sudo_5Board_3row.set ⟨park, hRowP⟩ (colour : Int)).set
              ⟨hole, by rw [Array.size_set]; exact hRowH⟩ (0 : Int)
          sudo_5Board_4cost := { b.sudo_5Board_4cost with
            sudo_5Costs_4ctrl := Int.ofNat (ctrl + 2) }
          sudo_5Board_11parked_from := (hole : Int) }) := by
  unfold Ecbs.park
  rw [unpark_idle b hIdle, ok_bind]
  conv => zeta
  rw [← ofNat_eq_natCast hole]
  rw [atL_ofNat b.sudo_5Board_3row hole hRowH, hColour, ok_bind]
  rw [beq_colour_ne_zero colour hCol]
  simp only [Bool.not_false, if_true]
  rw [hParkF, ← ofNat_eq_natCast park, atL_ofNat _ park hRowP, hZero, ok_bind, beq_zero_zero]
  simp only [pure_eq_ok, ok_bind, sudoAssert_true]
  rw [ofNat_eq_natCast park]
  rw [set_control_keep b park colour high control hRowP hCtrlN hParkC hHigh hLe, ok_bind]
  have hRowH0 : hole < (b.sudo_5Board_3row.set ⟨park, hRowP⟩ (colour : Int)).size := by
    rw [Array.size_set]; exact hRowH
  rw [putL_ofNat _ hole (0 : Int) hRowH0, ok_bind]
  rw [hCtrl, ← ofNat_eq_natCast ctrl, show (2 : Int) = Int.ofNat 2 from rfl,
    addI_ofNat ctrl 2 hFit, ok_bind]
  have hRead :
      ((b.sudo_5Board_3row.set ⟨park, hRowP⟩ (colour : Int)).set
        ⟨hole, by rw [Array.size_set]; exact hRowH⟩ (0 : Int))[park]'
        (by simp [Array.size_set]; exact hRowP) = (colour : Int) := by
    simp [Array.getElem_set, hne]
  simp only [hParkF]
  rw [← ofNat_eq_natCast park]
  rw [atL_ofNat _ park (by simp [Array.size_set]; exact hRowP), hRead]
  rfl

/-- `park_rung` on the keep branch: the parking hole does not beat the recorded high. -/
theorem park_rung_keep (b : Ecbs.Board) (holes : List Nat)
    (i hole park rung high control ctrl : Nat)
    (hClimb : Ecbs.climb_holes b = .ok (embed holes))
    (hIdx : b.sudo_5Board_8rung_idx = (i : Int))
    (hAt : i < holes.length) (hHole : holes[i] = hole)
    (hIdle : b.sudo_5Board_11parked_from = -1)
    (hParkF : b.sudo_5Board_9park_hole = (park : Int))
    (hRowH : hole < b.sudo_5Board_3row.size)
    (hRowP : park < b.sudo_5Board_3row.size)
    (hColour : b.sudo_5Board_3row[hole] = (rung : Int))
    (hZero : b.sudo_5Board_3row[park] = 0)
    (hRung : rung ≠ 0)
    (hCtrlN : b.sudo_5Board_1t.sudo_4Tier_7control = (control : Int))
    (hParkC : park < control)
    (hHigh : b.sudo_5Board_4cost.sudo_5Costs_15control_highest = (high : Int))
    (hLe : park ≤ high)
    (hCtrl : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = (ctrl : Int))
    (hFit : FitsLen (ctrl + 2))
    (hne : hole ≠ park)
    (hFitI : FitsLen (i + 1)) :
    Ecbs.park_rung b (rung : Int) =
      .ok { b with
        sudo_5Board_3row :=
          (b.sudo_5Board_3row.set ⟨park, hRowP⟩ (rung : Int)).set
            ⟨hole, by rw [Array.size_set]; exact hRowH⟩ (0 : Int)
        sudo_5Board_4cost := { b.sudo_5Board_4cost with
          sudo_5Costs_4ctrl := Int.ofNat (ctrl + 2) }
        sudo_5Board_11parked_from := (hole : Int)
        sudo_5Board_8rung_idx := Int.ofNat (i + 1) } := by
  unfold Ecbs.park_rung
  rw [hClimb, ok_bind]
  conv => zeta
  rw [hIdx, ← ofNat_eq_natCast i, atL_embed holes i hAt, hHole, ok_bind]
  rw [ofNat_eq_natCast hole]
  rw [park_keep b hole park rung high control ctrl
      hIdle hParkF hRowH hRowP hColour hZero hRung
      hCtrlN hParkC hHigh hLe hCtrl hFit hne, ok_bind]
  dsimp only
  rw [sudoAssertEq_int rfl 305, ok_bind]
  rw [hIdx, ← ofNat_eq_natCast i, show (1 : Int) = Int.ofNat 1 from rfl,
    addI_ofNat i 1 hFitI, ok_bind, pure_eq_ok]

/-- `unpark_rung` when nothing is parked: only the rung index returns to zero. -/
theorem unpark_rung_idle (b : Ecbs.Board)
    (h : b.sudo_5Board_11parked_from = -1) :
    Ecbs.unpark_rung b = .ok { b with sudo_5Board_8rung_idx := 0 } := by
  unfold Ecbs.unpark_rung
  rw [unpark_idle b h, ok_bind]
  conv => zeta
  rfl

/-- `unpark_rung` puts the parked colour back, then zeros the rung index. -/
theorem unpark_rung_back (b : Ecbs.Board) (src park colour high control ctrl : Nat)
    (hFrom : b.sudo_5Board_11parked_from = (src : Int))
    (hPark : b.sudo_5Board_9park_hole = (park : Int))
    (hRowS : src < b.sudo_5Board_3row.size)
    (hRowP : park < b.sudo_5Board_3row.size)
    (hColour : b.sudo_5Board_3row[park]'hRowP = (colour : Int))
    (hCtrlN : b.sudo_5Board_1t.sudo_4Tier_7control = (control : Int))
    (hSrcC : src < control)
    (hHigh : b.sudo_5Board_4cost.sudo_5Costs_15control_highest = (high : Int))
    (hLe : src ≤ high)
    (hCtrl : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = (ctrl : Int))
    (hFit : FitsLen (ctrl + 2)) :
    Ecbs.unpark_rung b =
      .ok { b with
        sudo_5Board_3row :=
          (b.sudo_5Board_3row.set ⟨src, hRowS⟩ (colour : Int)).set
            ⟨park, by rw [Array.size_set]; exact hRowP⟩ (0 : Int)
        sudo_5Board_11parked_from := -1
        sudo_5Board_4cost := { b.sudo_5Board_4cost with
          sudo_5Costs_4ctrl := Int.ofNat (ctrl + 2) }
        sudo_5Board_8rung_idx := 0 } := by
  unfold Ecbs.unpark_rung
  rw [unpark_back b src park colour high control ctrl
      hFrom hPark hRowS hRowP hColour hCtrlN hSrcC hHigh hLe hCtrl hFit, ok_bind]
  conv => zeta
  rfl

/-- `tally_put` writes `c` at `tally0 + j` and raises the recorded high. -/
theorem tally_put_raise (b : Ecbs.Board) (t0 j c high control : Nat)
    (hT0 : b.sudo_5Board_6tally0 = (t0 : Int))
    (hrow : t0 + j < b.sudo_5Board_3row.size)
    (hCtrlN : b.sudo_5Board_1t.sudo_4Tier_7control = (control : Int))
    (hic : t0 + j < control)
    (hHigh : b.sudo_5Board_4cost.sudo_5Costs_15control_highest = (high : Int))
    (hgt : high < t0 + j)
    (hfit : FitsLen (t0 + j)) :
    Ecbs.tally_put b (j : Int) (c : Int) =
      .ok { b with
        sudo_5Board_3row := b.sudo_5Board_3row.set ⟨t0 + j, hrow⟩ (c : Int)
        sudo_5Board_4cost := { b.sudo_5Board_4cost with
          sudo_5Costs_15control_highest := ((t0 + j : Nat) : Int) } } := by
  unfold Ecbs.tally_put
  conv =>
    lhs
    rw [hT0, ← ofNat_eq_natCast t0, ← ofNat_eq_natCast j]
  rw [addI_ofNat t0 j hfit, ok_bind]
  rw [ofNat_eq_natCast (t0 + j)]
  rw [set_control_raise b (t0 + j) c high control hrow hCtrlN hic hHigh hgt, ok_bind, pure_eq_ok]

/-- `tally_put` writes `c` at `tally0 + j` without moving the recorded high. -/
theorem tally_put_keep (b : Ecbs.Board) (t0 j c high control : Nat)
    (hT0 : b.sudo_5Board_6tally0 = (t0 : Int))
    (hrow : t0 + j < b.sudo_5Board_3row.size)
    (hCtrlN : b.sudo_5Board_1t.sudo_4Tier_7control = (control : Int))
    (hic : t0 + j < control)
    (hHigh : b.sudo_5Board_4cost.sudo_5Costs_15control_highest = (high : Int))
    (hle : t0 + j ≤ high)
    (hfit : FitsLen (t0 + j)) :
    Ecbs.tally_put b (j : Int) (c : Int) =
      .ok { b with
        sudo_5Board_3row := b.sudo_5Board_3row.set ⟨t0 + j, hrow⟩ (c : Int) } := by
  unfold Ecbs.tally_put
  conv =>
    lhs
    rw [hT0, ← ofNat_eq_natCast t0, ← ofNat_eq_natCast j]
  rw [addI_ofNat t0 j hfit, ok_bind]
  rw [ofNat_eq_natCast (t0 + j)]
  rw [set_control_keep b (t0 + j) c high control hrow hCtrlN hic hHigh hle, ok_bind, pure_eq_ok]

/-- `tally_note` records a new tally length past the old maximum. -/
theorem tally_note_raise (b : Ecbs.Board) (len tmax : Nat)
    (hlen : b.sudo_5Board_9tally_len = (len : Int))
    (hmax : b.sudo_5Board_4cost.sudo_5Costs_9tally_max = (tmax : Int))
    (hgt : tmax < len) :
    Ecbs.tally_note b =
      .ok { b with
        sudo_5Board_4cost := { b.sudo_5Board_4cost with
          sudo_5Costs_9tally_max := (len : Int) } } := by
  unfold Ecbs.tally_note
  rw [hlen, hmax]
  have hgtI : decide ((len : Int) > (tmax : Int)) = true := by
    rw [decide_eq_true_eq, ← ofNat_eq_natCast len, ← ofNat_eq_natCast tmax]
    exact (ofNat_lt_iff tmax len).mpr hgt
  rw [hgtI, if_pos rfl, pure_eq_ok]

/-- `tally_note` leaves the maximum alone when the length does not beat it. -/
theorem tally_note_keep (b : Ecbs.Board) (len tmax : Nat)
    (hlen : b.sudo_5Board_9tally_len = (len : Int))
    (hmax : b.sudo_5Board_4cost.sudo_5Costs_9tally_max = (tmax : Int))
    (hle : len ≤ tmax) :
    Ecbs.tally_note b = .ok b := by
  unfold Ecbs.tally_note
  rw [hlen, hmax]
  have hngt : decide ((len : Int) > (tmax : Int)) = false := by
    rw [decide_eq_false_iff_not, ← ofNat_eq_natCast len, ← ofNat_eq_natCast tmax]
    intro hgt
    exact Nat.not_lt.mpr hle ((ofNat_lt_iff tmax len).mp hgt)
  rw [hngt]
  simp only [Bool.false_eq_true, if_false, pure_eq_ok]

/-- `tally_start` lays one white peg at `tally0`. The hole is above the recorded high,
    and the new length `1` beats `tally_max`. -/
theorem tally_start_raise (b : Ecbs.Board) (t0 high control ctrl tmax : Nat)
    (hLen0 : b.sudo_5Board_9tally_len = 0)
    (hT0 : b.sudo_5Board_6tally0 = (t0 : Int))
    (hrow : t0 < b.sudo_5Board_3row.size)
    (hCtrlN : b.sudo_5Board_1t.sudo_4Tier_7control = (control : Int))
    (hic : t0 < control)
    (hHigh : b.sudo_5Board_4cost.sudo_5Costs_15control_highest = (high : Int))
    (hgt : high < t0)
    (hFitT : FitsLen t0)
    (hCtrl : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = (ctrl : Int))
    (hFitC : FitsLen (ctrl + 1))
    (hMax : b.sudo_5Board_4cost.sudo_5Costs_9tally_max = (tmax : Int))
    (hNote : tmax < 1) :
    Ecbs.tally_start b =
      .ok { b with
        sudo_5Board_3row := b.sudo_5Board_3row.set ⟨t0, hrow⟩ (1 : Int)
        sudo_5Board_9tally_len := 1
        sudo_5Board_4cost := { b.sudo_5Board_4cost with
          sudo_5Costs_15control_highest := (t0 : Int)
          sudo_5Costs_4ctrl := Int.ofNat (ctrl + 1)
          sudo_5Costs_9tally_max := 1 } } := by
  unfold Ecbs.tally_start
  rw [hLen0, sudoAssertEq_int rfl 344, ok_bind]
  have hrow0 : t0 + 0 < b.sudo_5Board_3row.size := by simpa using hrow
  conv =>
    pattern (Ecbs.tally_put b (0 : Int) (1 : Int))
    rw [show (0 : Int) = ((0 : Nat) : Int) from rfl, show (1 : Int) = ((1 : Nat) : Int) from rfl]
  rw [tally_put_raise b t0 0 1 high control hT0 hrow0 hCtrlN (by simpa using hic)
      hHigh (by simpa using hgt) (by simpa using hFitT), ok_bind]
  conv => zeta
  dsimp only
  rw [hCtrl, ← ofNat_eq_natCast ctrl, addI_ofNat_one ctrl hFitC, ok_bind]
  have hlen1 : (1 : Int) = ((1 : Nat) : Int) := rfl
  rw [tally_note_raise _ 1 tmax hlen1 (by simpa using hMax) hNote, ok_bind, pure_eq_ok]
  simp [hrow]

/-- `tally_add_one` lays one more white peg just past the tally. That hole is above
    the recorded high, and the new length beats `tally_max`. -/
theorem tally_add_one_raise (b : Ecbs.Board) (t0 len high control ctrl tmax : Nat)
    (hLen : b.sudo_5Board_9tally_len = (len : Int))
    (hT0 : b.sudo_5Board_6tally0 = (t0 : Int))
    (hrow : t0 + len < b.sudo_5Board_3row.size)
    (hZero : b.sudo_5Board_3row[t0 + len] = 0)
    (hCtrlN : b.sudo_5Board_1t.sudo_4Tier_7control = (control : Int))
    (hic : t0 + len < control)
    (hHigh : b.sudo_5Board_4cost.sudo_5Costs_15control_highest = (high : Int))
    (hgt : high < t0 + len)
    (hFitI : FitsLen (t0 + len))
    (hCtrl : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = (ctrl : Int))
    (hFitC : FitsLen (ctrl + 1))
    (hFitL : FitsLen (len + 1))
    (hMax : b.sudo_5Board_4cost.sudo_5Costs_9tally_max = (tmax : Int))
    (hNote : tmax < len + 1) :
    Ecbs.tally_add_one b =
      .ok { b with
        sudo_5Board_3row := b.sudo_5Board_3row.set ⟨t0 + len, hrow⟩ (1 : Int)
        sudo_5Board_9tally_len := Int.ofNat (len + 1)
        sudo_5Board_4cost := { b.sudo_5Board_4cost with
          sudo_5Costs_15control_highest := ((t0 + len : Nat) : Int)
          sudo_5Costs_4ctrl := Int.ofNat (ctrl + 1)
          sudo_5Costs_9tally_max := Int.ofNat (len + 1) } } := by
  unfold Ecbs.tally_add_one
  conv =>
    lhs
    rw [hLen, hT0]
  conv => zeta
  rw [← ofNat_eq_natCast t0, ← ofNat_eq_natCast len, addI_ofNat t0 len hFitI, ok_bind]
  rw [← ofNat_eq_natCast (t0 + len), atL_ofNat _ (t0 + len) hrow, hZero, ok_bind]
  rw [sudoAssertEq_int rfl 367, ok_bind]
  conv =>
    pattern (Ecbs.tally_put b (Int.ofNat len) (1 : Int))
    rw [ofNat_eq_natCast len, show (1 : Int) = ((1 : Nat) : Int) from rfl]
  rw [tally_put_raise b t0 len 1 high control hT0 hrow hCtrlN hic hHigh hgt hFitI, ok_bind]
  conv => zeta
  dsimp only
  rw [hLen, ← ofNat_eq_natCast len, addI_ofNat_one len hFitL, ok_bind]
  rw [hCtrl, ← ofNat_eq_natCast ctrl, addI_ofNat_one ctrl hFitC, ok_bind]
  rw [tally_note_raise _ (len + 1) tmax rfl (by simpa using hMax) hNote, ok_bind, pure_eq_ok]
  simp [ofNat_eq_natCast]

end EcbsLink2.Link2
