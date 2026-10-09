/-
  Pieces of `invert`: `set_control`, then the ladder walk. Proof-only.
  Not a security claim.
-/
import EcbsLink2.Link2.Board
import EcbsLink2.Link2.Cube

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

private theorem array_set_congr {a b : Array Int} (h : a = b) (i : Nat)
    (ha : i < a.size) (v : Int) :
    a.set ⟨i, ha⟩ v = b.set ⟨i, h ▸ ha⟩ v := by
  subst h
  rfl

/-- Write `1` into `count` holes starting at `start`. Used for both halves of `tally_double`. -/
def paintOnes (xs : List Nat) (start : Nat) : Nat → List Nat
  | 0 => xs
  | k + 1 => (paintOnes xs start k).set (start + k) 1

theorem paintOnes_length (xs : List Nat) (start k : Nat) :
    (paintOnes xs start k).length = xs.length := by
  induction k with
  | zero => rfl
  | succ k ih => simp [paintOnes, ih, List.length_set]

theorem paintOnes_get_hi (xs : List Nat) (start k j : Nat)
    (hk : start + k ≤ j) (hj : j < xs.length) :
    (paintOnes xs start k)[j]'(by rw [paintOnes_length]; exact hj) = xs[j] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hne : start + k ≠ j := by omega
    simp [paintOnes, List.getElem_set, hne, ih (by omega)]

/-- One red tally peg turned white. The hole does not beat the recorded high. -/
theorem tally_mark_white (b : Ecbs.Board) (xs : List Nat) (t0 j ctrl high control : Nat)
    (hT0 : b.sudo_5Board_6tally0 = (t0 : Int))
    (hRow : b.sudo_5Board_3row = embed xs)
    (hAt : t0 + j < xs.length)
    (hCell : xs[t0 + j] = 2)
    (hCtrlN : b.sudo_5Board_1t.sudo_4Tier_7control = (control : Int))
    (hic : t0 + j < control)
    (hHigh : b.sudo_5Board_4cost.sudo_5Costs_15control_highest = (high : Int))
    (hle : t0 + j ≤ high)
    (hCtrl : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = (ctrl : Int))
    (hfit : FitsLen (t0 + j))
    (hfitC : FitsLen (ctrl + 1)) :
    (do
        let ix ← SudoRt.addI b.sudo_5Board_6tally0 (Int.ofNat j)
        let c ← SudoRt.atL b.sudo_5Board_3row ix
        if SudoRt.SEq.beq c (2 : Int) then
          do
            let b ← Ecbs.tally_put b (Int.ofNat j) (1 : Int)
            let ctrl ← SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_4ctrl (1 : Int)
            pure (SudoRt.Flow.cont (ρ := Ecbs.Board)
              ({ b with
                sudo_5Board_4cost := { b.sudo_5Board_4cost with
                  sudo_5Costs_4ctrl := ctrl } } : Ecbs.Board))
        else
          pure (SudoRt.Flow.cont (ρ := Ecbs.Board) b)) =
      .ok (SudoRt.Flow.cont (ρ := Ecbs.Board)
        { b with
          sudo_5Board_3row := embed (xs.set (t0 + j) 1)
          sudo_5Board_4cost := { b.sudo_5Board_4cost with
            sudo_5Costs_4ctrl := Int.ofNat (ctrl + 1) } }) := by
  conv =>
    lhs
    rw [hT0, hRow, ← ofNat_eq_natCast t0]
  rw [addI_ofNat t0 j hfit, ok_bind]
  have hsz : t0 + j < (embed xs).size := by rw [size_embed]; exact hAt
  rw [atL_ofNat _ (t0 + j) hsz, ok_bind]
  have hget : (embed xs)[t0 + j] = (2 : Int) := by
    rw [show (embed xs)[t0 + j] = Int.ofNat (xs[t0 + j]) by
      simp [embed, Array.getElem_mk, List.getElem_map], hCell]
    rfl
  rw [hget]
  have hbeq : SudoRt.SEq.beq (2 : Int) (2 : Int) = true := by
    rw [sEq_int]; exact decide_eq_true rfl
  simp only [hbeq, if_true]
  conv =>
    pattern (Ecbs.tally_put b (Int.ofNat j) (1 : Int))
    rw [ofNat_eq_natCast j, show (1 : Int) = ((1 : Nat) : Int) from rfl]
  rw [tally_put_keep b t0 j 1 high control hT0
      (by rw [hRow, size_embed]; exact hAt) hCtrlN hic hHigh hle hfit, ok_bind]
  conv => zeta
  dsimp only
  rw [hCtrl, ← ofNat_eq_natCast ctrl, addI_ofNat_one ctrl hfitC, ok_bind, pure_eq_ok]
  have hset (ha : t0 + j < (embed xs).size) :
      (embed xs).set ⟨t0 + j, ha⟩ ((1 : Nat) : Int) = embed (xs.set (t0 + j) 1) := by
    apply Array.ext
    · simp [embed, size_embed, List.length_set]
    · intro i hi hi'
      simp [embed, Array.getElem_set, List.getElem_set, ofNat_eq_natCast]
  rw [array_set_congr hRow, hset]

private theorem row_ctrl_id (b : Ecbs.Board) (row : Array Int) (ctrl : Int)
    (hR : b.sudo_5Board_3row = row)
    (hC : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = ctrl) :
    ({ b with
        sudo_5Board_3row := row
        sudo_5Board_4cost := { b.sudo_5Board_4cost with
          sudo_5Costs_4ctrl := ctrl } } : Ecbs.Board) = b := by
  rw [← hR, ← hC]

/-- Replace the control row and the ctrl counter, leaving every other field. -/
def touchRow (b : Ecbs.Board) (row : Array Int) (ctrl : Int) : Ecbs.Board :=
  { b with
    sudo_5Board_3row := row
    sudo_5Board_4cost := { b.sudo_5Board_4cost with sudo_5Costs_4ctrl := ctrl } }

/-- One pass of the red-to-white loop inside `tally_double`, `j = 0` to `m - 1`. -/
def whitenStep (toV : Int) (σ : Int × Ecbs.Board) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Ecbs.Board) Ecbs.Board) :=
  do
    if σ.1 > toV then
      pure (SudoRt.Flow.brk (ρ := Ecbs.Board) (σ.1, σ.2))
    else
      match ← (do
        let ix ← SudoRt.addI σ.2.sudo_5Board_6tally0 σ.1
        let c ← SudoRt.atL σ.2.sudo_5Board_3row ix
        if SudoRt.SEq.beq c (2 : Int) then
          do
            let b ← Ecbs.tally_put σ.2 σ.1 (1 : Int)
            let ctrl ← SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_4ctrl (1 : Int)
            pure (SudoRt.Flow.cont (ρ := Ecbs.Board)
              ({ b with sudo_5Board_4cost :=
                  { b.sudo_5Board_4cost with sudo_5Costs_4ctrl := ctrl } } : Ecbs.Board))
        else
          pure (SudoRt.Flow.cont (ρ := Ecbs.Board) σ.2)) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Ecbs.Board) r)
      | .brk fs => pure (SudoRt.Flow.brk (ρ := Ecbs.Board) (σ.1, fs))
      | .cont fs => do
          if σ.1 == toV then
            pure (SudoRt.Flow.brk (ρ := Ecbs.Board) (σ.1, fs))
          else do
            let j' ← SudoRt.addI σ.1 (1 : Int)
            pure (SudoRt.Flow.cont (ρ := Ecbs.Board) (j', fs))

/-- The first half of `tally_double`: each of the `m` red pegs (value `2`) goes back to
    white. Those holes do not beat the recorded high, so the high stays. `m > 0`. -/
theorem tally_whiten_loop {β}
    (b : Ecbs.Board) (xs : List Nat) (t0 m ctrl high control : Nat)
    (after : Int × Ecbs.Board → Except SudoRt.Trap β)
    (onRet : Ecbs.Board → Except SudoRt.Trap β)
    (hm : 0 < m)
    (hT0 : b.sudo_5Board_6tally0 = (t0 : Int))
    (hRow : b.sudo_5Board_3row = embed xs)
    (hRoom : t0 + m ≤ xs.length)
    (hRed : ∀ j (hj : j < m), xs[t0 + j]'(by omega) = 2)
    (hCtrlN : b.sudo_5Board_1t.sudo_4Tier_7control = (control : Int))
    (hHigh : b.sudo_5Board_4cost.sudo_5Costs_15control_highest = (high : Int))
    (hTop : high = t0 + m - 1)
    (hCtrl : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = (ctrl : Int))
    (hIn : t0 + m ≤ control)
    (hfit : FitsLen (t0 + m))
    (hfitC : FitsLen (ctrl + m))
    (hfitM : FitsLen m) :
    SudoRt.runLoopOn (Int.ofNat 0, b)
      (fuelRange (Int.ofNat 0) (Int.ofNat (m - 1)))
      (whitenStep (Int.ofNat (m - 1)))
      after onRet =
    after (Int.ofNat (m - 1),
      touchRow b (embed (paintOnes xs t0 m)) (Int.ofNat (ctrl + m))) := by
  refine asc_goal (fromN := 0) (toN := m - 1)
    (fun i s => s = touchRow b (embed (paintOnes xs t0 i)) (Int.ofNat (ctrl + i)))
    (Nat.zero_le _) ?_ ?_ ?_
  · have hC : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl := by
      rw [hCtrl, ← ofNat_eq_natCast]
    change b = touchRow b (embed (paintOnes xs t0 0)) (Int.ofNat (ctrl + 0))
    rw [show paintOnes xs t0 0 = xs from rfl, show ctrl + 0 = ctrl by omega]
    exact (row_ctrl_id b (embed xs) (Int.ofNat ctrl) hRow hC).symm
  · intro i s _ hi hI
    have him : i < m := by omega
    have hAt : t0 + i < xs.length := by omega
    have hcell : (paintOnes xs t0 i)[t0 + i]'(by rw [paintOnes_length]; exact hAt) = 2 := by
      rw [paintOnes_get_hi xs t0 i (t0 + i) (by omega) hAt]
      exact hRed i him
    have hle : t0 + i ≤ high := by omega
    have hic : t0 + i < control := by omega
    have hfi : FitsLen (t0 + i) := FitsLen.of_le hfit (by omega)
    have hfc : FitsLen (ctrl + i + 1) := FitsLen.of_le hfitC (by omega)
    have hft : FitsLen (i + 1) := FitsLen.of_le hfitM (by omega)
    have hT : s.sudo_5Board_6tally0 = (t0 : Int) := by
      rw [hI]; simp [touchRow, hT0]
    have hRw : s.sudo_5Board_3row = embed (paintOnes xs t0 i) := by
      rw [hI]; rfl
    have hCN : s.sudo_5Board_1t.sudo_4Tier_7control = (control : Int) := by
      rw [hI]; exact hCtrlN
    have hHi : s.sudo_5Board_4cost.sudo_5Costs_15control_highest = (high : Int) := by
      rw [hI]; exact hHigh
    have hCt : s.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (ctrl + i) := by
      rw [hI]; rfl
    unfold whitenStep
    dsimp only
    split
    · next hgt => exact absurd hgt (not_gt_cast hi)
    · have hAtP : t0 + i < (paintOnes xs t0 i).length := by
        rw [paintOnes_length]; exact hAt
      have hmark := tally_mark_white s (paintOnes xs t0 i) t0 i (ctrl + i) high control
          hT hRw hAtP hcell hCN hic hHi hle hCt hfi hfc
      rw [hmark, ok_bind]
      dsimp only
      have hpaint : (paintOnes xs t0 i).set (t0 + i) 1 = paintOnes xs t0 (i + 1) := rfl
      have htouch :
          ({ s with
              sudo_5Board_3row := embed ((paintOnes xs t0 i).set (t0 + i) 1)
              sudo_5Board_4cost := { s.sudo_5Board_4cost with
                sudo_5Costs_4ctrl := Int.ofNat (ctrl + i + 1) } }) =
            touchRow b (embed (paintOnes xs t0 (i + 1))) (Int.ofNat (ctrl + (i + 1))) := by
        rw [hI, hpaint, show ctrl + i + 1 = ctrl + (i + 1) by omega]
        rfl
      rw [htouch]
      refine ⟨touchRow b (embed (paintOnes xs t0 (i + 1))) (Int.ofNat (ctrl + (i + 1))), rfl, ?_⟩
      simp only [pure_eq_ok]
      exact asc_tail (m - 1) i hft
        (touchRow b (embed (paintOnes xs t0 (i + 1))) (Int.ofNat (ctrl + (i + 1))))
  · intro s hI
    have hm1 : m - 1 + 1 = m := by omega
    rw [hI, hm1]

/-- Lay one white peg in an empty tally hole strictly above the recorded high. -/
theorem tally_lay_white (b : Ecbs.Board) (xs : List Nat) (t0 j ctrl high control : Nat)
    (hT0 : b.sudo_5Board_6tally0 = (t0 : Int))
    (hRow : b.sudo_5Board_3row = embed xs)
    (hAt : t0 + j < xs.length)
    (hCell : xs[t0 + j] = 0)
    (hCtrlN : b.sudo_5Board_1t.sudo_4Tier_7control = (control : Int))
    (hic : t0 + j < control)
    (hHigh : b.sudo_5Board_4cost.sudo_5Costs_15control_highest = (high : Int))
    (hgt : high < t0 + j)
    (hCtrl : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = (ctrl : Int))
    (hfit : FitsLen (t0 + j))
    (hfitC : FitsLen (ctrl + 1)) :
    (do
        let ix ← SudoRt.addI b.sudo_5Board_6tally0 (Int.ofNat j)
        let c ← SudoRt.atL b.sudo_5Board_3row ix
        let _ ← SudoRt.sudoAssertEq c (Int.ofNat 0) 359
        let b ← Ecbs.tally_put b (Int.ofNat j) (1 : Int)
        let ctrl ← SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_4ctrl (1 : Int)
        pure (SudoRt.Flow.cont (ρ := Ecbs.Board)
          ({ b with
            sudo_5Board_4cost := { b.sudo_5Board_4cost with
              sudo_5Costs_4ctrl := ctrl } } : Ecbs.Board))) =
      .ok (SudoRt.Flow.cont (ρ := Ecbs.Board)
        { b with
          sudo_5Board_3row := embed (xs.set (t0 + j) 1)
          sudo_5Board_4cost := { b.sudo_5Board_4cost with
            sudo_5Costs_15control_highest := ((t0 + j : Nat) : Int)
            sudo_5Costs_4ctrl := Int.ofNat (ctrl + 1) } }) := by
  conv =>
    lhs
    rw [hT0, hRow, ← ofNat_eq_natCast t0]
  rw [addI_ofNat t0 j hfit, ok_bind]
  have hsz : t0 + j < (embed xs).size := by rw [size_embed]; exact hAt
  rw [atL_ofNat _ (t0 + j) hsz, ok_bind]
  have hget : (embed xs)[t0 + j] = (0 : Int) := by
    simp [embed, Array.getElem_mk, List.getElem_map, hCell]
  rw [hget, show (0 : Int) = Int.ofNat 0 from rfl, sudoAssertEq_int rfl 359, ok_bind]
  conv =>
    pattern (Ecbs.tally_put b (Int.ofNat j) (1 : Int))
    rw [ofNat_eq_natCast j, show (1 : Int) = ((1 : Nat) : Int) from rfl]
  rw [tally_put_raise b t0 j 1 high control hT0
      (by rw [hRow, size_embed]; exact hAt) hCtrlN hic hHigh hgt hfit, ok_bind]
  conv => zeta
  dsimp only
  rw [hCtrl, ← ofNat_eq_natCast ctrl, addI_ofNat_one ctrl hfitC, ok_bind, pure_eq_ok]
  have hset (ha : t0 + j < (embed xs).size) :
      (embed xs).set ⟨t0 + j, ha⟩ ((1 : Nat) : Int) = embed (xs.set (t0 + j) 1) := by
    apply Array.ext
    · simp [embed, size_embed, List.length_set]
    · intro i hi hi'
      simp [embed, Array.getElem_set, List.getElem_set, ofNat_eq_natCast]
  rw [array_set_congr hRow, hset]

/-- Replace the control row, the ctrl counter, and the recorded high. -/
def touchGrow (b : Ecbs.Board) (row : Array Int) (ctrl high : Int) : Ecbs.Board :=
  { b with
    sudo_5Board_3row := row
    sudo_5Board_4cost := { b.sudo_5Board_4cost with
      sudo_5Costs_4ctrl := ctrl
      sudo_5Costs_15control_highest := high } }

private theorem touch_grow_id (b : Ecbs.Board) (row : Array Int) (ctrl high : Int)
    (hR : b.sudo_5Board_3row = row)
    (hC : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = ctrl)
    (hH : b.sudo_5Board_4cost.sudo_5Costs_15control_highest = high) :
    touchGrow b row ctrl high = b := by
  unfold touchGrow
  rw [← hR, ← hC, ← hH]

/-- The second half of `tally_double`: `m` empty holes, starting at `tally0 + m`,
    each become white and the recorded high walks up with them. `m > 0`. -/
def layStep (toV : Int) (σ : Int × Ecbs.Board) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Ecbs.Board) Ecbs.Board) :=
  do
    if σ.1 > toV then
      pure (SudoRt.Flow.brk (ρ := Ecbs.Board) (σ.1, σ.2))
    else
      match ← (do
        let ix ← SudoRt.addI σ.2.sudo_5Board_6tally0 σ.1
        let c ← SudoRt.atL σ.2.sudo_5Board_3row ix
        let _ ← SudoRt.sudoAssertEq c (Int.ofNat 0) 359
        let b ← Ecbs.tally_put σ.2 σ.1 (1 : Int)
        let ctrl ← SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_4ctrl (1 : Int)
        pure (SudoRt.Flow.cont (ρ := Ecbs.Board)
          ({ b with sudo_5Board_4cost :=
              { b.sudo_5Board_4cost with sudo_5Costs_4ctrl := ctrl } } : Ecbs.Board))) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Ecbs.Board) r)
      | .brk fs => pure (SudoRt.Flow.brk (ρ := Ecbs.Board) (σ.1, fs))
      | .cont fs => do
          if σ.1 == toV then
            pure (SudoRt.Flow.brk (ρ := Ecbs.Board) (σ.1, fs))
          else do
            let j' ← SudoRt.addI σ.1 (1 : Int)
            pure (SudoRt.Flow.cont (ρ := Ecbs.Board) (j', fs))

theorem tally_lay_loop {β}
    (b : Ecbs.Board) (ys : List Nat) (t0 m c0 control : Nat)
    (after : Int × Ecbs.Board → Except SudoRt.Trap β)
    (onRet : Ecbs.Board → Except SudoRt.Trap β)
    (hm : 0 < m)
    (hT0 : b.sudo_5Board_6tally0 = (t0 : Int))
    (hRow : b.sudo_5Board_3row = embed ys)
    (hRoom : t0 + 2 * m ≤ ys.length)
    (hZero : ∀ k (hk : k < m), ys[t0 + m + k]'(by omega) = 0)
    (hCtrlN : b.sudo_5Board_1t.sudo_4Tier_7control = (control : Int))
    (hHigh : b.sudo_5Board_4cost.sudo_5Costs_15control_highest = ((t0 + m - 1 : Nat) : Int))
    (hCtrl : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = (c0 : Int))
    (hIn : t0 + 2 * m ≤ control)
    (hfit : FitsLen (t0 + 2 * m))
    (hfitC : FitsLen (c0 + m))
    (hfitM : FitsLen (2 * m)) :
    SudoRt.runLoopOn (Int.ofNat m, b)
      (fuelRange (Int.ofNat m) (Int.ofNat (2 * m - 1)))
      (layStep (Int.ofNat (2 * m - 1)))
      after onRet =
    after (Int.ofNat (2 * m - 1),
      touchGrow b (embed (paintOnes ys (t0 + m) m))
        (Int.ofNat (c0 + m)) ((t0 + 2 * m - 1 : Nat) : Int)) := by
  have hCtrlI : b.sudo_5Board_1t.sudo_4Tier_7control = (control : Int) := hCtrlN
  refine asc_goal (fromN := m) (toN := 2 * m - 1)
    (fun i s => s = touchGrow b (embed (paintOnes ys (t0 + m) (i - m)))
        (Int.ofNat (c0 + (i - m))) ((t0 + i - 1 : Nat) : Int))
    (by omega) ?_ ?_ ?_
  · change b = touchGrow b (embed (paintOnes ys (t0 + m) (m - m)))
      (Int.ofNat (c0 + (m - m))) ((t0 + m - 1 : Nat) : Int)
    rw [show m - m = 0 by omega, show paintOnes ys (t0 + m) 0 = ys from rfl,
      show c0 + 0 = c0 by omega]
    have hC : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat c0 := by
      rw [hCtrl, ← ofNat_eq_natCast]
    exact (touch_grow_id b (embed ys) (Int.ofNat c0) ((t0 + m - 1 : Nat) : Int)
      hRow hC hHigh).symm
  · intro i s hlo hi hI
    have him : i < 2 * m := by omega
    have hkm : i - m < m := by omega
    have hAt : t0 + i < ys.length := by omega
    have hcell : (paintOnes ys (t0 + m) (i - m))[t0 + i]'(by
        rw [paintOnes_length]; exact hAt) = 0 := by
      rw [paintOnes_get_hi ys (t0 + m) (i - m) (t0 + i) (by omega) hAt]
      have hk : i - m < m := hkm
      simpa [show t0 + m + (i - m) = t0 + i by omega] using hZero (i - m) hk
    have hgt : t0 + i - 1 < t0 + i := by omega
    have hic : t0 + i < t0 + 2 * m := by omega
    have hfi : FitsLen (t0 + i) := FitsLen.of_le hfit (by omega)
    have hfc : FitsLen (c0 + (i - m) + 1) := FitsLen.of_le hfitC (by omega)
    have hft : FitsLen (i + 1) := FitsLen.of_le hfitM (by omega)
    have hT : s.sudo_5Board_6tally0 = (t0 : Int) := by
      rw [hI]; simp [touchGrow, hT0]
    have hRw : s.sudo_5Board_3row = embed (paintOnes ys (t0 + m) (i - m)) := by
      rw [hI]; rfl
    have hCN : s.sudo_5Board_1t.sudo_4Tier_7control = (control : Int) := by
      rw [hI]; exact hCtrlI
    have hHi : s.sudo_5Board_4cost.sudo_5Costs_15control_highest =
        ((t0 + i - 1 : Nat) : Int) := by rw [hI]; rfl
    have hCt : s.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (c0 + (i - m)) := by
      rw [hI]; rfl
    unfold layStep
    dsimp only
    split
    · next hgt' =>
        exact absurd hgt' (not_gt_cast (by omega : i ≤ 2 * m - 1))
    · have hAtP : t0 + i < (paintOnes ys (t0 + m) (i - m)).length := by
        rw [paintOnes_length]; exact hAt
      have hmark := tally_lay_white s (paintOnes ys (t0 + m) (i - m)) t0 i
          (c0 + (i - m)) (t0 + i - 1) control
          hT hRw hAtP hcell hCN (by omega) hHi (by omega) hCt hfi hfc
      rw [hmark, ok_bind]
      dsimp only
      have hpaint : (paintOnes ys (t0 + m) (i - m)).set (t0 + i) 1 =
          paintOnes ys (t0 + m) (i - m + 1) := by
        rw [show t0 + i = (t0 + m) + (i - m) by omega]
        rfl
      have hsub : i - m + 1 = i + 1 - m := by omega
      have htouch :
          ({ s with
              sudo_5Board_3row := embed ((paintOnes ys (t0 + m) (i - m)).set (t0 + i) 1)
              sudo_5Board_4cost := { s.sudo_5Board_4cost with
                sudo_5Costs_15control_highest := ((t0 + i : Nat) : Int)
                sudo_5Costs_4ctrl := Int.ofNat (c0 + (i - m) + 1) } }) =
            touchGrow b (embed (paintOnes ys (t0 + m) (i + 1 - m)))
              (Int.ofNat (c0 + (i + 1 - m))) ((t0 + (i + 1) - 1 : Nat) : Int) := by
        rw [hI, hpaint, hsub]
        rw [show c0 + (i - m) + 1 = c0 + (i + 1 - m) by omega]
        rw [show t0 + (i + 1) - 1 = t0 + i by omega]
        rfl
      rw [htouch]
      refine ⟨touchGrow b (embed (paintOnes ys (t0 + m) (i + 1 - m)))
          (Int.ofNat (c0 + (i + 1 - m))) ((t0 + (i + 1) - 1 : Nat) : Int), rfl, ?_⟩
      simp only [pure_eq_ok]
      exact asc_tail (2 * m - 1) i hft _
  · intro s hI
    have hm1 : 2 * m - 1 + 1 = 2 * m := by omega
    rw [hI, hm1, show 2 * m - m = m by omega]

/-- `tally_double` when the tally pegs are all red, the next `m` holes are empty,
    and the recorded high is the last red peg. Both halves run, the length becomes
    `2 · m`, and that length beats `tally_max`. -/
theorem tally_double_refines (b : Ecbs.Board) (xs : List Nat)
    (t0 m c0 high control tmax : Nat)
    (hm : 0 < m)
    (hLen : b.sudo_5Board_9tally_len = (m : Int))
    (hT0 : b.sudo_5Board_6tally0 = (t0 : Int))
    (hRow : b.sudo_5Board_3row = embed xs)
    (hRoom : t0 + 2 * m ≤ xs.length)
    (hRed : ∀ j (hj : j < m), xs[t0 + j]'(by omega) = 2)
    (hZero : ∀ k (hk : k < m), xs[t0 + m + k]'(by omega) = 0)
    (hCtrlN : b.sudo_5Board_1t.sudo_4Tier_7control = (control : Int))
    (hHigh : b.sudo_5Board_4cost.sudo_5Costs_15control_highest = (high : Int))
    (hTop : high = t0 + m - 1)
    (hCtrl : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = (c0 : Int))
    (hIn : t0 + 2 * m ≤ control)
    (hfit : FitsLen (t0 + 2 * m))
    (hfitC : FitsLen (c0 + 2 * m))
    (hfitM : FitsLen (2 * m))
    (hMax : b.sudo_5Board_4cost.sudo_5Costs_9tally_max = (tmax : Int))
    (hNote : tmax < 2 * m) :
    Ecbs.tally_double b =
      .ok { b with
        sudo_5Board_3row := embed (paintOnes (paintOnes xs t0 m) (t0 + m) m)
        sudo_5Board_9tally_len := Int.ofNat (2 * m)
        sudo_5Board_4cost := { b.sudo_5Board_4cost with
          sudo_5Costs_4ctrl := Int.ofNat (c0 + 2 * m)
          sudo_5Costs_15control_highest := ((t0 + 2 * m - 1 : Nat) : Int)
          sudo_5Costs_9tally_max := Int.ofNat (2 * m) } } := by
  unfold Ecbs.tally_double
  conv =>
    lhs
    rw [hLen]
  conv =>
    lhs
    zeta
  rw [← ofNat_eq_natCast m, subI_ofNat_one m hm (FitsLen.of_le hfitM (by omega)), ok_bind]
  rw [show (0 : Int) = Int.ofNat 0 from rfl, fuelRange_eq]
  conv =>
    lhs
    pattern (fun σ : Int × Ecbs.Board => _)
    change whitenStep (Int.ofNat (m - 1))
  have hRoom1 : t0 + m ≤ xs.length := by omega
  have hIn1 : t0 + m ≤ control := by omega
  have hfit1 : FitsLen (t0 + m) := FitsLen.of_le hfit (by omega)
  have hfitC1 : FitsLen (c0 + m) := FitsLen.of_le hfitC (by omega)
  rw [tally_whiten_loop b xs t0 m c0 high control _ _ hm hT0 hRow hRoom1 hRed
      hCtrlN hHigh hTop hCtrl hIn1 hfit1 hfitC1 (FitsLen.of_le hfitM (by omega))]
  dsimp only
  rw [show (2 : Int) = Int.ofNat 2 from rfl,
    mulI_ofNat 2 m (FitsLen.of_le hfitM (by omega)), ok_bind]
  rw [subI_ofNat_one (2 * m) (by omega) hfitM, ok_bind]
  rw [fuelRange_eq]
  conv =>
    pattern (fun σ : Int × Ecbs.Board => _)
    change layStep (Int.ofNat (2 * m - 1))
  let bW := touchRow b (embed (paintOnes xs t0 m)) (Int.ofNat (c0 + m))
  conv =>
    pattern (touchRow b (embed (paintOnes xs t0 m)) (Int.ofNat (c0 + m)))
    change bW
  have hT0W : bW.sudo_5Board_6tally0 = (t0 : Int) := by
    simp [bW, touchRow, hT0]
  have hRowW : bW.sudo_5Board_3row = embed (paintOnes xs t0 m) := by
    simp [bW, touchRow]
  have hZeroW : ∀ k (hk : k < m),
      (paintOnes xs t0 m)[t0 + m + k]'(by rw [paintOnes_length]; omega) = 0 := by
    intro k hk
    rw [paintOnes_get_hi xs t0 m (t0 + m + k) (by omega) (by omega)]
    exact hZero k hk
  have hCtrlW : bW.sudo_5Board_1t.sudo_4Tier_7control = (control : Int) := by
    simp [bW, touchRow, hCtrlN]
  have hHighW : bW.sudo_5Board_4cost.sudo_5Costs_15control_highest =
      ((t0 + m - 1 : Nat) : Int) := by
    simp [bW, touchRow, hHigh, hTop, ofNat_eq_natCast]
  have hCtW : bW.sudo_5Board_4cost.sudo_5Costs_4ctrl = ((c0 + m : Nat) : Int) := by
    simp [bW, touchRow, ofNat_eq_natCast]
  rw [tally_lay_loop bW (paintOnes xs t0 m) t0 m (c0 + m) control _ _ hm
      hT0W hRowW (by rw [paintOnes_length]; exact hRoom) hZeroW hCtrlW hHighW hCtW
      hIn hfit (FitsLen.of_le hfitC (by omega)) hfitM]
  dsimp only
  rw [ok_bind]
  let bG := touchGrow bW (embed (paintOnes (paintOnes xs t0 m) (t0 + m) m))
      (Int.ofNat (c0 + m + m)) ((t0 + 2 * m - 1 : Nat) : Int)
  let bL : Ecbs.Board := { bG with sudo_5Board_9tally_len := Int.ofNat (2 * m) }
  conv =>
    pattern (Ecbs.tally_note _)
    change Ecbs.tally_note bL
  have hlen : bL.sudo_5Board_9tally_len = ((2 * m : Nat) : Int) := by
    simp [bL, ofNat_eq_natCast]
  have hmax : bL.sudo_5Board_4cost.sudo_5Costs_9tally_max = (tmax : Int) := by
    simp [bL, bG, touchGrow, bW, touchRow, hMax]
  rw [tally_note_raise bL (2 * m) tmax hlen hmax hNote, ok_bind, pure_eq_ok]
  have hc : c0 + m + m = c0 + 2 * m := by omega
  simp [bL, bG, touchGrow, bW, touchRow, ofNat_eq_natCast, hc]

/-- The check `invert` runs before cubing: tally holes `0 .. m - 1` are white (`1`).
    The board is unchanged. `m > 0`. -/
def whiteStep (b : Ecbs.Board) (toV : Int) (j : Int) :
    Except SudoRt.Trap (SudoRt.Flow Int Ecbs.Board) :=
  do
    if j > toV then
      pure (SudoRt.Flow.brk (ρ := Ecbs.Board) j)
    else
      match ← (do
        let ix ← SudoRt.addI b.sudo_5Board_6tally0 j
        let c ← SudoRt.atL b.sudo_5Board_3row ix
        let _ ← SudoRt.sudoAssertEq c (1 : Int) 703
        pure (SudoRt.Flow.cont (ρ := Ecbs.Board) ())) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Ecbs.Board) r)
      | .brk _ => pure (SudoRt.Flow.brk (ρ := Ecbs.Board) j)
      | .cont _ => do
          if j == toV then
            pure (SudoRt.Flow.brk (ρ := Ecbs.Board) j)
          else do
            let j' ← SudoRt.addI j (1 : Int)
            pure (SudoRt.Flow.cont (ρ := Ecbs.Board) j')

theorem tally_whites_hold {β}
    (b : Ecbs.Board) (xs : List Nat) (t0 m : Nat)
    (after : Int → Except SudoRt.Trap β) (onRet : Ecbs.Board → Except SudoRt.Trap β)
    (hm : 0 < m)
    (hT0 : b.sudo_5Board_6tally0 = (t0 : Int))
    (hRow : b.sudo_5Board_3row = embed xs)
    (hRoom : t0 + m ≤ xs.length)
    (hWhite : ∀ j (hj : j < m), xs[t0 + j]'(by omega) = 1)
    (hfit : FitsLen (t0 + m)) (hfitM : FitsLen m) :
    SudoRt.runLoopOn (Int.ofNat 0) (fuelRange (Int.ofNat 0) (Int.ofNat (m - 1)))
      (whiteStep b (Int.ofNat (m - 1))) after onRet =
      after (Int.ofNat (m - 1)) := by
  refine asc_scan_ret_goal b (whiteStep b (Int.ofNat (m - 1))) after onRet
      (fun _ => false) 0 (m - 1) (by omega) (after (Int.ofNat (m - 1))) ?_ ?_ ?_
  · intro i _ hi
    unfold whiteStep
    dsimp only
    have hng : ¬ Int.ofNat i > Int.ofNat (m - 1) := not_gt_cast hi
    simp only [hng, Bool.false_eq_true, if_false]
    have hAt : t0 + i < xs.length := by omega
    have hfi : FitsLen (t0 + i) := FitsLen.of_le hfit (by omega)
    conv =>
      lhs
      rw [hT0, hRow, ← ofNat_eq_natCast t0]
    rw [addI_ofNat t0 i hfi, ok_bind]
    have hsz : t0 + i < (embed xs).size := by rw [size_embed]; exact hAt
    rw [atL_ofNat _ (t0 + i) hsz, ok_bind]
    have hget : (embed xs)[t0 + i] = (1 : Int) := by
      simp [embed, Array.getElem_mk, List.getElem_map, hWhite i (by omega), ofNat_eq_natCast]
    rw [hget, sudoAssertEq_int rfl 703, ok_bind, pure_eq_ok]
    simpa using asc_tail_idx (m - 1) i (FitsLen.of_le hfitM (by omega))
  · intro _
    rfl
  · intro _ _ _ hb
    cases hb

/-- Write `0` into `count` holes starting at `start`. `tally_clear` does this. -/
def paintZero (xs : List Nat) (start : Nat) : Nat → List Nat
  | 0 => xs
  | k + 1 => (paintZero xs start k).set (start + k) 0

theorem paintZero_length (xs : List Nat) (start k : Nat) :
    (paintZero xs start k).length = xs.length := by
  induction k with
  | zero => rfl
  | succ k ih => simp [paintZero, ih, List.length_set]

/-- One tally hole set back to empty. The hole does not beat the recorded high. -/
theorem tally_put_zero (b : Ecbs.Board) (xs : List Nat) (t0 j ctrl high control : Nat)
    (hT0 : b.sudo_5Board_6tally0 = (t0 : Int))
    (hRow : b.sudo_5Board_3row = embed xs)
    (hAt : t0 + j < xs.length)
    (hCtrlN : b.sudo_5Board_1t.sudo_4Tier_7control = (control : Int))
    (hic : t0 + j < control)
    (hHigh : b.sudo_5Board_4cost.sudo_5Costs_15control_highest = (high : Int))
    (hle : t0 + j ≤ high)
    (hCtrl : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = (ctrl : Int))
    (hfit : FitsLen (t0 + j))
    (hfitC : FitsLen (ctrl + 1)) :
    (do
        let b ← Ecbs.tally_put b (Int.ofNat j) (0 : Int)
        let ctrl ← SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_4ctrl (1 : Int)
        pure (SudoRt.Flow.cont (ρ := Ecbs.Board)
          ({ b with sudo_5Board_4cost :=
              { b.sudo_5Board_4cost with sudo_5Costs_4ctrl := ctrl } } : Ecbs.Board))) =
      .ok (SudoRt.Flow.cont (ρ := Ecbs.Board)
        (touchRow { b with sudo_5Board_3row := embed (xs.set (t0 + j) 0) }
          (embed (xs.set (t0 + j) 0)) (Int.ofNat (ctrl + 1)))) := by
  conv =>
    lhs
    rw [show (0 : Int) = ((0 : Nat) : Int) from rfl, ofNat_eq_natCast j]
  rw [tally_put_keep b t0 j 0 high control hT0
      (by rw [hRow, size_embed]; exact hAt) hCtrlN hic hHigh hle hfit, ok_bind]
  conv => zeta
  dsimp only
  rw [hCtrl, ← ofNat_eq_natCast ctrl, addI_ofNat_one ctrl hfitC, ok_bind, pure_eq_ok]
  have hset (ha : t0 + j < (embed xs).size) :
      (embed xs).set ⟨t0 + j, ha⟩ ((0 : Nat) : Int) = embed (xs.set (t0 + j) 0) := by
    apply Array.ext
    · simp [embed, size_embed, List.length_set]
    · intro i hi hi'
      simp [embed, Array.getElem_set, List.getElem_set]
  unfold touchRow
  rw [array_set_congr hRow, hset]

/-- `tally_clear` writes `0` over the tally and sets the length to `0`. The holes do not
    beat the recorded high, so that high stays. `m > 0`. -/
def clearStep (toV : Int) (σ : Int × Ecbs.Board) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Ecbs.Board) Ecbs.Board) :=
  do
    if σ.1 > toV then
      pure (SudoRt.Flow.brk (ρ := Ecbs.Board) (σ.1, σ.2))
    else
      match ← (do
        let b ← Ecbs.tally_put σ.2 σ.1 (0 : Int)
        let ctrl ← SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_4ctrl (1 : Int)
        pure (SudoRt.Flow.cont (ρ := Ecbs.Board)
          ({ b with sudo_5Board_4cost :=
              { b.sudo_5Board_4cost with sudo_5Costs_4ctrl := ctrl } } : Ecbs.Board))) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Ecbs.Board) r)
      | .brk fs => pure (SudoRt.Flow.brk (ρ := Ecbs.Board) (σ.1, fs))
      | .cont fs => do
          if σ.1 == toV then
            pure (SudoRt.Flow.brk (ρ := Ecbs.Board) (σ.1, fs))
          else do
            let j' ← SudoRt.addI σ.1 (1 : Int)
            pure (SudoRt.Flow.cont (ρ := Ecbs.Board) (j', fs))

theorem tally_clear_refines (b : Ecbs.Board) (xs : List Nat)
    (t0 m ctrl high control : Nat)
    (hm : 0 < m)
    (hLen : b.sudo_5Board_9tally_len = (m : Int))
    (hT0 : b.sudo_5Board_6tally0 = (t0 : Int))
    (hRow : b.sudo_5Board_3row = embed xs)
    (hRoom : t0 + m ≤ xs.length)
    (hCtrlN : b.sudo_5Board_1t.sudo_4Tier_7control = (control : Int))
    (hHigh : b.sudo_5Board_4cost.sudo_5Costs_15control_highest = (high : Int))
    (hTop : t0 + m - 1 ≤ high)
    (hCtrl : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = (ctrl : Int))
    (hIn : t0 + m ≤ control)
    (hfit : FitsLen (t0 + m))
    (hfitC : FitsLen (ctrl + m))
    (hfitM : FitsLen m) :
    Ecbs.tally_clear b =
      .ok { touchRow b (embed (paintZero xs t0 m)) (Int.ofNat (ctrl + m)) with
            sudo_5Board_9tally_len := 0 } := by
  unfold Ecbs.tally_clear
  conv =>
    lhs
    rw [hLen]
  conv =>
    lhs
    zeta
  rw [← ofNat_eq_natCast m, subI_ofNat_one m hm hfitM, ok_bind]
  rw [show (0 : Int) = Int.ofNat 0 from rfl, fuelRange_eq]
  conv =>
    lhs
    pattern (fun σ : Int × Ecbs.Board => _)
    change clearStep (Int.ofNat (m - 1))
  rw [except_bind_pure]
  refine asc_goal (fromN := 0) (toN := m - 1)
    (fun i s => s = touchRow b (embed (paintZero xs t0 i)) (Int.ofNat (ctrl + i)))
    (Nat.zero_le _) ?_ ?_ ?_
  · have hC : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl := by
      rw [hCtrl, ← ofNat_eq_natCast]
    change b = touchRow b (embed (paintZero xs t0 0)) (Int.ofNat (ctrl + 0))
    rw [show paintZero xs t0 0 = xs from rfl, show ctrl + 0 = ctrl by omega]
    exact (row_ctrl_id b (embed xs) (Int.ofNat ctrl) hRow hC).symm
  · intro i s _ hi hI
    unfold clearStep
    dsimp only
    have hng : ¬ Int.ofNat i > Int.ofNat (m - 1) := not_gt_cast hi
    simp only [hng, ite_false]
    have hAt : t0 + i < xs.length := by omega
    have hfi : FitsLen (t0 + i) := FitsLen.of_le hfit (by omega)
    have hfc : FitsLen (ctrl + i + 1) := FitsLen.of_le hfitC (by omega)
    have hft : FitsLen (i + 1) := FitsLen.of_le hfitM (by omega)
    have hT : s.sudo_5Board_6tally0 = (t0 : Int) := by
      rw [hI]; simp [touchRow, hT0]
    have hRw : s.sudo_5Board_3row = embed (paintZero xs t0 i) := by rw [hI]; rfl
    have hCN : s.sudo_5Board_1t.sudo_4Tier_7control = (control : Int) := by
      rw [hI]; exact hCtrlN
    have hHi : s.sudo_5Board_4cost.sudo_5Costs_15control_highest = (high : Int) := by
      rw [hI]; exact hHigh
    have hCt : s.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (ctrl + i) := by
      rw [hI]; rfl
    have hmark := tally_put_zero s (paintZero xs t0 i) t0 i (ctrl + i) high control
        hT hRw (by rw [paintZero_length]; exact hAt) hCN (by omega) hHi (by omega) hCt hfi hfc
    rw [hmark, ok_bind]
    dsimp only
    have hpaint : (paintZero xs t0 i).set (t0 + i) 0 = paintZero xs t0 (i + 1) := by
      rw [show t0 + i = t0 + i by rfl]
      rfl
    have htouch :
        touchRow { s with sudo_5Board_3row := embed ((paintZero xs t0 i).set (t0 + i) 0) }
          (embed ((paintZero xs t0 i).set (t0 + i) 0)) (Int.ofNat (ctrl + i + 1)) =
        touchRow b (embed (paintZero xs t0 (i + 1))) (Int.ofNat (ctrl + (i + 1))) := by
      rw [hI, hpaint, show ctrl + i + 1 = ctrl + (i + 1) by omega]
      rfl
    rw [htouch]
    refine ⟨touchRow b (embed (paintZero xs t0 (i + 1))) (Int.ofNat (ctrl + (i + 1))), rfl, ?_⟩
    simp only [pure_eq_ok]
    exact asc_tail (m - 1) i hft _
  · intro s hI
    have hm1 : m - 1 + 1 = m := by omega
    rw [hI, hm1]
    rfl

/-- One peg of the climb's cube loop, with the bench off. `Ecbs.cube` of `src` onto
    `dst`, then `tally_put` of `2` at peg `j` (a keep: the cell is at or below the
    recorded high), then the control counter increases by one. The prefix is
    `Spec.fieldCube`. The source home ends empty. `tally0` and `control_highest` stay. -/
theorem cube_tally_peg (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (w h r n k moves hole bench peak peakS cOps cg : Nat)
    (t0 j high control ctrl : Nat)
    (hmk : b.sudo_5Board_9marker_on = false)
    (hoff : b.sudo_5Board_8bench_on = false)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop1 : b.sudo_5Board_4cost.sudo_5Costs_3ops[1]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1))
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (hcg : b.sudo_5Board_1t.sudo_4Tier_7combgap = Int.ofNat cg)
    (hspan : 3 * (n - 1) + cg < bench)
    (hF : src < b.sudo_5Board_4held.size)
    (hHome : src < b.sudo_5Board_4home.size)
    (hHF : b.sudo_5Board_4held[src] = true)
    (hArr : b.sudo_5Board_4home[src] = embed xs)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hn0 : 0 < n)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hlenx : xs.length = n)
    (hf : FitsLen n)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hpeakS : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hxsT : allTritList xs)
    (h3 : FitsLen (3 * (n - 1)))
    (hfm : FitsLen (moves + 2 * n))
    (hw0 : 0 < w) (hh0 : 0 < h) (hrR : r < h) (hrP : 0 < r)
    (hnE : n = w * h - 1) (hkLe : k ≤ n) (hgap : n - k = w * r)
    (hwF : b.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w)
    (hhF : b.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h)
    (hrF : b.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r)
    (hkF : b.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k)
    (hHole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole)
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ bench ≤ 1000001)
    (hnsm : n ≤ 1000000)
    (hfitB : FitsLen bench)
    (hfold : FitsLen (moves + 2 * n + 3 * (bench - n)))
    (hT0 : b.sudo_5Board_6tally0 = (t0 : Int))
    (hrow : t0 + j < b.sudo_5Board_3row.size)
    (hCtrlN : b.sudo_5Board_1t.sudo_4Tier_7control = (control : Int))
    (hic : t0 + j < control)
    (hHigh : b.sudo_5Board_4cost.sudo_5Costs_15control_highest = (high : Int))
    (hle : t0 + j ≤ high)
    (hfitJ : FitsLen (t0 + j))
    (hCtrlV : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = (ctrl : Int))
    (hfctrl : FitsLen (ctrl + 1)) :
    ∃ b',
      (do
        let b1 ← Ecbs.cube b (dst : Int) (src : Int)
        let b2 ← Ecbs.tally_put b1 (j : Int) (2 : Int)
        let v ← SudoRt.addI b2.sudo_5Board_4cost.sudo_5Costs_4ctrl (1 : Int)
        pure { b2 with sudo_5Board_4cost :=
          { b2.sudo_5Board_4cost with sudo_5Costs_4ctrl := v } }) = .ok b' ∧
      b'.sudo_5Board_8bench_on = true ∧
      b'.sudo_5Board_8bench_to = (dst : Int) ∧
      b'.sudo_5Board_5bench =
        embed (laneFold n (n - k) (combStrip n bench xs)) ∧
      (laneFold n (n - k) (combStrip n bench xs)).take n = fieldCube n k bench xs ∧
      (∀ i, n ≤ i → i < bench →
        coeff (laneFold n (n - k) (combStrip n bench xs)) i = 0) ∧
      b'.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat (cubeMoves moves xs n k bench) ∧
      b'.sudo_5Board_4cost.sudo_5Costs_4peak =
        Int.ofNat (raisedPeak peak (countHeld (b.sudo_5Board_4held.set ⟨src, hF⟩ false) 7)) ∧
      b'.sudo_5Board_4cost.sudo_5Costs_6slides = b.sudo_5Board_4cost.sudo_5Costs_6slides ∧
      b'.sudo_5Board_1t = b.sudo_5Board_1t ∧
      b'.sudo_5Board_4home = b.sudo_5Board_4home.set ⟨src, hHome⟩ #[] ∧
      b'.sudo_5Board_4held = b.sudo_5Board_4held.set ⟨src, hF⟩ false ∧
      b'.sudo_5Board_9marker_on = false ∧
      b'.sudo_5Board_3row = b.sudo_5Board_3row.set ⟨t0 + j, hrow⟩ (2 : Int) ∧
      b'.sudo_5Board_6tally0 = b.sudo_5Board_6tally0 ∧
      b'.sudo_5Board_4cost.sudo_5Costs_15control_highest =
        b.sudo_5Board_4cost.sudo_5Costs_15control_highest ∧
      b'.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (ctrl + 1) ∧
      b'.sudo_5Board_4cost.sudo_5Costs_3ops =
        b.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨1, hops⟩ (Int.ofNat (cOps + 1)) := by
  obtain ⟨b1, hb, hon, hto, hbench, hpre, hhi, hmov, hpeakR, hslides, ht, _hsz, hhome, hheld,
      hmk, hrowEq, hop, htally, hhigh, hctrlB⟩ :=
    cube_refines b dst src xs w h r n k moves hole bench peak peakS cOps cg
      hmk hoff hops hop1 hfops hbl hcg hspan hF hHome hHF hArr h7 hn0 hn hlenx hf
      hmoves hpeak hpeakS hxsT h3 hfm hw0 hh0 hrR hrP hnE hkLe hgap hwF hhF hrF hkF hHole
      hsm hnsm hfitB hfold
  rw [hb, ok_bind]
  have hT0' : b1.sudo_5Board_6tally0 = (t0 : Int) := by rw [htally]; exact hT0
  have hrow1 : t0 + j < b1.sudo_5Board_3row.size := by rw [hrowEq]; exact hrow
  have hCtrl' : b1.sudo_5Board_1t.sudo_4Tier_7control = (control : Int) := by
    rw [ht]; exact hCtrlN
  have hHigh' : b1.sudo_5Board_4cost.sudo_5Costs_15control_highest = (high : Int) := by
    rw [hhigh]; exact hHigh
  conv =>
    pattern (Ecbs.tally_put b1 _ _)
    rw [show (2 : Int) = ((2 : Nat) : Int) from ofNat_eq_natCast 2]
  rw [tally_put_keep b1 t0 j 2 high control hT0' hrow1 hCtrl' hic hHigh' hle hfitJ, ok_bind]
  have hctrl2 :
      ({ b1 with sudo_5Board_3row :=
          b1.sudo_5Board_3row.set ⟨t0 + j, hrow1⟩ (2 : Int) }).sudo_5Board_4cost.sudo_5Costs_4ctrl =
        Int.ofNat ctrl := by
    rw [hctrlB, hCtrlV, ofNat_eq_natCast]
  rw [hctrl2, addI_ofNat_one ctrl hfctrl, ok_bind, pure_eq_ok]
  refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hon
  · simpa using hto
  · simpa using hbench
  · simpa using hpre
  · simpa using hhi
  · simpa using hmov
  · simpa using hpeakR
  · simpa using hslides
  · simpa using ht
  · simpa using hhome
  · simpa using hheld
  · simpa using hmk
  · apply Array.ext
    · rw [Array.size_set, Array.size_set, hrowEq]
    · intro i hi1 hi2
      by_cases hi : i = t0 + j
      · simp [hi, Array.getElem_set]
      · simp [Array.getElem_set, hi, hrowEq]
  · simpa using htally
  · simpa using hhigh
  · rfl
  · simpa using hop

/-- The same peg step when the bench is already on and aimed at `src`, with a zero
    tail. `cube_eq_live` names the slid cube; the peg and the control counter are
    the keep-write and `addI` on that board. -/
theorem cube_tally_peg_live (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (w h r n k moves slides hole bench peak peakS cOps cg : Nat)
    (t0 j high control ctrl : Nat)
    (hmk : b.sudo_5Board_9marker_on = false)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (src : Int))
    (hH : src < b.sudo_5Board_4home.size)
    (hD : src < b.sudo_5Board_4held.size)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hempty : b.sudo_5Board_4held[src] = false)
    (hbench : b.sudo_5Board_5bench = embed xs)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hn0 : 0 < n)
    (hpos : 0 < xs.length) (hnle : n ≤ xs.length)
    (hzero : ∀ i, n ≤ i → ∀ hi : i < xs.length, xs[i] = 0)
    (hf : FitsLen n) (hfitL : FitsLen xs.length)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak)
    (hpeg : FitsLen (2 * pegCount (xs.take n)))
    (hfitM : FitsLen (moves + 2 * pegCount (xs.take n)))
    (hfitS : FitsLen (slides + 2 * pegCount (xs.take n)))
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop1 : b.sudo_5Board_4cost.sudo_5Costs_3ops[1]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1))
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (hcg : b.sudo_5Board_1t.sudo_4Tier_7combgap = Int.ofNat cg)
    (hspan : 3 * (n - 1) + cg < bench)
    (hxsT : allTritList (xs.take n))
    (h3 : FitsLen (3 * (n - 1)))
    (hfm : FitsLen (moves + 2 * pegCount (xs.take n) + 2 * n))
    (hw0 : 0 < w) (hh0 : 0 < h) (hrR : r < h) (hrP : 0 < r)
    (hnE : n = w * h - 1) (hkLe : k ≤ n) (hgap : n - k = w * r)
    (hwF : b.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w)
    (hhF : b.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h)
    (hrF : b.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r)
    (hkF : b.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k)
    (hHole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole)
    (hpeakS : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ bench ≤ 1000001)
    (hnsm : n ≤ 1000000)
    (hfitB : FitsLen bench)
    (hfold : FitsLen (moves + 2 * pegCount (xs.take n) + 2 * n + 3 * (bench - n)))
    (hT0 : b.sudo_5Board_6tally0 = (t0 : Int))
    (hrow : t0 + j < b.sudo_5Board_3row.size)
    (hCtrlN : b.sudo_5Board_1t.sudo_4Tier_7control = (control : Int))
    (hic : t0 + j < control)
    (hHigh : b.sudo_5Board_4cost.sudo_5Costs_15control_highest = (high : Int))
    (hle : t0 + j ≤ high)
    (hfitJ : FitsLen (t0 + j))
    (hCtrlV : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = (ctrl : Int))
    (hfctrl : FitsLen (ctrl + 1)) :
    let ys := xs.take n
    let mv := moves + 2 * pegCount ys
    let pk := raisedPeak peak (countHeld (b.sudo_5Board_4held.set ⟨src, hD⟩ true) 7)
    let bS := settleBoard b src hH hD xs n moves slides peak
    let hFs := settle_held_lt b src hH hD xs n moves slides peak
    ∃ b',
      (do
        let b1 ← Ecbs.cube b (dst : Int) (src : Int)
        let b2 ← Ecbs.tally_put b1 (j : Int) (2 : Int)
        let v ← SudoRt.addI b2.sudo_5Board_4cost.sudo_5Costs_4ctrl (1 : Int)
        pure { b2 with sudo_5Board_4cost :=
          { b2.sudo_5Board_4cost with sudo_5Costs_4ctrl := v } }) = .ok b' ∧
      b'.sudo_5Board_8bench_on = true ∧
      b'.sudo_5Board_8bench_to = (dst : Int) ∧
      b'.sudo_5Board_5bench = embed (laneFold n (n - k) (combStrip n bench ys)) ∧
      (laneFold n (n - k) (combStrip n bench ys)).take n = fieldCube n k bench ys ∧
      (∀ i, n ≤ i → i < bench →
        coeff (laneFold n (n - k) (combStrip n bench ys)) i = 0) ∧
      b'.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat (cubeMoves mv ys n k bench) ∧
      b'.sudo_5Board_4cost.sudo_5Costs_4peak =
        Int.ofNat (raisedPeak pk (countHeld (bS.sudo_5Board_4held.set ⟨src, hFs⟩ false) 7)) ∧
      b'.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat (slides + 2 * pegCount ys) ∧
      b'.sudo_5Board_1t = b.sudo_5Board_1t ∧
      b'.sudo_5Board_4held = bS.sudo_5Board_4held.set ⟨src, hFs⟩ false ∧
      b'.sudo_5Board_3row = b.sudo_5Board_3row.set ⟨t0 + j, hrow⟩ (2 : Int) ∧
      b'.sudo_5Board_6tally0 = b.sudo_5Board_6tally0 ∧
      b'.sudo_5Board_4cost.sudo_5Costs_15control_highest =
        b.sudo_5Board_4cost.sudo_5Costs_15control_highest ∧
      b'.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (ctrl + 1) := by
  let bC := cubeLiveBoard b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops
  rw [cube_eq_live b dst src xs w h r n k moves slides hole bench peak peakS cOps cg
      hmk hon hto hH hD h7 hempty hbench hn hn0 hpos hnle hzero hf hfitL
      hmoves hslides hpeak hpeg hfitM hfitS hops hop1 hfops hbl hcg hspan hxsT h3 hfm
      hw0 hh0 hrR hrP hnE hkLe hgap hwF hhF hrF hkF hHole hpeakS hsm hnsm hfitB hfold]
  rw [show cubeLiveBoard b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops = bC from rfl]
  have hT0' : bC.sudo_5Board_6tally0 = (t0 : Int) := by
    rw [cube_live_tally b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops]
    exact hT0
  have hrowC :=
    cube_live_row b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops
  have hrow1 : t0 + j < bC.sudo_5Board_3row.size := by rw [hrowC]; exact hrow
  have hCtrl' : bC.sudo_5Board_1t.sudo_4Tier_7control = (control : Int) := by
    rw [cube_live_tier b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops]
    exact hCtrlN
  have hHigh' : bC.sudo_5Board_4cost.sudo_5Costs_15control_highest = (high : Int) := by
    rw [cube_live_highest b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops]
    exact hHigh
  rw [show (2 : Int) = ((2 : Nat) : Int) from rfl]
  simp only [ok_bind]
  rw [tally_put_keep bC t0 j 2 high control hT0' hrow1 hCtrl' hic hHigh' hle hfitJ, ok_bind]
  have hctrl2 :
      ({ bC with sudo_5Board_3row :=
          bC.sudo_5Board_3row.set ⟨t0 + j, hrow1⟩ (2 : Int) }).sudo_5Board_4cost.sudo_5Costs_4ctrl =
        Int.ofNat ctrl := by
    rw [cube_live_ctrl b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops,
      hCtrlV, ofNat_eq_natCast]
  rw [hctrl2, addI_ofNat_one ctrl hfctrl, ok_bind, pure_eq_ok]
  refine ⟨_, rfl,
      cube_live_on b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops,
      cube_live_to b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops,
      cube_live_bench b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops,
      cube_live_prefix n k bench xs,
      cube_live_high xs n k bench hn0 (by rw [hgap]; exact Nat.mul_pos hw0 hrP),
      cube_live_moves b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops,
      cube_live_peak b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops,
      cube_live_slides b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops,
      cube_live_tier b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops,
      cube_live_held b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops,
      ?_, cube_live_tally b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops,
      cube_live_highest b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops, rfl⟩
  · apply Array.ext
    · rw [Array.size_set, Array.size_set, hrowC]
    · intro i hi1 hi2
      by_cases hi : i = t0 + j
      · simp [hi, Array.getElem_set]
      · have hne : t0 + j ≠ i := fun h => hi h.symm
        rw [Array.getElem_set, if_neg (by simpa using hne),
          Array.getElem_set, if_neg (by simpa using hne)]
        have hget {a c : Array Int} (h : a = c) (k : Nat) (ha : k < a.size) :
            a[k] = c[k]'(h ▸ ha) := by subst h; rfl
        exact hget hrowC i (by rw [Array.size_set] at hi1; exact hi1)

/-- One live cube of `src` onto `dst`, then a red tally peg at `j` and `ctrl + 1`. -/
def pegStep (bC : Ecbs.Board) (t0 j : Nat)
    (hrow : t0 + j < bC.sudo_5Board_3row.size) (ctrl : Nat) : Ecbs.Board :=
  { bC with
    sudo_5Board_3row := bC.sudo_5Board_3row.set ⟨t0 + j, hrow⟩ ((2 : Nat) : Int)
    sudo_5Board_4cost := { bC.sudo_5Board_4cost with
      sudo_5Costs_4ctrl := Int.ofNat (ctrl + 1) } }

/-- The live cube-then-red-peg step is `pegStep` of the named live cube board. -/
theorem peg_step_eq (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (w h r n k moves slides hole bench peak peakS cOps cg : Nat)
    (t0 j high control ctrl : Nat)
    (hmk : b.sudo_5Board_9marker_on = false)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (src : Int))
    (hH : src < b.sudo_5Board_4home.size)
    (hD : src < b.sudo_5Board_4held.size)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hempty : b.sudo_5Board_4held[src] = false)
    (hbench : b.sudo_5Board_5bench = embed xs)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hn0 : 0 < n)
    (hpos : 0 < xs.length) (hnle : n ≤ xs.length)
    (hzero : ∀ i, n ≤ i → ∀ hi : i < xs.length, xs[i] = 0)
    (hf : FitsLen n) (hfitL : FitsLen xs.length)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak)
    (hpeg : FitsLen (2 * pegCount (xs.take n)))
    (hfitM : FitsLen (moves + 2 * pegCount (xs.take n)))
    (hfitS : FitsLen (slides + 2 * pegCount (xs.take n)))
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop1 : b.sudo_5Board_4cost.sudo_5Costs_3ops[1]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1))
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (hcg : b.sudo_5Board_1t.sudo_4Tier_7combgap = Int.ofNat cg)
    (hspan : 3 * (n - 1) + cg < bench)
    (hxsT : allTritList (xs.take n))
    (h3 : FitsLen (3 * (n - 1)))
    (hfm : FitsLen (moves + 2 * pegCount (xs.take n) + 2 * n))
    (hw0 : 0 < w) (hh0 : 0 < h) (hrR : r < h) (hrP : 0 < r)
    (hnE : n = w * h - 1) (hkLe : k ≤ n) (hgap : n - k = w * r)
    (hwF : b.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w)
    (hhF : b.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h)
    (hrF : b.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r)
    (hkF : b.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k)
    (hHole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole)
    (hpeakS : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ bench ≤ 1000001)
    (hnsm : n ≤ 1000000)
    (hfitB : FitsLen bench)
    (hfold : FitsLen (moves + 2 * pegCount (xs.take n) + 2 * n + 3 * (bench - n)))
    (hT0 : b.sudo_5Board_6tally0 = (t0 : Int))
    (hrow : t0 + j < b.sudo_5Board_3row.size)
    (hCtrlN : b.sudo_5Board_1t.sudo_4Tier_7control = (control : Int))
    (hic : t0 + j < control)
    (hHigh : b.sudo_5Board_4cost.sudo_5Costs_15control_highest = (high : Int))
    (hle : t0 + j ≤ high)
    (hfitJ : FitsLen (t0 + j))
    (hCtrlV : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = (ctrl : Int))
    (hfctrl : FitsLen (ctrl + 1)) :
    (do
        let b1 ← Ecbs.cube b (dst : Int) (src : Int)
        let b2 ← Ecbs.tally_put b1 (j : Int) (2 : Int)
        let v ← SudoRt.addI b2.sudo_5Board_4cost.sudo_5Costs_4ctrl (1 : Int)
        pure { b2 with sudo_5Board_4cost :=
          { b2.sudo_5Board_4cost with sudo_5Costs_4ctrl := v } }) =
      .ok (pegStep
        (cubeLiveBoard b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops)
        t0 j
        (by
          rw [cube_live_row b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops]
          exact hrow)
        ctrl) := by
  let bC := cubeLiveBoard b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops
  rw [cube_eq_live b dst src xs w h r n k moves slides hole bench peak peakS cOps cg
      hmk hon hto hH hD h7 hempty hbench hn hn0 hpos hnle hzero hf hfitL
      hmoves hslides hpeak hpeg hfitM hfitS hops hop1 hfops hbl hcg hspan hxsT h3 hfm
      hw0 hh0 hrR hrP hnE hkLe hgap hwF hhF hrF hkF hHole hpeakS hsm hnsm hfitB hfold]
  conv =>
    lhs
    rw [show cubeLiveBoard b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops = bC from rfl]
  have hT0' : bC.sudo_5Board_6tally0 = (t0 : Int) := by
    rw [cube_live_tally b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops]
    exact hT0
  have hrowC :=
    cube_live_row b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops
  have hrow1 : t0 + j < bC.sudo_5Board_3row.size := by rw [hrowC]; exact hrow
  have hCtrl' : bC.sudo_5Board_1t.sudo_4Tier_7control = (control : Int) := by
    rw [cube_live_tier b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops]
    exact hCtrlN
  have hHigh' : bC.sudo_5Board_4cost.sudo_5Costs_15control_highest = (high : Int) := by
    rw [cube_live_highest b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops]
    exact hHigh
  conv =>
    lhs
    rw [show (2 : Int) = ((2 : Nat) : Int) from rfl]
  simp only [ok_bind]
  rw [tally_put_keep bC t0 j 2 high control hT0' hrow1 hCtrl' hic hHigh' hle hfitJ, ok_bind]
  have hctrl2 :
      ({ bC with sudo_5Board_3row :=
          bC.sudo_5Board_3row.set ⟨t0 + j, hrow1⟩ (2 : Int) }).sudo_5Board_4cost.sudo_5Costs_4ctrl =
        Int.ofNat ctrl := by
    rw [cube_live_ctrl b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops,
      hCtrlV, ofNat_eq_natCast]
  rw [hctrl2, addI_ofNat_one ctrl hfctrl, ok_bind, pure_eq_ok]
  unfold pegStep
  rfl

/-- Paint `count` tally pegs red, starting at `start`. -/
def paintRed (xs : List Nat) (start : Nat) : Nat → List Nat
  | 0 => xs
  | k + 1 => (paintRed xs start k).set (start + k) 2

theorem paintRed_length (xs : List Nat) (start k : Nat) :
    (paintRed xs start k).length = xs.length := by
  induction k with
  | zero => rfl
  | succ k ih => simp [paintRed, ih, List.length_set]

theorem paintRed_succ (xs : List Nat) (start k : Nat) :
    paintRed xs start (k + 1) = (paintRed xs start k).set (start + k) 2 := rfl

/-- Control counter added by one emitted rung. A later rung unparks first (`+2`)
    and then parks (`+2`); the first rung only parks. The cube loop adds one per
    tally peg. A non-final rung doubles the tally (`+2 · tally`). A non-final red
    rung also lays one more peg (`+1`). -/
def rungCtrl (ctrl tally colour : Nat) (last parked : Bool) : Nat :=
  let base := ctrl + (if parked then 4 else 2) + tally
  let doubled := if last then base else base + 2 * tally
  if !last && colour = 2 then doubled + 1 else doubled

/-- Recorded high after that rung. A final rung does not move it. A non-final
    rung's double ends on the last new peg; a non-final red rung's extra peg
    is one past that. -/
def rungHigh (high t0 tally colour : Nat) (last : Bool) : Nat :=
  if last then high
  else if colour = 2 then t0 + 2 * tally
  else t0 + 2 * tally - 1

/-- Put a parked colour back, then lift `colour` from `hole` into the parking hole. -/
def afterPark (row : List Nat) (fromHole : Int) (park hole colour : Nat) : List Nat :=
  let base :=
    if fromHole < 0 then row
    else (row.set fromHole.toNat (row.getD park 0)).set park 0
  (base.set park colour).set hole 0

/-- Tally colours one rung leaves. The cube loop paints the current segment red.
    A non-final rung then whitens that segment and lays as many white pegs again.
    A non-final red rung adds one white peg past that. -/
def afterTally (row : List Nat) (t0 tally colour : Nat) (last : Bool) : List Nat :=
  let reds := paintRed row t0 tally
  if last then reds
  else
    let wide := paintOnes (paintOnes reds t0 tally) (t0 + tally) tally
    if colour = 2 then wide.set (t0 + 2 * tally) 1 else wide

def rungRow (row : List Nat) (fromHole : Int) (park hole t0 tally colour : Nat)
    (last : Bool) : List Nat :=
  afterTally (afterPark row fromHole park hole colour) t0 tally colour last

/-- The model state one rung of the climb carries: the gap polynomial, where the
    working value sits, the tally length, the park, and the control row the
    emitted rung actually leaves (park swap, red pegs, optional double and extra
    white). `fromHole < 0` means nothing is parked. The value pair is still
    `invRung`; `fieldInv` is not changed. -/
structure ClimbModel where
  n : Nat
  k : Nat
  benchlen : Nat
  gap : List Nat
  work : List Nat
  onBench : Bool
  tally : Nat
  t0 : Nat
  parkAt : Nat
  parked : Nat
  fromHole : Int
  ridx : Nat
  ctrl : Nat
  high : Nat
  row : List Nat

/-- Board shape for `ClimbModel`. The gap value is in home 5 when `onBench` is
    false, and on the bench aimed at home 5 when `onBench` is true. The bench
    list is that value in the first `n` holes and zeros after it. The control
    row, the control counter, the recorded high, the tally length, and the park
    are the model's, exactly. Marker off.

    Moves, slides, peak, and the ops array are not pinned. A cube's move count
    is `cubeMoves` of that step's nonzero pegs, a nocopy mul's is `mulMovesNo`,
    and a peak is `raisedPeak` of a count of seven homes, so none of them is a
    function of the climb state alone. The rung domain instead carries bounds
    that make every i64 fit check in the emitted rung succeed:
    `FitsLen (moves + m * pegCharge n bench)`,
    `FitsLen (slides + m * (2 * n))`, `FitsLen (cOps + m)`, and, for each live
    mul, `FitsLen (moves + 2 * n + n * (n + 1) + 3 * (bench - n))`. A red rung
    spends that mul bound twice and one extra `pegCharge`. Peak stays at most
    `max(peak, 7)`. Those are the bounds `invert_number_refines` requires. -/
structure ClimbInv (b : Ecbs.Board) (s : ClimbModel) : Prop where
  hG : 5 < b.sudo_5Board_4home.size
  hGs : 5 < b.sudo_5Board_4held.size
  marker : b.sudo_5Board_9marker_on = false
  len : b.sudo_5Board_9tally_len = (s.tally : Int)
  ctrl : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = (s.ctrl : Int)
  high : b.sudo_5Board_4cost.sudo_5Costs_15control_highest = (s.high : Int)
  t0 : b.sudo_5Board_6tally0 = (s.t0 : Int)
  row : b.sudo_5Board_3row = embed s.row
  park : b.sudo_5Board_9park_hole = (s.parkAt : Int)
  fromP : b.sudo_5Board_11parked_from = s.fromHole
  ridx : b.sudo_5Board_8rung_idx = (s.ridx : Int)
  gapHome : s.onBench = false →
    b.sudo_5Board_4held[5]'(hGs) = true ∧
      b.sudo_5Board_4home[5]'(hG) = embed s.gap
  gapBench : s.onBench = true →
    b.sudo_5Board_8bench_on = true ∧
      b.sudo_5Board_8bench_to = (5 : Int) ∧
      b.sudo_5Board_5bench =
        embed (s.gap.take s.n ++ List.replicate (s.benchlen - s.n) 0) ∧
      s.work = s.gap

/-- One emitted rung. The gap and the tally length are `invRung`. The row, the
    counter, the recorded high, the parked-from hole, and the rung index are the
    bookkeeping that rung leaves. `hole` is the climb hole whose colour is `rung`. -/
def modelRung (s : ClimbModel) (x : List Nat) (rung hole : Nat) (last : Bool) : ClimbModel :=
  let st := invRung s.n s.k s.benchlen x s.gap s.tally rung last
  let parked := decide (0 ≤ s.fromHole)
  { s with
    gap := st.1
    work := st.1
    onBench := true
    tally := st.2
    fromHole := (hole : Int)
    parked := rung
    ridx := s.ridx + 1
    ctrl := rungCtrl s.ctrl s.tally rung last parked
    high := rungHigh s.high s.t0 s.tally rung last
    row := rungRow s.row s.fromHole s.parkAt hole s.t0 s.tally rung last }

/-- The board after that model step. The new polynomial is on the bench aimed
    at the gap. The control row and the counter are `rungRow` and `rungCtrl`. -/
def postRungBoard (b : Ecbs.Board) (s : ClimbModel) (x : List Nat)
    (rung hole : Nat) (last : Bool) : Ecbs.Board :=
  let st := invRung s.n s.k s.benchlen x s.gap s.tally rung last
  let parked := decide (0 ≤ s.fromHole)
  { b with
    sudo_5Board_9tally_len := (st.2 : Int)
    sudo_5Board_8bench_on := true
    sudo_5Board_8bench_to := (5 : Int)
    sudo_5Board_5bench :=
      embed (st.1.take s.n ++ List.replicate (s.benchlen - s.n) 0)
    sudo_5Board_3row :=
      embed (rungRow s.row s.fromHole s.parkAt hole s.t0 s.tally rung last)
    sudo_5Board_11parked_from := (hole : Int)
    sudo_5Board_8rung_idx := ((s.ridx + 1 : Nat) : Int)
    sudo_5Board_4cost := { b.sudo_5Board_4cost with
      sudo_5Costs_4ctrl := ((rungCtrl s.ctrl s.tally rung last parked : Nat) : Int)
      sudo_5Costs_15control_highest :=
        ((rungHigh s.high s.t0 s.tally rung last : Nat) : Int) } }

theorem climbInv_post (b : Ecbs.Board) (s : ClimbModel) (x : List Nat)
    (rung hole : Nat) (last : Bool) (h : ClimbInv b s) :
    ClimbInv (postRungBoard b s x rung hole last)
      (modelRung s x rung hole last) := by
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
  · simpa [postRungBoard] using h.hG
  · simpa [postRungBoard] using h.hGs
  · simpa [postRungBoard] using h.marker
  · rfl
  · rfl
  · rfl
  · simpa [postRungBoard] using h.t0
  · rfl
  · simpa [postRungBoard] using h.park
  · rfl
  · rfl
  · intro hOff
    simp [modelRung] at hOff
  · intro _
    refine ⟨rfl, rfl, ?_, rfl⟩
    simp [modelRung, postRungBoard]

/-- The gap and the tally length of one model rung are exactly `invRung`, the
    step `invClimb` folds and `fieldInv` is built from. The bookkeeping fields
    are not part of that pair. -/
theorem modelRung_value (s : ClimbModel) (x : List Nat) (rung hole : Nat) (last : Bool) :
    ((modelRung s x rung hole last).gap, (modelRung s x rung hole last).tally) =
      invRung s.n s.k s.benchlen x s.gap s.tally rung last := by
  simp [modelRung, invRung]

/-- The white-peg scan inside one rung. Holes `tally0 .. tally0 + m - 1` are `1`.
    The board is unchanged. `m > 0`. -/
theorem white_scan_loop_refines (b : Ecbs.Board) (xs : List Nat) (t0 m : Nat)
    (hm : 0 < m)
    (hT0 : b.sudo_5Board_6tally0 = (t0 : Int))
    (hRow : b.sudo_5Board_3row = embed xs)
    (hRoom : t0 + m ≤ xs.length)
    (hWhite : ∀ j (hj : j < m), xs[t0 + j]'(by omega) = 1)
    (hfit : FitsLen (t0 + m)) (hfitM : FitsLen m) :
    SudoRt.runLoopOn (Int.ofNat 0) (fuelRange (Int.ofNat 0) (Int.ofNat (m - 1)))
      (whiteStep b (Int.ofNat (m - 1)))
      (fun j => .ok (b, j))
      (fun _ => .ok (b, (0 : Int))) =
    .ok (b, Int.ofNat (m - 1)) :=
  tally_whites_hold b xs t0 m (fun j => .ok (b, j)) (fun _ => .ok (b, 0))
    hm hT0 hRow hRoom hWhite hfit hfitM

/-- The scan does not disturb a climb invariant whose tally segment is white. -/
theorem climbInv_white (b : Ecbs.Board) (s : ClimbModel) (xs : List Nat)
    (h : ClimbInv b s) (hm : 0 < s.tally)
    (hRow : s.row = xs)
    (hRoom : s.t0 + s.tally ≤ xs.length)
    (hWhite : ∀ j (hj : j < s.tally), xs[s.t0 + j]'(by omega) = 1)
    (hfit : FitsLen (s.t0 + s.tally)) (hfitM : FitsLen s.tally) :
    SudoRt.runLoopOn (Int.ofNat 0) (fuelRange (Int.ofNat 0) (Int.ofNat (s.tally - 1)))
      (whiteStep b (Int.ofNat (s.tally - 1)))
      (fun j => .ok (b, j))
      (fun _ => .ok (b, (0 : Int))) =
    .ok (b, Int.ofNat (s.tally - 1)) := by
  have hT0 : b.sudo_5Board_6tally0 = (s.t0 : Int) := h.t0
  have hR : b.sudo_5Board_3row = embed xs := by rw [h.row, hRow]
  exact white_scan_loop_refines b xs s.t0 s.tally hm hT0 hR hRoom hWhite hfit hfitM

/-- Moves one live cube can add: two per prefix peg, two per comb peg, three per folded hole. -/
def pegCharge (n bench : Nat) : Nat := 4 * n + 3 * (bench - n)

theorem liveCubeMoves_le (moves : Nat) (xs : List Nat) (n k bench : Nat) :
    cubeMoves (moves + 2 * pegCount (xs.take n)) (xs.take n) n k bench ≤
      moves + pegCharge n bench := by
  have h := cubeMoves_le (moves + 2 * pegCount (xs.take n)) (xs.take n) n k bench
  have hp := pegCount_take_le xs n
  unfold pegCharge
  omega

theorem span_n_le (n cg bench : Nat) (hn : 0 < n) (h : 3 * (n - 1) + cg < bench) :
    n ≤ bench := by omega

/-- The bench list `Ecbs.cube` leaves for a strip whose first `n` holes are the input. -/
def cubeBench (n k bench : Nat) (xs : List Nat) : List Nat :=
  laneFold n (n - k) (combStrip n bench (xs.take n))

theorem cubeBench_off (n k bench : Nat) (g : List Nat) (hlen : g.length = n) :
    laneFold n (n - k) (combStrip n bench g) = cubeBench n k bench g := by
  unfold cubeBench
  have htake : g.take n = g := by
    rw [← hlen]
    exact List.take_length g
  rw [htake]

theorem cubeBench_length (n k bench : Nat) (xs : List Nat) (hn : n ≤ bench) :
    (cubeBench n k bench xs).length = bench := by
  unfold cubeBench
  rw [laneFold_length _ _ _ (by rw [combStrip_length]; exact hn), combStrip_length]

theorem cubeBench_prefix (n k bench : Nat) (xs : List Nat) :
    (cubeBench n k bench xs).take n = fieldCube n k bench (xs.take n) :=
  cube_live_prefix n k bench xs

theorem cubeBench_zero (n k bench : Nat) (xs : List Nat)
    (hn0 : 0 < n) (hgap0 : 0 < n - k) (hn : n ≤ bench) :
    ∀ i, n ≤ i → (hi : i < (cubeBench n k bench xs).length) →
      (cubeBench n k bench xs)[i] = 0 := by
  intro i hlo hi
  have hlen := cubeBench_length n k bench xs hn
  have hc := cube_live_high xs n k bench hn0 hgap0 i hlo (by rw [hlen] at hi; exact hi)
  rw [← coeff_eq_get _ _ hi]
  simpa [cubeBench] using hc

theorem cubeBench_trits (n k bench : Nat) (xs : List Nat)
    (hxs : allTritList (xs.take n)) (hspan : 3 * (n - 1) < bench) (hn : n ≤ bench) :
    allTritList (cubeBench n k bench xs) := by
  unfold cubeBench
  have hcs := combStrip_trits (xs.take n) n bench hxs hspan
  exact laneFold_trits n (n - k) (combStrip n bench (xs.take n)) hcs (Nat.sub_le _ _)
    (by rw [combStrip_length]; exact hn)

/-- `j` cubes of `g`, as the bench list. Zero cubes is `g` itself. -/
def cubeBenchIter (n k bench : Nat) (g : List Nat) : Nat → List Nat
  | 0 => g
  | j + 1 => cubeBench n k bench (cubeBenchIter n k bench g j)

theorem cubeBenchIter_prefix (n k bench : Nat) (g : List Nat) (hlen : g.length = n) :
    ∀ j, (cubeBenchIter n k bench g j).take n = cubeTimes n k bench g j
  | 0 => by
    simp [cubeBenchIter, cubeTimes]
    rw [← hlen, List.take_length]
  | j + 1 => by
    rw [cubeBenchIter, cubeBench_prefix, cubeBenchIter_prefix n k bench g hlen j, cubeTimes]

theorem cubeBenchIter_take_trits (n k bench : Nat) (g : List Nat)
    (hlen : g.length = n) (hxs : allTritList g)
    (hspan : 3 * (n - 1) < bench) (hn : n ≤ bench) :
    ∀ j, allTritList ((cubeBenchIter n k bench g j).take n)
  | 0 => by
    rw [cubeBenchIter, ← hlen, List.take_length]
    exact hxs
  | j + 1 => by
    rw [cubeBenchIter]
    exact allTritList_take
      (cubeBench_trits n k bench (cubeBenchIter n k bench g j)
        (cubeBenchIter_take_trits n k bench g hlen hxs hspan hn j) hspan hn) n

theorem cubeBenchIter_length (n k bench : Nat) (g : List Nat) (hn : n ≤ bench) :
    ∀ j, 0 < j → (cubeBenchIter n k bench g j).length = bench
  | j + 1, _ => by
    rw [cubeBenchIter, cubeBench_length _ _ _ _ hn]

theorem cubeBenchIter_zero (n k bench : Nat) (g : List Nat)
    (hn0 : 0 < n) (hgap0 : 0 < n - k) (hn : n ≤ bench) :
    ∀ j, 0 < j → ∀ i, n ≤ i →
      (hi : i < (cubeBenchIter n k bench g j).length) →
        (cubeBenchIter n k bench g j)[i] = 0
  | j + 1, _ => by
    intro i hlo hi
    unfold cubeBenchIter at hi
    unfold cubeBenchIter
    exact cubeBench_zero n k bench (cubeBenchIter n k bench g j) hn0 hgap0 hn i hlo hi

/-- The cube-then-red-peg step with the bench off. Same record as `pegStep`, on `cubeOffBoard`. -/
theorem peg_off_eq (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (w h r n k moves hole bench peak peakS cOps cg : Nat)
    (t0 j high control ctrl : Nat)
    (hmk : b.sudo_5Board_9marker_on = false)
    (hoff : b.sudo_5Board_8bench_on = false)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop1 : b.sudo_5Board_4cost.sudo_5Costs_3ops[1]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1))
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (hcg : b.sudo_5Board_1t.sudo_4Tier_7combgap = Int.ofNat cg)
    (hspan : 3 * (n - 1) + cg < bench)
    (hF : src < b.sudo_5Board_4held.size)
    (hHome : src < b.sudo_5Board_4home.size)
    (hHF : b.sudo_5Board_4held[src] = true)
    (hArr : b.sudo_5Board_4home[src] = embed xs)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hn0 : 0 < n)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hlenx : xs.length = n)
    (hf : FitsLen n)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hpeakS : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hxsT : allTritList xs)
    (h3 : FitsLen (3 * (n - 1)))
    (hfm : FitsLen (moves + 2 * n))
    (hw0 : 0 < w) (hh0 : 0 < h) (hrR : r < h) (hrP : 0 < r)
    (hnE : n = w * h - 1) (hkLe : k ≤ n) (hgap : n - k = w * r)
    (hwF : b.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w)
    (hhF : b.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h)
    (hrF : b.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r)
    (hkF : b.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k)
    (hHole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole)
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ bench ≤ 1000001)
    (hnsm : n ≤ 1000000)
    (hfitB : FitsLen bench)
    (hfold : FitsLen (moves + 2 * n + 3 * (bench - n)))
    (hT0 : b.sudo_5Board_6tally0 = (t0 : Int))
    (hrow : t0 + j < b.sudo_5Board_3row.size)
    (hCtrlN : b.sudo_5Board_1t.sudo_4Tier_7control = (control : Int))
    (hic : t0 + j < control)
    (hHigh : b.sudo_5Board_4cost.sudo_5Costs_15control_highest = (high : Int))
    (hle : t0 + j ≤ high)
    (hfitJ : FitsLen (t0 + j))
    (hCtrlV : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = (ctrl : Int))
    (hfctrl : FitsLen (ctrl + 1)) :
    (do
        let b1 ← Ecbs.cube b (dst : Int) (src : Int)
        let b2 ← Ecbs.tally_put b1 (j : Int) (2 : Int)
        let v ← SudoRt.addI b2.sudo_5Board_4cost.sudo_5Costs_4ctrl (1 : Int)
        pure { b2 with sudo_5Board_4cost :=
          { b2.sudo_5Board_4cost with sudo_5Costs_4ctrl := v } }) =
      .ok (pegStep
        (cubeOffBoard b dst src xs n k moves hole bench peak peakS cOps hops hF hHome)
        t0 j
        (by rw [cube_off_row b dst src xs n k moves hole bench peak peakS cOps hops hF hHome]; exact hrow)
        ctrl) := by
  let bC := cubeOffBoard b dst src xs n k moves hole bench peak peakS cOps hops hF hHome
  rw [cube_off_eq b dst src xs w h r n k moves hole bench peak peakS cOps cg
      hmk hoff hops hop1 hfops hbl hcg hspan hF hHome hHF hArr h7 hn0 hn hlenx hf
      hmoves hpeak hpeakS hxsT h3 hfm hw0 hh0 hrR hrP hnE hkLe hgap hwF hhF hrF hkF hHole
      hsm hnsm hfitB hfold]
  conv =>
    lhs
    rw [show cubeOffBoard b dst src xs n k moves hole bench peak peakS cOps hops hF hHome = bC from rfl]
  have hT0' : bC.sudo_5Board_6tally0 = (t0 : Int) := by
    rw [cube_off_tally b dst src xs n k moves hole bench peak peakS cOps hops hF hHome]
    exact hT0
  have hrowC := cube_off_row b dst src xs n k moves hole bench peak peakS cOps hops hF hHome
  have hrow1 : t0 + j < bC.sudo_5Board_3row.size := by rw [hrowC]; exact hrow
  have hCtrl' : bC.sudo_5Board_1t.sudo_4Tier_7control = (control : Int) := by
    rw [cube_off_tier b dst src xs n k moves hole bench peak peakS cOps hops hF hHome]
    exact hCtrlN
  have hHigh' : bC.sudo_5Board_4cost.sudo_5Costs_15control_highest = (high : Int) := by
    rw [cube_off_highest b dst src xs n k moves hole bench peak peakS cOps hops hF hHome]
    exact hHigh
  conv =>
    lhs
    rw [show (2 : Int) = ((2 : Nat) : Int) from rfl]
  simp only [ok_bind]
  rw [tally_put_keep bC t0 j 2 high control hT0' hrow1 hCtrl' hic hHigh' hle hfitJ, ok_bind]
  have hctrl2 :
      ({ bC with sudo_5Board_3row :=
          bC.sudo_5Board_3row.set ⟨t0 + j, hrow1⟩ (2 : Int) }).sudo_5Board_4cost.sudo_5Costs_4ctrl =
        Int.ofNat ctrl := by
    rw [cube_off_ctrl b dst src xs n k moves hole bench peak peakS cOps hops hF hHome,
      hCtrlV, ofNat_eq_natCast]
  rw [hctrl2, addI_ofNat_one ctrl hfctrl, ok_bind, pure_eq_ok]
  unfold pegStep
  rfl

theorem pegStep_hrow (bC : Ecbs.Board) (t0 j : Nat)
    (h1 h2 : t0 + j < bC.sudo_5Board_3row.size) (ctrl : Nat) :
    pegStep bC t0 j h1 ctrl = pegStep bC t0 j h2 ctrl := by
  unfold pegStep
  apply board_ext <;> rfl

/-- Fixed data for one climb rung's cube-peg loop. The value starts in home `src`
    with the bench off. `m` is the tally length, so the loop runs `j = 0 .. m - 1`. -/
structure PegCtx where
  b0 : Ecbs.Board
  src : Nat
  (g row0 : List Nat)
  (w h r n k bench cg : Nat)
  (moves0 slides0 hole0 peak0 peakS0 cOps0 : Nat)
  (t0 high control ctrl0 m : Nat)
  hm : 0 < m
  hmk : b0.sudo_5Board_9marker_on = false
  hoff : b0.sudo_5Board_8bench_on = false
  hops0 : 1 < b0.sudo_5Board_4cost.sudo_5Costs_3ops.size
  hop10 : b0.sudo_5Board_4cost.sudo_5Costs_3ops[1]'(hops0) = (cOps0 : Int)
  hbl : b0.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench
  hcg : b0.sudo_5Board_1t.sudo_4Tier_7combgap = Int.ofNat cg
  hspan : 3 * (n - 1) + cg < bench
  hF : src < b0.sudo_5Board_4held.size
  hHome : src < b0.sudo_5Board_4home.size
  hHF : b0.sudo_5Board_4held[src]'(hF) = true
  hArr : b0.sudo_5Board_4home[src]'(hHome) = embed g
  h7 : 7 ≤ b0.sudo_5Board_4held.size
  hn0 : 0 < n
  hn : b0.sudo_5Board_1t.sudo_4Tier_1n = (n : Int)
  hlenx : g.length = n
  hf : FitsLen n
  hmoves0 : b0.sudo_5Board_4cost.sudo_5Costs_5moves = (moves0 : Int)
  hpeak0 : b0.sudo_5Board_4cost.sudo_5Costs_4peak = (peak0 : Int)
  hpeakS0 : b0.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS0 : Int)
  hxsT : allTritList g
  h3 : FitsLen (3 * (n - 1))
  hw0 : 0 < w
  hh0 : 0 < h
  hrR : r < h
  hrP : 0 < r
  hnE : n = w * h - 1
  hkLe : k ≤ n
  hgap : n - k = w * r
  hwF : b0.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w
  hhF : b0.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h
  hrF : b0.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r
  hkF : b0.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k
  hHole0 : b0.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole0
  hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ bench ≤ 1000001
  hnsm : n ≤ 1000000
  hfitB : FitsLen bench
  hT0 : b0.sudo_5Board_6tally0 = (t0 : Int)
  hRow : b0.sudo_5Board_3row = embed row0
  hRoom : t0 + m ≤ row0.length
  hCtrlN : b0.sudo_5Board_1t.sudo_4Tier_7control = (control : Int)
  hHigh : b0.sudo_5Board_4cost.sudo_5Costs_15control_highest = (high : Int)
  hTop : t0 + m - 1 ≤ high
  hIn : t0 + m ≤ control
  hCtrl0 : b0.sudo_5Board_4cost.sudo_5Costs_4ctrl = (ctrl0 : Int)
  hslides0 : b0.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides0
  hfitRow : FitsLen (t0 + m)
  hfitM : FitsLen m
  hBudget : FitsLen (moves0 + m * pegCharge n bench)
  hSlide : FitsLen (slides0 + m * (2 * n))
  hOpsB : FitsLen (cOps0 + m)
  hCtrlB : FitsLen (ctrl0 + m)

theorem PegCtx.gap_pos (c : PegCtx) : 0 < c.n - c.k := by
  rw [c.hgap]
  exact Nat.mul_pos c.hw0 c.hrP

theorem PegCtx.n_le (c : PegCtx) : c.n ≤ c.bench :=
  span_n_le c.n c.cg c.bench c.hn0 c.hspan

theorem PegCtx.span3 (c : PegCtx) : 3 * (c.n - 1) < c.bench := by
  have h := c.hspan
  omega

/-- The state after `i` cube-then-red-peg steps, `i > 0`. The bench holds
    `cubeBenchIter i` and is aimed at `src`. Step 0 is the bench-off peg;
    every later step is the live one. -/
structure LivePeg (c : PegCtx) (i : Nat) where
  b : Ecbs.Board
  xs : List Nat
  (moves slides hole peak peakS cOps ctrl : Nat)
  tier : b.sudo_5Board_1t = c.b0.sudo_5Board_1t
  marker : b.sudo_5Board_9marker_on = false
  onB : b.sudo_5Board_8bench_on = true
  toB : b.sudo_5Board_8bench_to = (c.src : Int)
  hH : c.src < b.sudo_5Board_4home.size
  hD : c.src < b.sudo_5Board_4held.size
  h7 : 7 ≤ b.sudo_5Board_4held.size
  hempty : b.sudo_5Board_4held[c.src]'(hD) = false
  hbench : b.sudo_5Board_5bench = embed xs
  hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves
  hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides
  hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak
  hpeakS : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int)
  hHole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole
  hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size
  hop1 : b.sudo_5Board_4cost.sudo_5Costs_3ops[1]'(hops) = (cOps : Int)
  htally : b.sudo_5Board_6tally0 = c.b0.sudo_5Board_6tally0
  hhigh : b.sudo_5Board_4cost.sudo_5Costs_15control_highest =
    c.b0.sudo_5Board_4cost.sudo_5Costs_15control_highest
  hrow : b.sudo_5Board_3row = embed (paintRed c.row0 c.t0 i)
  hctrl : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = (ctrl : Int)
  hxs : xs = cubeBenchIter c.n c.k c.bench c.g i
  hzero : ∀ j, c.n ≤ j → (hj : j < xs.length) → xs[j] = 0
  htri : allTritList (xs.take c.n)
  hpos : 0 < xs.length
  hnle : c.n ≤ xs.length
  hmovB : moves ≤ c.moves0 + i * pegCharge c.n c.bench
  hsldB : slides ≤ c.slides0 + i * (2 * c.n)
  hcOps : cOps = c.cOps0 + i
  hctrlN : ctrl = c.ctrl0 + i

private theorem idx_get {α : Type} {a b : Array α} (h : a = b) (i : Nat) (ha : i < a.size) :
    a[i] = b[i]'(h ▸ ha) := by
  subst h
  rfl

def offRowPr (c : PegCtx) :
    c.t0 <
      (cubeOffBoard c.b0 c.src c.src c.g c.n c.k c.moves0 c.hole0 c.bench
        c.peak0 c.peakS0 c.cOps0 c.hops0 c.hF c.hHome).sudo_5Board_3row.size := by
  rw [cube_off_row c.b0 c.src c.src c.g c.n c.k c.moves0 c.hole0 c.bench
      c.peak0 c.peakS0 c.cOps0 c.hops0 c.hF c.hHome, c.hRow, size_embed]
  exact Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right c.hm) c.hRoom

/-- Bench-off cube of the home value, then the red peg at tally index 0. -/
def offPeg (c : PegCtx) : Ecbs.Board :=
  pegStep
    (cubeOffBoard c.b0 c.src c.src c.g c.n c.k c.moves0 c.hole0 c.bench
      c.peak0 c.peakS0 c.cOps0 c.hops0 c.hF c.hHome)
    c.t0 0 (offRowPr c) c.ctrl0

def pegFromOff (c : PegCtx) : LivePeg c 1 where
  b := offPeg c
  xs := cubeBench c.n c.k c.bench c.g
  moves := cubeMoves c.moves0 c.g c.n c.k c.bench
  slides := c.slides0
  hole := raisedHole c.hole0 (topIdx (combStrip c.n c.bench c.g))
  peak := raisedPeak c.peak0 (countHeld (c.b0.sudo_5Board_4held.set ⟨c.src, c.hF⟩ false) 7)
  peakS := raisedPeak c.peakS0 (countHeld c.b0.sudo_5Board_4held 7)
  cOps := c.cOps0 + 1
  ctrl := c.ctrl0 + 1
  tier := by
    unfold offPeg pegStep
    rw [cube_off_tier]
  marker := by
    unfold offPeg pegStep
    rw [cube_off_marker]
  onB := by
    unfold offPeg pegStep
    rw [cube_off_on]
  toB := by
    unfold offPeg pegStep
    rw [cube_off_to]
  hH := by
    unfold offPeg pegStep
    rw [cube_off_home, Array.size_set]
    exact c.hHome
  hD := by
    unfold offPeg pegStep
    rw [cube_off_held, Array.size_set]
    exact c.hF
  h7 := by
    unfold offPeg pegStep
    rw [cube_off_held, Array.size_set]
    exact c.h7
  hempty := by
    have hHeld : c.src < (offPeg c).sudo_5Board_4held.size := by
      unfold offPeg pegStep
      rw [cube_off_held, Array.size_set]
      exact c.hF
    have hb : (offPeg c).sudo_5Board_4held =
        c.b0.sudo_5Board_4held.set ⟨c.src, c.hF⟩ false := by
      unfold offPeg pegStep
      rw [cube_off_held]
    simpa [Array.getElem_set] using idx_get hb c.src hHeld
  hbench := by
    unfold offPeg pegStep
    rw [cube_off_bench, cubeBench_off c.n c.k c.bench c.g c.hlenx]
  hmoves := by
    unfold offPeg pegStep
    rw [cube_off_moves]
  hslides := by
    unfold offPeg pegStep
    rw [cube_off_slides, c.hslides0]
  hpeak := by
    unfold offPeg pegStep
    rw [cube_off_peak]
  hpeakS := by
    unfold offPeg pegStep
    rw [cube_off_strict, ofNat_eq_natCast]
  hHole := by
    unfold offPeg pegStep
    rw [cube_off_hole]
  hops := by
    unfold offPeg pegStep
    rw [cube_off_ops, Array.size_set]
    exact c.hops0
  hop1 := by
    have hOps : 1 < (offPeg c).sudo_5Board_4cost.sudo_5Costs_3ops.size := by
      unfold offPeg pegStep
      rw [cube_off_ops, Array.size_set]
      exact c.hops0
    have hb : (offPeg c).sudo_5Board_4cost.sudo_5Costs_3ops =
        c.b0.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨1, c.hops0⟩
          (Int.ofNat (c.cOps0 + 1)) := by
      unfold offPeg pegStep
      rw [cube_off_ops]
    simpa [Array.getElem_set, ofNat_eq_natCast] using idx_get hb 1 hOps
  htally := by
    unfold offPeg pegStep
    rw [cube_off_tally]
  hhigh := by
    unfold offPeg pegStep
    rw [cube_off_highest]
  hrow := by
    unfold offPeg pegStep
    have hbase :
        (cubeOffBoard c.b0 c.src c.src c.g c.n c.k c.moves0 c.hole0 c.bench
          c.peak0 c.peakS0 c.cOps0 c.hops0 c.hF c.hHome).sudo_5Board_3row =
          embed c.row0 := by
      rw [cube_off_row, c.hRow]
    rw [array_set_congr hbase (c.t0 + 0) (offRowPr c) ((2 : Nat) : Int)]
    apply Array.ext
    · simp [Array.size_set, embed, size_embed, paintRed_length]
    · intro i hi1 hi2
      by_cases hi : i = c.t0
      · simp [hi, Array.getElem_set, embed, paintRed, ofNat_eq_natCast]
      · have hne : c.t0 ≠ i := fun h => hi h.symm
        simp [Array.getElem_set, embed, paintRed, hne, List.getElem_set]
  hctrl := by
    unfold offPeg pegStep
    rw [ofNat_eq_natCast]
  hxs := by
    unfold cubeBenchIter
    rfl
  hzero := by
    intro j hlo hj
    exact cubeBench_zero c.n c.k c.bench c.g c.hn0 c.gap_pos c.n_le j hlo hj
  htri := by
    rw [show cubeBench c.n c.k c.bench c.g = cubeBenchIter c.n c.k c.bench c.g 1 from by
      unfold cubeBenchIter; rfl]
    exact cubeBenchIter_take_trits c.n c.k c.bench c.g c.hlenx c.hxsT c.span3 c.n_le 1
  hpos := by
    have hlen := cubeBench_length c.n c.k c.bench c.g c.n_le
    rw [hlen]
    exact Nat.lt_of_lt_of_le c.hn0 c.n_le
  hnle := by
    rw [cubeBench_length c.n c.k c.bench c.g c.n_le]
    exact c.n_le
  hmovB := by
    have h := cubeMoves_le c.moves0 c.g c.n c.k c.bench
    unfold pegCharge
    omega
  hsldB := by omega
  hcOps := rfl
  hctrlN := rfl

def liveRowPr (c : PegCtx) {i : Nat} (d : LivePeg c i) (hi : i < c.m) :
    c.t0 + i <
      (cubeLiveBoard d.b c.src c.src d.xs c.n c.k d.moves d.slides d.hole c.bench
        d.peak d.peakS d.cOps d.hH d.hD d.hops).sudo_5Board_3row.size := by
  rw [cube_live_row d.b c.src c.src d.xs c.n c.k d.moves d.slides d.hole c.bench
      d.peak d.peakS d.cOps d.hH d.hD d.hops,
    d.hrow, size_embed, paintRed_length]
  exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hi c.t0) c.hRoom

/-- One live cube of the bench onto `src`, then the red peg at tally index `i`. -/
def livePegBoard (c : PegCtx) {i : Nat} (d : LivePeg c i) (hi : i < c.m) : Ecbs.Board :=
  pegStep
    (cubeLiveBoard d.b c.src c.src d.xs c.n c.k d.moves d.slides d.hole c.bench
      d.peak d.peakS d.cOps d.hH d.hD d.hops)
    c.t0 i (liveRowPr c d hi) d.ctrl

def pegNext (c : PegCtx) {i : Nat} (d : LivePeg c i) (hi : i < c.m) : LivePeg c (i + 1) where
  b := livePegBoard c d hi
  xs := cubeBench c.n c.k c.bench d.xs
  moves := cubeMoves (d.moves + 2 * pegCount (d.xs.take c.n)) (d.xs.take c.n) c.n c.k c.bench
  slides := d.slides + 2 * pegCount (d.xs.take c.n)
  hole := raisedHole d.hole (topIdx (combStrip c.n c.bench (d.xs.take c.n)))
  peak :=
    let bS := settleBoard d.b c.src d.hH d.hD d.xs c.n d.moves d.slides d.peak
    let pk := raisedPeak d.peak (countHeld (d.b.sudo_5Board_4held.set ⟨c.src, d.hD⟩ true) 7)
    let hFs := settle_held_lt d.b c.src d.hH d.hD d.xs c.n d.moves d.slides d.peak
    raisedPeak pk (countHeld (bS.sudo_5Board_4held.set ⟨c.src, hFs⟩ false) 7)
  peakS :=
    let bS := settleBoard d.b c.src d.hH d.hD d.xs c.n d.moves d.slides d.peak
    raisedPeak d.peakS (countHeld bS.sudo_5Board_4held 7)
  cOps := d.cOps + 1
  ctrl := d.ctrl + 1
  tier := by
    unfold livePegBoard pegStep
    rw [cube_live_tier, d.tier]
  marker := by
    unfold livePegBoard pegStep
    rw [cube_live_marker]
  onB := by
    unfold livePegBoard pegStep
    rw [cube_live_on]
  toB := by
    unfold livePegBoard pegStep
    rw [cube_live_to]
  hH := by
    unfold livePegBoard pegStep
    rw [cube_live_home, Array.size_set]
    exact d.hH
  hD := by
    unfold livePegBoard pegStep
    rw [cube_live_held, Array.size_set]
    exact settle_held_lt d.b c.src d.hH d.hD d.xs c.n d.moves d.slides d.peak
  h7 := by
    unfold livePegBoard pegStep
    rw [cube_live_held, Array.size_set, settle_held_eq, Array.size_set]
    exact d.h7
  hempty := by
    have hHeld : c.src < (livePegBoard c d hi).sudo_5Board_4held.size := by
      unfold livePegBoard pegStep
      rw [cube_live_held, Array.size_set]
      exact settle_held_lt d.b c.src d.hH d.hD d.xs c.n d.moves d.slides d.peak
    have hb : (livePegBoard c d hi).sudo_5Board_4held =
        (settleBoard d.b c.src d.hH d.hD d.xs c.n d.moves d.slides d.peak).sudo_5Board_4held.set
          ⟨c.src, settle_held_lt d.b c.src d.hH d.hD d.xs c.n d.moves d.slides d.peak⟩ false := by
      unfold livePegBoard pegStep
      rw [cube_live_held]
    simpa [Array.getElem_set] using idx_get hb c.src hHeld
  hbench := by
    unfold livePegBoard pegStep
    rw [cube_live_bench]
    rfl
  hmoves := by
    unfold livePegBoard pegStep
    rw [cube_live_moves]
  hslides := by
    unfold livePegBoard pegStep
    rw [cube_live_slides]
  hpeak := by
    unfold livePegBoard pegStep
    simpa using
      cube_live_peak d.b c.src c.src d.xs c.n c.k d.moves d.slides d.hole c.bench
        d.peak d.peakS d.cOps d.hH d.hD d.hops
  hpeakS := by
    unfold livePegBoard pegStep
    simpa using
      cube_live_strict d.b c.src c.src d.xs c.n c.k d.moves d.slides d.hole c.bench
        d.peak d.peakS d.cOps d.hH d.hD d.hops
  hHole := by
    unfold livePegBoard pegStep
    rw [cube_live_hole]
  hops := by
    unfold livePegBoard pegStep
    rw [cube_live_ops, Array.size_set]
    exact d.hops
  hop1 := by
    have hOps : 1 < (livePegBoard c d hi).sudo_5Board_4cost.sudo_5Costs_3ops.size := by
      unfold livePegBoard pegStep
      rw [cube_live_ops, Array.size_set]
      exact d.hops
    have hb : (livePegBoard c d hi).sudo_5Board_4cost.sudo_5Costs_3ops =
        d.b.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨1, d.hops⟩ (Int.ofNat (d.cOps + 1)) := by
      unfold livePegBoard pegStep
      rw [cube_live_ops]
    simpa [Array.getElem_set, ofNat_eq_natCast] using idx_get hb 1 hOps
  htally := by
    unfold livePegBoard pegStep
    rw [cube_live_tally, d.htally]
  hhigh := by
    unfold livePegBoard pegStep
    rw [cube_live_highest, d.hhigh]
  hrow := by
    unfold livePegBoard pegStep
    have hbase :
        (cubeLiveBoard d.b c.src c.src d.xs c.n c.k d.moves d.slides d.hole c.bench
          d.peak d.peakS d.cOps d.hH d.hD d.hops).sudo_5Board_3row =
          embed (paintRed c.row0 c.t0 i) := by
      rw [cube_live_row, d.hrow]
    rw [array_set_congr hbase (c.t0 + i) (liveRowPr c d hi) ((2 : Nat) : Int)]
    apply Array.ext
    · simp [Array.size_set, embed, size_embed, paintRed_length]
    · intro j hj1 hj2
      by_cases hj : j = c.t0 + i
      · simp [hj, Array.getElem_set, embed, paintRed, ofNat_eq_natCast]
      · have hne : c.t0 + i ≠ j := fun h => hj h.symm
        simp [Array.getElem_set, embed, paintRed, hne, List.getElem_set]
  hctrl := by
    unfold livePegBoard pegStep
    rw [ofNat_eq_natCast, d.hctrlN]
  hxs := by
    rw [d.hxs]
    conv =>
      rhs
      unfold cubeBenchIter
  hzero := by
    intro j hlo hj
    exact cubeBench_zero c.n c.k c.bench d.xs c.hn0 c.gap_pos c.n_le j hlo hj
  htri := by
    exact allTritList_take
      (cubeBench_trits c.n c.k c.bench d.xs d.htri c.span3 c.n_le) c.n
  hpos := by
    rw [cubeBench_length c.n c.k c.bench d.xs c.n_le]
    exact Nat.lt_of_lt_of_le c.hn0 c.n_le
  hnle := by
    rw [cubeBench_length c.n c.k c.bench d.xs c.n_le]
    exact c.n_le
  hmovB := by
    have h := liveCubeMoves_le d.moves d.xs c.n c.k c.bench
    have hprev := d.hmovB
    have hmul : (i + 1) * pegCharge c.n c.bench =
        i * pegCharge c.n c.bench + pegCharge c.n c.bench := by
      rw [Nat.succ_mul]
    omega
  hsldB := by
    have hp := pegCount_take_le d.xs c.n
    have hprev := d.hsldB
    have hmul : (i + 1) * (2 * c.n) = i * (2 * c.n) + 2 * c.n := by
      rw [Nat.succ_mul]
    omega
  hcOps := by rw [d.hcOps]; omega
  hctrlN := by rw [d.hctrlN]; omega

/-- After `i` steps. `i = 0` is the bench-off start; `i > 0` is `pegPack`. -/
def pegPack (c : PegCtx) : ∀ i, 0 < i → i ≤ c.m → LivePeg c i
  | 0, h, _ => absurd h (Nat.not_lt_zero 0)
  | 1, _, _ => pegFromOff c
  | i + 2, _, hle =>
    pegNext c (pegPack c (i + 1) (Nat.succ_pos i) (Nat.le_of_succ_le hle))
      (Nat.lt_of_succ_le hle)

def pegBoard : PegCtx → Nat → Ecbs.Board
  | c, 0 => c.b0
  | c, 1 => if _h : 1 ≤ c.m then offPeg c else c.b0
  | c, i + 2 =>
    if h : i + 2 ≤ c.m then
      livePegBoard c (pegPack c (i + 1) (Nat.succ_pos i) (Nat.le_of_succ_le h))
        (Nat.lt_of_succ_le h)
    else
      c.b0

theorem pegBoard_zero (c : PegCtx) : pegBoard c 0 = c.b0 := by
  simp [pegBoard]

theorem pegBoard_one (c : PegCtx) : pegBoard c 1 = offPeg c := by
  have hle : 1 ≤ c.m := Nat.succ_le_of_lt c.hm
  simp [pegBoard, hle]

theorem cont_of_board (c : Except SudoRt.Trap Ecbs.Board) (b : Ecbs.Board) (h : c = .ok b) :
    (Except.bind c fun b' => pure (SudoRt.Flow.cont (ρ := Ecbs.Board) b')) =
      .ok (SudoRt.Flow.cont (ρ := Ecbs.Board) b) := by
  subst h
  rfl

/-- Cube `src` onto itself, paint tally index `j` red, then add one to the control counter.
    This is the body of the `for` in `invert`, before the loop decides to break or continue. -/
def cubePegBody (src : Nat) (b : Ecbs.Board) (j : Int) : Except SudoRt.Trap Ecbs.Board :=
  do
    let b1 ← Ecbs.cube b (src : Int) (src : Int)
    let b2 ← Ecbs.tally_put b1 j (2 : Int)
    let v ← SudoRt.addI b2.sudo_5Board_4cost.sudo_5Costs_4ctrl (1 : Int)
    pure { b2 with sudo_5Board_4cost :=
      { b2.sudo_5Board_4cost with sudo_5Costs_4ctrl := v } }

/-- The `for j` in `invert`: that body, then break on the last index. -/
def cubePegStep (src : Nat) (toV : Int) (σ : Int × Ecbs.Board) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Ecbs.Board) Ecbs.Board) :=
  do
    let j := σ.1
    let b := σ.2
    if j > toV then
      pure (SudoRt.Flow.brk (ρ := Ecbs.Board) (j, b))
    else
      match ← (cubePegBody src b j >>= fun b' =>
          pure (SudoRt.Flow.cont (ρ := Ecbs.Board) b')) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Ecbs.Board) r)
      | .brk fs => pure (SudoRt.Flow.brk (ρ := Ecbs.Board) (j, fs))
      | .cont fs => do
          if j == toV then
            pure (SudoRt.Flow.brk (ρ := Ecbs.Board) (j, fs))
          else do
            let j' ← SudoRt.addI j (1 : Int)
            pure (SudoRt.Flow.cont (ρ := Ecbs.Board) (j', fs))

theorem pegBoard_succ (c : PegCtx) (i : Nat) (h : i + 2 ≤ c.m) :
    pegBoard c (i + 2) =
      livePegBoard c (pegPack c (i + 1) (Nat.succ_pos i) (Nat.le_of_succ_le h))
        (Nat.lt_of_succ_le h) := by
  simp [pegBoard, h]

theorem peg_tail (src toN i : Nat) (b b' : Ecbs.Board)
    (hfit : FitsLen (i + 1))
    (hng : ¬ Int.ofNat i > Int.ofNat toN)
    (hbody : cubePegBody src b (i : Int) = .ok b') :
    cubePegStep src (Int.ofNat toN) (Int.ofNat i, b) =
      (if i = toN then .ok (SudoRt.Flow.brk (Int.ofNat i, b'))
        else .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), b'))) := by
  unfold cubePegStep
  dsimp
  rw [if_neg (show ¬ ((i : Int) > (toN : Int)) from hng)]
  rw [hbody, ok_bind, pure_eq_ok]
  exact asc_tail toN i hfit b'

theorem off_body (c : PegCtx) : cubePegBody c.src c.b0 ((0 : Nat) : Int) = .ok (offPeg c) := by
  have hrow : c.t0 + 0 < c.b0.sudo_5Board_3row.size := by
    rw [c.hRow, size_embed]
    exact Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right c.hm) c.hRoom
  have h1 : 1 ≤ c.m := Nat.succ_le_of_lt c.hm
  have hfops : FitsLen (c.cOps0 + 1) := FitsLen.of_le c.hOpsB (by omega)
  have hfctrl : FitsLen (c.ctrl0 + 1) := FitsLen.of_le c.hCtrlB (by omega)
  have hfold : FitsLen (c.moves0 + 2 * c.n + 3 * (c.bench - c.n)) := by
    refine FitsLen.of_le c.hBudget ?_
    have hpiece : 2 * c.n + 3 * (c.bench - c.n) ≤ pegCharge c.n c.bench := by
      unfold pegCharge
      omega
    have hmul : pegCharge c.n c.bench ≤ c.m * pegCharge c.n c.bench := by
      simpa using Nat.mul_le_mul_right (pegCharge c.n c.bench) h1
    have hassoc : c.moves0 + 2 * c.n + 3 * (c.bench - c.n) =
        c.moves0 + (2 * c.n + 3 * (c.bench - c.n)) := by omega
    rw [hassoc]
    exact Nat.add_le_add_left (Nat.le_trans hpiece hmul) c.moves0
  have hfm : FitsLen (c.moves0 + 2 * c.n) := FitsLen.of_le hfold (by omega)
  have hfitJ : FitsLen (c.t0 + 0) := FitsLen.of_le c.hfitRow (by omega)
  have hic : c.t0 + 0 < c.control := by
    exact Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right c.hm) c.hIn
  have hle : c.t0 + 0 ≤ c.high := by
    exact Nat.le_trans (Nat.le_sub_of_add_le (Nat.add_le_add_left h1 c.t0)) c.hTop
  refine Eq.trans (peg_off_eq c.b0 c.src c.src c.g c.w c.h c.r c.n c.k c.moves0 c.hole0
      c.bench c.peak0 c.peakS0 c.cOps0 c.cg c.t0 0 c.high c.control c.ctrl0
      c.hmk c.hoff c.hops0 c.hop10 hfops c.hbl c.hcg c.hspan c.hF c.hHome c.hHF c.hArr
      c.h7 c.hn0 c.hn c.hlenx c.hf c.hmoves0 c.hpeak0 c.hpeakS0 c.hxsT c.h3 hfm
      c.hw0 c.hh0 c.hrR c.hrP c.hnE c.hkLe c.hgap c.hwF c.hhF c.hrF c.hkF c.hHole0
      c.hsm c.hnsm c.hfitB hfold c.hT0 hrow c.hCtrlN hic c.hHigh hle hfitJ c.hCtrl0 hfctrl) ?_
  apply congrArg Except.ok
  apply pegStep_hrow

theorem live_body (c : PegCtx) {i : Nat} (d : LivePeg c i) (h0 : 0 < i) (hi : i < c.m) :
    cubePegBody c.src d.b (i : Int) = .ok (livePegBoard c d hi) := by
  have hlen : d.xs.length = c.bench := by
    rw [d.hxs, cubeBenchIter_length c.n c.k c.bench c.g c.n_le i h0]
  have hfitL : FitsLen d.xs.length := by rw [hlen]; exact c.hfitB
  have hp := pegCount_take_le d.xs c.n
  have hpiece : 2 * pegCount (d.xs.take c.n) + 2 * c.n + 3 * (c.bench - c.n) ≤
      pegCharge c.n c.bench := by
    unfold pegCharge
    omega
  have hi1 : i + 1 ≤ c.m := Nat.succ_le_of_lt hi
  have hmul : (i + 1) * pegCharge c.n c.bench =
      i * pegCharge c.n c.bench + pegCharge c.n c.bench := by rw [Nat.succ_mul]
  have htail : (i + 1) * pegCharge c.n c.bench ≤ c.m * pegCharge c.n c.bench :=
    Nat.mul_le_mul_right _ hi1
  have hmov : d.moves + 2 * pegCount (d.xs.take c.n) + 2 * c.n + 3 * (c.bench - c.n) ≤
      c.moves0 + c.m * pegCharge c.n c.bench := by
    have hprev := d.hmovB
    have hassoc : d.moves + 2 * pegCount (d.xs.take c.n) + 2 * c.n + 3 * (c.bench - c.n) =
        d.moves + (2 * pegCount (d.xs.take c.n) + 2 * c.n + 3 * (c.bench - c.n)) := by omega
    rw [hassoc]
    have h1 : d.moves + pegCharge c.n c.bench ≤
        c.moves0 + (i + 1) * pegCharge c.n c.bench := by
      rw [hmul, ← Nat.add_assoc]
      exact Nat.add_le_add hprev (Nat.le_refl _)
    exact Nat.le_trans (Nat.add_le_add_left hpiece d.moves)
      (Nat.le_trans h1 (Nat.add_le_add_left htail c.moves0))
  have hfold : FitsLen (d.moves + 2 * pegCount (d.xs.take c.n) + 2 * c.n +
      3 * (c.bench - c.n)) := FitsLen.of_le c.hBudget hmov
  have hfm : FitsLen (d.moves + 2 * pegCount (d.xs.take c.n) + 2 * c.n) :=
    FitsLen.of_le hfold (by omega)
  have hfitM : FitsLen (d.moves + 2 * pegCount (d.xs.take c.n)) :=
    FitsLen.of_le hfm (by omega)
  have hpeg : FitsLen (2 * pegCount (d.xs.take c.n)) := FitsLen.of_le hfitM (by omega)
  have hsld : d.slides + 2 * pegCount (d.xs.take c.n) ≤ c.slides0 + c.m * (2 * c.n) := by
    have hprev := d.hsldB
    have h2 : 2 * pegCount (d.xs.take c.n) ≤ 2 * c.n := by omega
    have hm2 : (i + 1) * (2 * c.n) = i * (2 * c.n) + 2 * c.n := by rw [Nat.succ_mul]
    have ht2 : (i + 1) * (2 * c.n) ≤ c.m * (2 * c.n) := Nat.mul_le_mul_right _ hi1
    omega
  have hfitS : FitsLen (d.slides + 2 * pegCount (d.xs.take c.n)) :=
    FitsLen.of_le c.hSlide hsld
  have hfops : FitsLen (d.cOps + 1) := by
    rw [d.hcOps]
    exact FitsLen.of_le c.hOpsB (Nat.add_le_add_left hi1 c.cOps0)
  have hfctrl : FitsLen (d.ctrl + 1) := by
    rw [d.hctrlN]
    exact FitsLen.of_le c.hCtrlB (Nat.add_le_add_left hi1 c.ctrl0)
  have hrow : c.t0 + i < d.b.sudo_5Board_3row.size := by
    rw [d.hrow, size_embed, paintRed_length]
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hi c.t0) c.hRoom
  have hic : c.t0 + i < c.control :=
    Nat.lt_of_lt_of_le (Nat.add_lt_add_left hi c.t0) c.hIn
  have hle : c.t0 + i ≤ c.high := by
    have : c.t0 + i ≤ c.t0 + c.m - 1 := by omega
    exact Nat.le_trans this c.hTop
  have hfitJ : FitsLen (c.t0 + i) :=
    FitsLen.of_le c.hfitRow (Nat.add_le_add_left (Nat.le_of_lt hi) c.t0)
  have hn : d.b.sudo_5Board_1t.sudo_4Tier_1n = (c.n : Int) := by rw [d.tier]; exact c.hn
  have hbl : d.b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat c.bench := by
    rw [d.tier]; exact c.hbl
  have hcg : d.b.sudo_5Board_1t.sudo_4Tier_7combgap = Int.ofNat c.cg := by
    rw [d.tier]; exact c.hcg
  have hwF : d.b.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat c.w := by rw [d.tier]; exact c.hwF
  have hhF : d.b.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat c.h := by rw [d.tier]; exact c.hhF
  have hrF : d.b.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat c.r := by rw [d.tier]; exact c.hrF
  have hkF : d.b.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat c.k := by rw [d.tier]; exact c.hkF
  have hCtrlN : d.b.sudo_5Board_1t.sudo_4Tier_7control = (c.control : Int) := by
    rw [d.tier]; exact c.hCtrlN
  have hT0 : d.b.sudo_5Board_6tally0 = (c.t0 : Int) := by rw [d.htally]; exact c.hT0
  have hHigh : d.b.sudo_5Board_4cost.sudo_5Costs_15control_highest = (c.high : Int) := by
    rw [d.hhigh]; exact c.hHigh
  refine Eq.trans (peg_step_eq d.b c.src c.src d.xs c.w c.h c.r c.n c.k d.moves d.slides d.hole
      c.bench d.peak d.peakS d.cOps c.cg c.t0 i c.high c.control d.ctrl
      d.marker d.onB d.toB d.hH d.hD d.h7 d.hempty d.hbench hn c.hn0 d.hpos d.hnle d.hzero
      c.hf hfitL d.hmoves d.hslides d.hpeak hpeg hfitM hfitS d.hops d.hop1 hfops hbl hcg c.hspan
      d.htri c.h3 hfm c.hw0 c.hh0 c.hrR c.hrP c.hnE c.hkLe c.hgap hwF hhF hrF hkF d.hHole d.hpeakS
      c.hsm c.hnsm c.hfitB hfold hT0 hrow hCtrlN hic hHigh hle hfitJ d.hctrl hfctrl) ?_
  apply congrArg Except.ok
  apply pegStep_hrow

/-- `j = 0 .. m - 1` cubes of the value in home `src`, each followed by a red tally peg.
    The first cube reads the home (bench off). Every later cube is the named live board.
    The bench prefix is `Spec.cubeTimes`. -/
theorem cube_peg_loop_refines (c : PegCtx) :
    SudoRt.runLoopOn (Int.ofNat 0, c.b0)
        (fuelRange (Int.ofNat 0) (Int.ofNat (c.m - 1)))
        (cubePegStep c.src (Int.ofNat (c.m - 1)))
        (fun σ => .ok σ)
        (fun r => .ok ((0 : Int), r)) =
      .ok (Int.ofNat (c.m - 1), pegBoard c c.m) := by
  refine asc_goal (fromN := 0) (toN := c.m - 1)
      (fun i s => s = pegBoard c i)
      (Nat.zero_le _) (pegBoard_zero c).symm ?_ ?_
  · intro i s _ hi hI
    have hle1 : i + 1 ≤ c.m := by
      have h := Nat.add_le_add_right hi 1
      rwa [Nat.sub_add_cancel (Nat.succ_le_of_lt c.hm)] at h
    have hfit : FitsLen (i + 1) := FitsLen.of_le c.hfitM hle1
    have hng : ¬ Int.ofNat i > Int.ofNat (c.m - 1) := not_gt_cast hi
    cases i with
    | zero =>
      have hs : s = c.b0 := by rw [hI, pegBoard_zero]
      rw [hs]
      have hbody := off_body c
      have hstep := peg_tail c.src (c.m - 1) 0 c.b0 (offPeg c) hfit hng hbody
      rw [hstep]
      refine ⟨offPeg c, ?_, rfl⟩
      exact (pegBoard_one c).symm
    | succ k =>
      have hlt : k + 1 < c.m :=
        Nat.lt_of_le_of_lt hi (Nat.sub_lt c.hm (by decide))
      have hle : k + 1 ≤ c.m := Nat.le_of_lt hlt
      let d := pegPack c (k + 1) (Nat.succ_pos k) hle
      have hsB : s = d.b := by
        rw [hI]
        cases k with
        | zero =>
          simp [pegBoard, pegPack, hle]
          rfl
        | succ j =>
          rw [pegBoard_succ c j hle]
          conv =>
            rhs
            unfold pegPack
          rfl
      rw [hsB]
      have hbody := live_body c d (Nat.succ_pos k) hlt
      have hstep := peg_tail c.src (c.m - 1) (k + 1) d.b (livePegBoard c d hlt)
        (by simpa using hfit) hng hbody
      rw [hstep]
      refine ⟨livePegBoard c d hlt, ?_, rfl⟩
      rw [show k + 1 + 1 = k + 2 from rfl]
      exact (pegBoard_succ c k hle1).symm
  · intro s hI
    have hm1 : c.m - 1 + 1 = c.m := Nat.sub_add_cancel (Nat.succ_le_of_lt c.hm)
    rw [hI, hm1]

/-- The polynomial on the bench after `m` cube-peg steps is `cubeTimes m` of the home value. -/
theorem pegPack_times (c : PegCtx) :
    ((pegPack c c.m c.hm (Nat.le_refl _)).xs).take c.n =
      cubeTimes c.n c.k c.bench c.g c.m := by
  rw [(pegPack c c.m c.hm (Nat.le_refl _)).hxs,
    cubeBenchIter_prefix c.n c.k c.bench c.g c.hlenx]

/-- `park_rung` on the keep branch: the record `park_rung_keep` returns. -/
def parkKeepBoard (b : Ecbs.Board) (hole park rung i ctrl : Nat)
    (hRowP : park < b.sudo_5Board_3row.size)
    (hRowH : hole < b.sudo_5Board_3row.size) : Ecbs.Board :=
  { b with
    sudo_5Board_3row :=
      (b.sudo_5Board_3row.set ⟨park, hRowP⟩ ((rung : Nat) : Int)).set
        ⟨hole, by rw [Array.size_set]; exact hRowH⟩ (0 : Int)
    sudo_5Board_4cost := { b.sudo_5Board_4cost with
      sudo_5Costs_4ctrl := Int.ofNat (ctrl + 2) }
    sudo_5Board_11parked_from := (hole : Int)
    sudo_5Board_8rung_idx := Int.ofNat (i + 1) }

theorem park_rung_keep_eq (b : Ecbs.Board) (holes : List Nat)
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
      .ok (parkKeepBoard b hole park rung i ctrl hRowP hRowH) := by
  rw [park_rung_keep b holes i hole park rung high control ctrl
      hClimb hIdx hAt hHole hIdle hParkF hRowH hRowP hColour hZero hRung
      hCtrlN hParkC hHigh hLe hCtrl hFit hne hFitI]
  rfl

/-- `clear` of a held home: the record `clear_held_refines` returns. -/
def clearHeldBoard (b : Ecbs.Board) (home : Nat) (xs : List Nat) (moves : Nat)
    (hH : home < b.sudo_5Board_4home.size)
    (hD : home < b.sudo_5Board_4held.size) : Ecbs.Board :=
  { b with
    sudo_5Board_4home := b.sudo_5Board_4home.set ⟨home, hH⟩ #[]
    sudo_5Board_4held := b.sudo_5Board_4held.set ⟨home, hD⟩ false
    sudo_5Board_4cost := { b.sudo_5Board_4cost with
      sudo_5Costs_5moves := Int.ofNat (moves + pegCount xs) } }

/-- One final white rung, nothing parked yet: park (keep), copy the gap into the
    spare, scan the white tally, cube-peg loop, live nocopy mul of gap by that
    spare, clear the gap. The result is those named boards in that order.
    `c.b0` is the board after the copy. Moves, slides, peak, and the ops array
    are whatever those named boards write; they are not rewritten by hand. -/
def rungFinalBoard (b : Ecbs.Board) (hole park rung i ctrl : Nat)
    (hRowP : park < b.sudo_5Board_3row.size)
    (hRowH : hole < b.sudo_5Board_3row.size)
    (g : List Nat) (moves peak : Nat)
    (hHs : 6 < (parkKeepBoard b hole park rung i ctrl hRowP hRowH).sudo_5Board_4home.size)
    (hDs : 6 < (parkKeepBoard b hole park rung i ctrl hRowP hRowH).sudo_5Board_4held.size)
    (c : PegCtx)
    (xs ys : List Nat)
    (w h r n k mvs slides holeM bench pk pkS cOps : Nat)
    (hH6 : 6 < (pegBoard c c.m).sudo_5Board_4home.size)
    (hD6 : 6 < (pegBoard c c.m).sudo_5Board_4held.size)
    (hops0 : 0 < (pegBoard c c.m).sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hH5 : 5 < (mulNoLiveBoard (pegBoard c c.m) 5 6 xs ys n k mvs slides holeM bench
        pk pkS cOps hH6 hD6 hops0).sudo_5Board_4home.size)
    (hD5 : 5 < (mulNoLiveBoard (pegBoard c c.m) 5 6 xs ys n k mvs slides holeM bench
        pk pkS cOps hH6 hD6 hops0).sudo_5Board_4held.size)
    (movesC : Nat) : Ecbs.Board :=
  -- `placeBoard (parkKeepBoard …)` is `c.b0`. The peg loop, the live mul, and the
  -- clear are applied to that board.
  let bG := pegBoard c c.m
  let bM := mulNoLiveBoard bG 5 6 xs ys n k mvs slides holeM bench pk pkS cOps hH6 hD6 hops0
  clearHeldBoard bM 5 xs movesC hH5 hD5

/-- Final white rung (`last`, colour not `2`), starting with nothing parked.
    Park, copy into the spare, the white scan, the cube-peg loop, the live
    nocopy mul, and `clear` of the gap. Each step is the named board already
    proved for that call. -/
theorem rung_final_refines (b : Ecbs.Board) (holes : List Nat)
    (i hole park rung high control ctrl : Nat)
    (hClimb : Ecbs.climb_holes b = .ok (embed holes))
    (hIdx : b.sudo_5Board_8rung_idx = (i : Int))
    (hAt : i < holes.length) (hHole : holes[i] = hole)
    (hIdle : b.sudo_5Board_11parked_from = -1)
    (hParkF : b.sudo_5Board_9park_hole = (park : Int))
    (hRowH : hole < b.sudo_5Board_3row.size)
    (hRowP : park < b.sudo_5Board_3row.size)
    (hColour : b.sudo_5Board_3row[hole] = (rung : Int))
    (hZeroP : b.sudo_5Board_3row[park] = 0)
    (hRung : rung ≠ 0) (hNotRed : rung ≠ 2)
    (hCtrlN : b.sudo_5Board_1t.sudo_4Tier_7control = (control : Int))
    (hParkC : park < control)
    (hHigh : b.sudo_5Board_4cost.sudo_5Costs_15control_highest = (high : Int))
    (hLe : park ≤ high)
    (hCtrl : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = (ctrl : Int))
    (hFit : FitsLen (ctrl + 2))
    (hne : hole ≠ park)
    (hFitI : FitsLen (i + 1))
    (g : List Nat) (moves peak : Nat)
    (hHs : 6 < (parkKeepBoard b hole park rung i ctrl hRowP hRowH).sudo_5Board_4home.size)
    (hDs : 6 < (parkKeepBoard b hole park rung i ctrl hRowP hRowH).sudo_5Board_4held.size)
    (hH5s : 5 < (parkKeepBoard b hole park rung i ctrl hRowP hRowH).sudo_5Board_4home.size)
    (hD5s : 5 < (parkKeepBoard b hole park rung i ctrl hRowP hRowH).sudo_5Board_4held.size)
    (h7 : 7 ≤ (parkKeepBoard b hole park rung i ctrl hRowP hRowH).sudo_5Board_4held.size)
    (hsrc : (parkKeepBoard b hole park rung i ctrl hRowP hRowH).sudo_5Board_4held[5] = true)
    (harr : (parkKeepBoard b hole park rung i ctrl hRowP hRowH).sudo_5Board_4home[5] = embed g)
    (hempty : (parkKeepBoard b hole park rung i ctrl hRowP hRowH).sudo_5Board_4held[6] = false)
    (hn : (parkKeepBoard b hole park rung i ctrl hRowP hRowH).sudo_5Board_1t.sudo_4Tier_1n =
      (g.length : Int))
    (hf : FitsLen g.length)
    (hmoves : (parkKeepBoard b hole park rung i ctrl hRowP hRowH).sudo_5Board_4cost.sudo_5Costs_5moves =
      (moves : Int))
    (hpeak : (parkKeepBoard b hole park rung i ctrl hRowP hRowH).sudo_5Board_4cost.sudo_5Costs_4peak =
      (peak : Int))
    (hfit : FitsLen (moves + pegCount g))
    (c : PegCtx) (hSrc6 : c.src = 6)
    (hCopy : c.b0 = placeBoard (parkKeepBoard b hole park rung i ctrl hRowP hRowH)
      6 hHs hDs g moves peak)
    (rowXs : List Nat)
    (hT0 : c.b0.sudo_5Board_6tally0 = (c.t0 : Int))
    (hRow : c.b0.sudo_5Board_3row = embed rowXs)
    (hRoom : c.t0 + c.m ≤ rowXs.length)
    (hWhite : ∀ j (hj : j < c.m), rowXs[c.t0 + j]'(by omega) = 1)
    (hfitW : FitsLen (c.t0 + c.m))
    (xs ys : List Nat)
    (w h r n k mvs slides holeM bench pk pkS cOps : Nat)
    (hH6 : 6 < (pegBoard c c.m).sudo_5Board_4home.size)
    (hD6 : 6 < (pegBoard c c.m).sudo_5Board_4held.size)
    (hops0 : 0 < (pegBoard c c.m).sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (mulHyps : Ecbs.mul (pegBoard c c.m) (5 : Int) (5 : Int) (6 : Int) false false false =
      .ok (mulNoLiveBoard (pegBoard c c.m) 5 6 xs ys n k mvs slides holeM bench
        pk pkS cOps hH6 hD6 hops0))
    (hH5 : 5 < (mulNoLiveBoard (pegBoard c c.m) 5 6 xs ys n k mvs slides holeM bench
        pk pkS cOps hH6 hD6 hops0).sudo_5Board_4home.size)
    (hD5 : 5 < (mulNoLiveBoard (pegBoard c c.m) 5 6 xs ys n k mvs slides holeM bench
        pk pkS cOps hH6 hD6 hops0).sudo_5Board_4held.size)
    (movesC : Nat)
    (hClear : Ecbs.clear (mulNoLiveBoard (pegBoard c c.m) 5 6 xs ys n k mvs slides holeM bench
        pk pkS cOps hH6 hD6 hops0) (5 : Int) =
      .ok (clearHeldBoard (mulNoLiveBoard (pegBoard c c.m) 5 6 xs ys n k mvs slides holeM bench
        pk pkS cOps hH6 hD6 hops0) 5 xs movesC hH5 hD5)) :
    (do
        let b ← Ecbs.park_rung b (rung : Int)
        let b ← Ecbs.copy_band b ((6 : Nat) : Int) ((5 : Nat) : Int) false
        let _ ← SudoRt.runLoopOn (Int.ofNat 0)
            (fuelRange (Int.ofNat 0) (Int.ofNat (c.m - 1)))
            (whiteStep b (Int.ofNat (c.m - 1)))
            (fun j => .ok (b, j))
            (fun _ => .ok (b, (0 : Int)))
        let out ← SudoRt.runLoopOn (Int.ofNat 0, b)
            (fuelRange (Int.ofNat 0) (Int.ofNat (c.m - 1)))
            (cubePegStep c.src (Int.ofNat (c.m - 1)))
            (fun σ => .ok σ)
            (fun r => .ok ((0 : Int), r))
        let b := out.2
        let b ← Ecbs.mul b (5 : Int) (5 : Int) (6 : Int) false false false
        Ecbs.clear b (5 : Int)) =
      .ok (rungFinalBoard b hole park rung i ctrl hRowP hRowH g moves peak hHs hDs c
        xs ys w h r n k mvs slides holeM bench pk pkS cOps hH6 hD6 hops0 hH5 hD5 movesC) := by
  rw [park_rung_keep_eq b holes i hole park rung high control ctrl
      hClimb hIdx hAt hHole hIdle hParkF hRowH hRowP hColour hZeroP hRung
      hCtrlN hParkC hHigh hLe hCtrl hFit hne hFitI, ok_bind]
  rw [copy_band_refines (parkKeepBoard b hole park rung i ctrl hRowP hRowH) 6 5 g moves peak
      hHs hDs hH5s hD5s h7 hsrc harr hempty hn hf hmoves hpeak hfit, ok_bind]
  rw [← hCopy]
  rw [white_scan_loop_refines c.b0 rowXs c.t0 c.m c.hm hT0 hRow hRoom hWhite hfitW c.hfitM,
    ok_bind]
  rw [cube_peg_loop_refines c, ok_bind]
  dsimp only
  rw [mulHyps, ok_bind, hClear]
  rfl

private theorem map_ofNat_inj {xs ys : List Nat}
    (h : xs.map Int.ofNat = ys.map Int.ofNat) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => simp at h
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      simp at h
      rw [Int.ofNat.inj h.1, ih h.2]

private theorem embed_inj {xs ys : List Nat} (h : embed xs = embed ys) : xs = ys := by
  exact map_ofNat_inj (by simpa [toList_embed] using congrArg Array.toList h)

private theorem ofNat_inj_nat {a b : Nat} (h : (a : Int) = (b : Int)) : a = b :=
  Int.ofNat.inj (by simpa [ofNat_eq_natCast] using h)

/-- A list is its prefix plus a zero tail when every later entry is `0`. -/
private theorem take_zero_pad (xs : List Nat) (n : Nat)
    (hz : ∀ i, n ≤ i → (hi : i < xs.length) → xs[i] = 0) :
    xs = xs.take n ++ List.replicate (xs.length - n) 0 := by
  apply List.ext_getElem
  · simp only [List.length_append, List.length_take, List.length_replicate]
    omega
  · intro i hi _
    by_cases hlt : i < n
    · have hlen : (xs.take n).length = min n xs.length := List.length_take n xs
      have hiL : i < (xs.take n).length := by rw [hlen]; omega
      rw [List.getElem_append_left hiL, List.getElem_take]
    · have htake : (xs.take n).length ≤ i := by
        rw [List.length_take]; omega
      rw [List.getElem_append_right htake, List.getElem_replicate]
      exact hz i (Nat.le_of_not_lt hlt) hi

private theorem pegStep_book (bC : Ecbs.Board) (t0 j : Nat)
    (hrow : t0 + j < bC.sudo_5Board_3row.size) (ctrl : Nat) :
    (pegStep bC t0 j hrow ctrl).sudo_5Board_11parked_from = bC.sudo_5Board_11parked_from ∧
    (pegStep bC t0 j hrow ctrl).sudo_5Board_8rung_idx = bC.sudo_5Board_8rung_idx ∧
    (pegStep bC t0 j hrow ctrl).sudo_5Board_9tally_len = bC.sudo_5Board_9tally_len ∧
    (pegStep bC t0 j hrow ctrl).sudo_5Board_6tally0 = bC.sudo_5Board_6tally0 ∧
    (pegStep bC t0 j hrow ctrl).sudo_5Board_9park_hole = bC.sudo_5Board_9park_hole ∧
    (pegStep bC t0 j hrow ctrl).sudo_5Board_4cost.sudo_5Costs_15control_highest =
      bC.sudo_5Board_4cost.sudo_5Costs_15control_highest ∧
    (pegStep bC t0 j hrow ctrl).sudo_5Board_4home.size = bC.sudo_5Board_4home.size ∧
    (pegStep bC t0 j hrow ctrl).sudo_5Board_4held.size = bC.sudo_5Board_4held.size := by
  unfold pegStep
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem cubeOff_book (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (n k moves hole bench peak peakS cOps : Nat)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hF : src < b.sudo_5Board_4held.size)
    (hHome : src < b.sudo_5Board_4home.size) :
    (cubeOffBoard b dst src xs n k moves hole bench peak peakS cOps hops hF hHome).sudo_5Board_11parked_from
      = b.sudo_5Board_11parked_from ∧
    (cubeOffBoard b dst src xs n k moves hole bench peak peakS cOps hops hF hHome).sudo_5Board_8rung_idx
      = b.sudo_5Board_8rung_idx ∧
    (cubeOffBoard b dst src xs n k moves hole bench peak peakS cOps hops hF hHome).sudo_5Board_9tally_len
      = b.sudo_5Board_9tally_len ∧
    (cubeOffBoard b dst src xs n k moves hole bench peak peakS cOps hops hF hHome).sudo_5Board_6tally0
      = b.sudo_5Board_6tally0 ∧
    (cubeOffBoard b dst src xs n k moves hole bench peak peakS cOps hops hF hHome).sudo_5Board_9park_hole
      = b.sudo_5Board_9park_hole ∧
    (cubeOffBoard b dst src xs n k moves hole bench peak peakS cOps hops hF hHome).sudo_5Board_4cost.sudo_5Costs_15control_highest
      = b.sudo_5Board_4cost.sudo_5Costs_15control_highest := by
  unfold cubeOffBoard
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem settle_book (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (n moves slides peak : Nat) :
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_11parked_from
      = b.sudo_5Board_11parked_from ∧
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_8rung_idx
      = b.sudo_5Board_8rung_idx ∧
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_9tally_len
      = b.sudo_5Board_9tally_len ∧
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_6tally0
      = b.sudo_5Board_6tally0 ∧
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_9park_hole
      = b.sudo_5Board_9park_hole ∧
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_4cost.sudo_5Costs_15control_highest
      = b.sudo_5Board_4cost.sudo_5Costs_15control_highest ∧
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_4cost.sudo_5Costs_4ctrl
      = b.sudo_5Board_4cost.sudo_5Costs_4ctrl ∧
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_3row
      = b.sudo_5Board_3row := by
  unfold settleBoard
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem offPeg_book (c : PegCtx) :
    (offPeg c).sudo_5Board_11parked_from = c.b0.sudo_5Board_11parked_from ∧
    (offPeg c).sudo_5Board_8rung_idx = c.b0.sudo_5Board_8rung_idx ∧
    (offPeg c).sudo_5Board_9tally_len = c.b0.sudo_5Board_9tally_len ∧
    (offPeg c).sudo_5Board_6tally0 = c.b0.sudo_5Board_6tally0 ∧
    (offPeg c).sudo_5Board_9park_hole = c.b0.sudo_5Board_9park_hole ∧
    (offPeg c).sudo_5Board_4cost.sudo_5Costs_15control_highest =
      c.b0.sudo_5Board_4cost.sudo_5Costs_15control_highest ∧
    (offPeg c).sudo_5Board_4home.size = c.b0.sudo_5Board_4home.size ∧
    (offPeg c).sudo_5Board_4held.size = c.b0.sudo_5Board_4held.size := by
  unfold offPeg pegStep cubeOffBoard
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, by simp [Array.size_set], by simp [Array.size_set]⟩

private theorem cubeLive_book (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (n k moves slides hole bench peak peakS cOps : Nat)
    (hH : src < b.sudo_5Board_4home.size) (hD : src < b.sudo_5Board_4held.size)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size) :
    (cubeLiveBoard b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_11parked_from
      = b.sudo_5Board_11parked_from ∧
    (cubeLiveBoard b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_8rung_idx
      = b.sudo_5Board_8rung_idx ∧
    (cubeLiveBoard b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_9tally_len
      = b.sudo_5Board_9tally_len ∧
    (cubeLiveBoard b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_6tally0
      = b.sudo_5Board_6tally0 ∧
    (cubeLiveBoard b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_9park_hole
      = b.sudo_5Board_9park_hole ∧
    (cubeLiveBoard b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_4cost.sudo_5Costs_15control_highest
      = b.sudo_5Board_4cost.sudo_5Costs_15control_highest := by
  let bS := settleBoard b src hH hD xs n moves slides peak
  have hS := settle_book b src hH hD xs n moves slides peak
  have hC := cubeOff_book bS dst src (xs.take n) n k (moves + 2 * pegCount (xs.take n)) hole bench
    (raisedPeak peak (countHeld (b.sudo_5Board_4held.set ⟨src, hD⟩ true) 7)) peakS cOps
    (settle_ops_lt b 1 src hops hH hD xs n moves slides peak)
    (settle_held_lt b src hH hD xs n moves slides peak)
    (settle_home_lt b src hH hD xs n moves slides peak)
  unfold cubeLiveBoard
  exact ⟨hC.1.trans hS.1, hC.2.1.trans hS.2.1, hC.2.2.1.trans hS.2.2.1,
    hC.2.2.2.1.trans hS.2.2.2.1, hC.2.2.2.2.1.trans hS.2.2.2.2.1,
    hC.2.2.2.2.2.trans hS.2.2.2.2.2.1⟩

private theorem livePeg_book (c : PegCtx) {i : Nat} (d : LivePeg c i) (hi : i < c.m) :
    (livePegBoard c d hi).sudo_5Board_11parked_from = d.b.sudo_5Board_11parked_from ∧
    (livePegBoard c d hi).sudo_5Board_8rung_idx = d.b.sudo_5Board_8rung_idx ∧
    (livePegBoard c d hi).sudo_5Board_9tally_len = d.b.sudo_5Board_9tally_len ∧
    (livePegBoard c d hi).sudo_5Board_6tally0 = d.b.sudo_5Board_6tally0 ∧
    (livePegBoard c d hi).sudo_5Board_9park_hole = d.b.sudo_5Board_9park_hole ∧
    (livePegBoard c d hi).sudo_5Board_4cost.sudo_5Costs_15control_highest =
      d.b.sudo_5Board_4cost.sudo_5Costs_15control_highest ∧
    (livePegBoard c d hi).sudo_5Board_4home.size = d.b.sudo_5Board_4home.size ∧
    (livePegBoard c d hi).sudo_5Board_4held.size = d.b.sudo_5Board_4held.size := by
  have hC := cubeLive_book d.b c.src c.src d.xs c.n c.k d.moves d.slides d.hole c.bench
    d.peak d.peakS d.cOps d.hH d.hD d.hops
  have hP := pegStep_book
    (cubeLiveBoard d.b c.src c.src d.xs c.n c.k d.moves d.slides d.hole c.bench
      d.peak d.peakS d.cOps d.hH d.hD d.hops)
    c.t0 i (liveRowPr c d hi) d.ctrl
  unfold livePegBoard
  refine ⟨hP.1.trans hC.1, hP.2.1.trans hC.2.1, hP.2.2.1.trans hC.2.2.1,
    hP.2.2.2.1.trans hC.2.2.2.1, hP.2.2.2.2.1.trans hC.2.2.2.2.1,
    hP.2.2.2.2.2.1.trans hC.2.2.2.2.2, ?_, ?_⟩
  · rw [hP.2.2.2.2.2.2.1, cube_live_home, Array.size_set]
  · rw [hP.2.2.2.2.2.2.2, cube_live_held, Array.size_set, settle_held_eq, Array.size_set]

/-- `pegPack` at `i` is the board `pegBoard` names, and it still carries the
    park, the rung index, the tally length, `tally0`, the parking hole, and the
    recorded high of the bench-off start. Home and held array sizes are unchanged. -/
theorem pegPack_board (c : PegCtx) (i : Nat) (h0 : 0 < i) (hle : i ≤ c.m) :
    (pegPack c i h0 hle).b = pegBoard c i ∧
    (pegPack c i h0 hle).b.sudo_5Board_11parked_from = c.b0.sudo_5Board_11parked_from ∧
    (pegPack c i h0 hle).b.sudo_5Board_8rung_idx = c.b0.sudo_5Board_8rung_idx ∧
    (pegPack c i h0 hle).b.sudo_5Board_9tally_len = c.b0.sudo_5Board_9tally_len ∧
    (pegPack c i h0 hle).b.sudo_5Board_6tally0 = c.b0.sudo_5Board_6tally0 ∧
    (pegPack c i h0 hle).b.sudo_5Board_9park_hole = c.b0.sudo_5Board_9park_hole ∧
    (pegPack c i h0 hle).b.sudo_5Board_4cost.sudo_5Costs_15control_highest =
      c.b0.sudo_5Board_4cost.sudo_5Costs_15control_highest ∧
    (pegPack c i h0 hle).b.sudo_5Board_4home.size = c.b0.sudo_5Board_4home.size ∧
    (pegPack c i h0 hle).b.sudo_5Board_4held.size = c.b0.sudo_5Board_4held.size := by
  match i with
  | 0 => exact absurd h0 (Nat.not_lt_zero 0)
  | 1 =>
    have hle1 : 1 ≤ c.m := hle
    simp only [pegPack, pegBoard, pegFromOff, hle1, dite_true]
    have hO := offPeg_book c
    exact ⟨trivial, hO.1, hO.2.1, hO.2.2.1, hO.2.2.2.1, hO.2.2.2.2.1, hO.2.2.2.2.2.1,
      hO.2.2.2.2.2.2.1, hO.2.2.2.2.2.2.2⟩
  | n + 2 =>
    have hle1 : n + 1 ≤ c.m := Nat.le_of_succ_le hle
    have h0' : 0 < n + 1 := Nat.succ_pos n
    have ih := pegPack_board c (n + 1) h0' hle1
    have hL := livePeg_book c (pegPack c (n + 1) h0' hle1) (Nat.lt_of_succ_le hle)
    simp only [pegPack, pegBoard, pegNext, hle, dite_true]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · trivial
    · rw [hL.1, ih.2.1]
    · rw [hL.2.1, ih.2.2.1]
    · rw [hL.2.2.1, ih.2.2.2.1]
    · rw [hL.2.2.2.1, ih.2.2.2.2.1]
    · rw [hL.2.2.2.2.1, ih.2.2.2.2.2.1]
    · rw [hL.2.2.2.2.2.1, ih.2.2.2.2.2.2.1]
    · rw [hL.2.2.2.2.2.2.1, ih.2.2.2.2.2.2.2.1]
    · rw [hL.2.2.2.2.2.2.2, ih.2.2.2.2.2.2.2.2]

private theorem place_book (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat) :
    (placeBoard b home hH hD xs moves peak).sudo_5Board_3row = b.sudo_5Board_3row ∧
    (placeBoard b home hH hD xs moves peak).sudo_5Board_11parked_from =
      b.sudo_5Board_11parked_from ∧
    (placeBoard b home hH hD xs moves peak).sudo_5Board_8rung_idx = b.sudo_5Board_8rung_idx ∧
    (placeBoard b home hH hD xs moves peak).sudo_5Board_9tally_len = b.sudo_5Board_9tally_len ∧
    (placeBoard b home hH hD xs moves peak).sudo_5Board_6tally0 = b.sudo_5Board_6tally0 ∧
    (placeBoard b home hH hD xs moves peak).sudo_5Board_9park_hole = b.sudo_5Board_9park_hole ∧
    (placeBoard b home hH hD xs moves peak).sudo_5Board_4cost.sudo_5Costs_15control_highest =
      b.sudo_5Board_4cost.sudo_5Costs_15control_highest ∧
    (placeBoard b home hH hD xs moves peak).sudo_5Board_4cost.sudo_5Costs_4ctrl =
      b.sudo_5Board_4cost.sudo_5Costs_4ctrl ∧
    (placeBoard b home hH hD xs moves peak).sudo_5Board_4home.size = b.sudo_5Board_4home.size ∧
    (placeBoard b home hH hD xs moves peak).sudo_5Board_4held.size = b.sudo_5Board_4held.size := by
  unfold placeBoard
  dsimp only
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by simp [Array.size_set], by simp [Array.size_set]⟩

private theorem clearHeld_book (b : Ecbs.Board) (home : Nat) (xs : List Nat) (moves : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size) :
    (clearHeldBoard b home xs moves hH hD).sudo_5Board_3row = b.sudo_5Board_3row ∧
    (clearHeldBoard b home xs moves hH hD).sudo_5Board_11parked_from = b.sudo_5Board_11parked_from ∧
    (clearHeldBoard b home xs moves hH hD).sudo_5Board_8rung_idx = b.sudo_5Board_8rung_idx ∧
    (clearHeldBoard b home xs moves hH hD).sudo_5Board_9tally_len = b.sudo_5Board_9tally_len ∧
    (clearHeldBoard b home xs moves hH hD).sudo_5Board_6tally0 = b.sudo_5Board_6tally0 ∧
    (clearHeldBoard b home xs moves hH hD).sudo_5Board_9park_hole = b.sudo_5Board_9park_hole ∧
    (clearHeldBoard b home xs moves hH hD).sudo_5Board_4cost.sudo_5Costs_15control_highest =
      b.sudo_5Board_4cost.sudo_5Costs_15control_highest ∧
    (clearHeldBoard b home xs moves hH hD).sudo_5Board_4cost.sudo_5Costs_4ctrl =
      b.sudo_5Board_4cost.sudo_5Costs_4ctrl ∧
    (clearHeldBoard b home xs moves hH hD).sudo_5Board_8bench_on = b.sudo_5Board_8bench_on ∧
    (clearHeldBoard b home xs moves hH hD).sudo_5Board_8bench_to = b.sudo_5Board_8bench_to ∧
    (clearHeldBoard b home xs moves hH hD).sudo_5Board_5bench = b.sudo_5Board_5bench ∧
    (clearHeldBoard b home xs moves hH hD).sudo_5Board_9marker_on = b.sudo_5Board_9marker_on ∧
    (clearHeldBoard b home xs moves hH hD).sudo_5Board_4home.size = b.sudo_5Board_4home.size ∧
    (clearHeldBoard b home xs moves hH hD).sudo_5Board_4held.size = b.sudo_5Board_4held.size := by
  unfold clearHeldBoard
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    by simp [Array.size_set], by simp [Array.size_set]⟩

/-- The bench list a nocopy mul leaves is `fieldMul` of the length-`n` prefix,
    then zeros. -/
theorem mul_bench_gap (n k bench : Nat) (xs ys : List Nat)
    (hn0 : 0 < n) (hgap0 : 0 < n - k) (hn : n ≤ bench) :
    let L := laneFold n (n - k) (school n xs (ys.take n) (List.replicate bench 0) false)
    L = fieldMul n k bench xs (ys.take n) ++ List.replicate (bench - n) 0 := by
  intro L
  have hsch : (school n xs (ys.take n) (List.replicate bench 0) false).length = bench := by
    simpa [List.length_replicate] using
      school_length xs (ys.take n) (List.replicate bench 0) false n
  have hlen : L.length = bench := by
    simpa [L, hsch] using
      laneFold_length n (n - k) (school n xs (ys.take n) (List.replicate bench 0) false)
        (by rw [hsch]; exact hn)
  have hpre : L.take n = fieldMul n k bench xs (ys.take n) := by
    simpa [L] using mul_live_prefix n k bench xs ys
  have hz : ∀ i, n ≤ i → (hi : i < L.length) → L[i] = 0 := by
    intro i hlo hi
    have hcoeff := mul_no_high xs (ys.take n) n k bench hn0 hgap0 i hlo (by rw [hlen] at hi; exact hi)
    have hget := coeff_eq_get L i hi
    -- mul_no_high is about `ys`, not `ys.take n`. The school argument differs.
    exact (hget.symm.trans hcoeff)
  have hpad := take_zero_pad L n hz
  rw [hpad, hpre, hlen]

private theorem mulOff_book (b : Ecbs.Board) (dst second : Nat) (xs ys : List Nat)
    (n k moves hole bench peak peakS cOps : Nat)
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hS : second < b.sudo_5Board_4held.size)
    (hHomeS : second < b.sudo_5Board_4home.size) :
    (mulNoOffBoard b dst second xs ys n k moves hole bench peak peakS cOps hops hS hHomeS).sudo_5Board_11parked_from
      = b.sudo_5Board_11parked_from ∧
    (mulNoOffBoard b dst second xs ys n k moves hole bench peak peakS cOps hops hS hHomeS).sudo_5Board_8rung_idx
      = b.sudo_5Board_8rung_idx ∧
    (mulNoOffBoard b dst second xs ys n k moves hole bench peak peakS cOps hops hS hHomeS).sudo_5Board_9tally_len
      = b.sudo_5Board_9tally_len ∧
    (mulNoOffBoard b dst second xs ys n k moves hole bench peak peakS cOps hops hS hHomeS).sudo_5Board_6tally0
      = b.sudo_5Board_6tally0 ∧
    (mulNoOffBoard b dst second xs ys n k moves hole bench peak peakS cOps hops hS hHomeS).sudo_5Board_9park_hole
      = b.sudo_5Board_9park_hole ∧
    (mulNoOffBoard b dst second xs ys n k moves hole bench peak peakS cOps hops hS hHomeS).sudo_5Board_4cost.sudo_5Costs_15control_highest
      = b.sudo_5Board_4cost.sudo_5Costs_15control_highest ∧
    (mulNoOffBoard b dst second xs ys n k moves hole bench peak peakS cOps hops hS hHomeS).sudo_5Board_4cost.sudo_5Costs_4ctrl
      = b.sudo_5Board_4cost.sudo_5Costs_4ctrl ∧
    (mulNoOffBoard b dst second xs ys n k moves hole bench peak peakS cOps hops hS hHomeS).sudo_5Board_3row
      = b.sudo_5Board_3row := by
  unfold mulNoOffBoard
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem mulLive_book (b : Ecbs.Board) (dst second : Nat) (xs ys : List Nat)
    (n k moves slides hole bench peak peakS cOps : Nat)
    (hH : second < b.sudo_5Board_4home.size) (hD : second < b.sudo_5Board_4held.size)
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size) :
    (mulNoLiveBoard b dst second xs ys n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_11parked_from
      = b.sudo_5Board_11parked_from ∧
    (mulNoLiveBoard b dst second xs ys n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_8rung_idx
      = b.sudo_5Board_8rung_idx ∧
    (mulNoLiveBoard b dst second xs ys n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_9tally_len
      = b.sudo_5Board_9tally_len ∧
    (mulNoLiveBoard b dst second xs ys n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_6tally0
      = b.sudo_5Board_6tally0 ∧
    (mulNoLiveBoard b dst second xs ys n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_9park_hole
      = b.sudo_5Board_9park_hole ∧
    (mulNoLiveBoard b dst second xs ys n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_4cost.sudo_5Costs_15control_highest
      = b.sudo_5Board_4cost.sudo_5Costs_15control_highest ∧
    (mulNoLiveBoard b dst second xs ys n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_4cost.sudo_5Costs_4ctrl
      = b.sudo_5Board_4cost.sudo_5Costs_4ctrl ∧
    (mulNoLiveBoard b dst second xs ys n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_3row
      = b.sudo_5Board_3row := by
  let bS := settleBoard b second hH hD ys n moves slides peak
  have hS := settle_book b second hH hD ys n moves slides peak
  have hM := mulOff_book bS dst second xs (ys.take n) n k (moves + 2 * pegCount (ys.take n)) hole bench
    (raisedPeak peak (countHeld (b.sudo_5Board_4held.set ⟨second, hD⟩ true) 7)) peakS cOps
    (settle_ops_lt b 0 second hops hH hD ys n moves slides peak)
    (settle_held_lt b second hH hD ys n moves slides peak)
    (settle_home_lt b second hH hD ys n moves slides peak)
  unfold mulNoLiveBoard
  exact ⟨hM.1.trans hS.1, hM.2.1.trans hS.2.1, hM.2.2.1.trans hS.2.2.1,
    hM.2.2.2.1.trans hS.2.2.2.1, hM.2.2.2.2.1.trans hS.2.2.2.2.1,
    hM.2.2.2.2.2.1.trans hS.2.2.2.2.2.1, hM.2.2.2.2.2.2.1.trans hS.2.2.2.2.2.2.1,
    hM.2.2.2.2.2.2.2.trans hS.2.2.2.2.2.2.2⟩

/-- Parking on the keep branch is `afterPark` when nothing is parked yet. -/
private theorem parkKeep_row (b : Ecbs.Board) (xs : List Nat)
    (hole park rung i ctrl : Nat)
    (hRowP : park < b.sudo_5Board_3row.size)
    (hRowH : hole < b.sudo_5Board_3row.size)
    (hrow : b.sudo_5Board_3row = embed xs)
    (hp : park < xs.length) (hh : hole < xs.length) :
    (parkKeepBoard b hole park rung i ctrl hRowP hRowH).sudo_5Board_3row =
      embed ((xs.set park rung).set hole 0) := by
  apply Array.ext
  · unfold parkKeepBoard
    rw [Array.size_set, Array.size_set, hrow, size_embed, size_embed, List.length_set, List.length_set]
  · intro j _hj1 _hj2
    by_cases hj : hole = j
    · simp [parkKeepBoard, hj, hrow, embed, Array.getElem_set, Array.getElem_mk,
        List.getElem_set, ofNat_eq_natCast, hh]
    · by_cases hpj : park = j
      · simp [parkKeepBoard, hj, hpj, hrow, embed, Array.getElem_set, Array.getElem_mk,
          List.getElem_set, ofNat_eq_natCast, hp]
      · simp [parkKeepBoard, hj, hpj, hrow, embed, Array.getElem_set, Array.getElem_mk,
          List.getElem_set, ofNat_eq_natCast]

/-- On a final rung the model does not double and does not lay the extra peg.
    A non-red rung's gap is `fieldMul` of the gap by `cubeTimes`. -/
theorem model_final_white (s : ClimbModel) (x : List Nat) (rung hole : Nat)
    (hNe : rung ≠ 2) (hFrom : s.fromHole < 0) :
    (modelRung s x rung hole true).gap =
      fieldMul s.n s.k s.benchlen s.gap
        (cubeTimes s.n s.k s.benchlen s.gap s.tally) ∧
    (modelRung s x rung hole true).tally = s.tally ∧
    (modelRung s x rung hole true).onBench = true ∧
    (modelRung s x rung hole true).work =
      fieldMul s.n s.k s.benchlen s.gap
        (cubeTimes s.n s.k s.benchlen s.gap s.tally) ∧
    (modelRung s x rung hole true).ctrl = s.ctrl + 2 + s.tally ∧
    (modelRung s x rung hole true).high = s.high ∧
    (modelRung s x rung hole true).row =
      paintRed (afterPark s.row s.fromHole s.parkAt hole rung) s.t0 s.tally ∧
    (modelRung s x rung hole true).fromHole = (hole : Int) ∧
    (modelRung s x rung hole true).ridx = s.ridx + 1 ∧
    (modelRung s x rung hole true).t0 = s.t0 ∧
    (modelRung s x rung hole true).parkAt = s.parkAt ∧
    (modelRung s x rung hole true).n = s.n ∧
    (modelRung s x rung hole true).k = s.k ∧
    (modelRung s x rung hole true).benchlen = s.benchlen := by
  have hpark : decide (0 ≤ s.fromHole) = false := by
    rw [decide_eq_false_iff_not]
    omega
  simp [modelRung, invRung, rungCtrl, rungHigh, rungRow, afterTally, hNe, hpark]

/-- A final white rung, nothing parked yet. The named board — park, copy, the
    cube-peg loop, `mulNoLiveBoard`, `clear` — satisfies `ClimbInv` for
    `modelRung`. The gap is the `fieldMul` projection of that mul. The control
    row is the park write, then the red tally pegs. The counter is the park
    write plus one per tally peg. Moves, slides, peak, and the ops array stay
    under the bounds in `ClimbInv`'s docstring. -/
theorem climbInv_rung_final (b : Ecbs.Board) (s : ClimbModel) (x : List Nat)
    (hole park rung i ctrl : Nat)
    (hRowP : park < b.sudo_5Board_3row.size)
    (hRowH : hole < b.sudo_5Board_3row.size)
    (g : List Nat) (moves peak : Nat)
    (hHs : 6 < (parkKeepBoard b hole park rung i ctrl hRowP hRowH).sudo_5Board_4home.size)
    (hDs : 6 < (parkKeepBoard b hole park rung i ctrl hRowP hRowH).sudo_5Board_4held.size)
    (c : PegCtx)
    (hInv : ClimbInv b s) (hFrom : s.fromHole = -1) (hNe : rung ≠ 2)
    (hParkF : b.sudo_5Board_9park_hole = (park : Int))
    (hCtrl0 : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = (ctrl : Int))
    (hIdx : b.sudo_5Board_8rung_idx = (i : Int))
    (hCopy : c.b0 = placeBoard (parkKeepBoard b hole park rung i ctrl hRowP hRowH)
      6 hHs hDs g moves peak)
    (hmt : c.m = s.tally) (hgg : c.g = s.gap) (hnn : c.n = s.n) (hkk : c.k = s.k)
    (hbb : c.bench = s.benchlen)
    (xs ys : List Nat) (hxs : xs = c.g)
    (hys : ys = (pegPack c c.m c.hm (Nat.le_refl _)).xs)
    (w h r n k mvs slides holeM bench pk pkS cOps : Nat)
    (hn : n = c.n) (hk : k = c.k) (hb : bench = c.bench)
    (hH6 : 6 < (pegBoard c c.m).sudo_5Board_4home.size)
    (hD6 : 6 < (pegBoard c c.m).sudo_5Board_4held.size)
    (hops0 : 0 < (pegBoard c c.m).sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hH5 : 5 < (mulNoLiveBoard (pegBoard c c.m) 5 6 xs ys n k mvs slides holeM bench
        pk pkS cOps hH6 hD6 hops0).sudo_5Board_4home.size)
    (hD5 : 5 < (mulNoLiveBoard (pegBoard c c.m) 5 6 xs ys n k mvs slides holeM bench
        pk pkS cOps hH6 hD6 hops0).sudo_5Board_4held.size)
    (movesC : Nat) :
    ClimbInv
      (rungFinalBoard b hole park rung i ctrl hRowP hRowH g moves peak hHs hDs c
        xs ys w h r n k mvs slides holeM bench pk pkS cOps hH6 hD6 hops0 hH5 hD5 movesC)
      (modelRung s x rung hole true) := by
  have hlt : s.fromHole < 0 := by rw [hFrom]; decide
  have hMod := model_final_white s x rung hole hNe hlt
  subst hn hk hb hxs hys
  let d := pegPack c c.m c.hm (Nat.le_refl _)
  have hPack := pegPack_board c c.m c.hm (Nat.le_refl _)
  let bM := mulNoLiveBoard (pegBoard c c.m) 5 6 c.g d.xs c.n c.k mvs slides holeM c.bench
    pk pkS cOps hH6 hD6 hops0
  have hMul := mulLive_book (pegBoard c c.m) 5 6 c.g d.xs c.n c.k mvs slides holeM c.bench
    pk pkS cOps hH6 hD6 hops0
  have hClr := clearHeld_book bM 5 c.g movesC hH5 hD5
  have hPl := place_book (parkKeepBoard b hole park rung i ctrl hRowP hRowH) 6 hHs hDs g moves peak
  have hpAt : park = s.parkAt :=
    ofNat_inj_nat (by rw [← hParkF, hInv.park])
  have hpL : park < s.row.length := by
    have hsz := hRowP
    rw [hInv.row, size_embed] at hsz
    exact hsz
  have hhL : hole < s.row.length := by
    have hsz := hRowH
    rw [hInv.row, size_embed] at hsz
    exact hsz
  have hParkRow := parkKeep_row b s.row hole park rung i ctrl hRowP hRowH hInv.row hpL hhL
  have hRow0 : c.row0 = (s.row.set park rung).set hole 0 := by
    apply embed_inj
    rw [← c.hRow, hCopy, hPl.1, hParkRow]
  have hAfter : afterPark s.row s.fromHole s.parkAt hole rung =
      (s.row.set park rung).set hole 0 := by
    simp [afterPark, hFrom, hpAt]
  have ht0 : c.t0 = s.t0 := by
    have hpres : c.b0.sudo_5Board_6tally0 = b.sudo_5Board_6tally0 := by
      rw [hCopy, hPl.2.2.2.2.1]
      unfold parkKeepBoard
      rfl
    exact ofNat_inj_nat (by rw [← c.hT0, hpres, hInv.t0])
  have hctrlN : c.ctrl0 = s.ctrl + 2 := by
    have hpres : c.b0.sudo_5Board_4cost.sudo_5Costs_4ctrl =
        Int.ofNat (ctrl + 2) := by
      rw [hCopy, hPl.2.2.2.2.2.2.2.1]
      unfold parkKeepBoard
      rfl
    have hctrl : ctrl = s.ctrl := ofNat_inj_nat (by rw [← hCtrl0, hInv.ctrl])
    exact ofNat_inj_nat (by rw [← c.hCtrl0, hpres, hctrl, ofNat_eq_natCast])
  have hiN : i = s.ridx := ofNat_inj_nat (by rw [← hIdx, hInv.ridx])
  unfold rungFinalBoard
  dsimp only
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
  · rw [hClr.2.2.2.2.2.2.2.2.2.2.2.2.1, mul_live_home, Array.size_set, ← hPack.1,
      hPack.2.2.2.2.2.2.2.1, hCopy, hPl.2.2.2.2.2.2.2.2.1]
    unfold parkKeepBoard
    simpa [Array.size_set] using hInv.hG
  · rw [hClr.2.2.2.2.2.2.2.2.2.2.2.2.2, mul_live_held, Array.size_set, settle_held_eq,
      Array.size_set, ← hPack.1, hPack.2.2.2.2.2.2.2.2, hCopy, hPl.2.2.2.2.2.2.2.2.2]
    unfold parkKeepBoard
    simpa [Array.size_set] using hInv.hGs
  · rw [hClr.2.2.2.2.2.2.2.2.2.2.2.1, mul_live_marker]
  · rw [hClr.2.2.2.1, hMul.2.2.1, ← hPack.1, hPack.2.2.2.1, hCopy, hPl.2.2.2.1]
    unfold parkKeepBoard
    rw [hInv.len, hMod.2.1]
  · rw [hClr.2.2.2.2.2.2.2.1, hMul.2.2.2.2.2.2.1, ← hPack.1, d.hctrl, d.hctrlN, hctrlN,
      hMod.2.2.2.2.1]
    omega
  · rw [hClr.2.2.2.2.2.2.1, hMul.2.2.2.2.2.1, ← hPack.1, hPack.2.2.2.2.2.2.1, hCopy,
      hPl.2.2.2.2.2.2.1]
    unfold parkKeepBoard
    rw [hInv.high, hMod.2.2.2.2.2.1]
  · rw [hClr.2.2.2.2.1, hMul.2.2.2.1, ← hPack.1, hPack.2.2.2.2.1, hCopy, hPl.2.2.2.2.1]
    unfold parkKeepBoard
    rw [hInv.t0, hMod.2.2.2.2.2.2.2.2.2.1]
  · rw [hClr.1, hMul.2.2.2.2.2.2.2, ← hPack.1, d.hrow, hRow0, ht0, hmt, hMod.2.2.2.2.2.2.1, hAfter]
  · rw [hClr.2.2.2.2.2.1, hMul.2.2.2.2.1, ← hPack.1, hPack.2.2.2.2.2.1, hCopy, hPl.2.2.2.2.2.1]
    unfold parkKeepBoard
    rw [hInv.park, hMod.2.2.2.2.2.2.2.2.2.2.1]
  · rw [hClr.2.1, hMul.1, ← hPack.1, hPack.2.1, hCopy, hPl.2.1]
    unfold parkKeepBoard
    rw [hMod.2.2.2.2.2.2.2.1]
  · rw [hClr.2.2.1, hMul.2.1, ← hPack.1, hPack.2.2.1, hCopy, hPl.2.2.1]
    unfold parkKeepBoard
    rw [hiN, hMod.2.2.2.2.2.2.2.2.1, ofNat_eq_natCast]
    rfl
  · intro hOff
    simp [modelRung] at hOff
  · intro _
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hClr.2.2.2.2.2.2.2.2.1]
      simp [bM, mulNoLiveBoard, mul_no_on]
    · rw [hClr.2.2.2.2.2.2.2.2.2.1]
      simp [bM, mulNoLiveBoard, mul_no_to]
    · rw [hClr.2.2.2.2.2.2.2.2.2.2.1, mul_live_bench]
      have hgap := mul_bench_gap c.n c.k c.bench c.g d.xs c.hn0 c.gap_pos c.n_le
      have hpre : d.xs.take c.n = cubeTimes c.n c.k c.bench c.g c.m := by
        simpa [d] using pegPack_times c
      rw [hgap, hpre, hmt, hgg, hnn, hkk, hbb, ← hMod.1]
      have hnM : (modelRung s x rung hole true).n = s.n := rfl
      have hbM : (modelRung s x rung hole true).benchlen = s.benchlen := rfl
      rw [hnM, hbM]
      have hlen : (fieldMul c.n c.k c.bench c.g (d.xs.take c.n)).length = c.n := by
        rw [← mul_live_prefix c.n c.k c.bench c.g d.xs, List.length_take]
        have hsch : (school c.n c.g (d.xs.take c.n) (List.replicate c.bench 0) false).length =
            c.bench := by
          simpa [List.length_replicate] using
            school_length c.g (d.xs.take c.n) (List.replicate c.bench 0) false c.n
        have hll : (laneFold c.n (c.n - c.k)
            (school c.n c.g (d.xs.take c.n) (List.replicate c.bench 0) false)).length = c.bench := by
          rw [laneFold_length]
          · exact hsch
          · rw [hsch]; exact c.n_le
        rw [hll, Nat.min_eq_left c.n_le]
      have htake : (modelRung s x rung hole true).gap.take s.n =
          (modelRung s x rung hole true).gap := by
        have hgl : (modelRung s x rung hole true).gap.length = s.n := by
          rw [hMod.1, ← hnn, ← hkk, ← hbb, ← hgg, ← hmt, ← hpre, hlen]
        rw [← hgl]
        exact List.take_length _
      rw [htake]
    · rw [hMod.2.2.2.1, hMod.1]

/-- `tally_double` after a rung that has already returned `.ok b`. For a non-final
    white rung, `step` is the park-copy-scan-cube-mul-clear composition. -/
theorem rung_double_refines (step : Except SudoRt.Trap Ecbs.Board) (b : Ecbs.Board)
    (xs : List Nat) (t0 m c0 high control tmax : Nat)
    (hStep : step = .ok b)
    (hm : 0 < m)
    (hLen : b.sudo_5Board_9tally_len = (m : Int))
    (hT0 : b.sudo_5Board_6tally0 = (t0 : Int))
    (hRow : b.sudo_5Board_3row = embed xs)
    (hRoom : t0 + 2 * m ≤ xs.length)
    (hRed : ∀ j (hj : j < m), xs[t0 + j]'(by omega) = 2)
    (hZero : ∀ k (hk : k < m), xs[t0 + m + k]'(by omega) = 0)
    (hCtrlN : b.sudo_5Board_1t.sudo_4Tier_7control = (control : Int))
    (hHigh : b.sudo_5Board_4cost.sudo_5Costs_15control_highest = (high : Int))
    (hTop : high = t0 + m - 1)
    (hCtrl : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = (c0 : Int))
    (hIn : t0 + 2 * m ≤ control)
    (hfit : FitsLen (t0 + 2 * m))
    (hfitC : FitsLen (c0 + 2 * m))
    (hfitM : FitsLen (2 * m))
    (hMax : b.sudo_5Board_4cost.sudo_5Costs_9tally_max = (tmax : Int))
    (hNote : tmax < 2 * m) :
    (do
        let b ← step
        Ecbs.tally_double b) =
      .ok { b with
        sudo_5Board_3row := embed (paintOnes (paintOnes xs t0 m) (t0 + m) m)
        sudo_5Board_9tally_len := Int.ofNat (2 * m)
        sudo_5Board_4cost := { b.sudo_5Board_4cost with
          sudo_5Costs_4ctrl := Int.ofNat (c0 + 2 * m)
          sudo_5Costs_15control_highest := ((t0 + 2 * m - 1 : Nat) : Int)
          sudo_5Costs_9tally_max := Int.ofNat (2 * m) } } := by
  rw [hStep, ok_bind,
    tally_double_refines b xs t0 m c0 high control tmax hm hLen hT0 hRow hRoom hRed hZero
      hCtrlN hHigh hTop hCtrl hIn hfit hfitC hfitM hMax hNote]

end EcbsLink2.Link2
