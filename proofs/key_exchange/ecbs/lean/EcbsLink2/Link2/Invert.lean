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

end EcbsLink2.Link2
