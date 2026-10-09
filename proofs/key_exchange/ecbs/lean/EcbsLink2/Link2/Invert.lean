/-
  Pieces of `invert`: `set_control`, then the ladder walk. Proof-only.
  Not a security claim.
-/
import EcbsLink2.Link2.Board
import EcbsLink2.Link2.BoardBuild
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

theorem paintOnes_get_lo (xs : List Nat) (start k j : Nat)
    (hj : j < k) (hk : start + k ≤ xs.length) :
    (paintOnes xs start k)[start + j]'(by
      rw [paintOnes_length]
      exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj start) hk) = 1 := by
  induction k generalizing j with
  | zero => omega
  | succ k ih =>
    simp only [paintOnes]
    by_cases hlast : j = k
    · subst hlast
      simp [List.getElem_set]
    · have hne : start + k ≠ start + j := by omega
      simp [List.getElem_set, hne]
      exact ih j (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hj) hlast) (Nat.le_of_succ_le hk)

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

theorem paintRed_get_hi (xs : List Nat) (start k j : Nat)
    (hk : start + k ≤ j) (hj : j < xs.length) :
    (paintRed xs start k)[j]'(by rw [paintRed_length]; exact hj) = xs[j] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hne : start + k ≠ j := by omega
    simp [paintRed, List.getElem_set, hne, ih (by omega)]

theorem paintRed_get_lo (xs : List Nat) (start k j : Nat)
    (hj : j < k) (hk : start + k ≤ xs.length) :
    (paintRed xs start k)[start + j]'(by
      rw [paintRed_length]
      exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj start) hk) = 2 := by
  induction k generalizing j with
  | zero => omega
  | succ k ih =>
    simp only [paintRed]
    by_cases hlast : j = k
    · subst hlast
      simp [List.getElem_set]
    · have hne : start + k ≠ start + j := by omega
      simp [List.getElem_set, hne]
      exact ih j (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hj) hlast) (Nat.le_of_succ_le hk)

/-- Control counter added by one emitted rung. A later rung unparks first (`+2`)
    and then parks (`+2`); the first rung only parks. The cube loop adds one per
    tally peg. A non-final rung doubles the tally (`+2 · tally`). A non-final red
    rung also lays one more peg (`+1`). -/
def rungCtrl (ctrl tally colour : Nat) (last parked : Bool) : Nat :=
  let base := ctrl + (if parked then 4 else 2) + tally
  let doubled := if last then base else base + 2 * tally
  if !last && colour = 2 then doubled + 1 else doubled

/-- One rung of `rungCtrl` adds at most `3 · tally + 5`: the park write (at most 4),
    the `tally` red pegs, the doubled white segment, and one extra peg. -/
theorem rungCtrl_inc (ctrl tally colour : Nat) (last parked : Bool) :
    rungCtrl ctrl tally colour last parked ≤ ctrl + 3 * tally + 5 := by
  unfold rungCtrl
  by_cases hL : last <;> by_cases hP : parked <;> by_cases hR : colour = 2 <;>
    simp [hL, hP, hR] <;> omega

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

theorem afterPark_length (row : List Nat) (fromHole : Int) (park hole colour : Nat) :
    (afterPark row fromHole park hole colour).length = row.length := by
  unfold afterPark
  by_cases hF : fromHole < 0
  · simp [hF, List.length_set]
  · simp [hF, List.length_set]

theorem afterTally_length (row : List Nat) (t0 tally colour : Nat) (last : Bool) :
    (afterTally row t0 tally colour last).length = row.length := by
  unfold afterTally
  by_cases hL : last
  · simp [hL, paintRed_length]
  · simp only [hL, Bool.false_eq_true, if_false]
    by_cases hR : colour = 2
    · simp [hR, List.length_set, paintOnes_length, paintRed_length]
    · simp [hR, paintOnes_length, paintRed_length]

theorem rungRow_length (row : List Nat) (fromHole : Int) (park hole t0 tally colour : Nat)
    (last : Bool) :
    (rungRow row fromHole park hole t0 tally colour last).length = row.length := by
  unfold rungRow
  rw [afterTally_length, afterPark_length]

/-- Writes of `afterPark` sit strictly before the tally origin, so the tally
    segment and everything past it are unchanged. -/
theorem afterPark_get (row : List Nat) (fromHole : Int) (park hole colour j : Nat)
    (hp : park < j) (hh : hole < j)
    (hfrom : fromHole < 0 ∨ fromHole.toNat < j)
    (hj : j < row.length) :
    (afterPark row fromHole park hole colour)[j]'(by
      rw [afterPark_length]; exact hj) = row[j] := by
  unfold afterPark
  by_cases hF : fromHole < 0
  · have hneP : park ≠ j := by omega
    have hneH : hole ≠ j := by omega
    simp [hF, List.getElem_set, hneP, hneH]
  · have hneS : fromHole.toNat ≠ j := by
      cases hfrom with
      | inl h => exact absurd h hF
      | inr h => omega
    have hneP : park ≠ j := by omega
    have hneH : hole ≠ j := by omega
    simp [hF, List.getElem_set, hneS, hneP, hneH]

/-- While rungs remain, the tally segment is white and every later hole is empty.
    After the final rung the segment is red. "Beyond the current length" is the
    empty tail. -/
structure RowSeg (row : List Nat) (t0 tally : Nat) (finished : Bool) : Prop where
  room : t0 + tally ≤ row.length
  colour : ∀ j (hj : j < tally),
    row[t0 + j]'(Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj t0) room) =
      if finished then 2 else 1
  beyond : finished = false → ∀ j, tally ≤ j → ∀ (h : t0 + j < row.length),
    row[t0 + j]'h = 0

theorem paintRed_seg (row : List Nat) (t0 tally : Nat)
    (hroom : t0 + tally ≤ row.length)
    (hwhite : ∀ j (hj : j < tally),
      row[t0 + j]'(Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj t0) hroom) = 1)
    (htail : ∀ j, tally ≤ j → ∀ (h : t0 + j < row.length), row[t0 + j]'h = 0) :
    RowSeg (paintRed row t0 tally) t0 tally true := by
  refine ⟨by rw [paintRed_length]; exact hroom, ?_, ?_⟩
  · intro j hj
    have hget := paintRed_get_lo row t0 tally j hj hroom
    simpa using hget
  · intro hfin
    cases hfin

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

/-- The same cube-peg loop, started from a board whose first cube equals the
    bench-off first peg. A later rung starts with the bench aimed at the gap.
    `cube_settle_other` makes that first cube the bench-off cube of the slid
    board, so the loop is `pegBoard` of a `PegCtx` whose `b0` is that slide
    and whose `hoff` holds. -/
theorem cube_peg_loop_from (c : PegCtx) (b : Ecbs.Board)
    (hbody0 : cubePegBody c.src b ((0 : Nat) : Int) = .ok (offPeg c)) :
    SudoRt.runLoopOn (Int.ofNat 0, b)
        (fuelRange (Int.ofNat 0) (Int.ofNat (c.m - 1)))
        (cubePegStep c.src (Int.ofNat (c.m - 1)))
        (fun σ => .ok σ)
        (fun r => .ok ((0 : Int), r)) =
      .ok (Int.ofNat (c.m - 1), pegBoard c c.m) := by
  refine asc_goal (fromN := 0) (toN := c.m - 1)
      (fun i s => if i = 0 then s = b else s = pegBoard c i)
      (Nat.zero_le _) (by simp) ?_ ?_
  · intro i s _ hi hI
    have hle1 : i + 1 ≤ c.m := by
      have h := Nat.add_le_add_right hi 1
      rwa [Nat.sub_add_cancel (Nat.succ_le_of_lt c.hm)] at h
    have hfit : FitsLen (i + 1) := FitsLen.of_le c.hfitM hle1
    have hng : ¬ Int.ofNat i > Int.ofNat (c.m - 1) := not_gt_cast hi
    cases i with
    | zero =>
      have hs : s = b := by simpa using hI
      rw [hs]
      have hstep := peg_tail c.src (c.m - 1) 0 b (offPeg c) hfit hng hbody0
      rw [hstep]
      refine ⟨offPeg c, ?_, rfl⟩
      show (if (1 : Nat) = 0 then offPeg c = b else offPeg c = pegBoard c 1)
      rw [if_neg (by decide : (1 : Nat) ≠ 0)]
      exact (pegBoard_one c).symm
    | succ k =>
      have hlt : k + 1 < c.m :=
        Nat.lt_of_le_of_lt hi (Nat.sub_lt c.hm (by decide))
      have hle : k + 1 ≤ c.m := Nat.le_of_lt hlt
      let d := pegPack c (k + 1) (Nat.succ_pos k) hle
      have hI' : s = pegBoard c (k + 1) := by
        have hne : k + 1 ≠ 0 := by omega
        simpa [hne] using hI
      have hsB : s = d.b := by
        rw [hI']
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
      have hne : k + 2 ≠ 0 := by omega
      change (if k + 2 = 0 then livePegBoard c d hlt = b
        else livePegBoard c d hlt = pegBoard c (k + 2))
      rw [if_neg hne]
      exact (pegBoard_succ c k hle1).symm
  · intro s hI
    have hm1 : c.m - 1 + 1 = c.m := Nat.sub_add_cancel (Nat.succ_le_of_lt c.hm)
    have hne : c.m - 1 + 1 ≠ 0 := by
      rw [hm1]
      omega
    change (if c.m - 1 + 1 = 0 then s = b else s = pegBoard c (c.m - 1 + 1)) at hI
    rw [if_neg hne] at hI
    rw [hI, hm1]

theorem cubePegBody_cube (src : Nat) (b b' : Ecbs.Board) (j : Int)
    (h : Ecbs.cube b (src : Int) (src : Int) = Ecbs.cube b' (src : Int) (src : Int)) :
    cubePegBody src b j = cubePegBody src b' j := by
  unfold cubePegBody
  rw [h]

/-- A later rung's cube-peg loop. The bench is on and aimed at `home` (the gap),
    not at `src` (the spare). `c.b0` is that bench slid into `home`, so `c.hoff`
    holds, and the emitted loop is `pegBoard c`. -/
theorem cube_peg_loop_settled (c : PegCtx) (b : Ecbs.Board) (home : Nat) (xs : List Nat)
    (n moves slides peak : Nat)
    (hmk : b.sudo_5Board_9marker_on = false)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (home : Int))
    (hH : home < b.sudo_5Board_4home.size)
    (hD : home < b.sudo_5Board_4held.size)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hempty : b.sudo_5Board_4held[home] = false)
    (hbench : b.sudo_5Board_5bench = embed xs)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
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
    (hop1 : b.sudo_5Board_4cost.sudo_5Costs_3ops[1]'(hops) = (c.cOps0 : Int))
    (hfops : FitsLen (c.cOps0 + 1))
    (hS : c.b0 = settleBoard b home hH hD xs n moves slides peak) :
    SudoRt.runLoopOn (Int.ofNat 0, b)
        (fuelRange (Int.ofNat 0) (Int.ofNat (c.m - 1)))
        (cubePegStep c.src (Int.ofNat (c.m - 1)))
        (fun σ => .ok σ)
        (fun r => .ok ((0 : Int), r)) =
      .ok (Int.ofNat (c.m - 1), pegBoard c c.m) := by
  have hcube := cube_settle_other b c.src c.src home xs n moves slides peak c.cOps0
    hmk hon hto hH hD h7 hempty hbench hn hpos hnle hzero hf hfitL
    hmoves hslides hpeak hpeg hfitM hfitS hops hop1 hfops
  rw [← hS] at hcube
  have hbody := cubePegBody_cube c.src b c.b0 ((0 : Nat) : Int) hcube
  exact cube_peg_loop_from c b (hbody.trans (off_body c))

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

/-- `place` writes the home, the held flag, the move counter, and sometimes the
    peak. The marker, the bench flag, the ops array, the slide counter, the tier,
    the strict peak, and the recorded bench hole stay as they were. -/
private theorem place_idle (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat) :
    (placeBoard b home hH hD xs moves peak).sudo_5Board_9marker_on =
      b.sudo_5Board_9marker_on ∧
    (placeBoard b home hH hD xs moves peak).sudo_5Board_8bench_on =
      b.sudo_5Board_8bench_on ∧
    (placeBoard b home hH hD xs moves peak).sudo_5Board_4cost.sudo_5Costs_3ops =
      b.sudo_5Board_4cost.sudo_5Costs_3ops ∧
    (placeBoard b home hH hD xs moves peak).sudo_5Board_4cost.sudo_5Costs_6slides =
      b.sudo_5Board_4cost.sudo_5Costs_6slides ∧
    (placeBoard b home hH hD xs moves peak).sudo_5Board_1t = b.sudo_5Board_1t ∧
    (placeBoard b home hH hD xs moves peak).sudo_5Board_4cost.sudo_5Costs_11peak_strict =
      b.sudo_5Board_4cost.sudo_5Costs_11peak_strict ∧
    (placeBoard b home hH hD xs moves peak).sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole := by
  unfold placeBoard
  dsimp only
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem place_moves (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat) :
    (placeBoard b home hH hD xs moves peak).sudo_5Board_4cost.sudo_5Costs_5moves =
      Int.ofNat (moves + pegCount xs) := by
  unfold placeBoard
  dsimp only
  split <;> rfl

private theorem place_peak (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int)) :
    (placeBoard b home hH hD xs moves peak).sudo_5Board_4cost.sudo_5Costs_4peak =
      Int.ofNat (if peak < countHeld (b.sudo_5Board_4held.set ⟨home, hD⟩ true) 7
        then countHeld (b.sudo_5Board_4held.set ⟨home, hD⟩ true) 7
        else peak) := by
  unfold placeBoard
  dsimp only
  split
  · next hlt => simp [hlt, ofNat_eq_natCast]
  · next hnk =>
      simp [hnk]
      rw [hpeak]

private theorem place_held_here (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat)
    (hF : home < (placeBoard b home hH hD xs moves peak).sudo_5Board_4held.size) :
    (placeBoard b home hH hD xs moves peak).sudo_5Board_4held[home] = true := by
  have hEq : (placeBoard b home hH hD xs moves peak).sudo_5Board_4held =
      b.sudo_5Board_4held.set ⟨home, hD⟩ true := by
    unfold placeBoard
    dsimp only
    split <;> rfl
  simpa [Array.getElem_set] using idx_get hEq home hF

private theorem place_home_here (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat)
    (hF : home < (placeBoard b home hH hD xs moves peak).sudo_5Board_4home.size) :
    (placeBoard b home hH hD xs moves peak).sudo_5Board_4home[home] = embed xs := by
  have hEq : (placeBoard b home hH hD xs moves peak).sudo_5Board_4home =
      b.sudo_5Board_4home.set ⟨home, hH⟩ (embed xs) := by
    unfold placeBoard
    dsimp only
    split <;> rfl
  simpa [Array.getElem_set] using idx_get hEq home hF

private theorem place_held_other (b : Ecbs.Board) (home other : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat)
    (hne : home ≠ other)
    (hO : other < b.sudo_5Board_4held.size)
    (hF : other < (placeBoard b home hH hD xs moves peak).sudo_5Board_4held.size) :
    (placeBoard b home hH hD xs moves peak).sudo_5Board_4held[other] =
      b.sudo_5Board_4held[other] := by
  have hEq : (placeBoard b home hH hD xs moves peak).sudo_5Board_4held =
      b.sudo_5Board_4held.set ⟨home, hD⟩ true := by
    unfold placeBoard
    dsimp only
    split <;> rfl
  rw [show (placeBoard b home hH hD xs moves peak).sudo_5Board_4held[other] =
      (b.sudo_5Board_4held.set ⟨home, hD⟩ true)[other]'(hEq ▸ hF) from idx_get hEq other hF]
  rw [Array.getElem_set, if_neg hne]

private theorem place_home_other (b : Ecbs.Board) (home other : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat)
    (hne : home ≠ other)
    (hO : other < b.sudo_5Board_4home.size)
    (hF : other < (placeBoard b home hH hD xs moves peak).sudo_5Board_4home.size) :
    (placeBoard b home hH hD xs moves peak).sudo_5Board_4home[other] =
      b.sudo_5Board_4home[other] := by
  have hEq : (placeBoard b home hH hD xs moves peak).sudo_5Board_4home =
      b.sudo_5Board_4home.set ⟨home, hH⟩ (embed xs) := by
    unfold placeBoard
    dsimp only
    split <;> rfl
  rw [show (placeBoard b home hH hD xs moves peak).sudo_5Board_4home[other] =
      (b.sudo_5Board_4home.set ⟨home, hH⟩ (embed xs))[other]'(hEq ▸ hF) from
    idx_get hEq other hF]
  rw [Array.getElem_set, if_neg hne]

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

/-- The board `unpark` leaves when a colour is parked: that colour goes back to
    `src`, the parking hole is cleared, and the counter grows by two. -/
def unparkedBoard (b : Ecbs.Board) (src park prev ctrl : Nat)
    (hRowS : src < b.sudo_5Board_3row.size)
    (hRowP : park < b.sudo_5Board_3row.size) : Ecbs.Board :=
  { b with
    sudo_5Board_3row :=
      (b.sudo_5Board_3row.set ⟨src, hRowS⟩ (prev : Int)).set
        ⟨park, by rw [Array.size_set]; exact hRowP⟩ (0 : Int)
    sudo_5Board_11parked_from := -1
    sudo_5Board_4cost := { b.sudo_5Board_4cost with
      sudo_5Costs_4ctrl := Int.ofNat (ctrl + 2) } }

/-- `park` when a colour is already parked. Unpark restores it, then the keep-park
    lifts `rung` from `hole`. The counter grows by four. `hole` is neither the
    restored hole nor the parking hole, so its colour survives the restore. -/
theorem park_resume (b : Ecbs.Board) (src hole park prev rung high control ctrl : Nat)
    (hFrom : b.sudo_5Board_11parked_from = (src : Int))
    (hParkF : b.sudo_5Board_9park_hole = (park : Int))
    (hRowS : src < b.sudo_5Board_3row.size)
    (hRowH : hole < b.sudo_5Board_3row.size)
    (hRowP : park < b.sudo_5Board_3row.size)
    (hPrev : b.sudo_5Board_3row[park] = (prev : Int))
    (hColour : b.sudo_5Board_3row[hole] = (rung : Int))
    (hRung : rung ≠ 0)
    (hCtrlN : b.sudo_5Board_1t.sudo_4Tier_7control = (control : Int))
    (hSrcC : src < control) (hParkC : park < control)
    (hHigh : b.sudo_5Board_4cost.sudo_5Costs_15control_highest = (high : Int))
    (hLeS : src ≤ high) (hLeP : park ≤ high)
    (hCtrl : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = (ctrl : Int))
    (hFitU : FitsLen (ctrl + 2)) (hFit : FitsLen ((ctrl + 2) + 2))
    (hneP : hole ≠ park) (hneS : hole ≠ src) :
    Ecbs.park b (hole : Int) =
      .ok ((rung : Int),
        { unparkedBoard b src park prev ctrl hRowS hRowP with
          sudo_5Board_3row :=
            ((unparkedBoard b src park prev ctrl hRowS hRowP).sudo_5Board_3row.set
              ⟨park, by
                simp [unparkedBoard, Array.size_set]; exact hRowP⟩ (rung : Int)).set
              ⟨hole, by
                simp [unparkedBoard, Array.size_set]; exact hRowH⟩ (0 : Int)
          sudo_5Board_4cost :=
            { (unparkedBoard b src park prev ctrl hRowS hRowP).sudo_5Board_4cost with
              sudo_5Costs_4ctrl := Int.ofNat ((ctrl + 2) + 2) }
          sudo_5Board_11parked_from := (hole : Int) }) := by
  let bU := unparkedBoard b src park prev ctrl hRowS hRowP
  have hRowHU : hole < bU.sudo_5Board_3row.size := by
    simp [bU, unparkedBoard, Array.size_set]; exact hRowH
  have hRowPU : park < bU.sudo_5Board_3row.size := by
    simp [bU, unparkedBoard, Array.size_set]; exact hRowP
  have hpN : park ≠ hole := fun h => hneP h.symm
  have hsN : src ≠ hole := fun h => hneS h.symm
  have hColourU : bU.sudo_5Board_3row[hole] = (rung : Int) := by
    simp [bU, unparkedBoard, Array.getElem_set, hpN, hsN, hColour]
  have hZeroU : bU.sudo_5Board_3row[park] = 0 := by
    simp [bU, unparkedBoard, Array.getElem_set]
  have hCtrlU : bU.sudo_5Board_4cost.sudo_5Costs_4ctrl = ((ctrl + 2 : Nat) : Int) := by
    simp [bU, unparkedBoard, ofNat_eq_natCast]
  have hIdle : bU.sudo_5Board_11parked_from = -1 := by simp [bU, unparkedBoard]
  have hParkU : bU.sudo_5Board_9park_hole = (park : Int) := by simp [bU, unparkedBoard, hParkF]
  have hHighU : bU.sudo_5Board_4cost.sudo_5Costs_15control_highest = (high : Int) := by
    simp [bU, unparkedBoard, hHigh]
  have hCtrlNU : bU.sudo_5Board_1t.sudo_4Tier_7control = (control : Int) := by
    simp [bU, unparkedBoard, hCtrlN]
  unfold Ecbs.park
  rw [unpark_back b src park prev high control ctrl hFrom hParkF hRowS hRowP hPrev
      hCtrlN hSrcC hHigh hLeS hCtrl hFitU, ok_bind]
  exact park_keep bU hole park rung high control (ctrl + 2)
      hIdle hParkU hRowHU hRowPU hColourU hZeroU hRung hCtrlNU hParkC hHighU hLeP
      hCtrlU hFit hneP

/-- `park_rung` when a colour is already parked: unpark, then the keep-park, then
    the rung index steps. -/
theorem park_rung_resume (b : Ecbs.Board) (holes : List Nat)
    (i src hole park prev rung high control ctrl : Nat)
    (hClimb : Ecbs.climb_holes b = .ok (embed holes))
    (hIdx : b.sudo_5Board_8rung_idx = (i : Int))
    (hAt : i < holes.length) (hHole : holes[i] = hole)
    (hFrom : b.sudo_5Board_11parked_from = (src : Int))
    (hParkF : b.sudo_5Board_9park_hole = (park : Int))
    (hRowS : src < b.sudo_5Board_3row.size)
    (hRowH : hole < b.sudo_5Board_3row.size)
    (hRowP : park < b.sudo_5Board_3row.size)
    (hPrev : b.sudo_5Board_3row[park] = (prev : Int))
    (hColour : b.sudo_5Board_3row[hole] = (rung : Int))
    (hRung : rung ≠ 0)
    (hCtrlN : b.sudo_5Board_1t.sudo_4Tier_7control = (control : Int))
    (hSrcC : src < control) (hParkC : park < control)
    (hHigh : b.sudo_5Board_4cost.sudo_5Costs_15control_highest = (high : Int))
    (hLeS : src ≤ high) (hLeP : park ≤ high)
    (hCtrl : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = (ctrl : Int))
    (hFitU : FitsLen (ctrl + 2)) (hFit : FitsLen ((ctrl + 2) + 2))
    (hneP : hole ≠ park) (hneS : hole ≠ src)
    (hFitI : FitsLen (i + 1)) :
    Ecbs.park_rung b (rung : Int) =
      .ok { unparkedBoard b src park prev ctrl hRowS hRowP with
        sudo_5Board_3row :=
          ((unparkedBoard b src park prev ctrl hRowS hRowP).sudo_5Board_3row.set
            ⟨park, by simp [unparkedBoard, Array.size_set]; exact hRowP⟩ (rung : Int)).set
            ⟨hole, by simp [unparkedBoard, Array.size_set]; exact hRowH⟩ (0 : Int)
        sudo_5Board_4cost :=
          { (unparkedBoard b src park prev ctrl hRowS hRowP).sudo_5Board_4cost with
            sudo_5Costs_4ctrl := Int.ofNat ((ctrl + 2) + 2) }
        sudo_5Board_11parked_from := (hole : Int)
        sudo_5Board_8rung_idx := Int.ofNat (i + 1) } := by
  unfold Ecbs.park_rung
  rw [hClimb, ok_bind]
  conv => zeta
  rw [hIdx, ← ofNat_eq_natCast i, atL_embed holes i hAt, hHole, ok_bind]
  rw [ofNat_eq_natCast hole]
  rw [park_resume b src hole park prev rung high control ctrl
      hFrom hParkF hRowS hRowH hRowP hPrev hColour hRung hCtrlN hSrcC hParkC
      hHigh hLeS hLeP hCtrl hFitU hFit hneP hneS, ok_bind]
  dsimp only
  rw [sudoAssertEq_int rfl 305, ok_bind]
  have hIdxU : (unparkedBoard b src park prev ctrl hRowS hRowP).sudo_5Board_8rung_idx =
      b.sudo_5Board_8rung_idx := by simp [unparkedBoard]
  rw [hIdxU, hIdx, ← ofNat_eq_natCast i, show (1 : Int) = Int.ofNat 1 from rfl,
    addI_ofNat i 1 hFitI, ok_bind, pure_eq_ok]

/-- Moves one live nocopy mul can add: the settle into the spare, the schoolbook,
    and the lane fold. -/
def mulCharge (n bench : Nat) : Nat :=
  2 * n + n * (n + 1) + 3 * (bench - n)

/-- Moves of the heaviest rung: a non-final red rung that unparks first.
    Unpark and park add none. The copy and the clear add at most `n` each.
    The `m` cube-pegs add at most `pegCharge` each, which also covers a settle
    into a different home before the first cube. One live mul adds at most
    `mulCharge`. The red cube and the red mul add one more of each. Doubling
    and the extra white peg add no moves. -/
def rungCharge (n bench m : Nat) : Nat :=
  2 * n + (m + 1) * pegCharge n bench + 2 * mulCharge n bench

/-- Slides of that rung: `2 · n` for each of the `m` pegs, the gap mul, the red
    cube, and the red mul. -/
def rungSlideCharge (n m : Nat) : Nat :=
  (m + 3) * (2 * n)

/-- Ops of that rung. The cube slot grows by `m + 1` and the mul slot by `2`,
    so every slot grows by at most `m + 3`. -/
def rungOpCharge (m : Nat) : Nat :=
  m + 3

theorem mulCharge_ge (n bench : Nat) (moves : Nat) (xs ys : List Nat) (k : Nat)
    (hn : n ≤ bench) (hp : pegCount (ys.take n) ≤ n) :
    moves + 2 * pegCount (ys.take n) + n * (n + 1) + 3 * (bench - n) ≤
      moves + mulCharge n bench := by
  unfold mulCharge
  omega

theorem charge_final_white (n bench m : Nat) :
    n + m * pegCharge n bench + mulCharge n bench + n ≤ rungCharge n bench m := by
  unfold rungCharge
  have hp : m * pegCharge n bench ≤ (m + 1) * pegCharge n bench :=
    Nat.mul_le_mul_right _ (Nat.le_succ m)
  have hc : mulCharge n bench ≤ mulCharge n bench + mulCharge n bench :=
    Nat.le_add_right _ _
  have h2 : mulCharge n bench + mulCharge n bench = 2 * mulCharge n bench := by
    rw [Nat.two_mul]
  have hsum : n + n = 2 * n := by rw [Nat.two_mul]
  omega

theorem charge_open_white (n bench m : Nat) :
    n + m * pegCharge n bench + mulCharge n bench + n ≤ rungCharge n bench m :=
  charge_final_white n bench m

theorem charge_final_red (n bench m : Nat) :
    n + m * pegCharge n bench + mulCharge n bench + n + pegCharge n bench +
        mulCharge n bench ≤
      rungCharge n bench m := by
  unfold rungCharge
  have hsum : n + n = 2 * n := by rw [Nat.two_mul]
  have hpeg : m * pegCharge n bench + pegCharge n bench = (m + 1) * pegCharge n bench := by
    rw [Nat.succ_mul]
  have hmul : mulCharge n bench + mulCharge n bench = 2 * mulCharge n bench := by
    rw [Nat.two_mul]
  omega

theorem charge_open_red (n bench m : Nat) :
    n + m * pegCharge n bench + mulCharge n bench + n + pegCharge n bench +
        mulCharge n bench ≤
      rungCharge n bench m :=
  charge_final_red n bench m

theorem slide_open_red (n m : Nat) :
    m * (2 * n) + 2 * n + 2 * n + 2 * n ≤ rungSlideCharge n m := by
  unfold rungSlideCharge
  have h : (m + 3) * (2 * n) = m * (2 * n) + 3 * (2 * n) := by rw [Nat.add_mul]
  have h3 : 3 * (2 * n) = 2 * n + 2 * n + 2 * n := by omega
  omega

theorem op_open_red (m : Nat) : m + 1 + 2 ≤ rungOpCharge m := by
  unfold rungOpCharge
  omega

/-- With `n > 0`, one `rungCharge` dominates one `rungCtrl` step. -/
theorem rungCharge_ge_ctrl (n bench m : Nat) (hn : 0 < n) :
    3 * m + 5 ≤ rungCharge n bench m := by
  have h4n : 4 ≤ 4 * n := by
    have : 1 ≤ n := hn
    omega
  have hpeg : 4 ≤ 4 * n + 3 * (bench - n) := Nat.le_trans h4n (Nat.le_add_right _ _)
  have hmul : (m + 1) * 4 ≤ (m + 1) * (4 * n + 3 * (bench - n)) :=
    Nat.mul_le_mul_left _ hpeg
  have h2 : 2 ≤ 2 * n := by omega
  unfold rungCharge pegCharge
  have hlow : 2 * n + (m + 1) * 4 ≤
      2 * n + (m + 1) * (4 * n + 3 * (bench - n)) :=
    Nat.add_le_add_left hmul _
  have hrest : 2 * n + (m + 1) * (4 * n + 3 * (bench - n)) ≤
      2 * n + (m + 1) * (4 * n + 3 * (bench - n)) +
        2 * mulCharge n bench :=
    Nat.le_add_right _ _
  have hnum : 3 * m + 5 ≤ 2 + (m + 1) * 4 := by omega
  have h2n : 2 + (m + 1) * 4 ≤ 2 * n + (m + 1) * 4 := Nat.add_le_add_right h2 _
  exact Nat.le_trans hnum (Nat.le_trans h2n (Nat.le_trans hlow hrest))

/-- `2 · tally + 1` fits an i64 because it is at most one `rungCharge`, and the
    budget fits `R` of those. -/
theorem double_len_fit {moves0 R n bench m tally : Nat}
    (hn : 0 < n) (hR : 0 < R) (ht : tally ≤ m)
    (hf : FitsLen (moves0 + R * rungCharge n bench m)) :
    FitsLen (2 * tally + 1) := by
  have hstep := rungCharge_ge_ctrl n bench m hn
  have h1 : 2 * tally + 1 ≤ 3 * m + 5 := by omega
  have h2 : rungCharge n bench m ≤ R * rungCharge n bench m :=
    Nat.le_mul_of_pos_left (rungCharge n bench m) hR
  exact FitsLen.of_le hf (by omega)

/-- An index strictly below the control row fits an i64 when `control + 1` does.
    That is the tier's `fits_control`. -/
theorem double_index_fit {t0 m control : Nat}
    (h : t0 + 2 * m < control) (hc : FitsLen (control + 1)) :
    FitsLen (t0 + 2 * m) ∧ FitsLen (2 * m) ∧ FitsLen (2 * m + 1) := by
  refine ⟨FitsLen.of_le hc (by omega), FitsLen.of_le hc (by omega),
    FitsLen.of_le hc (by omega)⟩

/-- The running counter plus one extra peg fits when the budget's `fitCtrl` does. -/
theorem double_ctrl_fit {ctrl tally ctrl0 done R mMax : Nat}
    (hctrl : ctrl ≤ ctrl0 + done * (3 * mMax + 5))
    (ht : tally ≤ mMax) (hd : done ≤ R)
    (hf : FitsLen (ctrl0 + (R + 1) * (3 * mMax + 5))) :
    FitsLen (ctrl + 3 * tally) ∧
      FitsLen (ctrl + tally + 2 * tally + 1) := by
  have hS : 3 * tally + 1 ≤ 3 * mMax + 5 := by omega
  have hbody : ctrl + 3 * tally + 1 ≤
      ctrl0 + (done + 1) * (3 * mMax + 5) := by
    have hmul : (done + 1) * (3 * mMax + 5) =
        done * (3 * mMax + 5) + (3 * mMax + 5) := by
      rw [Nat.succ_mul]
    omega
  have hdone : ctrl0 + (done + 1) * (3 * mMax + 5) ≤
      ctrl0 + (R + 1) * (3 * mMax + 5) := by
    have hle : done + 1 ≤ R + 1 := by omega
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hle) _
  refine ⟨FitsLen.of_le hf (by omega), FitsLen.of_le hf (by omega)⟩

theorem rungCharge_mono (n bench m mMax : Nat) (h : m ≤ mMax) :
    rungCharge n bench m ≤ rungCharge n bench mMax := by
  unfold rungCharge
  have h1 : (m + 1) * pegCharge n bench ≤ (mMax + 1) * pegCharge n bench :=
    Nat.mul_le_mul_right _ (Nat.add_le_add_right h 1)
  omega

theorem rungSlideCharge_mono (n m mMax : Nat) (h : m ≤ mMax) :
    rungSlideCharge n m ≤ rungSlideCharge n mMax := by
  unfold rungSlideCharge
  exact Nat.mul_le_mul_right _ (Nat.add_le_add_right h 3)

theorem rungOpCharge_mono (m mMax : Nat) (h : m ≤ mMax) :
    rungOpCharge m ≤ rungOpCharge mMax := by
  unfold rungOpCharge
  omega

/-- After `k` rungs, `k ≤ R`, a counter that stayed under `k` charges still fits
    the `R`-charge budget. This is the moves, slides, and ops fit in the domain
    of `invert_number_refines`. -/
theorem rung_budget_fit (base k R charge value : Nat)
    (hk : k ≤ R) (hval : value ≤ base + k * charge)
    (hFit : FitsLen (base + R * charge)) : FitsLen value := by
  apply FitsLen.of_le hFit
  have hk' : k * charge ≤ R * charge := Nat.mul_le_mul_right _ hk
  omega

/-- Park, copy, the white scan, the cube-peg loop, the live nocopy mul, and
    clear. `hPark` is either the idle keep-park or the unpark-then-park. -/
theorem rung_prefix_refines (b bPark : Ecbs.Board) (rung : Nat)
    (hPark : Ecbs.park_rung b (rung : Int) = .ok bPark)
    (g : List Nat) (moves peak : Nat)
    (hHs : 6 < bPark.sudo_5Board_4home.size)
    (hDs : 6 < bPark.sudo_5Board_4held.size)
    (hH5s : 5 < bPark.sudo_5Board_4home.size)
    (hD5s : 5 < bPark.sudo_5Board_4held.size)
    (h7 : 7 ≤ bPark.sudo_5Board_4held.size)
    (hsrc : bPark.sudo_5Board_4held[5] = true)
    (harr : bPark.sudo_5Board_4home[5] = embed g)
    (hempty : bPark.sudo_5Board_4held[6] = false)
    (hn : bPark.sudo_5Board_1t.sudo_4Tier_1n = (g.length : Int))
    (hf : FitsLen g.length)
    (hmoves : bPark.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hpeak : bPark.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hfit : FitsLen (moves + pegCount g))
    (c : PegCtx)
    (hCopy : c.b0 = placeBoard bPark 6 hHs hDs g moves peak)
    (rowXs : List Nat)
    (hT0 : c.b0.sudo_5Board_6tally0 = (c.t0 : Int))
    (hRow : c.b0.sudo_5Board_3row = embed rowXs)
    (hRoom : c.t0 + c.m ≤ rowXs.length)
    (hWhite : ∀ j (hj : j < c.m), rowXs[c.t0 + j]'(by omega) = 1)
    (hfitW : FitsLen (c.t0 + c.m))
    (xs ys : List Nat)
    (n k mvs slides holeM bench pk pkS cOps : Nat)
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
      .ok (clearHeldBoard (mulNoLiveBoard (pegBoard c c.m) 5 6 xs ys n k mvs slides holeM bench
        pk pkS cOps hH6 hD6 hops0) 5 xs movesC hH5 hD5) := by
  rw [hPark, ok_bind]
  rw [copy_band_refines bPark 6 5 g moves peak hHs hDs hH5s hD5s h7 hsrc harr hempty
      hn hf hmoves hpeak hfit, ok_bind]
  rw [← hCopy]
  rw [white_scan_loop_refines c.b0 rowXs c.t0 c.m c.hm hT0 hRow hRoom hWhite hfitW c.hfitM,
    ok_bind]
  rw [cube_peg_loop_refines c, ok_bind]
  dsimp only
  rw [mulHyps, ok_bind, hClear]

/-- The board after the clear, once the final/non-final and white/red branches
    have run. `bD` is the doubled board, `bMulF` the final red product, `bAdd`
    the non-final red board after the extra white peg. -/
def rungStepBoard (bC bD bMulF bAdd : Ecbs.Board) (last : Bool) (rung : Nat) : Ecbs.Board :=
  if last then
    if rung = 2 then bMulF else bC
  else
    if rung = 2 then bAdd else bD

private theorem beq_rung_two (rung : Nat) (h : rung = 2) :
    SudoRt.SEq.beq (rung : Int) (2 : Int) = true := by
  rw [sEq_int, ← ofNat_eq_natCast rung, show (2 : Int) = Int.ofNat 2 from rfl, h]
  exact decide_eq_true rfl

private theorem beq_rung_not_two (rung : Nat) (h : rung ≠ 2) :
    SudoRt.SEq.beq (rung : Int) (2 : Int) = false := by
  rw [sEq_int, ← ofNat_eq_natCast rung, show (2 : Int) = Int.ofNat 2 from rfl]
  rw [decide_eq_false_iff_not]
  intro hEq
  exact h (Int.ofNat.inj hEq)

/-- One emitted rung after the park-through-clear prefix, for every
    final/non-final and white/red combination. `pre` is that prefix, so the
    park is the idle keep or the unpark-then-park, whichever proved `pre`.
    A non-final rung doubles. A red rung cubes the gap and multiplies by `x`.
    A non-final red rung then lays one white peg. -/
theorem rung_step_refines (pre : Except SudoRt.Trap Ecbs.Board) (bC bD bCubeF bMulF
    bCubeO bMulO bAdd : Ecbs.Board) (last : Bool) (rung : Nat) (x : Int)
    (hPre : pre = .ok bC)
    (hDouble : Ecbs.tally_double bC = .ok bD)
    (hCubeF : Ecbs.cube bC (6 : Int) (5 : Int) = .ok bCubeF)
    (hMulF : Ecbs.mul bCubeF (5 : Int) x (6 : Int) false false false = .ok bMulF)
    (hCubeO : Ecbs.cube bD (6 : Int) (5 : Int) = .ok bCubeO)
    (hMulO : Ecbs.mul bCubeO (5 : Int) x (6 : Int) false false false = .ok bMulO)
    (hAdd : Ecbs.tally_add_one bMulO = .ok bAdd) :
    (do
        let b ← pre
        if !last then
          do
            let b ← Ecbs.tally_double b
            if SudoRt.SEq.beq (rung : Int) (2 : Int) then
              do
                let b ← Ecbs.cube b (6 : Int) (5 : Int)
                let b ← Ecbs.mul b (5 : Int) x (6 : Int) false false false
                if !last then Ecbs.tally_add_one b else pure b
            else pure b
        else if SudoRt.SEq.beq (rung : Int) (2 : Int) then
          do
            let b ← Ecbs.cube b (6 : Int) (5 : Int)
            let b ← Ecbs.mul b (5 : Int) x (6 : Int) false false false
            if !last then Ecbs.tally_add_one b else pure b
        else pure b) =
      .ok (rungStepBoard bC bD bMulF bAdd last rung) := by
  rw [hPre, ok_bind]
  by_cases hL : last
  · rw [hL]
    simp only [Bool.not_true, if_false]
    by_cases hR : rung = 2
    · rw [beq_rung_two rung hR]
      simp only [if_true]
      rw [hCubeF, ok_bind, hMulF, ok_bind]
      simp only [Bool.not_true, if_false, pure_eq_ok]
      simp [rungStepBoard, hL, hR]
    · rw [beq_rung_not_two rung hR]
      simp only [Bool.false_eq_true, if_false, pure_eq_ok]
      simp [rungStepBoard, hL, hR]
  · have hLf : last = false := by simpa using hL
    rw [hLf]
    simp only [Bool.not_false, if_true]
    rw [hDouble, ok_bind]
    by_cases hR : rung = 2
    · rw [beq_rung_two rung hR]
      simp only [if_true]
      rw [hCubeO, ok_bind, hMulO, ok_bind, hAdd]
      simp [rungStepBoard, hLf, hR]
    · rw [beq_rung_not_two rung hR]
      simp only [Bool.false_eq_true, if_false, pure_eq_ok]
      simp [rungStepBoard, hLf, hR]

/-- Tally length `invRung` leaves. A final rung keeps it. A non-final rung doubles
    it, and a non-final red rung adds one. -/
def tallyAfter (tally rung : Nat) (last : Bool) : Nat :=
  let tally1 := if last then tally else 2 * tally
  if rung = 2 then (if last then tally1 else tally1 + 1) else tally1

theorem invRung_tally (n k bench : Nat) (x g : List Nat) (tally rung : Nat) (last : Bool) :
    (invRung n k bench x g tally rung last).2 = tallyAfter tally rung last := by
  unfold invRung tallyAfter
  by_cases hL : last <;> by_cases hR : rung = 2 <;> simp [hL, hR]

theorem modelRung_tally (s : ClimbModel) (x : List Nat) (rung hole : Nat) (last : Bool) :
    (modelRung s x rung hole last).tally = tallyAfter s.tally rung last := by
  simp [modelRung, invRung_tally]

theorem tallyAfter_le (tally rung : Nat) (last : Bool) :
    tallyAfter tally rung last ≤ 2 * tally + 1 := by
  unfold tallyAfter
  by_cases hL : last <;> by_cases hR : rung = 2 <;> simp [hL, hR] <;> omega

theorem paintOnes_get_before (xs : List Nat) (start k j : Nat)
    (hj : j < start) (hlen : j < xs.length) :
    (paintOnes xs start k)[j]'(by rw [paintOnes_length]; exact hlen) = xs[j] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hne : start + k ≠ j := Nat.ne_of_gt (Nat.lt_of_lt_of_le hj (Nat.le_add_right _ _))
    simp [paintOnes, List.getElem_set, hne, ih]

/-- A non-final white rung doubles the tally: both halves are white, and holes
    past `2 · tally` stay empty. -/
theorem openWhite_seg (row : List Nat) (t0 tally : Nat)
    (hroom : t0 + 2 * tally ≤ row.length)
    (htail : ∀ j, tally ≤ j → ∀ (h : t0 + j < row.length), row[t0 + j]'h = 0) :
    RowSeg (paintOnes (paintOnes (paintRed row t0 tally) t0 tally) (t0 + tally) tally)
      t0 (2 * tally) false := by
  let reds := paintRed row t0 tally
  let back := paintOnes reds t0 tally
  let wide := paintOnes back (t0 + tally) tally
  have htwo : 2 * tally = tally + tally := Nat.two_mul tally
  have hroom' : t0 + tally + tally ≤ row.length := by
    simpa [htwo, Nat.add_assoc] using hroom
  have hhalf : t0 + tally ≤ row.length := Nat.le_trans (Nat.le_add_right _ _) hroom'
  have hlenW : t0 + 2 * tally ≤ wide.length := by
    simpa [wide, back, reds, paintOnes_length, paintRed_length] using hroom
  refine ⟨hlenW, ?_, ?_⟩
  · intro j hj
    by_cases hfst : j < tally
    · have hback := paintOnes_get_lo reds t0 tally j hfst
        (by simpa [reds, paintRed_length] using hhalf)
      have hpre : t0 + j < t0 + tally := Nat.add_lt_add_left hfst t0
      have hlenB : t0 + j < back.length := by
        simpa [back, reds, paintOnes_length, paintRed_length] using
          (Nat.lt_of_lt_of_le hpre hhalf)
      have hbefore := paintOnes_get_before back (t0 + tally) tally (t0 + j) hpre hlenB
      have : wide[t0 + j]'(by
          simpa [wide, back, reds, paintOnes_length, paintRed_length] using
            (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj t0) hroom)) = 1 := by
        simpa [wide, hbefore] using hback
      simpa [wide] using this
    · have hsec : j - tally < tally := by omega
      have hidx : (t0 + tally) + (j - tally) = t0 + j := by omega
      have hlo := paintOnes_get_lo back (t0 + tally) tally (j - tally) hsec
        (by simpa [back, reds, paintOnes_length, paintRed_length] using hroom')
      have : wide[(t0 + tally) + (j - tally)] = 1 := hlo
      simpa [wide, hidx] using this
  · intro _ j hj h
    have hrow : t0 + j < row.length := by
      simpa [wide, back, reds, paintOnes_length, paintRed_length] using h
    have h0 := htail j (by omega) hrow
    have hr := paintRed_get_hi row t0 tally (t0 + j) (by omega) hrow
    have hb := paintOnes_get_hi reds t0 tally (t0 + j) (by omega)
      (by simpa [reds, paintRed_length] using hrow)
    have hw := paintOnes_get_hi back (t0 + tally) tally (t0 + j) (by omega)
      (by simpa [back, reds, paintOnes_length, paintRed_length] using hrow)
    simpa [wide, hw, hb, hr] using h0

theorem afterPark_seg (row : List Nat) (fromHole : Int) (park hole colour t0 tally : Nat)
    (hseg : RowSeg row t0 tally false) (hp : park < t0) (hh : hole < t0)
    (hfrom : fromHole < 0 ∨ fromHole.toNat < t0) :
    RowSeg (afterPark row fromHole park hole colour) t0 tally false := by
  have hlen : t0 + tally ≤ (afterPark row fromHole park hole colour).length := by
    rw [afterPark_length]; exact hseg.room
  refine ⟨hlen, ?_, ?_⟩
  · intro j hj
    have hget := afterPark_get row fromHole park hole colour (t0 + j)
      (Nat.lt_of_lt_of_le hp (Nat.le_add_right _ _))
      (Nat.lt_of_lt_of_le hh (Nat.le_add_right _ _))
      (by
        cases hfrom with
        | inl h => exact Or.inl h
        | inr h => exact Or.inr (Nat.lt_of_lt_of_le h (Nat.le_add_right _ _)))
      (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj t0) hseg.room)
    simpa [hget] using hseg.colour j hj
  · intro _ j hj h
    have hrow : t0 + j < row.length := by rw [afterPark_length] at h; exact h
    have hget := afterPark_get row fromHole park hole colour (t0 + j)
      (by omega) (by omega)
      (by
        cases hfrom with
        | inl hf => exact Or.inl hf
        | inr hf => exact Or.inr (by omega))
      hrow
    have hz := hseg.beyond rfl j hj hrow
    rw [hget, hz]

/-- One model rung, park writes before `t0`. A final rung turns the white segment
    red. A non-final white rung doubles it. The empty tail past the new length
    stays empty when the row has room for that write. -/
theorem rungRow_final_seg (row : List Nat) (fromHole : Int) (park hole t0 tally colour : Nat)
    (hseg : RowSeg row t0 tally false) (hp : park < t0) (hh : hole < t0)
    (hfrom : fromHole < 0 ∨ fromHole.toNat < t0) :
    RowSeg (rungRow row fromHole park hole t0 tally colour true) t0 tally true := by
  have hpark := afterPark_seg row fromHole park hole colour t0 tally hseg hp hh hfrom
  have hred := paintRed_seg (afterPark row fromHole park hole colour) t0 tally hpark.room
    (by
      intro j hj
      simpa using hpark.colour j hj)
    (by
      intro j hj h
      exact hpark.beyond rfl j hj h)
  simpa [rungRow, afterTally] using hred

theorem rungRow_open_white_seg (row : List Nat) (fromHole : Int)
    (park hole t0 tally colour : Nat) (hseg : RowSeg row t0 tally false)
    (hp : park < t0) (hh : hole < t0) (hfrom : fromHole < 0 ∨ fromHole.toNat < t0)
    (hroom : t0 + 2 * tally ≤ row.length) (hcolour : colour ≠ 2) :
    RowSeg (rungRow row fromHole park hole t0 tally colour false) t0 (2 * tally) false := by
  have hpark := afterPark_seg row fromHole park hole colour t0 tally hseg hp hh hfrom
  have htail : ∀ j, tally ≤ j → ∀ (h : t0 + j < (afterPark row fromHole park hole colour).length),
      (afterPark row fromHole park hole colour)[t0 + j]'h = 0 := by
    intro j hj h
    exact hpark.beyond rfl j hj h
  have hwhite := openWhite_seg (afterPark row fromHole park hole colour) t0 tally
    (by rw [afterPark_length]; exact hroom) htail
  have hne : (colour = 2) = False := by simpa using hcolour
  simpa [rungRow, afterTally, hne] using hwhite

/-- Tally length along a rung list. The head is the next rung; `last` is the
    empty tail, so the final element of the list is the final rung. -/
def climbTally (tally : Nat) : List Nat → Nat
  | [] => tally
  | r :: rs => climbTally (tallyAfter tally r rs.isEmpty) rs

/-- Tally length after the prefix `done`, with `rest` still to come, so a rung
    in `done` is final only when nothing remains after it in `done ++ rest`. -/
def climbTallyPrefix (tally : Nat) : List Nat → List Nat → Nat
  | [], _ => tally
  | r :: done, rest =>
    climbTallyPrefix (tallyAfter tally r ((done ++ rest).isEmpty)) done rest

theorem climbTallyPrefix_nil (tally : Nat) (rest : List Nat) :
    climbTallyPrefix tally [] rest = tally := rfl

theorem climbTallyPrefix_snoc (tally : Nat) (done rest : List Nat) (r : Nat) :
    climbTallyPrefix tally (done ++ [r]) rest =
      tallyAfter (climbTallyPrefix tally done (r :: rest)) r rest.isEmpty := by
  induction done generalizing tally with
  | nil =>
    simp [climbTallyPrefix]
  | cons h done ih =>
    simp [climbTallyPrefix, List.cons_append, ih]

theorem climbTallyPrefix_full (tally : Nat) (rs : List Nat) :
    climbTallyPrefix tally rs [] = climbTally tally rs := by
  induction rs generalizing tally with
  | nil => rfl
  | cons r rs ih =>
    simp [climbTally, climbTallyPrefix, ih]

theorem climbTallyPrefix_le (tally : Nat) (done rest : List Nat) :
    climbTallyPrefix tally done rest ≤ (tally + 1) * 2 ^ done.length := by
  induction done generalizing tally rest with
  | nil =>
    simp [climbTallyPrefix]
  | cons r done ih =>
    simp [climbTallyPrefix]
    have hAfter := tallyAfter_le tally r ((done ++ rest).isEmpty)
    have hih := ih (tallyAfter tally r ((done ++ rest).isEmpty)) rest
    have hstep : tallyAfter tally r ((done ++ rest).isEmpty) + 1 ≤ 2 * (tally + 1) := by
      omega
    calc
      climbTallyPrefix (tallyAfter tally r ((done ++ rest).isEmpty)) done rest
          ≤ (tallyAfter tally r ((done ++ rest).isEmpty) + 1) * 2 ^ done.length := hih
      _ ≤ (2 * (tally + 1)) * 2 ^ done.length :=
          Nat.mul_le_mul_right _ hstep
      _ = (tally + 1) * 2 ^ (done.length + 1) := by
          rw [Nat.mul_comm 2 (tally + 1), Nat.mul_assoc, Nat.pow_succ,
            Nat.mul_comm (2 ^ done.length) 2]

theorem invClimb_tally (n k bench : Nat) (x g : List Nat) (tally : Nat) (rs : List Nat) :
    (invClimb n k bench x (g, tally) rs).2 = climbTally tally rs := by
  induction rs generalizing g tally with
  | nil => simp [invClimb, climbTally]
  | cons r rs ih =>
    have h2 := invRung_tally n k bench x g tally r rs.isEmpty
    simp [invClimb, climbTally, h2, ih]

/-- Fold `modelRung`. The hole does not affect the gap or the tally. -/
def modelClimb (s : ClimbModel) (x : List Nat)
    (hole : ClimbModel → Nat → Bool → Nat) : List Nat → ClimbModel
  | [] => s
  | r :: rs =>
    modelClimb (modelRung s x r (hole s r rs.isEmpty) rs.isEmpty) x hole rs

theorem modelClimb_spec (s : ClimbModel) (x : List Nat)
    (hole : ClimbModel → Nat → Bool → Nat) (rs : List Nat) :
    ((modelClimb s x hole rs).gap, (modelClimb s x hole rs).tally) =
      invClimb s.n s.k s.benchlen x (s.gap, s.tally) rs := by
  induction rs generalizing s with
  | nil => simp [modelClimb, invClimb]
  | cons r rs ih =>
    rw [modelClimb]
    have ih' := ih (modelRung s x r (hole s r rs.isEmpty) rs.isEmpty)
    rw [ih']
    simp [modelRung, invClimb, modelRung_value]

theorem modelClimb_tally (s : ClimbModel) (x : List Nat)
    (hole : ClimbModel → Nat → Bool → Nat) (rs : List Nat) :
    (modelClimb s x hole rs).tally = climbTally s.tally rs := by
  rw [← invClimb_tally, ← modelClimb_spec]

/-- `raisedPeak` against a count of at most seven homes stays at most `max(peak, 7)`. -/
theorem raisedPeak_carry (peak occ : Nat) (ho : occ ≤ 7) :
    raisedPeak peak occ ≤ max peak 7 := by
  unfold raisedPeak
  by_cases h : peak < occ
  · simp [h]
    exact Nat.le_trans ho (Nat.le_max_right peak 7)
  · simp [h]
    exact Nat.le_max_left _ _

theorem countHeld_seven (held : Array Bool) : countHeld held 7 ≤ 7 := by
  have : ∀ i, countHeld held i ≤ i := by
    intro i
    induction i with
    | zero => simp [countHeld]
    | succ i ih =>
      unfold countHeld
      have : (if held.getD i false then 1 else 0) ≤ 1 := by split <;> decide
      omega
  exact this 7

theorem peak_carry (peak0 pk pk' : Nat) (h : pk ≤ max peak0 7) (h' : pk' ≤ max pk 7) :
    pk' ≤ max peak0 7 := by
  have hmax : max pk 7 ≤ max peak0 7 := by
    apply Nat.max_le.mpr
    exact ⟨h, Nat.le_max_right _ _⟩
  exact Nat.le_trans h' hmax

/-- Budgets for one climb. `mMax` bounds the tally. It is at most the geometric
    envelope `(tally0 + 1) · 2 ^ R`, which `climbTallyPrefix_le` always gives.
    A shipped tier uses a smaller cap, the holes left in the control row after
    the tally origin: that envelope does not fit the control row of Demo, Toy,
    Hobby, or Serious. The three `FitsLen` facts are the moves, slides, and ops
    fit in the domain of `invert_number_refines`, taken at this cap. -/
structure ClimbBudget where
  n : Nat
  bench : Nat
  moves0 : Nat
  slides0 : Nat
  ops0 : Nat
  peak0 : Nat
  tally0 : Nat
  R : Nat
  mMax : Nat
  mMax_le : mMax ≤ (tally0 + 1) * 2 ^ R
  fitM : FitsLen (moves0 + R * rungCharge n bench mMax)
  fitS : FitsLen (slides0 + R * rungSlideCharge n mMax)
  fitO : FitsLen (ops0 + R * (mMax + 3))
  /-- Counter at the start of the climb. One `rungCtrl` step is at most
      `3 · mMax + 5`, so the counter after every rung still fits an i64. -/
  ctrl0 : Nat
  fitCtrl : FitsLen (ctrl0 + (R + 1) * (3 * mMax + 5))
  x : List Nat
  xHome : Nat
  w : Nat
  h : Nat
  r : Nat
  cg : Nat
  control : Nat
  /-- Control-row length plus one fits an i64. This is `BoardOk.fits_control`
      for each shipped tier. -/
  fitControl : FitsLen (control + 1)
  ladder0 : Nat

/-- One rung's counter growth: at most one `rungCharge` of the current tally,
    one slide charge, `mMax + 3` on every ops slot, and a peak that is
    `raisedPeak` against at most seven homes. -/
structure RungDelta (b b' : Ecbs.Board) (base : ClimbBudget) (m : Nat) : Prop where
  moves : ∃ (mv mv' : Nat),
    b.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int) ∧
    b'.sudo_5Board_4cost.sudo_5Costs_5moves = (mv' : Int) ∧
    mv' ≤ mv + rungCharge base.n base.bench m
  slides : ∃ (sl sl' : Nat),
    b.sudo_5Board_4cost.sudo_5Costs_6slides = (sl : Int) ∧
    b'.sudo_5Board_4cost.sudo_5Costs_6slides = (sl' : Int) ∧
    sl' ≤ sl + rungSlideCharge base.n m
  opsSize : b'.sudo_5Board_4cost.sudo_5Costs_3ops.size =
    b.sudo_5Board_4cost.sudo_5Costs_3ops.size
  ops : ∀ i (hi : i < b.sudo_5Board_4cost.sudo_5Costs_3ops.size),
    ∃ (c c' : Nat),
      b.sudo_5Board_4cost.sudo_5Costs_3ops[i] = (c : Int) ∧
      b'.sudo_5Board_4cost.sudo_5Costs_3ops[i]'(opsSize ▸ hi) = (c' : Int) ∧
      c' ≤ c + (base.mMax + 3)
  peak : ∃ (pk pk' : Nat),
    b.sudo_5Board_4cost.sudo_5Costs_4peak = (pk : Int) ∧
    b'.sudo_5Board_4cost.sudo_5Costs_4peak = (pk' : Int) ∧
    pk' ≤ max pk 7

/-- The climb hole `park_rung` reads, and the colour sitting there.
    `climb_holes` walks `ladder0 + R - 1` down to `ladder0`. The hole for
    rung index `ridx` is that list at `ridx`. -/
def climbAt (ladder0 len i : Nat) : Nat := ladder0 + len - 1 - i

structure ParkRead (b : Ecbs.Board) (s : ClimbModel) (rest : List Nat)
    (base : ClimbBudget) : Prop where
  ladder0B : b.sudo_5Board_7ladder0 = (base.ladder0 : Int)
  nrungsB : b.sudo_5Board_6nrungs = (base.R : Int)
  climbH : Ecbs.climb_holes b =
    .ok (embed (downFrom (base.ladder0 + base.R - 1) base.R))
  holeLt : climbAt base.ladder0 base.R s.ridx < s.row.length
  parkLt : s.parkAt < s.row.length
  parkNe : climbAt base.ladder0 base.R s.ridx ≠ s.parkAt
  parkLe : s.parkAt ≤ s.high
  parkIn : s.parkAt < base.control
  parkCell : s.fromHole < 0 → s.row[s.parkAt]'(parkLt) = 0
  fromIdle : s.fromHole < 0 → s.fromHole = -1
  fromNat : 0 ≤ s.fromHole → s.fromHole = ((s.fromHole.toNat : Nat) : Int)
  srcOk : 0 ≤ s.fromHole →
    s.fromHole.toNat < s.row.length ∧ s.fromHole.toNat < base.control ∧
      s.fromHole.toNat ≤ s.high ∧
      s.fromHole.toNat ≠ climbAt base.ladder0 base.R s.ridx
  parkHeld : 0 ≤ s.fromHole → ∃ prev, s.row[s.parkAt]'(parkLt) = prev
  nextRung : ∀ r rs, rest = r :: rs →
    s.row[climbAt base.ladder0 base.R s.ridx]'(holeLt) = r ∧ r ≠ 0
  fit2 : FitsLen (s.ctrl + 2)
  fit4 : FitsLen ((s.ctrl + 2) + 2)
  fitI : FitsLen (s.ridx + 1)
  l0pos : 0 < base.ladder0
  fitL0 : FitsLen base.ladder0
  fitLR : FitsLen (base.ladder0 + base.R)

/-- Naturals the cube-peg loop reads: ops slot 1, the strict peak, the recorded
    bench hole, the trit gap, and the i64 room for one loop. -/
structure PegRead (b : Ecbs.Board) (s : ClimbModel) (base : ClimbBudget) : Prop where
  opsGt : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size
  cOps : ∃ (c : Nat), b.sudo_5Board_4cost.sudo_5Costs_3ops[1]'(opsGt) = (c : Int)
  peakS : ∃ (p : Nat), b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (p : Int)
  holeM : ∃ (h : Nat), b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = (h : Int)
  trits : allTritList s.gap
  top : 0 < s.tally → s.t0 + s.tally - 1 ≤ s.high
  fitRow : FitsLen (s.t0 + s.tally)
  fitTall : FitsLen s.tally
  fitCtrl : FitsLen (s.ctrl + s.tally)
  n_pos : 0 < s.n
  span : 3 * (s.n - 1) + base.cg < s.benchlen
  small : base.w ≤ 1000000 ∧ base.h ≤ 1000000 ∧ base.r ≤ 1000000 ∧
    s.benchlen ≤ 1000001
  n_small : s.n ≤ 1000000
  fitN : FitsLen s.n
  fitBn : FitsLen s.benchlen
  fit3 : FitsLen (3 * (s.n - 1))

/-- What one rung reads off the board, beyond the gap polynomial and the counters.
    The spare (home 6) is empty. When the gap sits on the bench, home 5 is clear.
    When it sits in the home, the bench is off. The input home stays held. The
    tier layout is the board's. `seg` is the white tally and the empty holes
    past it, or the red segment once the final rung has run. -/
structure ClimbShape (b : Ecbs.Board) (s : ClimbModel) (rest : List Nat)
    (base : ClimbBudget) : Prop where
  spareH : 6 < b.sudo_5Board_4home.size
  spareD : 6 < b.sudo_5Board_4held.size
  spareE : b.sudo_5Board_4held[6] = false
  h7 : 7 ≤ b.sudo_5Board_4held.size
  gapClear : s.onBench = true →
    b.sudo_5Board_4held[5]'(Nat.lt_of_lt_of_le (by decide : (5 : Nat) < 7) h7) = false
  offWhenHome : s.onBench = false → b.sudo_5Board_8bench_on = false
  xD : base.xHome < b.sudo_5Board_4held.size
  xH : base.xHome < b.sudo_5Board_4home.size
  xHeld : b.sudo_5Board_4held[base.xHome] = true
  xArr : b.sudo_5Board_4home[base.xHome] = embed base.x
  xNe5 : base.xHome ≠ 5
  xNe6 : base.xHome ≠ 6
  gapLen : s.gap.length = s.n
  seg : RowSeg s.row s.t0 s.tally rest.isEmpty
  tierN : b.sudo_5Board_1t.sudo_4Tier_1n = (s.n : Int)
  tierK : b.sudo_5Board_1t.sudo_4Tier_1k = (s.k : Int)
  tierB : b.sudo_5Board_1t.sudo_4Tier_8benchlen = (s.benchlen : Int)
  tierW : b.sudo_5Board_1t.sudo_4Tier_1w = (base.w : Int)
  tierH : b.sudo_5Board_1t.sudo_4Tier_1h = (base.h : Int)
  tierR : b.sudo_5Board_1t.sudo_4Tier_1r = (base.r : Int)
  tierCg : b.sudo_5Board_1t.sudo_4Tier_7combgap = (base.cg : Int)
  tierC : b.sudo_5Board_1t.sudo_4Tier_7control = (base.control : Int)
  rowLen : s.row.length = base.control
  w0 : 0 < base.w
  h0 : 0 < base.h
  r0 : 0 < base.r
  rlt : base.r < base.h
  n_eq : s.n = base.w * base.h - 1
  k_le : s.k ≤ s.n
  gap_eq : s.n - s.k = base.w * base.r
  park : ParkRead b s rest base
  peg : PegRead b s base

/-- Induction hypothesis after the prefix `done`, with `rest` still to run.
    The tally length is `climbTallyPrefix`, proved from the rung list. The
    counters are at most `done.length` charges. `shape` is the spare, the gap
    home, the tally segment past the current length, the held input, and the
    tier layout. -/
structure ClimbInvK (done rest : List Nat) (b : Ecbs.Board) (s : ClimbModel)
    (base : ClimbBudget) : Prop where
  inv : ClimbInv b s
  idx : s.ridx = done.length
  hn : s.n = base.n
  hbench : s.benchlen = base.bench
  htally0 : s.tally = climbTallyPrefix base.tally0 done rest
  kLe : (done ++ rest).length ≤ base.R
  shape : ClimbShape b s rest base
  moves : ∃ (mv : Nat),
    b.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int) ∧
    mv ≤ base.moves0 + done.length * rungCharge base.n base.bench base.mMax
  slides : ∃ (sl : Nat),
    b.sudo_5Board_4cost.sudo_5Costs_6slides = (sl : Int) ∧
    sl ≤ base.slides0 + done.length * rungSlideCharge base.n base.mMax
  ops : ∀ i (hi : i < b.sudo_5Board_4cost.sudo_5Costs_3ops.size),
    ∃ (c : Nat), b.sudo_5Board_4cost.sudo_5Costs_3ops[i] = (c : Int) ∧
      c ≤ base.ops0 + done.length * (base.mMax + 3)
  peak : ∃ (pk : Nat),
    b.sudo_5Board_4cost.sudo_5Costs_4peak = (pk : Int) ∧
    pk ≤ max base.peak0 7
  /-- The recorded high is the last peg of the current tally. -/
  highTop : 0 < s.tally → s.high = s.t0 + s.tally - 1
  /-- A rung that is not the last has room to double: the next `tally` holes,
      and the hole one past them, sit on the control row. -/
  openRoom : 2 ≤ rest.length → s.t0 + 2 * s.tally < base.control
  /-- Those holes are empty. `k = tally` is the extra white peg after a double. -/
  openZero : 2 ≤ rest.length → ∀ k, k ≤ s.tally →
    ∀ (hix : s.t0 + s.tally + k < s.row.length),
      s.row[s.t0 + s.tally + k] = 0
  /-- `tally_max` is a natural below twice the current length. -/
  tmaxLt : ∃ tmax : Nat,
    b.sudo_5Board_4cost.sudo_5Costs_9tally_max = (tmax : Int) ∧
      (0 < s.tally → tmax < 2 * s.tally)
  /-- The control counter stays within `ctrl0` plus one `rungCtrl` step per
      finished rung. -/
  ctrlLe : s.ctrl ≤ base.ctrl0 + done.length * (3 * base.mMax + 5)

/-- The geometric envelope is a legal cap for whatever list is being climbed. -/
theorem climbCap_geom (tally0 R mMax : Nat) (rs done rest : List Nat)
    (hm : mMax = (tally0 + 1) * 2 ^ R)
    (hR : rs.length = R)
    (hrs : rs = done ++ rest) :
    climbTallyPrefix tally0 done rest ≤ mMax := by
  rw [hm]
  have hpre := climbTallyPrefix_le tally0 done rest
  have hlen : done.length ≤ R := by
    have hlenr : (done ++ rest).length = rs.length := by rw [hrs]
    simp at hlenr
    omega
  have hpow : 2 ^ done.length ≤ 2 ^ R :=
    Nat.pow_le_pow_right (by decide : 0 < 2) hlen
  exact Nat.le_trans hpre (Nat.mul_le_mul_left _ hpow)

theorem ClimbInvK.tally_le {done rest : List Nat} {b : Ecbs.Board} {s : ClimbModel}
    {base : ClimbBudget} (h : ClimbInvK done rest b s base)
    (hCap : climbTallyPrefix base.tally0 done rest ≤ base.mMax) :
    s.tally ≤ base.mMax := by
  rw [h.htally0]
  exact hCap

theorem ClimbInvK.moves_fit {done rest : List Nat} {b : Ecbs.Board} {s : ClimbModel}
    {base : ClimbBudget} (h : ClimbInvK done rest b s base) :
    ∃ (mv : Nat), b.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int) ∧ FitsLen mv := by
  obtain ⟨mv, heq, hle⟩ := h.moves
  have hk : done.length ≤ base.R := by
    have := h.kLe
    simp at this
    omega
  exact ⟨mv, heq, rung_budget_fit base.moves0 done.length base.R
    (rungCharge base.n base.bench base.mMax) mv hk hle base.fitM⟩

/-- `rungHigh` keeps "high = last peg of the tally" as the length grows. -/
private theorem modelRung_highTop (s : ClimbModel) (x : List Nat) (rung hole : Nat)
    (last : Bool) (hTop : 0 < s.tally → s.high = s.t0 + s.tally - 1) :
    0 < (modelRung s x rung hole last).tally →
      (modelRung s x rung hole last).high =
        (modelRung s x rung hole last).t0 +
          (modelRung s x rung hole last).tally - 1 := by
  intro hpos
  have ht : (modelRung s x rung hole last).tally = tallyAfter s.tally rung last :=
    modelRung_tally s x rung hole last
  have hh : (modelRung s x rung hole last).high =
      rungHigh s.high s.t0 s.tally rung last := by
    simp [modelRung]
  have h0 : (modelRung s x rung hole last).t0 = s.t0 := by
    simp [modelRung]
  rw [ht] at hpos
  rw [hh, h0, ht]
  by_cases hL : last
  · have hta : tallyAfter s.tally rung last = s.tally := by
      simp [tallyAfter, hL]
    have hhi : rungHigh s.high s.t0 s.tally rung last = s.high := by
      simp [rungHigh, hL]
    rw [hta] at hpos
    rw [hhi, hta]
    exact hTop hpos
  · by_cases hR : rung = 2
    · have hta : tallyAfter s.tally rung last = 2 * s.tally + 1 := by
        simp [tallyAfter, hL, hR]
      have hhi : rungHigh s.high s.t0 s.tally rung last = s.t0 + 2 * s.tally := by
        simp [rungHigh, hL, hR]
      rw [hhi, hta]
      omega
    · have hta : tallyAfter s.tally rung last = 2 * s.tally := by
        simp [tallyAfter, hL, hR]
      have hhi : rungHigh s.high s.t0 s.tally rung last =
          s.t0 + 2 * s.tally - 1 := by
        simp [rungHigh, hL, hR]
      rw [hhi, hta]

/-- One rung preserves the counter bounds. The new tally is the model's
    `tallyAfter`, so it stays under `mMax` by `climbTallyPrefix_le`.
    The recorded high stays the last peg. Room for the next double, the empty
    tail, and `tally_max` are supplied the way `ClimbShape` is: the step that
    builds the new board knows them, and this lemma records them. -/
theorem climbInvK_succ {done rest : List Nat} {r : Nat} {b b' : Ecbs.Board}
    {s : ClimbModel} {base : ClimbBudget} {x : List Nat} {hole : Nat}
    (h : ClimbInvK done (r :: rest) b s base)
    (hinv : ClimbInv b' (modelRung s x r hole rest.isEmpty))
    (hδ : RungDelta b b' base s.tally)
    (hCap : climbTallyPrefix base.tally0 done (r :: rest) ≤ base.mMax)
    (hshape : ClimbShape b' (modelRung s x r hole rest.isEmpty) rest base)
    (hopen : 2 ≤ rest.length →
      (modelRung s x r hole rest.isEmpty).t0 +
        2 * (modelRung s x r hole rest.isEmpty).tally < base.control)
    (hzero : 2 ≤ rest.length →
      ∀ k, k ≤ (modelRung s x r hole rest.isEmpty).tally →
        ∀ (hix : (modelRung s x r hole rest.isEmpty).t0 +
            (modelRung s x r hole rest.isEmpty).tally + k <
            (modelRung s x r hole rest.isEmpty).row.length),
          (modelRung s x r hole rest.isEmpty).row[
            (modelRung s x r hole rest.isEmpty).t0 +
              (modelRung s x r hole rest.isEmpty).tally + k] = 0)
    (htmax : ∃ tmax : Nat,
      b'.sudo_5Board_4cost.sudo_5Costs_9tally_max = (tmax : Int) ∧
        (0 < (modelRung s x r hole rest.isEmpty).tally →
          tmax < 2 * (modelRung s x r hole rest.isEmpty).tally)) :
    ClimbInvK (done ++ [r]) rest b' (modelRung s x r hole rest.isEmpty) base := by
  have hT := h.tally_le hCap
  have hm : rungCharge base.n base.bench s.tally ≤
      rungCharge base.n base.bench base.mMax :=
    rungCharge_mono base.n base.bench s.tally base.mMax hT
  have hs : rungSlideCharge base.n s.tally ≤ rungSlideCharge base.n base.mMax :=
    rungSlideCharge_mono base.n s.tally base.mMax hT
  refine
    { inv := hinv
      idx := ?_
      hn := ?_
      hbench := ?_
      htally0 := ?_
      kLe := ?_
      shape := hshape
      moves := ?_
      slides := ?_
      ops := ?_
      peak := ?_
      highTop := modelRung_highTop s x r hole rest.isEmpty h.highTop
      openRoom := hopen
      openZero := hzero
      tmaxLt := htmax
      ctrlLe := ?_ }
  · simp [modelRung, h.idx, List.length_append]
  · simp [modelRung, h.hn]
  · simp [modelRung, h.hbench]
  · rw [modelRung_tally, h.htally0]
    exact (climbTallyPrefix_snoc base.tally0 done rest r).symm
  · simpa [List.length_append, List.cons_append] using h.kLe
  · obtain ⟨mv, mv', hb, hb', hle⟩ := hδ.moves
    obtain ⟨mv0, hb0, hbound⟩ := h.moves
    have hmv : mv = mv0 := ofNat_inj_nat (hb.symm.trans hb0)
    refine ⟨mv', hb', ?_⟩
    have hlen : (done ++ [r]).length = done.length + 1 := by simp
    rw [hlen]
    have : mv' ≤ base.moves0 + (done.length + 1) * rungCharge base.n base.bench base.mMax := by
      have h1 : mv' ≤ mv + rungCharge base.n base.bench s.tally := hle
      have h2 : mv + rungCharge base.n base.bench s.tally ≤
          mv + rungCharge base.n base.bench base.mMax := Nat.add_le_add_left hm _
      have h3 : mv ≤ base.moves0 + done.length * rungCharge base.n base.bench base.mMax := by
        rw [hmv]; exact hbound
      have h4 : (done.length + 1) * rungCharge base.n base.bench base.mMax =
          done.length * rungCharge base.n base.bench base.mMax +
            rungCharge base.n base.bench base.mMax := by
        rw [Nat.succ_mul]
      omega
    exact this
  · obtain ⟨sl, sl', hb, hb', hle⟩ := hδ.slides
    obtain ⟨sl0, hb0, hbound⟩ := h.slides
    have hsl : sl = sl0 := ofNat_inj_nat (hb.symm.trans hb0)
    refine ⟨sl', hb', ?_⟩
    have hlen : (done ++ [r]).length = done.length + 1 := by simp
    rw [hlen]
    have : sl' ≤ base.slides0 + (done.length + 1) * rungSlideCharge base.n base.mMax := by
      have h1 : sl' ≤ sl + rungSlideCharge base.n s.tally := hle
      have h4 : (done.length + 1) * rungSlideCharge base.n base.mMax =
          done.length * rungSlideCharge base.n base.mMax +
            rungSlideCharge base.n base.mMax := by
        rw [Nat.succ_mul]
      omega
    exact this
  · intro i hi
    have hi0 : i < b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
      rw [← hδ.opsSize]; exact hi
    obtain ⟨c, c', hc, hc', hle⟩ := hδ.ops i hi0
    obtain ⟨c0, hc0, hbound⟩ := h.ops i hi0
    have hcEq : c = c0 := ofNat_inj_nat (hc.symm.trans hc0)
    refine ⟨c', hc', ?_⟩
    have hlen : (done ++ [r]).length = done.length + 1 := by simp
    rw [hlen]
    have h4 : (done.length + 1) * (base.mMax + 3) =
        done.length * (base.mMax + 3) + (base.mMax + 3) := by
      rw [Nat.succ_mul]
    omega
  · obtain ⟨pk, pk', hb, hb', hle⟩ := hδ.peak
    obtain ⟨pk0, hb0, hbound⟩ := h.peak
    have hpk : pk = pk0 := ofNat_inj_nat (hb.symm.trans hb0)
    refine ⟨pk', hb', peak_carry base.peak0 pk pk' (by rw [hpk]; exact hbound) hle⟩
  · have hctrl : (modelRung s x r hole rest.isEmpty).ctrl =
        rungCtrl s.ctrl s.tally r rest.isEmpty (decide (0 ≤ s.fromHole)) := by
      simp [modelRung]
    rw [hctrl]
    have hlen : (done ++ [r]).length = done.length + 1 := by simp
    rw [hlen]
    have hinc := rungCtrl_inc s.ctrl s.tally r rest.isEmpty (decide (0 ≤ s.fromHole))
    have hmul : 3 * s.tally + 5 ≤ 3 * base.mMax + 5 := by
      have := Nat.mul_le_mul_left 3 hT
      omega
    have hgrow : s.ctrl + 3 * s.tally + 5 ≤
        base.ctrl0 + done.length * (3 * base.mMax + 5) + (3 * base.mMax + 5) := by
      have hle := h.ctrlLe
      omega
    have hsum : done.length * (3 * base.mMax + 5) + (3 * base.mMax + 5) =
        (done.length + 1) * (3 * base.mMax + 5) := by
      rw [← Nat.succ_mul]
    apply Nat.le_trans hinc
    apply Nat.le_trans hgrow
    rw [Nat.add_assoc, hsum]
    exact Nat.le_refl _

/-- The emitted climb, one rung at a time. `last` is the empty tail. -/
def climbEmit (step : Ecbs.Board → Nat → Bool → Except SudoRt.Trap Ecbs.Board)
    (b : Ecbs.Board) : List Nat → Except SudoRt.Trap Ecbs.Board
  | [] => .ok b
  | r :: rs => do
      let b ← step b r rs.isEmpty
      climbEmit step b rs

/-- Induction over a rung list. The list is the climb order, which for `invert`
    is `(rungList (n − 1)).reverse`, so the final rung is last. Each step is an
    emitted rung (`rung_step_refines` under that rung's domain) whose counters
    grow by at most one charge and whose board satisfies `ClimbInv` for
    `modelRung`. The tally bound is the model's, not a separate assumption. -/
theorem climb_refines
    (step : Ecbs.Board → Nat → Bool → Except SudoRt.Trap Ecbs.Board)
    (rs : List Nat) (b0 : Ecbs.Board) (s0 : ClimbModel) (base : ClimbBudget)
    (x : List Nat) (hole : ClimbModel → Nat → Bool → Nat)
    (h0 : ClimbInvK [] rs b0 s0 base)
    (hR : rs.length = base.R)
    (hn : s0.n = base.n) (hbench : s0.benchlen = base.bench)
    (hCap : ∀ done rest, rs = done ++ rest →
      climbTallyPrefix base.tally0 done rest ≤ base.mMax)
    (hstep : ∀ (done rest : List Nat) (r : Nat) (b : Ecbs.Board) (s : ClimbModel),
      rs = done ++ r :: rest →
      ∀ (hK : ClimbInvK done (r :: rest) b s base),
      ∃ b', step b r rest.isEmpty = .ok b' ∧
        ClimbInv b' (modelRung s x r (hole s r rest.isEmpty) rest.isEmpty) ∧
        RungDelta b b' base s.tally ∧
        ClimbShape b' (modelRung s x r (hole s r rest.isEmpty) rest.isEmpty) rest base ∧
        (2 ≤ rest.length →
          (modelRung s x r (hole s r rest.isEmpty) rest.isEmpty).t0 +
            2 * (modelRung s x r (hole s r rest.isEmpty) rest.isEmpty).tally <
              base.control) ∧
        (2 ≤ rest.length →
          ∀ k, k ≤ (modelRung s x r (hole s r rest.isEmpty) rest.isEmpty).tally →
            ∀ (hix : (modelRung s x r (hole s r rest.isEmpty) rest.isEmpty).t0 +
                (modelRung s x r (hole s r rest.isEmpty) rest.isEmpty).tally + k <
                (modelRung s x r (hole s r rest.isEmpty) rest.isEmpty).row.length),
              (modelRung s x r (hole s r rest.isEmpty) rest.isEmpty).row[
                (modelRung s x r (hole s r rest.isEmpty) rest.isEmpty).t0 +
                  (modelRung s x r (hole s r rest.isEmpty) rest.isEmpty).tally + k] = 0) ∧
        (∃ tmax : Nat,
          b'.sudo_5Board_4cost.sudo_5Costs_9tally_max = (tmax : Int) ∧
            (0 < (modelRung s x r (hole s r rest.isEmpty) rest.isEmpty).tally →
              tmax < 2 * (modelRung s x r (hole s r rest.isEmpty) rest.isEmpty).tally))) :
    ∃ b' s', climbEmit step b0 rs = .ok b' ∧ s' = modelClimb s0 x hole rs ∧
      ClimbInvK rs [] b' s' base ∧
      (s'.gap, s'.tally) = invClimb s0.n s0.k s0.benchlen x (s0.gap, s0.tally) rs ∧
      s'.tally ≤ base.mMax := by
  have hmain : ∀ (done rest : List Nat) (b : Ecbs.Board) (s : ClimbModel),
      rs = done ++ rest →
      ClimbInvK done rest b s base →
      ∃ b' s', climbEmit step b rest = .ok b' ∧
        s' = modelClimb s x hole rest ∧
        ClimbInvK (done ++ rest) [] b' s' base := by
    intro done rest
    induction rest generalizing done with
    | nil =>
      intro b s hrs h
      exact ⟨b, s, by simp [climbEmit], rfl, by simpa using h⟩
    | cons r rest ih =>
      intro b s hrs h
      obtain ⟨b1, hb1, hinv, hδ, hshape, hopen, hzero, htmax⟩ :=
        hstep done rest r b s hrs h
      have hK := climbInvK_succ h hinv hδ (hCap done (r :: rest) hrs) hshape
        hopen hzero htmax
      have hrs' : rs = (done ++ [r]) ++ rest := by
        simp [hrs, List.append_assoc]
      obtain ⟨b', s', hfold, hs', hK'⟩ := ih (done ++ [r]) b1
        (modelRung s x r (hole s r rest.isEmpty) rest.isEmpty) hrs' hK
      refine ⟨b', s', ?_, ?_, ?_⟩
      · rw [climbEmit, hb1, ok_bind]
        exact hfold
      · simp [modelClimb, hs']
      · simpa [List.append_assoc] using hK'
  obtain ⟨b', s', hfold, hs', hK⟩ := hmain [] rs b0 s0 (by simp) h0
  refine ⟨b', s', hfold, hs', hK, ?_, hK.tally_le (hCap rs [] (by simp))⟩
  rw [hs']
  exact modelClimb_spec s0 x hole rs

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
    (hcube : 3 * (t.n - 1) + t.combgap < t.benchlen)
    (hmul : 2 * (t.n - 1) < t.benchlen) : TierSat t := by
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
    (by decide) (by decide)

theorem toy_tier_sat : TierSat Spec.toy := by
  have hR : tierR Spec.toy = 4 := by unfold tierR; rw [toy_rungs]; decide
  have hClimb : tierClimb Spec.toy = [1, 2, 2, 1] := by unfold tierClimb; rw [toy_rungs]; decide
  have hO : tallyOrigin Spec.toy = 22 := by unfold tallyOrigin; rw [hR]; decide
  have hRoom : rowRoom Spec.toy = 18 := by unfold rowRoom; rw [hO]; decide
  have hG : geomCap Spec.toy = 32 := by unfold geomCap; rw [hR]
  exact tierSat_num Spec.toy 22 18 32 4 [1, 2, 2, 1] hO hRoom hG hR hClimb
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)

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
    (by decide) (by decide)

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
    (by decide) (by decide)

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

/-- Clear home 5. The spare and every other home stay. The gap home is empty. -/
theorem clearHeld_gap (b : Ecbs.Board) (xs : List Nat) (moves : Nat)
    (hH : 5 < b.sudo_5Board_4home.size) (hD : 5 < b.sudo_5Board_4held.size) :
    (clearHeldBoard b 5 xs moves hH hD).sudo_5Board_4held[5]'(by
      simp [clearHeldBoard, Array.size_set]; exact hD) = false := by
  simp [clearHeldBoard, Array.getElem_set]

theorem clearHeld_keep (b : Ecbs.Board) (home other : Nat) (xs : List Nat) (moves : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (hO : other < b.sudo_5Board_4held.size) (hne : other ≠ home)
    (h : b.sudo_5Board_4held[other] = false) :
    (clearHeldBoard b home xs moves hH hD).sudo_5Board_4held[other]'(by
      simp [clearHeldBoard, Array.size_set]; exact hO) = false := by
  simp [clearHeldBoard, Array.getElem_set, Ne.symm hne, h]

theorem clearHeld_keep_held (b : Ecbs.Board) (home other : Nat) (xs : List Nat) (moves : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (hO : other < b.sudo_5Board_4held.size) (hne : other ≠ home)
    (h : b.sudo_5Board_4held[other] = true) :
    (clearHeldBoard b home xs moves hH hD).sudo_5Board_4held[other]'(by
      simp [clearHeldBoard, Array.size_set]; exact hO) = true := by
  simp [clearHeldBoard, Array.getElem_set, Ne.symm hne, h]

/-- Re-establish the shape on a board that still holds the input, still has an
    empty spare, and has cleared the gap, with the model's new tally segment. -/
theorem shape_refresh {b : Ecbs.Board} {s : ClimbModel} {done : List Nat}
    {base : ClimbBudget} (h : ClimbShape b s done base)
    (b' : Ecbs.Board) (s' : ClimbModel) (rest : List Nat)
    (hn : s'.n = s.n) (hk : s'.k = s.k) (hb : s'.benchlen = s.benchlen)
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
    (hpeg : PegRead b' s' base) :
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
    (hnb : s.n ≤ s.benchlen)
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
    (h : ClimbInvK done (r :: rest) b s base) :
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

/-- The bench-off cube-peg loop's context. The gap sits in home 5, so the bench
    is off and the spare is empty. Copying the gap into the spare is `place`.
    That board is the `PegCtx`: home 6 holds the gap, the bench stays off, and
    the move counter has grown by the nonzero count of the gap. The cube-loop
    budget is one rung charge of the climb, which already covers that copy. -/
theorem peg_of_shape {done rest : List Nat} {r : Nat} {b : Ecbs.Board} {s : ClimbModel}
    {base : ClimbBudget} (h : ClimbInvK done (r :: rest) b s base)
    (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax)
    (hhome : s.onBench = false) :
    ∃ (mv pk sl : Nat) (c : PegCtx),
      b.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int) ∧
      b.sudo_5Board_4cost.sudo_5Costs_4peak = (pk : Int) ∧
      b.sudo_5Board_4cost.sudo_5Costs_6slides = (sl : Int) ∧
      mv ≤ base.moves0 + done.length * rungCharge base.n base.bench base.mMax ∧
      sl ≤ base.slides0 + done.length * rungSlideCharge base.n base.mMax ∧
      c.b0 = placeBoard b 6 h.shape.spareH h.shape.spareD s.gap mv pk ∧
      Ecbs.copy_band b ((6 : Nat) : Int) ((5 : Nat) : Int) false = .ok c.b0 ∧
      c.src = 6 ∧ c.g = s.gap ∧ c.m = s.tally ∧ c.row0 = s.row ∧
      c.n = s.n ∧ c.k = s.k ∧ c.bench = s.benchlen ∧
      c.moves0 = mv + pegCount s.gap ∧ c.slides0 = sl ∧ c.t0 = s.t0 ∧
      c.ctrl0 = s.ctrl ∧ c.high = s.high ∧ c.control = base.control ∧
      c.b0.sudo_5Board_9tally_len = (s.tally : Int) ∧
      c.b0.sudo_5Board_4cost.sudo_5Costs_9tally_max =
        b.sudo_5Board_4cost.sudo_5Costs_9tally_max := by
  obtain ⟨mv, hmv, hmvLe⟩ := h.moves
  obtain ⟨sl, hsl, hslLe⟩ := h.slides
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
    apply FitsLen.of_le base.fitM
    have hle : mv + pegCount s.gap + s.tally * pegCharge s.n s.benchlen ≤
        base.moves0 + (done.length + 1) * rungCharge base.n base.bench base.mMax := by
      have hstep : (done.length + 1) * rungCharge base.n base.bench base.mMax =
          done.length * rungCharge base.n base.bench base.mMax +
            rungCharge base.n base.bench base.mMax := by
        rw [Nat.succ_mul]
      omega
    have hR : (done.length + 1) * rungCharge base.n base.bench base.mMax ≤
        base.R * rungCharge base.n base.bench base.mMax :=
      Nat.mul_le_mul_right _ hk
    omega
  have hfitCopy : FitsLen (mv + pegCount s.gap) :=
    FitsLen.of_le hmovFit (by omega)
  have hcopy := copy_band_refines b 6 5 s.gap mv pk
    h.shape.spareH h.shape.spareD h.inv.hG h.inv.hGs h.shape.h7
    hgapH.1 hgapH.2 h.shape.spareE
    (by rw [h.shape.gapLen]; exact h.shape.tierN)
    (by rw [h.shape.gapLen]; exact h.shape.peg.fitN)
    hmv hpk hfitCopy
  let b1 := placeBoard b 6 h.shape.spareH h.shape.spareD s.gap mv pk
  have hbook := place_book b 6 h.shape.spareH h.shape.spareD s.gap mv pk
  have hidle := place_idle b 6 h.shape.spareH h.shape.spareD s.gap mv pk
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
      simpa using place_held_here b 6 h.shape.spareH h.shape.spareD s.gap mv pk hF
    hArr := by
      have hF : 6 < b1.sudo_5Board_4home.size := by
        rw [hbook.2.2.2.2.2.2.2.2.1]; exact h.shape.spareH
      simpa using place_home_here b 6 h.shape.spareH h.shape.spareD s.gap mv pk hF
    h7 := by rw [hbook.2.2.2.2.2.2.2.2.2]; exact h.shape.h7
    hn0 := h.shape.peg.n_pos
    hn := by rw [hidle.2.2.2.2.1]; exact h.shape.tierN
    hlenx := h.shape.gapLen
    hf := h.shape.peg.fitN
    hmoves0 := by
      rw [place_moves b 6 h.shape.spareH h.shape.spareD s.gap mv pk]
      exact ofNat_eq_natCast _
    hpeak0 := by
      rw [place_peak b 6 h.shape.spareH h.shape.spareD s.gap mv pk hpk]
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
      apply FitsLen.of_le base.fitS
      have hslide : s.tally * (2 * s.n) ≤ rungSlideCharge base.n base.mMax := by
        unfold rungSlideCharge
        have hn : s.n = base.n := h.hn
        have hmul : s.tally * (2 * s.n) ≤ (base.mMax + 3) * (2 * s.n) :=
          Nat.mul_le_mul_right _ (Nat.le_trans hT (Nat.le_add_right _ _))
        simpa [hn] using hmul
      have hstep : sl + s.tally * (2 * s.n) ≤
          base.slides0 + (done.length + 1) * rungSlideCharge base.n base.mMax := by
        have hsucc : (done.length + 1) * rungSlideCharge base.n base.mMax =
            done.length * rungSlideCharge base.n base.mMax +
              rungSlideCharge base.n base.mMax := by rw [Nat.succ_mul]
        omega
      have hR : (done.length + 1) * rungSlideCharge base.n base.mMax ≤
          base.R * rungSlideCharge base.n base.mMax :=
        Nat.mul_le_mul_right _ hk
      omega
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
  }, hmv, hpk, hsl, hmvLe, hslLe, rfl, hcopy, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hlen0, hmax0⟩

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
  let bC := cubeLiveBoard d.b c.src c.src d.xs c.n c.k d.moves d.slides d.hole c.bench
    d.peak d.peakS d.cOps d.hH d.hD d.hops
  have hLiveH : (livePegBoard c d hi).sudo_5Board_4held = bC.sudo_5Board_4held := by
    unfold livePegBoard pegStep; rfl
  have hLiveHome : (livePegBoard c d hi).sudo_5Board_4home = bC.sudo_5Board_4home := by
    unfold livePegBoard pegStep; rfl
  have hLiveOps : (livePegBoard c d hi).sudo_5Board_4cost.sudo_5Costs_3ops =
      bC.sudo_5Board_4cost.sudo_5Costs_3ops := by
    unfold livePegBoard pegStep; rfl
  have hC := cube_live_held d.b c.src c.src d.xs c.n c.k d.moves d.slides d.hole c.bench
    d.peak d.peakS d.cOps d.hH d.hD d.hops
  have hS := settle_held_eq d.b c.src d.hH d.hD d.xs c.n d.moves d.slides d.peak
  have hHomeEq : bC.sudo_5Board_4home =
      d.b.sudo_5Board_4home.set ⟨c.src, d.hH⟩ #[] :=
    cube_live_home d.b c.src c.src d.xs c.n c.k d.moves d.slides d.hole c.bench
      d.peak d.peakS d.cOps d.hH d.hD d.hops
  have hOpsEq : bC.sudo_5Board_4cost.sudo_5Costs_3ops =
      d.b.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨1, d.hops⟩ (Int.ofNat (d.cOps + 1)) :=
    cube_live_ops d.b c.src c.src d.xs c.n c.k d.moves d.slides d.hole c.bench
      d.peak d.peakS d.cOps d.hH d.hD d.hops
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
private theorem pegPack_keep (c : PegCtx) (first : Nat) (xs0 : List Nat) (cMul : Nat)
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
    {base : ClimbBudget} (h : ClimbInvK done (r :: rest) b s base)
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
      moves + 2 * pegCount (ys.take c.n) + c.n * (c.n + 1) + 3 * (c.bench - c.n) ≤
        base.moves0 + base.R * rungCharge base.n base.bench base.mMax ∧
      moves ≤ base.moves0 + done.length * rungCharge base.n base.bench base.mMax +
        base.n + s.tally * pegCharge base.n base.bench ∧
      slides + 2 * pegCount (ys.take c.n) ≤
        base.slides0 + base.R * rungSlideCharge base.n base.mMax ∧
      slides ≤ base.slides0 + done.length * rungSlideCharge base.n base.mMax +
        s.tally * (2 * base.n) ∧
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
        .ok (mulNoLiveBoard bM 5 6 c.g ys c.n c.k moves slides hole c.bench
          peak peakS cOps hH hD hops) := by
  obtain ⟨mv, pk, sl, c, hmv, hpk, hsl, hmvLe, hslLe, hb0, hcopy, hsrc, hg, hmEq, _hrow0,
      hn, hkN, hbch, hmv0, hsl0, ht0, hctrl0, hhigh0, hcontrol, hlen0, hmax0⟩ :=
    peg_of_shape h hm hT hhome
  have hk : done.length + 1 ≤ base.R := by
    have hlen := h.kLe
    rw [List.length_append, List.length_cons] at hlen
    omega
  have hbook := place_book b 6 h.shape.spareH h.shape.spareD s.gap mv pk
  have hidle := place_idle b 6 h.shape.spareH h.shape.spareD s.gap mv pk
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
      ((place_held_other b 6 5 h.shape.spareH h.shape.spareD s.gap mv pk
        (by decide) h.inv.hGs (hHeldEq ▸ hFD)).trans (h.inv.gapHome hhome).1)
  have hArr5 : c.b0.sudo_5Board_4home[5] = embed c.g := by
    rw [(idx_get hHomeEq5 5 hFH).trans
        (place_home_other b 6 5 h.shape.spareH h.shape.spareD s.gap mv pk
          (by decide) h.inv.hG (hHomeEq5 ▸ hFH)),
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
  have hcap : c.moves0 + c.m * pegCharge c.n c.bench + mulCharge c.n c.bench ≤
      base.moves0 + base.R * rungCharge base.n base.bench base.mMax := by
    rw [hmv0, hmEq, hn, hbch]
    have hpegN : pegCount s.gap ≤ base.n := by
      have h1 : pegCount s.gap ≤ s.gap.length := pegCount_le s.gap
      rw [h.shape.gapLen, h.hn] at h1
      exact h1
    have hpiece : pegCount s.gap + s.tally * pegCharge s.n s.benchlen +
        mulCharge s.n s.benchlen ≤ rungCharge base.n base.bench base.mMax := by
      unfold rungCharge
      rw [h.hn, h.hbench, Nat.two_mul (base.n), Nat.two_mul (mulCharge base.n base.bench)]
      have hA : pegCount s.gap ≤ base.n + base.n := Nat.le_trans hpegN (Nat.le_add_left _ _)
      have hB : s.tally * pegCharge base.n base.bench ≤
          (base.mMax + 1) * pegCharge base.n base.bench :=
        Nat.mul_le_mul_right _ (Nat.le_succ_of_le hT)
      have hC : mulCharge base.n base.bench ≤
          mulCharge base.n base.bench + mulCharge base.n base.bench :=
        Nat.le_add_right _ _
      omega
    have hassoc : mv + pegCount s.gap + s.tally * pegCharge s.n s.benchlen +
        mulCharge s.n s.benchlen =
        mv + (pegCount s.gap + s.tally * pegCharge s.n s.benchlen +
          mulCharge s.n s.benchlen) := by
      rw [← Nat.add_assoc, ← Nat.add_assoc]
    have hleft : mv + pegCount s.gap + s.tally * pegCharge s.n s.benchlen +
        mulCharge s.n s.benchlen ≤ mv + rungCharge base.n base.bench base.mMax := by
      rw [hassoc]
      exact Nat.add_le_add_left hpiece mv
    have hmvR : mv + rungCharge base.n base.bench base.mMax ≤
        base.moves0 + done.length * rungCharge base.n base.bench base.mMax +
          rungCharge base.n base.bench base.mMax :=
      Nat.add_le_add_right hmvLe _
    have hsplit : base.moves0 + done.length * rungCharge base.n base.bench base.mMax +
        rungCharge base.n base.bench base.mMax =
        base.moves0 + (done.length + 1) * rungCharge base.n base.bench base.mMax := by
      rw [Nat.add_assoc, ← Nat.succ_mul]
    have hR : base.moves0 + (done.length + 1) * rungCharge base.n base.bench base.mMax ≤
        base.moves0 + base.R * rungCharge base.n base.bench base.mMax :=
      Nat.add_le_add_left (Nat.mul_le_mul_right _ hk) _
    exact Nat.le_trans hleft (Nat.le_trans hmvR (Nat.le_trans (Nat.le_of_eq hsplit) hR))
  have hfold : FitsLen (d.moves + 2 * pegCount (d.xs.take c.n) + c.n * (c.n + 1) +
      3 * (c.bench - c.n)) :=
    FitsLen.of_le base.fitM (Nat.le_trans hsum hcap)
  have hfm : FitsLen (d.moves + 2 * pegCount (d.xs.take c.n) + c.n * (c.n + 1)) :=
    FitsLen.of_le hfold (by omega)
  have hfitM : FitsLen (d.moves + 2 * pegCount (d.xs.take c.n)) :=
    FitsLen.of_le hfm (by omega)
  have hpegF : FitsLen (2 * pegCount (d.xs.take c.n)) := FitsLen.of_le hfitM (by omega)
  have hsPrev := d.hsldB
  have hsld : d.slides + 2 * pegCount (d.xs.take c.n) ≤
      base.slides0 + base.R * rungSlideCharge base.n base.mMax := by
    have h2 : 2 * pegCount (d.xs.take c.n) ≤ 2 * c.n := by omega
    have hSlidesEq : c.slides0 + c.m * (2 * c.n) = sl + s.tally * (2 * s.n) := by
      rw [hsl0, hmEq, hn]
    have hloc : d.slides + 2 * pegCount (d.xs.take c.n) ≤
        sl + (s.tally + 1) * (2 * s.n) := by
      have hprev' : d.slides ≤ sl + s.tally * (2 * s.n) := by
        exact Nat.le_trans hsPrev (Nat.le_of_eq hSlidesEq)
      have h2s : 2 * pegCount (d.xs.take c.n) ≤ 2 * s.n := by
        rw [← hn]; exact h2
      have hmul : (s.tally + 1) * (2 * s.n) = s.tally * (2 * s.n) + 2 * s.n := by
        rw [Nat.succ_mul]
      omega
    have hpiece : (s.tally + 1) * (2 * s.n) ≤ rungSlideCharge base.n base.mMax := by
      unfold rungSlideCharge
      rw [h.hn]
      have ht : s.tally + 1 ≤ base.mMax + 3 := by omega
      exact Nat.mul_le_mul_right _ ht
    have h1 : d.slides + 2 * pegCount (d.xs.take c.n) ≤
        sl + rungSlideCharge base.n base.mMax :=
      Nat.le_trans hloc (Nat.add_le_add_left hpiece sl)
    have h2 : sl + rungSlideCharge base.n base.mMax ≤
        base.slides0 + done.length * rungSlideCharge base.n base.mMax +
          rungSlideCharge base.n base.mMax :=
      Nat.add_le_add_right hslLe _
    have hsplit : base.slides0 + done.length * rungSlideCharge base.n base.mMax +
        rungSlideCharge base.n base.mMax =
        base.slides0 + (done.length + 1) * rungSlideCharge base.n base.mMax := by
      rw [Nat.add_assoc, ← Nat.succ_mul]
    have hR : base.slides0 + (done.length + 1) * rungSlideCharge base.n base.mMax ≤
        base.slides0 + base.R * rungSlideCharge base.n base.mMax :=
      Nat.add_le_add_left (Nat.mul_le_mul_right _ hk) _
    exact Nat.le_trans h1 (Nat.le_trans h2 (Nat.le_trans (Nat.le_of_eq hsplit) hR))
  have hfitS : FitsLen (d.slides + 2 * pegCount (d.xs.take c.n)) :=
    FitsLen.of_le base.fitS hsld
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
  have hmul := mul_eq_live d.b 5 5 6 c.g d.xs c.w c.h c.r c.n c.k d.moves d.slides
    d.hole c.bench d.peak d.peakS cMul
    d.marker d.onB hto hH6 hD6 d.h7 hempty d.hbench
    hnB c.hn0 d.hpos d.hnle d.hzero c.hf hfitL
    d.hmoves d.hslides d.hpeak hpegF hfitM hfitS
    hkeep.opsLt hkeep.op0 hfops hbl
    hkeep.heldLt hkeep.homeLt hkeep.held hkeep.arr (by decide) c.hlenx
    hspan2 c.hxsT hfi hfm
    c.hw0 c.hh0 c.hrR c.hrP c.hnE c.hkLe c.hgap hwF hhF hrF hkF
    d.hHole d.hpeakS c.hsm c.hnsm c.hfitB hfold
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
      ((place_held_other b 6 base.xHome h.shape.spareH h.shape.spareD s.gap mv pk
        (Ne.symm h.shape.xNe6) h.shape.xD (hXHeldEq ▸ hXFD0)).trans h.shape.xHeld)
  have hXArr0 : c.b0.sudo_5Board_4home[base.xHome] = embed base.x := by
    rw [(idx_get hXHomeEq base.xHome hXFH0).trans
        (place_home_other b 6 base.xHome h.shape.spareH h.shape.spareD s.gap mv pk
          (Ne.symm h.shape.xNe6) h.shape.xH (hXHomeEq ▸ hXFH0)),
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
    Nat.le_trans hsum hcap,
    (by
      have hpeg : pegCount s.gap ≤ base.n := by
        have hlen : pegCount s.gap ≤ s.gap.length := pegCount_le s.gap
        rw [h.shape.gapLen, h.hn] at hlen
        exact hlen
      have hbound : c.moves0 + c.m * pegCharge c.n c.bench ≤
          base.moves0 + done.length * rungCharge base.n base.bench base.mMax +
            base.n + s.tally * pegCharge base.n base.bench := by
        rw [hmv0, hmEq, hn, hbch, h.hn, h.hbench]
        have hpeg' : pegCount s.gap ≤ base.n := hpeg
        omega
      exact Nat.le_trans d.hmovB hbound),
    hsld,
    (by
      have hbound : c.slides0 + c.m * (2 * c.n) ≤
          base.slides0 + done.length * rungSlideCharge base.n base.mMax +
            s.tally * (2 * base.n) := by
        rw [hsl0, hmEq, hn, h.hn]
        exact Nat.add_le_add_right hslLe _
      exact Nat.le_trans d.hsldB hbound),
    ⟨d.cOps, d.hops, d.hop1, hCubeFit⟩,
    (by rw [d.hrow, _hrow0, ht0, hmEq]),
    d.tier, d.marker,
    (by
      rw [hPack.2.2.2.2.2.2.2.2]
      exact c.h7),
    hkeep.op0, hcLe, hctrl0, hhigh0, hcontrol, hlen0, hmax0, ht0,
    hmul⟩

/-- A live nocopy mul clears the second home. A different home, and the array it holds, stay. -/
private theorem mulLive_keep (b : Ecbs.Board) (dst second first : Nat) (xs ys : List Nat)
    (n k moves slides hole bench peak peakS cOps : Nat) (xs0 : List Nat)
    (hH : second < b.sudo_5Board_4home.size) (hD : second < b.sudo_5Board_4held.size)
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hne : first ≠ second)
    (hFD : first < b.sudo_5Board_4held.size)
    (hFH : first < b.sudo_5Board_4home.size)
    (hHeld : b.sudo_5Board_4held[first] = true)
    (hArr : b.sudo_5Board_4home[first] = embed xs0) :
    CellKeep (mulNoLiveBoard b dst second xs ys n k moves slides hole bench peak peakS cOps
      hH hD hops) first xs0 := by
  let bM := mulNoLiveBoard b dst second xs ys n k moves slides hole bench peak peakS cOps hH hD hops
  have hHeldM := mul_live_held b dst second xs ys n k moves slides hole bench peak peakS cOps hH hD hops
  have hS := settle_held_eq b second hH hD ys n moves slides peak
  have hHomeM := mul_live_home b dst second xs ys n k moves slides hole bench peak peakS cOps hH hD hops
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
        (settleBoard b second hH hD ys n moves slides peak).sudo_5Board_4held.size := by
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

private theorem mul_live_aimed (b : Ecbs.Board) (dst second : Nat) (xs ys : List Nat)
    (n k moves slides hole bench peak peakS cOps : Nat)
    (hH : second < b.sudo_5Board_4home.size) (hD : second < b.sudo_5Board_4held.size)
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size) :
    (mulNoLiveBoard b dst second xs ys n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_8bench_on =
        true ∧
      (mulNoLiveBoard b dst second xs ys n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_8bench_to =
        (dst : Int) := by
  unfold mulNoLiveBoard
  refine ⟨?_, ?_⟩
  · simpa using
      mul_no_on (settleBoard b second hH hD ys n moves slides peak) dst second xs (ys.take n)
        n k (moves + 2 * pegCount (ys.take n)) hole bench
        (raisedPeak peak (countHeld (b.sudo_5Board_4held.set ⟨second, hD⟩ true) 7)) peakS cOps
        (settle_ops_lt b 0 second hops hH hD ys n moves slides peak)
        (settle_held_lt b second hH hD ys n moves slides peak)
        (settle_home_lt b second hH hD ys n moves slides peak)
  · simpa using
      mul_no_to (settleBoard b second hH hD ys n moves slides peak) dst second xs (ys.take n)
        n k (moves + 2 * pegCount (ys.take n)) hole bench
        (raisedPeak peak (countHeld (b.sudo_5Board_4held.set ⟨second, hD⟩ true) 7)) peakS cOps
        (settle_ops_lt b 0 second hops hH hD ys n moves slides peak)
        (settle_held_lt b second hH hD ys n moves slides peak)
        (settle_home_lt b second hH hD ys n moves slides peak)

theorem mulMovesNo_bound (moves n k bench : Nat) (xs ys : List Nat)
    (hn : n ≤ bench) :
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

private theorem mul_live_hole (b : Ecbs.Board) (dst second : Nat) (xs ys : List Nat)
    (n k moves slides hole bench peak peakS cOps : Nat)
    (hH : second < b.sudo_5Board_4home.size) (hD : second < b.sudo_5Board_4held.size)
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size) :
    (mulNoLiveBoard b dst second xs ys n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      Int.ofNat (raisedHole hole (topIdx
        (school n xs (ys.take n) (List.replicate bench 0) false))) := by
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
      Ecbs.clear bMul ((5 : Nat) : Int) = .ok bClear := by
  obtain ⟨c, bLoop, ys, moves, slides, hole, peak, peakS, cMul, hH, hD, hops,
      _hcopy, _hsrc, _hg, hmEq, hn, _hkN, hbch, _hpeg, _hys, hGap, _hX, _hFit, hMov,
      _hSFit, _hSLe,       _hOp, _hRow, _htier, _hmk, _h7, _hop0, _hOpsLe,       _hctrl0, _hhigh0, _hcontrol, _hlen0, _hmax0, _ht0, hmul⟩ :=
    mul_of_shape h hm hT hhome
  let bMul := mulNoLiveBoard bLoop 5 6 c.g ys c.n c.k moves slides hole c.bench
    peak peakS cMul hH hD hops
  have hKeep := mulLive_keep bLoop 5 6 5 c.g ys c.n c.k moves slides hole c.bench
    peak peakS cMul c.g hH hD hops (by decide) hGap.heldLt hGap.homeLt hGap.held hGap.arr
  let mvC := mulMovesNo (moves + 2 * pegCount (ys.take c.n)) c.g (ys.take c.n)
    c.n c.k c.bench
  have hmvC : bMul.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mvC := by
    simpa [bMul, mvC] using
      mul_live_moves bLoop 5 6 c.g ys c.n c.k moves slides hole c.bench peak peakS cMul
        hH hD hops
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
  exact ⟨bLoop, bMul, _, hmul, hclear⟩

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

private theorem replicate_trits (k : Nat) : allTritList (List.replicate k 0) := by
  intro x hx
  simp [List.mem_replicate] at hx
  rcases hx with ⟨_, rfl⟩
  decide

/-- `clear` writes one home. A different home, and the array it holds, stay. -/
private theorem clearCell_keep (b : Ecbs.Board) (home first : Nat) (xs : List Nat)
    (moves : Nat) (xs0 : List Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (hne : home ≠ first) (hk : CellKeep b first xs0) :
    CellKeep (clearHeldBoard b home xs moves hH hD) first xs0 := by
  let bC := clearHeldBoard b home xs moves hH hD
  have hHeldEq : bC.sudo_5Board_4held = b.sudo_5Board_4held.set ⟨home, hD⟩ false := by
    simp [bC, clearHeldBoard]
  have hHomeEq : bC.sudo_5Board_4home = b.sudo_5Board_4home.set ⟨home, hH⟩ #[] := by
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
private theorem cubeLive_keep (b : Ecbs.Board) (dst src first : Nat) (xs : List Nat)
    (n k moves slides hole bench peak peakS cOps : Nat) (xs0 : List Nat)
    (hH : src < b.sudo_5Board_4home.size) (hD : src < b.sudo_5Board_4held.size)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hne : first ≠ src)
    (hFD : first < b.sudo_5Board_4held.size)
    (hFH : first < b.sudo_5Board_4home.size)
    (hHeld : b.sudo_5Board_4held[first] = true)
    (hArr : b.sudo_5Board_4home[first] = embed xs0) :
    CellKeep (cubeLiveBoard b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops)
      first xs0 := by
  let bC := cubeLiveBoard b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops
  have hHeldC := cube_live_held b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops
  have hS := settle_held_eq b src hH hD xs n moves slides peak
  have hHomeC := cube_live_home b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops
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
        (settleBoard b src hH hD xs n moves slides peak).sudo_5Board_4held.size := by
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
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (n moves slides peak : Nat) :
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_4cost.sudo_5Costs_9tally_max =
      b.sudo_5Board_4cost.sudo_5Costs_9tally_max := by
  unfold settleBoard
  split <;> rfl

private theorem cubeLive_tmax (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (n k moves slides hole bench peak peakS cOps : Nat)
    (hH : src < b.sudo_5Board_4home.size) (hD : src < b.sudo_5Board_4held.size)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size) :
    (cubeLiveBoard b dst src xs n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_4cost.sudo_5Costs_9tally_max =
      b.sudo_5Board_4cost.sudo_5Costs_9tally_max := by
  unfold cubeLiveBoard
  rw [cubeOff_tmax, settle_tmax]

private theorem pegPack_tmax (c : PegCtx) (i : Nat) (h0 : 0 < i) (hle : i ≤ c.m) :
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
    rw [pegStep_tmax, cubeLive_tmax]
    exact ih

private theorem place_tmax (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat) :
    (placeBoard b home hH hD xs moves peak).sudo_5Board_4cost.sudo_5Costs_9tally_max =
      b.sudo_5Board_4cost.sudo_5Costs_9tally_max := by
  unfold placeBoard
  dsimp only
  split <;> rfl

private theorem mulLive_tmax (b : Ecbs.Board) (dst second : Nat) (xs ys : List Nat)
    (n k moves slides hole bench peak peakS cOps : Nat)
    (hH : second < b.sudo_5Board_4home.size) (hD : second < b.sudo_5Board_4held.size)
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size) :
    (mulNoLiveBoard b dst second xs ys n k moves slides hole bench peak peakS cOps hH hD hops).sudo_5Board_4cost.sudo_5Costs_9tally_max =
      b.sudo_5Board_4cost.sudo_5Costs_9tally_max := by
  unfold mulNoLiveBoard mulNoOffBoard
  rw [settle_tmax]

private theorem clear_tmax (b : Ecbs.Board) (home : Nat) (xs : List Nat) (moves : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size) :
    (clearHeldBoard b home xs moves hH hD).sudo_5Board_4cost.sudo_5Costs_9tally_max =
      b.sudo_5Board_4cost.sudo_5Costs_9tally_max := rfl

set_option maxHeartbeats 1000000 in
/-- Final rung. After the gap mul and the clear, the emitter cubes that product
    onto the spare and multiplies the cube by the held input. This rung does not
    double the tally. Both results are the named live boards, and the same live
    results hold for any board that agrees on the fields the cube and the mul
    read: replacing the row, tally length, control counter, recorded high, and
    `tally_max` copies those fields onto the result. The input's length and trits
    are the per-call reads of that mul; `ClimbInvK` does not store them. Moves
    and slides stay within one `rungCharge` of this rung. -/
theorem red_cube_mul {done rest : List Nat} {r : Nat} {b : Ecbs.Board}
    {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvK done (r :: rest) b s base)
    (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax)
    (hhome : s.onBench = false)
    (hxLen : base.x.length = base.n) (hxT : allTritList base.x) :
    ∃ (bLoop bMul bClear bCube bRed : Ecbs.Board),
      Ecbs.mul bLoop ((5 : Nat) : Int) ((5 : Nat) : Int) ((6 : Nat) : Int)
          false false false = .ok bMul ∧
      Ecbs.clear bMul ((5 : Nat) : Int) = .ok bClear ∧
      Ecbs.cube bClear ((6 : Nat) : Int) ((5 : Nat) : Int) = .ok bCube ∧
      Ecbs.mul bCube ((5 : Nat) : Int) (base.xHome : Int) ((6 : Nat) : Int)
          false false false = .ok bRed ∧
      (∃ (mv sl : Nat),
        bRed.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int) ∧
        bRed.sudo_5Board_4cost.sudo_5Costs_6slides = (sl : Int) ∧
        mv ≤ base.moves0 + (done.length + 1) * rungCharge base.n base.bench base.mMax ∧
        sl ≤ base.slides0 + (done.length + 1) * rungSlideCharge base.n base.mMax) ∧
      bClear.sudo_5Board_9tally_len = (s.tally : Int) ∧
      bClear.sudo_5Board_6tally0 = (s.t0 : Int) ∧
      bClear.sudo_5Board_3row = embed (paintRed s.row s.t0 s.tally) ∧
      bClear.sudo_5Board_1t.sudo_4Tier_7control = (base.control : Int) ∧
      bClear.sudo_5Board_4cost.sudo_5Costs_15control_highest = (s.high : Int) ∧
      bClear.sudo_5Board_4cost.sudo_5Costs_4ctrl = ((s.ctrl + s.tally : Nat) : Int) ∧
      bClear.sudo_5Board_4cost.sudo_5Costs_9tally_max =
        b.sudo_5Board_4cost.sudo_5Costs_9tally_max ∧
      bCube.sudo_5Board_6tally0 = (s.t0 : Int) ∧
      bRed.sudo_5Board_6tally0 = (s.t0 : Int) ∧
      bCube.sudo_5Board_1t = bClear.sudo_5Board_1t ∧
      bRed.sudo_5Board_1t = bClear.sudo_5Board_1t ∧
      (∀ (row : Array Int) (len ctrl high tmax : Int),
        Ecbs.cube (withTally bClear row len ctrl high tmax)
            ((6 : Nat) : Int) ((5 : Nat) : Int) =
          .ok (withTally bCube row len ctrl high tmax)) ∧
      (∀ (row : Array Int) (len ctrl high tmax : Int),
        Ecbs.mul (withTally bCube row len ctrl high tmax)
            ((5 : Nat) : Int) (base.xHome : Int) ((6 : Nat) : Int)
            false false false =
          .ok (withTally bRed row len ctrl high tmax)) := by
  obtain ⟨c, bLoop, ys, moves, slides, hole, peak, peakS, cMul, hH, hD, hops,
      _hcopy, _hsrc, _hg, hmEq, hn, _hkN, hbch, hpegB, _hys, hGap, hX, _hFit, hMov,
      _hSFit, hSLe, hOp, hRow, htier, _hmk, h7, _hop0, hOpsLe, hctrl0, hhighS,
      hcontrol, hlen0, hmax0, ht0, hmulG⟩ :=
    mul_of_shape h hm hT hhome
  let bMul := mulNoLiveBoard bLoop 5 6 c.g ys c.n c.k moves slides hole c.bench
    peak peakS cMul hH hD hops
  have hKeep := mulLive_keep bLoop 5 6 5 c.g ys c.n c.k moves slides hole c.bench
    peak peakS cMul c.g hH hD hops (by decide) hGap.heldLt hGap.homeLt hGap.held hGap.arr
  have hXMul := mulLive_keep bLoop 5 6 base.xHome c.g ys c.n c.k moves slides hole c.bench
    peak peakS cMul base.x hH hD hops h.shape.xNe6 hX.heldLt hX.homeLt hX.held hX.arr
  let mvC := mulMovesNo (moves + 2 * pegCount (ys.take c.n)) c.g (ys.take c.n)
    c.n c.k c.bench
  have hmvC : bMul.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mvC := by
    simpa [bMul, mvC] using
      mul_live_moves bLoop 5 6 c.g ys c.n c.k moves slides hole c.bench peak peakS cMul
        hH hD hops
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
  have hcn : c.n = base.n := hn.trans h.hn
  have hcb : c.bench = base.bench := hbch.trans h.hbench
  have hk : done.length + 1 ≤ base.R := by
    have hlen := h.kLe
    rw [List.length_append, List.length_cons] at hlen
    omega
  let L := laneFold c.n (c.n - c.k)
    (school c.n c.g (ys.take c.n) (List.replicate c.bench 0) false)
  have hschLen : (school c.n c.g (ys.take c.n) (List.replicate c.bench 0) false).length =
      c.bench := by
    simpa [List.length_replicate] using
      school_length c.g (ys.take c.n) (List.replicate c.bench 0) false c.n
  have hlenL : L.length = c.bench := by
    simpa [L, hschLen] using
      laneFold_length c.n (c.n - c.k)
        (school c.n c.g (ys.take c.n) (List.replicate c.bench 0) false)
        (by rw [hschLen]; exact c.n_le)
  have hzeroL : ∀ i, c.n ≤ i → ∀ hi : i < L.length, L[i] = 0 := by
    intro i hlo hi
    have hcoeff := mul_no_high c.g (ys.take c.n) c.n c.k c.bench c.hn0 c.gap_pos i hlo
      (hlenL ▸ hi)
    exact (coeff_eq_get L i hi).symm.trans hcoeff
  have hposL : 0 < L.length := by
    rw [hlenL]; exact Nat.lt_of_lt_of_le c.hn0 c.n_le
  have hnleL : c.n ≤ L.length := by rw [hlenL]; exact c.n_le
  have hfitL : FitsLen L.length := by rw [hlenL]; exact c.hfitB
  have htriL : allTritList (L.take c.n) := by
    have hrep : allTritList (List.replicate c.bench 0) := replicate_trits c.bench
    have hwide : ∀ i, i < c.n → i + (c.n - 1) < (List.replicate c.bench 0).length := by
      intro i hi
      rw [List.length_replicate]
      have h2 : 2 * (c.n - 1) < c.bench := by
        have hs := c.hspan
        omega
      omega
    have hschT := school_trits c.g (ys.take c.n) (List.replicate c.bench 0) false c.n hrep hwide
    have hfoldT := laneFold_trits c.n (c.n - c.k)
      (school c.n c.g (ys.take c.n) (List.replicate c.bench 0) false)
      hschT (Nat.sub_le _ _) (by rw [hschLen]; exact c.n_le)
    exact allTritList_take hfoldT c.n
  let pegL := pegCount (L.take c.n)
  have hpegL : 2 * pegL ≤ 2 * c.n := by
    have hp := pegCount_take_le L c.n
    simp only [pegL] at hp
    omega
  have hcubeLe : 2 * pegL + 2 * c.n + 3 * (c.bench - c.n) ≤ pegCharge c.n c.bench := by
    unfold pegCharge
    omega
  have hpegY : 2 * pegCount (ys.take c.n) ≤ 2 * c.n := by
    have hp := pegCount_take_le ys c.n
    omega
  have hMovN : moves ≤ base.moves0 + done.length * rungCharge base.n base.bench base.mMax +
      base.n + s.tally * pegCharge base.n base.bench := hMov
  have hSLeN : slides ≤ base.slides0 + done.length * rungSlideCharge base.n base.mMax +
      s.tally * (2 * base.n) := hSLe
  have hmvN : mvC ≤ moves + mulCharge base.n base.bench := by
    rw [← show mulCharge c.n c.bench = mulCharge base.n base.bench by rw [hcn, hcb]]
    exact hmvC_le
  have hpegBase : pegCount c.g ≤ base.n := by rw [← hcn]; exact hpegN
  have hcubeBase : 2 * pegL + 2 * base.n + 3 * (base.bench - base.n) ≤
      pegCharge base.n base.bench := by
    rw [← hcn, ← hcb]; exact hcubeLe
  have hRedU := redMulBudget base.moves0 done.length base.n base.bench base.mMax s.tally
    moves mvC (pegCount c.g) pegL hT hMovN hmvN hpegBase hcubeBase
  have hSlideU := redSlideBudget base.slides0 done.length base.n base.mMax s.tally
    slides (pegCount (ys.take c.n)) pegL 0 hT hSLeN
    (by rw [← hcn]; exact hpegY) (by rw [← hcn]; exact hpegL) (by omega : 2 * 0 ≤ 2 * base.n)
  let movesC := mvC + pegCount c.g
  let slidesC := slides + 2 * pegCount (ys.take c.n)
  let bSettle := settleBoard bLoop 6 hH hD ys c.n moves slides peak
  let peakC := raisedPeak
    (raisedPeak peak (countHeld (bLoop.sudo_5Board_4held.set ⟨6, hD⟩ true) 7))
    (countHeld (bSettle.sudo_5Board_4held.set
      ⟨6, settle_held_lt bLoop 6 hH hD ys c.n moves slides peak⟩ false) 7)
  let holeC := raisedHole hole
    (topIdx (school c.n c.g (ys.take c.n) (List.replicate c.bench 0) false))
  let peakSC := raisedPeak peakS (countHeld bSettle.sudo_5Board_4held 7)
  have hpeakM : bMul.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peakC := by
    simpa [bMul, peakC, bSettle] using
      mul_live_peak bLoop 5 6 c.g ys c.n c.k moves slides hole c.bench peak peakS cMul hH hD hops
  have hslidesM : bMul.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slidesC := by
    simpa [bMul, slidesC] using
      mul_live_slides bLoop 5 6 c.g ys c.n c.k moves slides hole c.bench peak peakS cMul hH hD hops
  have hholeM : bMul.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat holeC := by
    simpa [bMul, holeC] using
      mul_live_hole bLoop 5 6 c.g ys c.n c.k moves slides hole c.bench peak peakS cMul hH hD hops
  have hstrictM : bMul.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat peakSC := by
    simpa [bMul, peakSC, bSettle] using
      mul_live_strict bLoop 5 6 c.g ys c.n c.k moves slides hole c.bench peak peakS cMul hH hD hops
  have hbenchM : bMul.sudo_5Board_5bench = embed L := by
    simpa [bMul, L] using
      mul_live_bench bLoop 5 6 c.g ys c.n c.k moves slides hole c.bench peak peakS cMul hH hD hops
  have hmkM : bMul.sudo_5Board_9marker_on = false := by
    simpa [bMul] using
      mul_live_marker bLoop 5 6 c.g ys c.n c.k moves slides hole c.bench peak peakS cMul hH hD hops
  have haim := mul_live_aimed bLoop 5 6 c.g ys c.n c.k moves slides hole c.bench
    peak peakS cMul hH hD hops
  have htierM : bMul.sudo_5Board_1t = bLoop.sudo_5Board_1t := by
    simpa [bMul] using
      mul_live_tier bLoop 5 6 c.g ys c.n c.k moves slides hole c.bench peak peakS cMul hH hD hops
  have hbudget : mvC + pegCount c.g ≤
      base.moves0 + base.R * rungCharge base.n base.bench base.mMax := by
    have hsmall : mvC + pegCount c.g ≤
        mvC + pegCount c.g + 2 * pegL + 2 * base.n + 3 * (base.bench - base.n) +
          mulCharge base.n base.bench := by
      omega
    exact Nat.le_trans hsmall
      (Nat.le_trans hRedU (Nat.add_le_add_left (Nat.mul_le_mul_right _ hk) _))
  have hfitC : FitsLen (mvC + pegCount c.g) := FitsLen.of_le base.fitM hbudget
  have hclear := clear_held_refines bMul 5 c.g mvC hKeep.homeLt hKeep.heldLt
    hKeep.held hKeep.arr hmvC hfitN hfitC
  let bClear := clearHeldBoard bMul 5 c.g mvC hKeep.homeLt hKeep.heldLt
  have hclearEq : Ecbs.clear bMul ((5 : Nat) : Int) = .ok bClear := by
    simpa [bClear, clearHeldBoard] using hclear
  have hXClear : CellKeep bClear base.xHome base.x :=
    clearCell_keep bMul 5 base.xHome c.g mvC base.x hKeep.homeLt hKeep.heldLt
      (Ne.symm h.shape.xNe5) hXMul
  have hH5 : 5 < bClear.sudo_5Board_4home.size := by
    simp [bClear, clearHeldBoard, Array.size_set]
    exact hKeep.homeLt
  have hD5 : 5 < bClear.sudo_5Board_4held.size := by
    simp [bClear, clearHeldBoard, Array.size_set]
    exact hKeep.heldLt
  have hemptyC : bClear.sudo_5Board_4held[5]'hD5 = false := by
    have hEq : bClear.sudo_5Board_4held =
        bMul.sudo_5Board_4held.set ⟨5, hKeep.heldLt⟩ false := by
      simp [bClear, clearHeldBoard]
    rw [show bClear.sudo_5Board_4held[5] =
        (bMul.sudo_5Board_4held.set ⟨5, hKeep.heldLt⟩ false)[5]'(hEq ▸ hD5) from
      idx_get hEq 5 hD5]
    simp [Array.getElem_set]
  have h7C : 7 ≤ bClear.sudo_5Board_4held.size := by
    have hszC : bClear.sudo_5Board_4held.size = bMul.sudo_5Board_4held.size := by
      simp [bClear, clearHeldBoard, Array.size_set]
    rw [hszC]
    have hHeld := mul_live_held bLoop 5 6 c.g ys c.n c.k moves slides hole c.bench
      peak peakS cMul hH hD hops
    have hS := settle_held_eq bLoop 6 hH hD ys c.n moves slides peak
    have hsz : bMul.sudo_5Board_4held.size = bLoop.sudo_5Board_4held.size := by
      rw [hHeld]
      simp only [Array.size_set]
      rw [hS]
      simp only [Array.size_set]
    rw [hsz]
    exact h7
  have hmkC : bClear.sudo_5Board_9marker_on = false := by
    simp [bClear, clearHeldBoard, hmkM]
  have honC : bClear.sudo_5Board_8bench_on = true := by
    simp [bClear, clearHeldBoard]
    exact haim.1
  have htoC : bClear.sudo_5Board_8bench_to = (5 : Int) := by
    simp [bClear, clearHeldBoard]
    exact haim.2
  have hbenchC : bClear.sudo_5Board_5bench = embed L := by
    simp [bClear, clearHeldBoard, hbenchM]
  have hmovesC : bClear.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat movesC := by
    simp [bClear, clearHeldBoard, movesC]
  have hslidesC : bClear.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slidesC := by
    simp [bClear, clearHeldBoard, hslidesM]
  have hpeakC : bClear.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peakC := by
    simp [bClear, clearHeldBoard, hpeakM]
  have hholeC : bClear.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat holeC := by
    simp [bClear, clearHeldBoard, hholeM]
  have hstrictC : bClear.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakSC : Int) := by
    simpa [bClear, clearHeldBoard, ofNat_eq_natCast] using hstrictM
  have htierC : bClear.sudo_5Board_1t = c.b0.sudo_5Board_1t := by
    have h1 : bClear.sudo_5Board_1t = bMul.sudo_5Board_1t := by
      simp [bClear, clearHeldBoard]
    rw [h1, htierM, htier]
  have hnC : bClear.sudo_5Board_1t.sudo_4Tier_1n = (c.n : Int) := by rw [htierC]; exact c.hn
  have hblC : bClear.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat c.bench := by
    rw [htierC]; exact c.hbl
  have hcgC : bClear.sudo_5Board_1t.sudo_4Tier_7combgap = Int.ofNat c.cg := by
    rw [htierC]; exact c.hcg
  have hwC : bClear.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat c.w := by rw [htierC]; exact c.hwF
  have hhC : bClear.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat c.h := by rw [htierC]; exact c.hhF
  have hrC : bClear.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat c.r := by rw [htierC]; exact c.hrF
  have hkC : bClear.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat c.k := by rw [htierC]; exact c.hkF
  obtain ⟨cCube, h1Loop, hop1Loop, hCubeFit⟩ := hOp
  have hMulOps := mul_live_ops bLoop 5 6 c.g ys c.n c.k moves slides hole c.bench
    peak peakS cMul hH hD hops
  have hSettleOps := settle_ops bLoop 6 hH hD ys c.n moves slides peak
  have hop1M : ∀ (h1 : 1 < bMul.sudo_5Board_4cost.sudo_5Costs_3ops.size),
      bMul.sudo_5Board_4cost.sudo_5Costs_3ops[1] = (cCube : Int) := by
    intro h1
    have hget := idx_get hMulOps 1 h1
    rw [hget, Array.getElem_set, if_neg (by decide : (0 : Nat) ≠ 1)]
    have hsz : 1 < (settleBoard bLoop 6 hH hD ys c.n moves slides peak).sudo_5Board_4cost.sudo_5Costs_3ops.size := by
      rw [hSettleOps]; exact h1Loop
    exact (idx_get hSettleOps 1 hsz).trans hop1Loop
  have hOpsEq : bClear.sudo_5Board_4cost.sudo_5Costs_3ops =
      bMul.sudo_5Board_4cost.sudo_5Costs_3ops := by
    simp [bClear, clearHeldBoard]
  have hopsC : 1 < bClear.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    have hsz : bClear.sudo_5Board_4cost.sudo_5Costs_3ops.size =
        bLoop.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
      rw [hOpsEq, hMulOps, Array.size_set, hSettleOps]
    rw [hsz]; exact h1Loop
  have hop1C : bClear.sudo_5Board_4cost.sudo_5Costs_3ops[1]'hopsC = (cCube : Int) :=
    (idx_get hOpsEq 1 hopsC).trans (hop1M _)
  have hUfit : movesC + 2 * pegL + 2 * c.n + 3 * (c.bench - c.n) ≤
      base.moves0 + base.R * rungCharge base.n base.bench base.mMax := by
    have hle : movesC + 2 * pegL + 2 * c.n + 3 * (c.bench - c.n) ≤
        movesC + 2 * pegL + 2 * base.n + 3 * (base.bench - base.n) +
          mulCharge base.n base.bench := by
      rw [hcn, hcb]
      exact Nat.le_add_right _ _
    have hrest : movesC + 2 * pegL + 2 * base.n + 3 * (base.bench - base.n) +
        mulCharge base.n base.bench ≤
        base.moves0 + (done.length + 1) * rungCharge base.n base.bench base.mMax := by
      simpa [movesC] using hRedU
    exact Nat.le_trans hle (Nat.le_trans hrest
      (Nat.add_le_add_left (Nat.mul_le_mul_right _ hk) _))
  have hfoldC : FitsLen (movesC + 2 * pegL + 2 * c.n + 3 * (c.bench - c.n)) :=
    FitsLen.of_le base.fitM (by simpa [pegL] using hUfit)
  have hfmC : FitsLen (movesC + 2 * pegL + 2 * c.n) := FitsLen.of_le hfoldC (by omega)
  have hfitMC : FitsLen (movesC + 2 * pegL) := FitsLen.of_le hfmC (by omega)
  have hpegF : FitsLen (2 * pegL) := FitsLen.of_le hfitMC (by omega)
  have hslideFit : slidesC + 2 * pegL ≤
      base.slides0 + base.R * rungSlideCharge base.n base.mMax := by
    have h0 : slides + 2 * pegCount (ys.take c.n) + 2 * pegL ≤
        base.slides0 + (done.length + 1) * rungSlideCharge base.n base.mMax := by
      simpa [Nat.mul_zero, Nat.add_zero] using hSlideU
    have hEq : slidesC + 2 * pegL =
        slides + 2 * pegCount (ys.take c.n) + 2 * pegL := by
      simp [slidesC]
    rw [hEq]
    exact Nat.le_trans h0 (Nat.add_le_add_left (Nat.mul_le_mul_right _ hk) _)
  have hfitSC : FitsLen (slidesC + 2 * pegL) := FitsLen.of_le base.fitS (by
    simpa [pegL] using hslideFit)
  have hcube := cube_eq_live bClear 6 5 L c.w c.h c.r c.n c.k movesC slidesC holeC
    c.bench peakC peakSC cCube c.cg
    hmkC honC htoC hH5 hD5 h7C hemptyC hbenchC
    hnC c.hn0 hposL hnleL hzeroL
    c.hf hfitL hmovesC hslidesC hpeakC
    (by simpa [pegL] using hpegF) (by simpa [pegL] using hfitMC)
    (by simpa [pegL] using hfitSC)
    hopsC hop1C hCubeFit
    hblC hcgC c.hspan htriL c.h3 hfmC
    c.hw0 c.hh0 c.hrR c.hrP c.hnE c.hkLe c.hgap
    hwC hhC hrC hkC
    hholeC hstrictC c.hsm c.hnsm c.hfitB (by simpa [pegL] using hfoldC)
  let bCube := cubeLiveBoard bClear 6 5 L c.n c.k movesC slidesC holeC c.bench
    peakC peakSC cCube hH5 hD5 hopsC
  have hcubeEq : Ecbs.cube bClear ((6 : Nat) : Int) ((5 : Nat) : Int) = .ok bCube := by
    simpa [bCube] using hcube
  let mvCube := cubeMoves (movesC + 2 * pegL) (L.take c.n) c.n c.k c.bench
  have hmvCube : bCube.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mvCube := by
    rw [show bCube = cubeLiveBoard bClear 6 5 L c.n c.k movesC slidesC holeC c.bench
        peakC peakSC cCube hH5 hD5 hopsC from rfl]
    simpa [mvCube, pegL] using
      cube_live_moves bClear 6 5 L c.n c.k movesC slidesC holeC c.bench peakC peakSC cCube
        hH5 hD5 hopsC
  let slidesCube := slidesC + 2 * pegL
  have hslidesCube : bCube.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slidesCube := by
    simpa [bCube, slidesCube, pegL] using
      cube_live_slides bClear 6 5 L c.n c.k movesC slidesC holeC c.bench peakC peakSC cCube
        hH5 hD5 hopsC
  let ysC := laneFold c.n (c.n - c.k) (combStrip c.n c.bench (L.take c.n))
  have hbenchR : bCube.sudo_5Board_5bench = embed ysC := by
    simpa [bCube, ysC] using
      cube_live_bench bClear 6 5 L c.n c.k movesC slidesC holeC c.bench peakC peakSC cCube
        hH5 hD5 hopsC
  have hlenY : ysC.length = c.bench := by
    have hcomb : (combStrip c.n c.bench (L.take c.n)).length = c.bench :=
      combStrip_length c.n c.bench (L.take c.n)
    simpa [ysC, hcomb] using
      laneFold_length c.n (c.n - c.k) (combStrip c.n c.bench (L.take c.n))
        (by rw [hcomb]; exact c.n_le)
  have hzeroY : ∀ i, c.n ≤ i → ∀ hi : i < ysC.length, ysC[i] = 0 := by
    intro i hlo hi
    have hcoeff := cube_live_high L c.n c.k c.bench c.hn0 c.gap_pos i hlo (hlenY ▸ hi)
    exact (coeff_eq_get ysC i hi).symm.trans hcoeff
  have hposY : 0 < ysC.length := by
    rw [hlenY]; exact Nat.lt_of_lt_of_le c.hn0 c.n_le
  have hnleY : c.n ≤ ysC.length := by rw [hlenY]; exact c.n_le
  have hfitY : FitsLen ysC.length := by rw [hlenY]; exact c.hfitB
  have htriY : allTritList (ysC.take c.n) := by
    have hcomb := combStrip_trits (L.take c.n) c.n c.bench htriL c.span3
    have hlenC : (combStrip c.n c.bench (L.take c.n)).length = c.bench :=
      combStrip_length c.n c.bench (L.take c.n)
    have hfold := laneFold_trits c.n (c.n - c.k) (combStrip c.n c.bench (L.take c.n))
      hcomb (Nat.sub_le _ _) (by rw [hlenC]; exact c.n_le)
    simpa [ysC] using allTritList_take hfold c.n
  let bSCube := settleBoard bClear 5 hH5 hD5 L c.n movesC slidesC peakC
  let peakCube := raisedPeak
    (raisedPeak peakC (countHeld (bClear.sudo_5Board_4held.set ⟨5, hD5⟩ true) 7))
    (countHeld (bSCube.sudo_5Board_4held.set
      ⟨5, settle_held_lt bClear 5 hH5 hD5 L c.n movesC slidesC peakC⟩ false) 7)
  let peakSRed := raisedPeak peakSC (countHeld bSCube.sudo_5Board_4held 7)
  let holeRed := raisedHole holeC (topIdx (combStrip c.n c.bench (L.take c.n)))
  have hpeakR : bCube.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peakCube := by
    simpa [bCube, peakCube, bSCube] using
      cube_live_peak bClear 6 5 L c.n c.k movesC slidesC holeC c.bench peakC peakSC cCube
        hH5 hD5 hopsC
  have hstrictR : bCube.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakSRed : Int) := by
    simpa [bCube, peakSRed, bSCube, ofNat_eq_natCast] using
      cube_live_strict bClear 6 5 L c.n c.k movesC slidesC holeC c.bench peakC peakSC cCube
        hH5 hD5 hopsC
  have hholeR : bCube.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat holeRed := by
    simpa [bCube, holeRed] using
      cube_live_hole bClear 6 5 L c.n c.k movesC slidesC holeC c.bench peakC peakSC cCube
        hH5 hD5 hopsC
  have hmkR : bCube.sudo_5Board_9marker_on = false := by
    simpa [bCube] using
      cube_live_marker bClear 6 5 L c.n c.k movesC slidesC holeC c.bench peakC peakSC cCube
        hH5 hD5 hopsC
  have honR : bCube.sudo_5Board_8bench_on = true := by
    simpa [bCube] using
      cube_live_on bClear 6 5 L c.n c.k movesC slidesC holeC c.bench peakC peakSC cCube
        hH5 hD5 hopsC
  have htoR : bCube.sudo_5Board_8bench_to = (6 : Int) := by
    simpa [bCube] using
      cube_live_to bClear 6 5 L c.n c.k movesC slidesC holeC c.bench peakC peakSC cCube
        hH5 hD5 hopsC
  have htierR : bCube.sudo_5Board_1t = bClear.sudo_5Board_1t := by
    simpa [bCube] using
      cube_live_tier bClear 6 5 L c.n c.k movesC slidesC holeC c.bench peakC peakSC cCube
        hH5 hD5 hopsC
  have hXCube : CellKeep bCube base.xHome base.x :=
    cubeLive_keep bClear 6 5 base.xHome L c.n c.k movesC slidesC holeC c.bench
      peakC peakSC cCube base.x hH5 hD5 hopsC h.shape.xNe5
      hXClear.heldLt hXClear.homeLt hXClear.held hXClear.arr
  have hH6C : 6 < bClear.sudo_5Board_4home.size := by
    have hHomeM := mul_live_home bLoop 5 6 c.g ys c.n c.k moves slides hole c.bench
      peak peakS cMul hH hD hops
    have hszM : bMul.sudo_5Board_4home.size = bLoop.sudo_5Board_4home.size := by
      rw [hHomeM, Array.size_set]
    have hszC : bClear.sudo_5Board_4home.size = bMul.sudo_5Board_4home.size := by
      simp [bClear, clearHeldBoard, Array.size_set]
    rw [hszC, hszM]; exact hH
  have hD6C : 6 < bClear.sudo_5Board_4held.size := by
    rw [show bClear.sudo_5Board_4held.size = bMul.sudo_5Board_4held.size by
      simp [bClear, clearHeldBoard, Array.size_set]]
    have hHeld := mul_live_held bLoop 5 6 c.g ys c.n c.k moves slides hole c.bench
      peak peakS cMul hH hD hops
    have hS := settle_held_eq bLoop 6 hH hD ys c.n moves slides peak
    have hsz : bMul.sudo_5Board_4held.size = bLoop.sudo_5Board_4held.size := by
      rw [hHeld]; simp only [Array.size_set]; rw [hS]; simp only [Array.size_set]
    rw [hsz]; exact hD
  have hempty6C : bClear.sudo_5Board_4held[6]'hD6C = false := by
    have hHeld := mul_live_held bLoop 5 6 c.g ys c.n c.k moves slides hole c.bench
      peak peakS cMul hH hD hops
    have h6M : 6 < bMul.sudo_5Board_4held.size := by
      rw [show bClear.sudo_5Board_4held.size = bMul.sudo_5Board_4held.size by
        simp [bClear, clearHeldBoard, Array.size_set]] at hD6C
      exact hD6C
    have hget := idx_get hHeld 6 h6M
    have hfalse : bMul.sudo_5Board_4held[6] = false := by
      rw [hget, Array.getElem_set, if_pos rfl]
    have hEq : bClear.sudo_5Board_4held =
        bMul.sudo_5Board_4held.set ⟨5, hKeep.heldLt⟩ false := by
      simp [bClear, clearHeldBoard]
    rw [show bClear.sudo_5Board_4held[6] =
        (bMul.sudo_5Board_4held.set ⟨5, hKeep.heldLt⟩ false)[6]'(hEq ▸ hD6C) from
      idx_get hEq 6 hD6C]
    rw [Array.getElem_set, if_neg (by decide : (5 : Nat) ≠ 6)]
    exact hfalse
  have hH6R : 6 < bCube.sudo_5Board_4home.size := by
    rw [show bCube.sudo_5Board_4home =
        bClear.sudo_5Board_4home.set ⟨5, hH5⟩ #[] by
      simpa [bCube] using
        cube_live_home bClear 6 5 L c.n c.k movesC slidesC holeC c.bench peakC peakSC cCube
          hH5 hD5 hopsC]
    simp [Array.size_set]
    exact hH6C
  have hD6R : 6 < bCube.sudo_5Board_4held.size := by
    have hHeld := cube_live_held bClear 6 5 L c.n c.k movesC slidesC holeC c.bench
      peakC peakSC cCube hH5 hD5 hopsC
    have hsz : bCube.sudo_5Board_4held.size = bClear.sudo_5Board_4held.size := by
      rw [hHeld]
      simp only [Array.size_set]
      rw [settle_held_eq bClear 5 hH5 hD5 L c.n movesC slidesC peakC]
      simp only [Array.size_set]
    rw [hsz]; exact hD6C
  have hother6 := cube_live_held_other bClear bCube 6 5 6 L c.n c.k movesC slidesC holeC c.bench
      peakC peakSC cCube hH5 hD5 hopsC rfl (by decide) hD6C hD6R
  have hempty6R := hother6.trans hempty6C
  have h7R : 7 ≤ bCube.sudo_5Board_4held.size := by
    have hHeld := cube_live_held bClear 6 5 L c.n c.k movesC slidesC holeC c.bench
      peakC peakSC cCube hH5 hD5 hopsC
    have hsz : bCube.sudo_5Board_4held.size = bClear.sudo_5Board_4held.size := by
      rw [hHeld]
      simp only [Array.size_set]
      rw [settle_held_eq bClear 5 hH5 hD5 L c.n movesC slidesC peakC]
      simp only [Array.size_set]
    rw [hsz]
    exact h7C
  have hCubeOps := cube_live_ops bClear 6 5 L c.n c.k movesC slidesC holeC c.bench
    peakC peakSC cCube hH5 hD5 hopsC
  have hops0R : 0 < bCube.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [hCubeOps, Array.size_set]
    exact Nat.lt_trans (by decide : (0 : Nat) < 1) hopsC
  have h0C : 0 < bClear.sudo_5Board_4cost.sudo_5Costs_3ops.size :=
    Nat.lt_trans (by decide : (0 : Nat) < 1) hopsC
  have hopMul : ∀ (h0 : 0 < bMul.sudo_5Board_4cost.sudo_5Costs_3ops.size),
      bMul.sudo_5Board_4cost.sudo_5Costs_3ops[0] = ((cMul + 1 : Nat) : Int) := by
    intro h0
    have hg := idx_get hMulOps 0 h0
    rw [hg, Array.getElem_set]
    simp [ofNat_eq_natCast]
  have hopClear := (idx_get hOpsEq 0 h0C).trans (hopMul _)
  have hop0FromCube := cube_live_op0 bClear bCube 6 5 L c.n c.k movesC slidesC holeC c.bench
    peakC peakSC cCube hH5 hD5 hopsC rfl hops0R
  have hop0R := hop0FromCube.trans hopClear
  have hfopsR : FitsLen ((cMul + 1) + 1) := by
    apply FitsLen.of_le base.fitO
    have hstep : cMul + 2 ≤ base.ops0 + (done.length + 1) * (base.mMax + 3) := by
      have hsucc : (done.length + 1) * (base.mMax + 3) =
          done.length * (base.mMax + 3) + (base.mMax + 3) := by rw [Nat.succ_mul]
      omega
    have hR : (done.length + 1) * (base.mMax + 3) ≤ base.R * (base.mMax + 3) :=
      Nat.mul_le_mul_right _ hk
    omega
  let pegY := pegCount (ysC.take c.n)
  have hpegZ : 2 * pegY ≤ 2 * c.n := by
    have hp := pegCount_take_le ysC c.n
    simp only [pegY] at hp
    omega
  have hmvCubeLe : mvCube ≤ movesC + 2 * pegL + 2 * c.n + 3 * (c.bench - c.n) := by
    have hle := cubeMoves_le (movesC + 2 * pegL) (L.take c.n) c.n c.k c.bench
    simpa [mvCube, Nat.add_assoc] using hle
  have hRedFit : mvCube + 2 * pegY + c.n * (c.n + 1) + 3 * (c.bench - c.n) ≤
      base.moves0 + base.R * rungCharge base.n base.bench base.mMax := by
    have hmulLe : 2 * pegY + c.n * (c.n + 1) + 3 * (c.bench - c.n) ≤ mulCharge c.n c.bench := by
      unfold mulCharge
      omega
    have hsum : mvCube + 2 * pegY + c.n * (c.n + 1) + 3 * (c.bench - c.n) ≤
        movesC + 2 * pegL + 2 * c.n + 3 * (c.bench - c.n) + mulCharge c.n c.bench := by
      omega
    have hU : movesC + 2 * pegL + 2 * c.n + 3 * (c.bench - c.n) + mulCharge c.n c.bench ≤
        base.moves0 + (done.length + 1) * rungCharge base.n base.bench base.mMax := by
      rw [hcn, hcb]
      simpa [movesC] using hRedU
    exact Nat.le_trans hsum (Nat.le_trans hU
      (Nat.add_le_add_left (Nat.mul_le_mul_right _ hk) _))
  have hfoldR : FitsLen (mvCube + 2 * pegY + c.n * (c.n + 1) + 3 * (c.bench - c.n)) :=
    FitsLen.of_le base.fitM hRedFit
  have hfmR : FitsLen (mvCube + 2 * pegY + c.n * (c.n + 1)) :=
    FitsLen.of_le hfoldR (by omega)
  have hfitMR : FitsLen (mvCube + 2 * pegY) := FitsLen.of_le hfmR (by omega)
  have hpegFR : FitsLen (2 * pegY) := FitsLen.of_le hfitMR (by omega)
  have hslideR : slidesCube + 2 * pegY ≤
      base.slides0 + base.R * rungSlideCharge base.n base.mMax := by
    have hZ : 2 * pegY ≤ 2 * base.n := by rw [← hcn]; exact hpegZ
    have hthree := redSlideBudget base.slides0 done.length base.n base.mMax s.tally
      slides (pegCount (ys.take c.n)) pegL pegY hT hSLeN
      (by rw [← hcn]; exact hpegY) (by rw [← hcn]; exact hpegL) hZ
    have hle : slidesCube + 2 * pegY ≤
        slides + 2 * pegCount (ys.take c.n) + 2 * pegL + 2 * pegY := by
      simp [slidesCube]
    exact Nat.le_trans hle (Nat.le_trans hthree
      (Nat.add_le_add_left (Nat.mul_le_mul_right _ hk) _))
  have hfitSR : FitsLen (slidesCube + 2 * pegY) := FitsLen.of_le base.fitS hslideR
  have hlenx : base.x.length = c.n := by rw [hxLen, ← hcn]
  have hspan2 : 2 * (c.n - 1) < c.bench := by
    have hs := c.hspan
    omega
  have hfi : FitsLen (2 * (c.n - 1)) := FitsLen.of_le c.h3 (by omega)
  have hmulR := mul_eq_live bCube 5 base.xHome 6 base.x ysC c.w c.h c.r c.n c.k
    mvCube slidesCube holeRed c.bench peakCube peakSRed (cMul + 1)
    hmkR honR htoR hH6R hD6R h7R hempty6R hbenchR
    (by rw [htierR]; exact hnC) c.hn0 hposY hnleY hzeroY
    c.hf hfitY hmvCube hslidesCube hpeakR
    hpegFR hfitMR hfitSR
    hops0R hop0R hfopsR
    (by rw [htierR]; exact hblC)
    hXCube.heldLt hXCube.homeLt hXCube.held hXCube.arr h.shape.xNe6
    hlenx hspan2 hxT hfi hfmR
    c.hw0 c.hh0 c.hrR c.hrP c.hnE c.hkLe c.hgap
    (by rw [htierR]; exact hwC) (by rw [htierR]; exact hhC)
    (by rw [htierR]; exact hrC) (by rw [htierR]; exact hkC)
    hholeR hstrictR c.hsm c.hnsm c.hfitB hfoldR
  let bRed := mulNoLiveBoard bCube 5 6 base.x ysC c.n c.k mvCube slidesCube holeRed
    c.bench peakCube peakSRed (cMul + 1) hH6R hD6R hops0R
  have hmulEq : Ecbs.mul bCube ((5 : Nat) : Int) (base.xHome : Int) ((6 : Nat) : Int)
      false false false = .ok bRed := by
    simpa [bRed] using hmulR
  let mvRed := mulMovesNo (mvCube + 2 * pegY) base.x (ysC.take c.n) c.n c.k c.bench
  have hmvRed : bRed.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mvRed := by
    simpa [bRed, mvRed, pegY] using
      mul_live_moves bCube 5 6 base.x ysC c.n c.k mvCube slidesCube holeRed c.bench
        peakCube peakSRed (cMul + 1) hH6R hD6R hops0R
  let slRed := slidesCube + 2 * pegY
  have hslRed : bRed.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slRed := by
    simpa [bRed, slRed, pegY] using
      mul_live_slides bCube 5 6 base.x ysC c.n c.k mvCube slidesCube holeRed c.bench
        peakCube peakSRed (cMul + 1) hH6R hD6R hops0R
  have hmvRedLe : mvRed ≤ base.moves0 + (done.length + 1) *
      rungCharge base.n base.bench base.mMax := by
    have hstep := mulMovesNo_bound mvCube c.n c.k c.bench base.x ysC c.n_le
    have hrest : 2 * pegY + c.n * (c.n + 1) + 3 * (c.bench - c.n) ≤ mulCharge c.n c.bench := by
      unfold mulCharge
      simp only [pegY] at hpegZ
      omega
    have h1 : mvRed ≤ mvCube + mulCharge c.n c.bench := by
      simpa [mvRed, pegY] using Nat.le_trans hstep (by omega)
    have h2 : mvCube + mulCharge c.n c.bench ≤
        movesC + 2 * pegL + 2 * c.n + 3 * (c.bench - c.n) + mulCharge c.n c.bench := by
      omega
    have h3 : movesC + 2 * pegL + 2 * c.n + 3 * (c.bench - c.n) + mulCharge c.n c.bench ≤
        base.moves0 + (done.length + 1) * rungCharge base.n base.bench base.mMax := by
      rw [hcn, hcb]
      simpa [movesC] using hRedU
    exact Nat.le_trans h1 (Nat.le_trans h2 h3)
  have hslRedLe : slRed ≤ base.slides0 + (done.length + 1) *
      rungSlideCharge base.n base.mMax := by
    have hZ : 2 * pegY ≤ 2 * base.n := by rw [← hcn]; exact hpegZ
    have hthree := redSlideBudget base.slides0 done.length base.n base.mMax s.tally
      slides (pegCount (ys.take c.n)) pegL pegY hT hSLeN
      (by rw [← hcn]; exact hpegY) (by rw [← hcn]; exact hpegL) hZ
    have hle : slRed ≤ slides + 2 * pegCount (ys.take c.n) + 2 * pegL + 2 * pegY := by
      simp [slRed, slidesCube]
    exact Nat.le_trans hle hthree
  have hcubeAny : ∀ (row : Array Int) (len ctrl high tmax : Int),
      Ecbs.cube (withTally bClear row len ctrl high tmax)
          ((6 : Nat) : Int) ((5 : Nat) : Int) =
        .ok (withTally bCube row len ctrl high tmax) := by
    intro row len ctrl high tmax
    simpa [bCube] using
      cube_eq_live_withTally bClear 6 5 L c.w c.h c.r c.n c.k movesC slidesC holeC
        c.bench peakC peakSC cCube c.cg
        hmkC honC htoC hH5 hD5 h7C hemptyC hbenchC
        hnC c.hn0 hposL hnleL hzeroL
        c.hf hfitL hmovesC hslidesC hpeakC
        (by simpa [pegL] using hpegF) (by simpa [pegL] using hfitMC)
        (by simpa [pegL] using hfitSC)
        hopsC hop1C hCubeFit
        hblC hcgC c.hspan htriL c.h3 hfmC
        c.hw0 c.hh0 c.hrR c.hrP c.hnE c.hkLe c.hgap
        hwC hhC hrC hkC
        hholeC hstrictC c.hsm c.hnsm c.hfitB (by simpa [pegL] using hfoldC)
        row len ctrl high tmax
  have hmulAny : ∀ (row : Array Int) (len ctrl high tmax : Int),
      Ecbs.mul (withTally bCube row len ctrl high tmax)
          ((5 : Nat) : Int) (base.xHome : Int) ((6 : Nat) : Int)
          false false false =
        .ok (withTally bRed row len ctrl high tmax) := by
    intro row len ctrl high tmax
    simpa [bRed] using
      mul_eq_live_withTally bCube 5 base.xHome 6 base.x ysC c.w c.h c.r c.n c.k
        mvCube slidesCube holeRed c.bench peakCube peakSRed (cMul + 1)
        hmkR honR htoR hH6R hD6R h7R hempty6R hbenchR
        (by rw [htierR]; exact hnC) c.hn0 hposY hnleY hzeroY
        c.hf hfitY hmvCube hslidesCube hpeakR
        hpegFR hfitMR hfitSR
        hops0R hop0R hfopsR
        (by rw [htierR]; exact hblC)
        hXCube.heldLt hXCube.homeLt hXCube.held hXCube.arr h.shape.xNe6
        hlenx hspan2 hxT hfi hfmR
        c.hw0 c.hh0 c.hrR c.hrP c.hnE c.hkLe c.hgap
        (by rw [htierR]; exact hwC) (by rw [htierR]; exact hhC)
        (by rw [htierR]; exact hrC) (by rw [htierR]; exact hkC)
        hholeR hstrictR c.hsm c.hnsm c.hfitB hfoldR
        row len ctrl high tmax
  have hbookM := mulLive_book bLoop 5 6 c.g ys c.n c.k moves slides hole c.bench
    peak peakS cMul hH hD hops
  have hbookC := clearHeld_book bMul 5 c.g mvC hKeep.homeLt hKeep.heldLt
  let dp := pegPack c c.m c.hm (Nat.le_refl _)
  have hpb := pegPack_board c c.m c.hm (Nat.le_refl _)
  have hbPack : dp.b = bLoop := hpb.1.trans hpegB.symm
  have hlenC : bClear.sudo_5Board_9tally_len = (s.tally : Int) := by
    rw [hbookC.2.2.2.1, hbookM.2.2.1, ← hbPack, hpb.2.2.2.1, hlen0]
  have hhighC : bClear.sudo_5Board_4cost.sudo_5Costs_15control_highest = (s.high : Int) := by
    rw [hbookC.2.2.2.2.2.2.1, hbookM.2.2.2.2.2.1, ← hbPack, hpb.2.2.2.2.2.2.1,
      c.hHigh, hhighS]
  have hctrlC : bClear.sudo_5Board_4cost.sudo_5Costs_4ctrl =
      ((s.ctrl + s.tally : Nat) : Int) := by
    have hpack : dp.b.sudo_5Board_4cost.sudo_5Costs_4ctrl =
        ((s.ctrl + s.tally : Nat) : Int) := by
      rw [dp.hctrl, dp.hctrlN, hctrl0, hmEq]
    rw [hbookC.2.2.2.2.2.2.2.1, hbookM.2.2.2.2.2.2.1, ← hbPack, hpack]
  have ht0C : bClear.sudo_5Board_6tally0 = (s.t0 : Int) := by
    rw [hbookC.2.2.2.2.1, hbookM.2.2.2.1, ← hbPack, hpb.2.2.2.2.1, c.hT0, ht0]
  have hrowC : bClear.sudo_5Board_3row = embed (paintRed s.row s.t0 s.tally) := by
    rw [hbookC.1, hbookM.2.2.2.2.2.2.2, hRow]
  have hctrlN : bClear.sudo_5Board_1t.sudo_4Tier_7control = (base.control : Int) := by
    have htM : bMul.sudo_5Board_1t = bLoop.sudo_5Board_1t := by
      simpa [bMul] using
        mul_live_tier bLoop 5 6 c.g ys c.n c.k moves slides hole c.bench peak peakS cMul
          hH hD hops
    have htC : bClear.sudo_5Board_1t = bMul.sudo_5Board_1t := by
      simp [bClear, clearHeldBoard]
    rw [htC, htM, htier, c.hCtrlN, hcontrol]
  have hmaxC : bClear.sudo_5Board_4cost.sudo_5Costs_9tally_max =
      b.sudo_5Board_4cost.sudo_5Costs_9tally_max := by
    rw [clear_tmax, mulLive_tmax, ← hbPack, pegPack_tmax c c.m c.hm (Nat.le_refl _), hmax0]
  have ht0Cube : bCube.sudo_5Board_6tally0 = (s.t0 : Int) := by
    have h1 := cube_live_tally bClear 6 5 L c.n c.k movesC slidesC holeC c.bench
      peakC peakSC cCube hH5 hD5 hopsC
    exact h1.trans ht0C
  have ht0Red : bRed.sudo_5Board_6tally0 = (s.t0 : Int) := by
    have h1 := mul_live_tally bCube 5 6 base.x ysC c.n c.k mvCube slidesCube holeRed
      c.bench peakCube peakSRed (cMul + 1) hH6R hD6R hops0R
    exact h1.trans ht0Cube
  have htierCube : bCube.sudo_5Board_1t = bClear.sudo_5Board_1t := by
    simpa [bCube] using
      cube_live_tier bClear 6 5 L c.n c.k movesC slidesC holeC c.bench
        peakC peakSC cCube hH5 hD5 hopsC
  have htierRed : bRed.sudo_5Board_1t = bClear.sudo_5Board_1t := by
    have h1 := mul_live_tier bCube 5 6 base.x ysC c.n c.k mvCube slidesCube holeRed
      c.bench peakCube peakSRed (cMul + 1) hH6R hD6R hops0R
    exact h1.trans htierCube
  refine ⟨bLoop, bMul, bClear, bCube, bRed, hmulG, hclearEq, hcubeEq, hmulEq,
    ⟨mvRed, slRed, ?_, ?_, hmvRedLe, hslRedLe⟩,
    hlenC, ht0C, hrowC, hctrlN, hhighC, hctrlC, hmaxC,
    ht0Cube, ht0Red, htierCube, htierRed, hcubeAny, hmulAny⟩
  · simpa [ofNat_eq_natCast] using hmvRed
  · simpa [ofNat_eq_natCast] using hslRed



/-- Non-final rung, before `cube spare gap`. Doubles the red tally on the cleared
    gap board. The recorded high, the empty tail, and `tally_max` are read from
    `ClimbInvK`. The spare cube and the mul by the input on that doubled board
    are the corollary `red_doubled_cube_mul`; this theorem stops at the double.
    The i64 fits on the counter, the index, and the new length follow from
    `fitCtrl`, `fitControl`, and the running `rungCharge` bound. -/
theorem red_open_double {done rest : List Nat} {r : Nat} {b : Ecbs.Board}
    {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvK done (r :: rest) b s base)
    (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax)
    (hhome : s.onBench = false) (hrest : rest ≠ []) :
    ∃ (bLoop bMul bClear bD : Ecbs.Board),
      Ecbs.mul bLoop ((5 : Nat) : Int) ((5 : Nat) : Int) ((6 : Nat) : Int)
          false false false = .ok bMul ∧
      Ecbs.clear bMul ((5 : Nat) : Int) = .ok bClear ∧
      Ecbs.tally_double bClear = .ok bD := by
  have hge : 2 ≤ (r :: rest).length := by
    cases rest with
    | nil => exact absurd rfl hrest
    | cons _ _ => simp
  have hRoom : s.t0 + 2 * s.tally < base.control := h.openRoom hge
  have hHighEq : s.high = s.t0 + s.tally - 1 := h.highTop hm
  obtain ⟨tmax, hMax, hNote0⟩ := h.tmaxLt
  have hNote : tmax < 2 * s.tally := hNote0 hm
  have hRpos : 0 < base.R := by
    have hk := h.kLe
    rw [List.length_append, List.length_cons] at hk
    omega
  have hn0 : 0 < base.n := by rw [← h.hn]; exact h.shape.peg.n_pos
  have hFitL1 : FitsLen (2 * s.tally + 1) :=
    double_len_fit hn0 hRpos hT base.fitM
  have hFitM : FitsLen (2 * s.tally) := FitsLen.of_le hFitL1 (by omega)
  have hFitI : FitsLen (s.t0 + 2 * s.tally) :=
    (double_index_fit hRoom base.fitControl).1
  have hdone : done.length ≤ base.R := by
    have hk := h.kLe
    rw [List.length_append] at hk
    omega
  have hCtrlPair := double_ctrl_fit h.ctrlLe hT hdone base.fitCtrl
  have hFitC : FitsLen (s.ctrl + 3 * s.tally) := hCtrlPair.1
  obtain ⟨c, bLoop, ys, moves, slides, hole, peak, peakS, cMul, hH, hD, hops,
      _hcopy, _hsrc, _hg, hmEq, hn, _hkN, hbch, hpegB, _hys, hGap, _hX, _hFit, hMov,
      _hSFit, _hSLe, _hOp, hRow, _htier, _hmk, _h7, _hop0, _hOpsLe, hctrl0, hhighS,
      hcontrol, hlen0, hmax0, ht0, hmul⟩ :=
    mul_of_shape h hm hT hhome
  let bMul := mulNoLiveBoard bLoop 5 6 c.g ys c.n c.k moves slides hole c.bench
    peak peakS cMul hH hD hops
  have hKeep := mulLive_keep bLoop 5 6 5 c.g ys c.n c.k moves slides hole c.bench
    peak peakS cMul c.g hH hD hops (by decide) hGap.heldLt hGap.homeLt hGap.held hGap.arr
  let mvC := mulMovesNo (moves + 2 * pegCount (ys.take c.n)) c.g (ys.take c.n)
    c.n c.k c.bench
  have hmvC : bMul.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mvC := by
    simpa [bMul, mvC] using
      mul_live_moves bLoop 5 6 c.g ys c.n c.k moves slides hole c.bench peak peakS cMul
        hH hD hops
  have hfitN : FitsLen c.g.length := by rw [c.hlenx]; exact c.hf
  have hpegN : pegCount c.g ≤ c.n := by rw [← c.hlenx]; exact pegCount_le c.g
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
      have hadd := Nat.add_le_add hmvC_le hpegN
      rw [hmulC, hcn] at hadd
      exact hadd
    have h2 : moves + mulCharge base.n base.bench + base.n ≤
        base.moves0 + done.length * rungCharge base.n base.bench base.mMax +
          (base.n + s.tally * pegCharge base.n base.bench) +
          (mulCharge base.n base.bench + base.n) := by
      have hadd := Nat.add_le_add_right hMov (mulCharge base.n base.bench + base.n)
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
      have hadd := Nat.add_le_add_left hpiece
        (base.moves0 + done.length * rungCharge base.n base.bench base.mMax)
      simpa [Nat.add_assoc] using hadd
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
  let bClear := clearHeldBoard bMul 5 c.g mvC hKeep.homeLt hKeep.heldLt
  have hclearEq : Ecbs.clear bMul ((5 : Nat) : Int) = .ok bClear := by
    simpa [bClear, clearHeldBoard] using hclear
  have hbookM := mulLive_book bLoop 5 6 c.g ys c.n c.k moves slides hole c.bench
    peak peakS cMul hH hD hops
  have hbookC := clearHeld_book bMul 5 c.g mvC hKeep.homeLt hKeep.heldLt
  let dp := pegPack c c.m c.hm (Nat.le_refl _)
  have hpb := pegPack_board c c.m c.hm (Nat.le_refl _)
  have hbPack : dp.b = bLoop := hpb.1.trans hpegB.symm
  have hlenC : bClear.sudo_5Board_9tally_len = (s.tally : Int) := by
    rw [hbookC.2.2.2.1, hbookM.2.2.1, ← hbPack, hpb.2.2.2.1, hlen0]
  have hhighC : bClear.sudo_5Board_4cost.sudo_5Costs_15control_highest =
      ((s.t0 + s.tally - 1 : Nat) : Int) := by
    rw [hbookC.2.2.2.2.2.2.1, hbookM.2.2.2.2.2.1, ← hbPack, hpb.2.2.2.2.2.2.1,
      c.hHigh, hhighS, hHighEq]
  have hctrlC : bClear.sudo_5Board_4cost.sudo_5Costs_4ctrl =
      ((s.ctrl + s.tally : Nat) : Int) := by
    have hpack : dp.b.sudo_5Board_4cost.sudo_5Costs_4ctrl = ((s.ctrl + s.tally : Nat) : Int) := by
      rw [dp.hctrl, dp.hctrlN, hctrl0, hmEq]
    rw [hbookC.2.2.2.2.2.2.2.1, hbookM.2.2.2.2.2.2.1, ← hbPack, hpack]
  have ht0C : bClear.sudo_5Board_6tally0 = (s.t0 : Int) := by
    rw [hbookC.2.2.2.2.1, hbookM.2.2.2.1, ← hbPack, hpb.2.2.2.2.1, c.hT0, ht0]
  have hrowC : bClear.sudo_5Board_3row = embed (paintRed s.row s.t0 s.tally) := by
    rw [hbookC.1, hbookM.2.2.2.2.2.2.2, hRow]
  have hctrlN : bClear.sudo_5Board_1t.sudo_4Tier_7control = (base.control : Int) := by
    have htM : bMul.sudo_5Board_1t = bLoop.sudo_5Board_1t := by
      simpa [bMul] using
        mul_live_tier bLoop 5 6 c.g ys c.n c.k moves slides hole c.bench peak peakS cMul hH hD hops
    have htC : bClear.sudo_5Board_1t = bMul.sudo_5Board_1t := by
      simp [bClear, clearHeldBoard]
    rw [htC, htM, _htier, c.hCtrlN, hcontrol]
  have hmaxC : bClear.sudo_5Board_4cost.sudo_5Costs_9tally_max = (tmax : Int) := by
    rw [clear_tmax, mulLive_tmax, ← hbPack, pegPack_tmax c c.m c.hm (Nat.le_refl _),
      hmax0, hMax]
  have hopen : rest ≠ [] := hrest
  let xs := paintRed s.row s.t0 s.tally
  have hRed : ∀ j (hj : j < s.tally),
      xs[s.t0 + j]'(by
        simp [xs, paintRed_length]
        exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj s.t0) h.shape.seg.room) = 2 := by
    intro j hj
    simpa [xs] using paintRed_get_lo s.row s.t0 s.tally j hj h.shape.seg.room
  have hZero : ∀ k (hk : k < s.tally),
      xs[s.t0 + s.tally + k]'(by
        simp [xs, paintRed_length, h.shape.rowLen]
        omega) = 0 := by
    intro k hk
    have hlen : s.row.length = base.control := h.shape.rowLen
    have hix : s.t0 + (s.tally + k) < s.row.length := by
      rw [hlen]
      omega
    have hsrc := h.openZero hge k (Nat.le_of_lt hk)
      (by simpa [Nat.add_assoc] using hix)
    have hsrc' : s.row[s.t0 + s.tally + k]'(by omega) = 0 := hsrc
    have hget := paintRed_get_hi s.row s.t0 s.tally (s.t0 + s.tally + k)
      (by omega) (by omega)
    simpa [xs] using hget.trans hsrc'
  have hfitC0 : FitsLen (s.ctrl + s.tally + 2 * s.tally) :=
    FitsLen.of_le hFitC (by omega)
  have htally := tally_double_refines bClear xs s.t0 s.tally (s.ctrl + s.tally)
    (s.t0 + s.tally - 1) base.control tmax hm hlenC ht0C hrowC
    (by
      change s.t0 + 2 * s.tally ≤ (paintRed s.row s.t0 s.tally).length
      rw [paintRed_length, h.shape.rowLen]
      exact Nat.le_of_lt hRoom)
    hRed hZero hctrlN hhighC rfl hctrlC (Nat.le_of_lt hRoom) hFitI
    hfitC0 hFitM hmaxC hNote
  exact ⟨bLoop, bMul, bClear, _, hmul, hclearEq, htally⟩

/-- Non-final rung. `tally_double` changes only the row, the tally length, the
    control counter, the recorded high, and `tally_max`. The live spare cube and
    the live mul by the input on that doubled board are the final-rung results
    with those fields copied across. `tally_add_one` then lays the extra white
    peg at `t0 + 2 · tally`, which was empty, and the recorded high becomes
    that hole. -/
theorem red_doubled_cube_mul {done rest : List Nat} {r : Nat} {b : Ecbs.Board}
    {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvK done (r :: rest) b s base)
    (hm : 0 < s.tally) (hT : s.tally ≤ base.mMax)
    (hhome : s.onBench = false) (hrest : rest ≠ [])
    (hxLen : base.x.length = base.n) (hxT : allTritList base.x) :
    ∃ (bClear bD bCube bRed bAdd : Ecbs.Board),
      Ecbs.tally_double bClear = .ok bD ∧
      Ecbs.cube bD ((6 : Nat) : Int) ((5 : Nat) : Int) = .ok bCube ∧
      Ecbs.mul bCube ((5 : Nat) : Int) (base.xHome : Int) ((6 : Nat) : Int)
          false false false = .ok bRed ∧
      Ecbs.tally_add_one bRed = .ok bAdd ∧
      bAdd.sudo_5Board_4cost.sudo_5Costs_15control_highest =
        ((s.t0 + 2 * s.tally : Nat) : Int) ∧
      ∃ (hix : s.t0 + 2 * s.tally < bRed.sudo_5Board_3row.size),
        bRed.sudo_5Board_3row[s.t0 + 2 * s.tally] = 0 := by
  have hge : 2 ≤ (r :: rest).length := by
    cases rest with
    | nil => exact absurd rfl hrest
    | cons _ _ => simp
  have hRoom : s.t0 + 2 * s.tally < base.control := h.openRoom hge
  have hHighEq : s.high = s.t0 + s.tally - 1 := h.highTop hm
  obtain ⟨tmax, hMax, hNote0⟩ := h.tmaxLt
  have hNote : tmax < 2 * s.tally := hNote0 hm
  have hRpos : 0 < base.R := by
    have hk := h.kLe
    rw [List.length_append, List.length_cons] at hk
    omega
  have hn0 : 0 < base.n := by rw [← h.hn]; exact h.shape.peg.n_pos
  have hFitL1 : FitsLen (2 * s.tally + 1) :=
    double_len_fit hn0 hRpos hT base.fitM
  have hFitM : FitsLen (2 * s.tally) := FitsLen.of_le hFitL1 (by omega)
  have hFitI : FitsLen (s.t0 + 2 * s.tally) :=
    (double_index_fit hRoom base.fitControl).1
  have hdone : done.length ≤ base.R := by
    have hk := h.kLe
    rw [List.length_append] at hk
    omega
  have hCtrlPair := double_ctrl_fit h.ctrlLe hT hdone base.fitCtrl
  have hFitC : FitsLen (s.ctrl + 3 * s.tally) := hCtrlPair.1
  have hFitC1 : FitsLen (s.ctrl + s.tally + 2 * s.tally + 1) := hCtrlPair.2
  obtain ⟨_bLoop, _bMul, bClear, bCube0, bRed0, _hmul, _hclear, _hcube, _hred,
      _hbounds, hlenC, ht0C, hrowC, hctrlN, hhighC, hctrlC, hmaxC,
      ht0Cube, ht0Red, htierCube, htierRed, hcubeF, hmulF⟩ :=
    red_cube_mul h hm hT hhome hxLen hxT
  let xs := paintRed s.row s.t0 s.tally
  have hRed : ∀ j (hj : j < s.tally),
      xs[s.t0 + j]'(by
        simp [xs, paintRed_length]
        exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj s.t0) h.shape.seg.room) = 2 := by
    intro j hj
    simpa [xs] using paintRed_get_lo s.row s.t0 s.tally j hj h.shape.seg.room
  have hZero : ∀ k (hk : k < s.tally),
      xs[s.t0 + s.tally + k]'(by
        simp [xs, paintRed_length, h.shape.rowLen]
        omega) = 0 := by
    intro k hk
    have hlen : s.row.length = base.control := h.shape.rowLen
    have hix : s.t0 + (s.tally + k) < s.row.length := by
      rw [hlen]
      omega
    have hsrc := h.openZero hge k (Nat.le_of_lt hk)
      (by simpa [Nat.add_assoc] using hix)
    have hsrc' : s.row[s.t0 + s.tally + k]'(by omega) = 0 := hsrc
    have hget := paintRed_get_hi s.row s.t0 s.tally (s.t0 + s.tally + k)
      (by omega) (by omega)
    simpa [xs] using hget.trans hsrc'
  have hhighTop : bClear.sudo_5Board_4cost.sudo_5Costs_15control_highest =
      ((s.t0 + s.tally - 1 : Nat) : Int) := by
    rw [hhighC, hHighEq]
  have hmaxNat : bClear.sudo_5Board_4cost.sudo_5Costs_9tally_max = (tmax : Int) :=
    hmaxC.trans hMax
  have hfitC0 : FitsLen (s.ctrl + s.tally + 2 * s.tally) :=
    FitsLen.of_le hFitC (by omega)
  have htally := tally_double_refines bClear xs s.t0 s.tally (s.ctrl + s.tally)
    (s.t0 + s.tally - 1) base.control tmax hm hlenC ht0C hrowC
    (by
      change s.t0 + 2 * s.tally ≤ (paintRed s.row s.t0 s.tally).length
      rw [paintRed_length, h.shape.rowLen]
      exact Nat.le_of_lt hRoom)
    hRed hZero hctrlN hhighTop rfl hctrlC (Nat.le_of_lt hRoom) hFitI
    hfitC0 hFitM hmaxNat hNote
  let rowD := embed (paintOnes (paintOnes xs s.t0 s.tally) (s.t0 + s.tally) s.tally)
  let lenD : Int := Int.ofNat (2 * s.tally)
  let ctrlD : Int := Int.ofNat (s.ctrl + s.tally + 2 * s.tally)
  let highD : Int := ((s.t0 + 2 * s.tally - 1 : Nat) : Int)
  let maxD : Int := Int.ofNat (2 * s.tally)
  have htallyW : Ecbs.tally_double bClear =
      .ok (withTally bClear rowD lenD ctrlD highD maxD) := by
    simpa [rowD, lenD, ctrlD, highD, maxD, withTally] using htally
  let bD := withTally bClear rowD lenD ctrlD highD maxD
  let bCube := withTally bCube0 rowD lenD ctrlD highD maxD
  let bRed := withTally bRed0 rowD lenD ctrlD highD maxD
  let wide := paintOnes (paintOnes xs s.t0 s.tally) (s.t0 + s.tally) s.tally
  have hlenW : wide.length = base.control := by
    simp [wide, xs, paintOnes_length, paintRed_length, h.shape.rowLen]
  have hroom2 : s.t0 + s.tally + s.tally < base.control := by
    simpa [Nat.two_mul, Nat.add_assoc] using hRoom
  have hixW : s.t0 + s.tally + s.tally < wide.length := by
    rw [hlenW]; exact hroom2
  have hcell : wide[s.t0 + s.tally + s.tally]'hixW = 0 := by
    have hmid : (paintOnes xs s.t0 s.tally).length = base.control := by
      simp [xs, paintOnes_length, paintRed_length, h.shape.rowLen]
    have h1 := paintOnes_get_hi (paintOnes xs s.t0 s.tally) (s.t0 + s.tally) s.tally
      (s.t0 + s.tally + s.tally) (by omega) (by rw [hmid]; exact hroom2)
    have h2 := paintOnes_get_hi xs s.t0 s.tally (s.t0 + s.tally + s.tally)
      (by omega) (by simp [xs, paintRed_length, h.shape.rowLen]; exact hroom2)
    have h3 := paintRed_get_hi s.row s.t0 s.tally (s.t0 + s.tally + s.tally)
      (by omega) (by rw [h.shape.rowLen]; exact hroom2)
    have h4 := h.openZero hge s.tally (Nat.le_refl _)
      (by rw [h.shape.rowLen]; exact hroom2)
    rw [h1, h2, h3]
    exact h4
  have hrowR : bRed.sudo_5Board_3row = embed wide := by
    simp [bRed, withTally, rowD, wide]
  have hixR : s.t0 + 2 * s.tally < bRed.sudo_5Board_3row.size := by
    have hEq : s.t0 + 2 * s.tally = s.t0 + s.tally + s.tally := by
      rw [Nat.two_mul, Nat.add_assoc]
    rw [hEq, hrowR, size_embed]; exact hixW
  have hzeroR : bRed.sudo_5Board_3row[s.t0 + 2 * s.tally]'hixR = 0 := by
    have hEq : s.t0 + 2 * s.tally = s.t0 + s.tally + s.tally := by
      rw [Nat.two_mul, Nat.add_assoc]
    have hixA : s.t0 + s.tally + s.tally < bRed.sudo_5Board_3row.size := by
      rw [← hEq]; exact hixR
    have hget := get_embed wide (s.t0 + s.tally + s.tally) (hrowR ▸ hixA)
    have hidx := idx_get hrowR (s.t0 + s.tally + s.tally) hixA
    have hA : bRed.sudo_5Board_3row[s.t0 + s.tally + s.tally] = 0 := by
      rw [hidx, hget, hcell]
      rfl
    simpa [hEq] using hA
  have ht0R : bRed.sudo_5Board_6tally0 = (s.t0 : Int) := by
    simp [bRed, withTally, ht0Red]
  have hctrlR : bRed.sudo_5Board_1t.sudo_4Tier_7control = (base.control : Int) := by
    have h1 : bRed.sudo_5Board_1t = bRed0.sudo_5Board_1t := by
      simp [bRed, withTally]
    rw [h1, htierRed, hctrlN]
  have hlenR : bRed.sudo_5Board_9tally_len = ((2 * s.tally : Nat) : Int) := by
    simp [bRed, withTally, lenD]
  have hhighR : bRed.sudo_5Board_4cost.sudo_5Costs_15control_highest =
      ((s.t0 + 2 * s.tally - 1 : Nat) : Int) := by
    simp [bRed, withTally, highD]
  have hctrlNum : bRed.sudo_5Board_4cost.sudo_5Costs_4ctrl =
      ((s.ctrl + s.tally + 2 * s.tally : Nat) : Int) := by
    simp [bRed, withTally, ctrlD]
  have hmaxR : bRed.sudo_5Board_4cost.sudo_5Costs_9tally_max =
      ((2 * s.tally : Nat) : Int) := by
    simp [bRed, withTally, maxD]
  have hadd := tally_add_one_raise bRed s.t0 (2 * s.tally)
      (s.t0 + 2 * s.tally - 1) base.control
      (s.ctrl + s.tally + 2 * s.tally) (2 * s.tally)
      hlenR ht0R hixR hzeroR hctrlR hRoom hhighR (by omega) hFitI
      hctrlNum hFitC1 hFitL1 hmaxR (by omega)
  let bAdd := { bRed with
    sudo_5Board_3row := bRed.sudo_5Board_3row.set ⟨s.t0 + 2 * s.tally, hixR⟩ (1 : Int)
    sudo_5Board_9tally_len := Int.ofNat (2 * s.tally + 1)
    sudo_5Board_4cost := { bRed.sudo_5Board_4cost with
      sudo_5Costs_15control_highest := ((s.t0 + 2 * s.tally : Nat) : Int)
      sudo_5Costs_4ctrl := Int.ofNat (s.ctrl + s.tally + 2 * s.tally + 1)
      sudo_5Costs_9tally_max := Int.ofNat (2 * s.tally + 1) } }
  refine ⟨bClear, bD, bCube, bRed, bAdd, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [bD] using htallyW
  · simpa [bD, bCube] using hcubeF rowD lenD ctrlD highD maxD
  · simpa [bCube, bRed] using hmulF rowD lenD ctrlD highD maxD
  · simpa [bAdd] using hadd
  · simp [bAdd]
  · exact ⟨hixR, hzeroR⟩

/-- While rungs remain, the tally segment is white, so the scan in the next rung
    leaves the board unchanged. -/
theorem white_of_shape (b : Ecbs.Board) (s : ClimbModel) (rest : List Nat)
    (base : ClimbBudget) (hinv : ClimbInv b s) (hshape : ClimbShape b s rest base)
    (hrest : rest ≠ []) (hm : 0 < s.tally)
    (hfit : FitsLen (s.t0 + s.tally)) (hfitM : FitsLen s.tally) :
    SudoRt.runLoopOn (Int.ofNat 0) (fuelRange (Int.ofNat 0) (Int.ofNat (s.tally - 1)))
      (whiteStep b (Int.ofNat (s.tally - 1)))
      (fun j => .ok (b, j))
      (fun _ => .ok (b, (0 : Int))) =
    .ok (b, Int.ofNat (s.tally - 1)) := by
  have hfin : rest.isEmpty = false := by
    cases rest with
    | nil => exact absurd rfl hrest
    | cons _ _ => rfl
  have hwhite : ∀ j (hj : j < s.tally), s.row[s.t0 + j]'(by
      exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj s.t0) hshape.seg.room) = 1 := by
    intro j hj
    have hc := hshape.seg.colour j hj
    simpa [hfin] using hc
  exact white_scan_loop_refines b s.row s.t0 s.tally hm hinv.t0 hinv.row hshape.seg.room
    hwhite hfit hfitM

end EcbsLink2.Link2
