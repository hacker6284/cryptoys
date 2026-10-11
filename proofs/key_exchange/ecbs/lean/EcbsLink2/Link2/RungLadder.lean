/-
  Park, copy, the comb, the schoolbook lay, doubling, and the extra peg return
  a board whose ladder array is the one they were given. Each `.ok` step is a
  `Keeps` fact. The white scan is already `white_loop_ladder`; its result is
  discarded. The cube loop's stepper is `combStep`.
-/
import EcbsLink2.Link2.LadderKeep
import EcbsLink2.Link2.Invert

namespace EcbsLink2.Link2

open MegaDreifach.Link2

theorem withMoves_ladder (b : Ecbs.Board) (m : Int) :
    (withMoves b m).sudo_5Board_6ladder = b.sudo_5Board_6ladder := rfl

/-- A comb step writes the strip and the move counter. -/
theorem combBody_ladder (v strip : Array Int) (i : Int) (b : Ecbs.Board)
    (fl : SudoRt.Flow (Array Int × Ecbs.Board) Ecbs.Board)
    (h : combBody v strip i b = .ok fl) :
    match fl with
    | .cont fs => fs.2.sudo_5Board_6ladder = b.sudo_5Board_6ladder
    | .brk fs => fs.2.sudo_5Board_6ladder = b.sudo_5Board_6ladder
    | .ret r => r.sudo_5Board_6ladder = b.sudo_5Board_6ladder := by
  unfold combBody at h
  dsimp only at h
  cases hc : SudoRt.atL v i with
  | error _ =>
    rw [hc] at h
    simp only [error_bind] at h
    cases h
  | ok c =>
    rw [hc] at h
    simp only [ok_bind] at h
    by_cases hz : SudoRt.SEq.beq c (0 : Int) = true
    · rw [hz] at h
      simp only [Bool.not_true, Bool.false_eq_true, if_false, pure_eq_ok] at h
      cases h
      rfl
    · have hzf : SudoRt.SEq.beq c (0 : Int) = false := eq_false_of_ne_true hz
      rw [hzf] at h
      simp only [Bool.not_false, if_true] at h
      cases hix : SudoRt.mulI (3 : Int) i with
      | error _ =>
        rw [hix] at h
        simp only [error_bind] at h
        cases h
      | ok ix =>
        rw [hix] at h
        simp only [ok_bind] at h
        cases hp : SudoRt.putL strip ix c with
          | error _ =>
            rw [hp] at h
            simp only [error_bind] at h
            cases h
          | ok _ =>
            rw [hp] at h
            simp only [ok_bind] at h
            cases hm : SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_5moves (2 : Int) with
            | error _ =>
              rw [hm] at h
              simp only [error_bind] at h
              cases h
            | ok _ =>
              rw [hm] at h
              simp only [ok_bind, pure_eq_ok] at h
              cases h
              rfl

theorem combStep_ladder (v : Array Int) (toV : Int)
    (σ : Int × (Array Int × Ecbs.Board))
    (fl : SudoRt.Flow (Int × (Array Int × Ecbs.Board)) Ecbs.Board)
    (h : combStep v toV σ = .ok fl) :
    match fl with
    | .cont s => s.2.2.sudo_5Board_6ladder = σ.2.2.sudo_5Board_6ladder
    | .brk s => s.2.2.sudo_5Board_6ladder = σ.2.2.sudo_5Board_6ladder
    | .ret r => r.sudo_5Board_6ladder = σ.2.2.sudo_5Board_6ladder := by
  unfold combStep at h
  dsimp only at h
  by_cases hgt : σ.1 > toV
  · rw [if_pos hgt, pure_eq_ok] at h
    cases h
    rfl
  · rw [if_neg hgt] at h
    cases hb : combBody v σ.2.1 σ.1 σ.2.2 with
    | error _ =>
      rw [hb] at h
      simp only [error_bind] at h
      cases h
    | ok flb =>
      rw [hb] at h
      simp only [ok_bind] at h
      have hbody := combBody_ladder v σ.2.1 σ.1 σ.2.2 flb hb
      cases flb with
      | ret r =>
        simp only [pure_eq_ok] at h
        cases h
        exact hbody
      | brk fs =>
        simp only [pure_eq_ok] at h
        cases h
        exact hbody
      | cont fs =>
        dsimp only at h
        by_cases hlast : (σ.1 == toV) = true
        · simp only [if_pos hlast, pure_eq_ok, toPure_eq_ok] at h
          cases h
          exact hbody
        · rw [if_neg hlast] at h
          cases hi : SudoRt.addI σ.1 (1 : Int) with
          | error _ =>
            rw [hi] at h
            simp only [error_bind] at h
            cases h
          | ok _ =>
            rw [hi] at h
            simp only [ok_bind, pure_eq_ok] at h
            cases h
            exact hbody

/-- One red-to-white peg. `tally_put` writes the control row. -/
theorem whitenStep_ladder (toV : Int) (σ : Int × Ecbs.Board)
    (fl : SudoRt.Flow (Int × Ecbs.Board) Ecbs.Board)
    (h : whitenStep toV σ = .ok fl) :
    match fl with
    | .cont s => s.2.sudo_5Board_6ladder = σ.2.sudo_5Board_6ladder
    | .brk s => s.2.sudo_5Board_6ladder = σ.2.sudo_5Board_6ladder
    | .ret r => r.sudo_5Board_6ladder = σ.2.sudo_5Board_6ladder := by
  unfold whitenStep at h
  dsimp only at h
  by_cases hgt : σ.1 > toV
  · rw [if_pos hgt, pure_eq_ok] at h
    cases h
    rfl
  · rw [if_neg hgt] at h
    cases hix : SudoRt.addI σ.2.sudo_5Board_6tally0 σ.1 with
    | error _ =>
      rw [hix] at h
      simp only [error_bind] at h
      cases h
    | ok ix =>
      rw [hix] at h
      simp only [ok_bind] at h
      cases hc : SudoRt.atL σ.2.sudo_5Board_3row ix with
      | error _ =>
        rw [hc] at h
        simp only [error_bind] at h
        cases h
      | ok c =>
        rw [hc] at h
        simp only [ok_bind] at h
        by_cases hred : SudoRt.SEq.beq c (2 : Int) = true
        · rw [if_pos hred] at h
          cases hp : Ecbs.tally_put σ.2 σ.1 (1 : Int) with
          | error _ =>
            rw [hp] at h
            simp only [error_bind] at h
            cases h
          | ok b1 =>
            rw [hp] at h
            simp only [ok_bind] at h
            cases hv : SudoRt.addI b1.sudo_5Board_4cost.sudo_5Costs_4ctrl (1 : Int) with
            | error _ =>
              rw [hv] at h
              simp only [error_bind] at h
              cases h
            | ok _ =>
              rw [hv] at h
              simp only [ok_bind, pure_eq_ok] at h
              have hput := tally_put_ladder σ.2 b1 σ.1 (1 : Int) hp
              by_cases hlast : (σ.1 == toV) = true
              · simp only [if_pos hlast, pure_eq_ok, toPure_eq_ok] at h
                cases h
                exact hput
              · rw [if_neg hlast] at h
                cases hj : SudoRt.addI σ.1 (1 : Int) with
                | error _ =>
                  rw [hj] at h
                  simp only [error_bind] at h
                  cases h
                | ok _ =>
                  rw [hj] at h
                  simp only [ok_bind, pure_eq_ok, toPure_eq_ok] at h
                  cases h
                  exact hput
        · have hbf : SudoRt.SEq.beq c (2 : Int) = false := eq_false_of_ne_true hred
          rw [hbf] at h
          simp only [Bool.false_eq_true, if_false, pure_eq_ok, toPure_eq_ok, ok_bind] at h
          by_cases hlast : (σ.1 == toV) = true
          · simp only [if_pos hlast, pure_eq_ok, toPure_eq_ok] at h
            cases h
            rfl
          · rw [if_neg hlast] at h
            cases hj : SudoRt.addI σ.1 (1 : Int) with
            | error _ =>
              rw [hj] at h
              simp only [error_bind] at h
              cases h
            | ok _ =>
              rw [hj] at h
              simp only [ok_bind, pure_eq_ok] at h
              cases h
              rfl

/-- One white peg in the empty half of `tally_double`. -/
theorem layStep_ladder (toV : Int) (σ : Int × Ecbs.Board)
    (fl : SudoRt.Flow (Int × Ecbs.Board) Ecbs.Board)
    (h : layStep toV σ = .ok fl) :
    match fl with
    | .cont s => s.2.sudo_5Board_6ladder = σ.2.sudo_5Board_6ladder
    | .brk s => s.2.sudo_5Board_6ladder = σ.2.sudo_5Board_6ladder
    | .ret r => r.sudo_5Board_6ladder = σ.2.sudo_5Board_6ladder := by
  unfold layStep at h
  dsimp only at h
  by_cases hgt : σ.1 > toV
  · rw [if_pos hgt, pure_eq_ok] at h
    cases h
    rfl
  · rw [if_neg hgt] at h
    cases hix : SudoRt.addI σ.2.sudo_5Board_6tally0 σ.1 with
    | error _ =>
      rw [hix] at h
      simp only [error_bind] at h
      cases h
    | ok ix =>
      rw [hix] at h
      simp only [ok_bind] at h
      cases hc : SudoRt.atL σ.2.sudo_5Board_3row ix with
      | error _ =>
        rw [hc] at h
        simp only [error_bind] at h
        cases h
      | ok c =>
        rw [hc] at h
        simp only [ok_bind] at h
        cases ha : SudoRt.sudoAssertEq c (Int.ofNat 0) 359 with
        | error _ =>
          rw [ha] at h
          simp only [error_bind] at h
          cases h
        | ok _ =>
          rw [ha] at h
          simp only [ok_bind] at h
          cases hp : Ecbs.tally_put σ.2 σ.1 (1 : Int) with
          | error _ =>
            rw [hp] at h
            simp only [error_bind] at h
            cases h
          | ok b1 =>
            rw [hp] at h
            simp only [ok_bind] at h
            cases hv : SudoRt.addI b1.sudo_5Board_4cost.sudo_5Costs_4ctrl (1 : Int) with
            | error _ =>
              rw [hv] at h
              simp only [error_bind] at h
              cases h
            | ok _ =>
              rw [hv] at h
              simp only [ok_bind, pure_eq_ok, toPure_eq_ok] at h
              have hput := tally_put_ladder σ.2 b1 σ.1 (1 : Int) hp
              by_cases hlast : (σ.1 == toV) = true
              · simp only [if_pos hlast, pure_eq_ok, toPure_eq_ok] at h
                cases h
                exact hput
              · rw [if_neg hlast] at h
                cases hj : SudoRt.addI σ.1 (1 : Int) with
                | error _ =>
                  rw [hj] at h
                  simp only [error_bind] at h
                  cases h
                | ok _ =>
                  rw [hj] at h
                  simp only [ok_bind, pure_eq_ok, toPure_eq_ok] at h
                  cases h
                  exact hput

/-- One schoolbook column. The board write is `withMoves`. -/
theorem layDo_ladder (a strip : Array Int) (i j : Int) (mir : Bool) (b : Ecbs.Board)
    (fl : SudoRt.Flow (Array Int × Ecbs.Board) Ecbs.Board)
    (h : layDo a strip i j mir b = .ok fl) :
    match fl with
    | .cont fs => fs.2.sudo_5Board_6ladder = b.sudo_5Board_6ladder
    | .brk fs => fs.2.sudo_5Board_6ladder = b.sudo_5Board_6ladder
    | .ret r => r.sudo_5Board_6ladder = b.sudo_5Board_6ladder := by
  unfold layDo at h
  dsimp only at h
  cases hd : SudoRt.atL a j with
  | error _ =>
    rw [hd] at h
    simp only [error_bind] at h
    cases h
  | ok d =>
    rw [hd] at h
    simp only [ok_bind] at h
    by_cases hz : SudoRt.SEq.beq d (0 : Int) = true
    · rw [hz] at h
      simp only [Bool.not_true, Bool.false_eq_true, if_false, pure_eq_ok] at h
      cases h
      rfl
    · have hzf : SudoRt.SEq.beq d (0 : Int) = false := eq_false_of_ne_true hz
      rw [hzf] at h
      simp only [Bool.not_false, if_true] at h
      cases mir with
      | true =>
        simp only [if_true] at h
        cases hf : Ecbs.flip d with
        | error _ =>
          rw [hf] at h
          simp only [error_bind] at h
          cases h
        | ok d' =>
          rw [hf] at h
          simp only [ok_bind] at h
          cases hi : SudoRt.addI i j with
          | error _ =>
            rw [hi] at h
            simp only [error_bind] at h
            cases h
          | ok ix =>
            rw [hi] at h
            simp only [ok_bind] at h
            cases hc : SudoRt.atL strip ix with
              | error _ =>
                rw [hc] at h
                simp only [error_bind] at h
                cases h
              | ok cur =>
                rw [hc] at h
                simp only [ok_bind] at h
                cases hs : SudoRt.addI cur d' with
                | error _ =>
                  rw [hs] at h
                  simp only [error_bind] at h
                  cases h
                | ok sum =>
                  rw [hs] at h
                  simp only [ok_bind] at h
                  cases hr : SudoRt.modI sum (3 : Int) with
                  | error _ =>
                    rw [hr] at h
                    simp only [error_bind] at h
                    cases h
                  | ok r =>
                    rw [hr] at h
                    simp only [ok_bind] at h
                    cases hp : SudoRt.putL strip ix r with
                    | error _ =>
                      rw [hp] at h
                      simp only [error_bind] at h
                      cases h
                    | ok _ =>
                      rw [hp] at h
                      simp only [ok_bind] at h
                      cases hm : SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_5moves (1 : Int) with
                      | error _ =>
                        rw [hm] at h
                        simp only [error_bind] at h
                        cases h
                      | ok _ =>
                        rw [hm] at h
                        simp only [ok_bind, pure_eq_ok] at h
                        cases h
                        rfl
      | false =>
        rw [if_neg Bool.false_ne_true] at h
        cases hi : SudoRt.addI i j with
        | error _ =>
          rw [hi] at h
          simp only [error_bind] at h
          cases h
        | ok ix =>
          rw [hi] at h
          simp only [ok_bind] at h
          cases hc : SudoRt.atL strip ix with
            | error _ =>
              rw [hc] at h
              simp only [error_bind] at h
              cases h
            | ok cur =>
              rw [hc] at h
              simp only [ok_bind] at h
              cases hs : SudoRt.addI cur d with
              | error _ =>
                rw [hs] at h
                simp only [error_bind] at h
                cases h
              | ok sum =>
                rw [hs] at h
                simp only [ok_bind] at h
                cases hr : SudoRt.modI sum (3 : Int) with
                | error _ =>
                  rw [hr] at h
                  simp only [error_bind] at h
                  cases h
                | ok r =>
                  rw [hr] at h
                  simp only [ok_bind] at h
                  cases hp : SudoRt.putL strip ix r with
                  | error _ =>
                    rw [hp] at h
                    simp only [error_bind] at h
                    cases h
                  | ok _ =>
                    rw [hp] at h
                    simp only [ok_bind] at h
                    cases hm : SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_5moves (1 : Int) with
                    | error _ =>
                      rw [hm] at h
                      simp only [error_bind] at h
                      cases h
                    | ok _ =>
                      rw [hm] at h
                      simp only [ok_bind, pure_eq_ok] at h
                      cases h
                      rfl

private theorem unpark_tail_ladder (b b' : Ecbs.Board)
    (h : (do
        let row ← SudoRt.putL b.sudo_5Board_3row b.sudo_5Board_9park_hole (0 : Int)
        let n ← SudoRt.negI (1 : Int)
        let v ← SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_4ctrl (2 : Int)
        pure ({ b with
          sudo_5Board_3row := row
          sudo_5Board_11parked_from := n
          sudo_5Board_4cost :=
            { b.sudo_5Board_4cost with sudo_5Costs_4ctrl := v } } : Ecbs.Board)) = .ok b') :
    b'.sudo_5Board_6ladder = b.sudo_5Board_6ladder := by
  cases hp : SudoRt.putL b.sudo_5Board_3row b.sudo_5Board_9park_hole (0 : Int) with
  | error _ =>
    rw [hp] at h
    simp only [error_bind] at h; cases h
  | ok row =>
    rw [hp] at h
    simp only [ok_bind] at h
    cases hn : SudoRt.negI (1 : Int) with
    | error _ =>
      rw [hn] at h
      simp only [error_bind] at h; cases h
    | ok n =>
      rw [hn] at h
      simp only [ok_bind] at h
      cases hv : SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_4ctrl (2 : Int) with
      | error _ =>
        rw [hv] at h
        simp only [error_bind] at h; cases h
      | ok _ =>
        rw [hv] at h
        simp only [ok_bind] at h
        cases h
        rfl

theorem unpark_keeps : Keeps Ecbs.unpark := by
  intro b b' h
  unfold Ecbs.unpark at h
  dsimp only at h
  by_cases hlt : decide (b.sudo_5Board_11parked_from < (0 : Int)) = true
  · rw [if_pos hlt] at h
    exact keeps_pure b b' h
  · rw [if_neg hlt] at h
    cases ha : SudoRt.atL b.sudo_5Board_3row b.sudo_5Board_9park_hole with
    | error _ =>
      rw [ha] at h
      simp only [error_bind] at h; cases h
    | ok c =>
      rw [ha] at h
      simp only [ok_bind] at h
      cases hs : Ecbs.set_control b b.sudo_5Board_11parked_from c with
      | error _ =>
        rw [hs] at h
        simp only [error_bind] at h; cases h
      | ok b1 =>
        rw [hs] at h
        simp only [ok_bind] at h
        exact (unpark_tail_ladder b1 b' h).trans
          (set_control_ladder b b1 b.sudo_5Board_11parked_from c hs)

private theorem park_tail_ladder (b1 : Ecbs.Board) (hole colour c : Int) (b' : Ecbs.Board)
    (h : (do
        let b2 ← Ecbs.set_control b1 b1.sudo_5Board_9park_hole colour
        let row ← SudoRt.putL b2.sudo_5Board_3row hole (0 : Int)
        let v ← SudoRt.addI b2.sudo_5Board_4cost.sudo_5Costs_4ctrl (2 : Int)
        let got ← SudoRt.atL row b2.sudo_5Board_9park_hole
        pure (got, { b2 with
          sudo_5Board_3row := row
          sudo_5Board_11parked_from := hole
          sudo_5Board_4cost :=
            { b2.sudo_5Board_4cost with sudo_5Costs_4ctrl := v } })) = .ok (c, b')) :
    b'.sudo_5Board_6ladder = b1.sudo_5Board_6ladder := by
  cases hs : Ecbs.set_control b1 b1.sudo_5Board_9park_hole colour with
  | error _ =>
    rw [hs] at h
    simp only [error_bind] at h; cases h
  | ok b2 =>
    rw [hs] at h
    simp only [ok_bind] at h
    cases hp : SudoRt.putL b2.sudo_5Board_3row hole (0 : Int) with
    | error _ =>
      rw [hp] at h
      simp only [error_bind] at h; cases h
    | ok row =>
      rw [hp] at h
      simp only [ok_bind] at h
      cases hv : SudoRt.addI b2.sudo_5Board_4cost.sudo_5Costs_4ctrl (2 : Int) with
      | error _ =>
        rw [hv] at h
        simp only [error_bind] at h; cases h
      | ok _ =>
        rw [hv] at h
        simp only [ok_bind] at h
        cases hg : SudoRt.atL row b2.sudo_5Board_9park_hole with
        | error _ =>
          rw [hg] at h
          simp only [error_bind] at h; cases h
        | ok _ =>
          rw [hg] at h
          simp only [ok_bind] at h
          cases h
          exact set_control_ladder b1 b2 b1.sudo_5Board_9park_hole colour hs

theorem park_ladder (b : Ecbs.Board) (hole c : Int) (b' : Ecbs.Board)
    (h : Ecbs.park b hole = .ok (c, b')) :
    b'.sudo_5Board_6ladder = b.sudo_5Board_6ladder := by
  unfold Ecbs.park at h
  dsimp only at h
  cases hu : Ecbs.unpark b with
  | error _ =>
    rw [hu] at h
    simp only [error_bind] at h; cases h
  | ok b1 =>
    rw [hu] at h
    simp only [ok_bind] at h
    have hlad1 : b1.sudo_5Board_6ladder = b.sudo_5Board_6ladder :=
      unpark_keeps b b1 hu
    cases ha : SudoRt.atL b1.sudo_5Board_3row hole with
    | error _ =>
      rw [ha] at h
      simp only [error_bind] at h; cases h
    | ok colour =>
      rw [ha] at h
      simp only [ok_bind] at h
      by_cases hbeq : SudoRt.SEq.beq colour (0 : Int) = true
      · rw [hbeq] at h
        simp only [Bool.not_true] at h
        rw [if_neg Bool.false_ne_true, pure_eq_ok, ok_bind] at h
        cases hs : SudoRt.sudoAssert false 294 with
        | error _ =>
          rw [hs] at h
          simp only [error_bind] at h; cases h
        | ok _ =>
          rw [hs] at h
          simp only [ok_bind] at h
          exact (park_tail_ladder b1 hole colour c b' h).trans hlad1
      · have hbf : SudoRt.SEq.beq colour (0 : Int) = false := Bool.eq_false_iff.mpr hbeq
        rw [hbf] at h
        simp only [Bool.not_false, if_true] at h
        cases hp : SudoRt.atL b1.sudo_5Board_3row b1.sudo_5Board_9park_hole with
        | error _ =>
          rw [hp] at h
          simp only [error_bind] at h; cases h
        | ok v =>
          rw [hp] at h
          simp only [ok_bind, pure_eq_ok, ok_bind] at h
          cases hs : SudoRt.sudoAssert (SudoRt.SEq.beq v (0 : Int)) 294 with
          | error _ =>
            rw [hs] at h
            simp only [error_bind] at h; cases h
          | ok _ =>
            rw [hs] at h
            simp only [ok_bind] at h
            exact (park_tail_ladder b1 hole colour c b' h).trans hlad1

theorem park_rung_keeps (r : Int) : Keeps (fun b => Ecbs.park_rung b r) := by
  intro b b' h
  unfold Ecbs.park_rung at h
  dsimp only at h
  cases hc : Ecbs.climb_holes b with
  | error _ =>
    rw [hc] at h
    simp only [error_bind] at h; cases h
  | ok holes =>
    rw [hc] at h
    simp only [ok_bind] at h
    cases ha : SudoRt.atL holes b.sudo_5Board_8rung_idx with
    | error _ =>
      rw [ha] at h
      simp only [error_bind] at h; cases h
    | ok hole =>
      rw [ha] at h
      simp only [ok_bind] at h
      cases hp : Ecbs.park b hole with
      | error _ =>
        rw [hp] at h
        simp only [error_bind] at h; cases h
      | ok p =>
        rw [hp] at h
        simp only [ok_bind] at h
        cases p with
        | mk got b1 =>
          dsimp only at h
          cases he : SudoRt.sudoAssertEq got r 305 with
          | error _ =>
            rw [he] at h
            simp only [error_bind] at h; cases h
          | ok _ =>
            rw [he] at h
            simp only [ok_bind] at h
            cases hi : SudoRt.addI b1.sudo_5Board_8rung_idx (1 : Int) with
            | error _ =>
              rw [hi] at h
              simp only [error_bind] at h; cases h
            | ok _ =>
              rw [hi] at h
              simp only [ok_bind, pure_eq_ok] at h
              cases h
              exact park_ladder b hole got b1 hp

theorem unpark_rung_keeps : Keeps Ecbs.unpark_rung := by
  intro b b' h
  unfold Ecbs.unpark_rung at h
  dsimp only at h
  cases hu : Ecbs.unpark b with
  | error _ =>
    rw [hu] at h
    simp only [error_bind] at h; cases h
  | ok b1 =>
    rw [hu] at h
    simp only [ok_bind, pure_eq_ok] at h
    cases h
    exact unpark_keeps b b1 hu

private theorem band_write_ladder (b : Ecbs.Board) (dst : Int) (s : Array Int) (b' : Ecbs.Board)
    (h : (do
        let ix := dst
        let home ← SudoRt.putL b.sudo_5Board_4home ix s
        let b := ({ b with sudo_5Board_4home := home } : Ecbs.Board)
        let ix := dst
        let held ← SudoRt.putL b.sudo_5Board_4held ix true
        let b := ({ b with sudo_5Board_4held := held } : Ecbs.Board)
        let n ← Ecbs.npeg s
        let mv ← SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_5moves n
        let b := ({ b with sudo_5Board_4cost :=
          { b.sudo_5Board_4cost with sudo_5Costs_5moves := mv } } : Ecbs.Board)
        let b ← Ecbs.note_peak b
        pure b) = .ok b') :
    b'.sudo_5Board_6ladder = b.sudo_5Board_6ladder := by
  dsimp only at h
  cases hh : SudoRt.putL b.sudo_5Board_4home dst s with
  | error _ =>
    rw [hh] at h
    simp only [error_bind] at h; cases h
  | ok home =>
    rw [hh] at h
    simp only [ok_bind] at h
    cases hd : SudoRt.putL
        ({ b with sudo_5Board_4home := home } : Ecbs.Board).sudo_5Board_4held dst true with
    | error _ =>
      rw [hd] at h
      simp only [error_bind] at h; cases h
    | ok held =>
      rw [hd] at h
      simp only [ok_bind] at h
      cases hn : Ecbs.npeg s with
      | error _ =>
        rw [hn] at h
        simp only [error_bind] at h; cases h
      | ok n =>
        rw [hn] at h
        simp only [ok_bind] at h
        cases hm : SudoRt.addI
            ({ { b with sudo_5Board_4home := home } with
                sudo_5Board_4held := held } : Ecbs.Board).sudo_5Board_4cost.sudo_5Costs_5moves
            n with
        | error _ =>
          rw [hm] at h
          simp only [error_bind] at h; cases h
        | ok mv =>
          rw [hm] at h
          simp only [ok_bind] at h
          let bN : Ecbs.Board :=
            { { { b with sudo_5Board_4home := home } with sudo_5Board_4held := held } with
              sudo_5Board_4cost :=
                { b.sudo_5Board_4cost with sudo_5Costs_5moves := mv } }
          cases hk : Ecbs.note_peak bN with
          | error _ =>
            rw [hk] at h
            simp only [error_bind] at h; cases h
          | ok _ =>
            rw [hk] at h
            simp only [ok_bind, pure_eq_ok] at h
            cases h
            exact (note_peak_ladder bN b' hk).trans rfl

private theorem flip_step_no_ret (toV : Int) (σ : Int × Array Int) (r : Ecbs.Board) :
    (do
      let i := σ.1
      let s := σ.2
      if i > toV then
        pure (SudoRt.Flow.brk (ρ := Ecbs.Board) (i, s))
      else
        match ← (do
          let c ← SudoRt.atL s i
          let f ← Ecbs.flip c
          let s ← SudoRt.putL s i f
          pure (SudoRt.Flow.cont (ρ := Ecbs.Board) s)) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Ecbs.Board) r)
        | .brk fs => pure (SudoRt.Flow.brk (ρ := Ecbs.Board) (i, fs))
        | .cont fs => do
            if i == toV then
              pure (SudoRt.Flow.brk (ρ := Ecbs.Board) (i, fs))
            else do
              let i' ← SudoRt.addI i (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Ecbs.Board) (i', fs))) ≠
      .ok (SudoRt.Flow.ret r) := by
  intro h
  dsimp only at h
  by_cases hgt : σ.1 > toV
  · rw [if_pos hgt, pure_eq_ok] at h
    cases h
  · rw [if_neg hgt] at h
    cases hc : SudoRt.atL σ.2 σ.1 with
    | error _ =>
      rw [hc] at h
      simp only [error_bind] at h; cases h
    | ok c =>
      rw [hc] at h
      simp only [ok_bind] at h
      cases hf : Ecbs.flip c with
      | error _ =>
        rw [hf] at h
        simp only [error_bind] at h; cases h
      | ok f =>
        rw [hf] at h
        simp only [ok_bind] at h
        cases hp : SudoRt.putL σ.2 σ.1 f with
        | error _ =>
          rw [hp] at h
          simp only [error_bind] at h; cases h
        | ok s' =>
          rw [hp] at h
          simp only [ok_bind, pure_eq_ok, map_ok] at h
          by_cases hbeq : (σ.1 == toV) = true
          · rw [if_pos hbeq] at h
            cases h
          · rw [if_neg hbeq] at h
            cases hi : SudoRt.addI σ.1 (1 : Int) with
            | error _ =>
              rw [hi, error_bind] at h
              cases h
            | ok _ =>
              rw [hi, ok_bind] at h
              cases h

theorem copy_band_keeps (dst src : Int) (mirror : Bool) :
    Keeps (fun b => Ecbs.copy_band b dst src mirror) := by
  intro b b' h
  unfold Ecbs.copy_band at h
  dsimp only at h
  cases hv : Ecbs.value b src with
  | error _ =>
    rw [hv] at h
    simp only [error_bind] at h; cases h
  | ok s =>
    rw [hv] at h
    simp only [ok_bind] at h
    cases he : Ecbs.need_empty b dst with
    | error _ =>
      rw [he] at h
      simp only [error_bind] at h; cases h
    | ok _ =>
      rw [he] at h
      simp only [ok_bind] at h
      cases mirror with
      | false =>
        exact band_write_ladder b dst s b' h
      | true =>
        simp only [if_true] at h
        cases hsub : SudoRt.subI (SudoRt.listLen s) (1 : Int) with
        | error _ =>
          rw [hsub] at h
          simp only [error_bind] at h; cases h
        | ok toV =>
          rw [hsub] at h
          simp only [ok_bind] at h
          rw [except_bind_pure] at h
          apply runLoopOn_ok_inv
            (P := fun _ => True)
            (Q := fun bd : Ecbs.Board => bd.sudo_5Board_6ladder = b.sudo_5Board_6ladder)
            (h := h)
          · exact trivial
          · exact fun _ _ _ _ => trivial
          · exact fun _ _ _ _ => trivial
          · intro σ r a _ hstep _
            exact absurd hstep (flip_step_no_ret toV σ r)
          · intro σ a _ ha
            exact band_write_ladder b dst σ.2 a ha

theorem tally_add_one_keeps : Keeps Ecbs.tally_add_one := by
  intro b b' h
  unfold Ecbs.tally_add_one at h
  dsimp only at h
  cases hi : SudoRt.addI b.sudo_5Board_6tally0 b.sudo_5Board_9tally_len with
  | error _ =>
    rw [hi] at h
    simp only [error_bind] at h; cases h
  | ok ix =>
    rw [hi] at h
    simp only [ok_bind] at h
    cases ha : SudoRt.atL b.sudo_5Board_3row ix with
    | error _ =>
      rw [ha] at h
      simp only [error_bind] at h; cases h
    | ok v =>
      rw [ha] at h
      simp only [ok_bind] at h
      cases hs : SudoRt.sudoAssertEq v (0 : Int) 367 with
      | error _ =>
        rw [hs] at h
        simp only [error_bind] at h; cases h
      | ok _ =>
        rw [hs] at h
        simp only [ok_bind] at h
        cases hp : Ecbs.tally_put b b.sudo_5Board_9tally_len (1 : Int) with
        | error _ =>
          rw [hp] at h
          simp only [error_bind] at h; cases h
        | ok b1 =>
          rw [hp] at h
          simp only [ok_bind] at h
          cases hl : SudoRt.addI b1.sudo_5Board_9tally_len (1 : Int) with
          | error _ =>
            rw [hl] at h
            simp only [error_bind] at h; cases h
          | ok n =>
            rw [hl] at h
            simp only [ok_bind] at h
            cases hc : SudoRt.addI
                ({ b1 with sudo_5Board_9tally_len := n } : Ecbs.Board).sudo_5Board_4cost.sudo_5Costs_4ctrl
                (1 : Int) with
            | error _ =>
              rw [hc] at h
              simp only [error_bind] at h; cases h
            | ok ctrl =>
              rw [hc] at h
              simp only [ok_bind] at h
              let bN : Ecbs.Board :=
                { { b1 with sudo_5Board_9tally_len := n } with
                  sudo_5Board_4cost :=
                    { b1.sudo_5Board_4cost with sudo_5Costs_4ctrl := ctrl } }
              cases hn : Ecbs.tally_note bN with
              | error _ =>
                rw [hn] at h
                simp only [error_bind] at h; cases h
              | ok _ =>
                rw [hn] at h
                simp only [ok_bind, pure_eq_ok] at h
                cases h
                exact (tally_note_ladder bN b' hn).trans (tally_put_ladder b b1 _ (1 : Int) hp)

/-- The comb loop keeps the ladder when `after` and `onRet` do, on the board
    the stepper hands them. -/
theorem comb_loop_ladder
    (v : Array Int) (toV j0 : Int) (fuel : Nat) (strip : Array Int) (b : Ecbs.Board)
    (after : Int × (Array Int × Ecbs.Board) → Except SudoRt.Trap Ecbs.Board)
    (onRet : Ecbs.Board → Except SudoRt.Trap Ecbs.Board)
    (hafter : ∀ s a,
      s.2.2.sudo_5Board_6ladder = b.sudo_5Board_6ladder →
        after s = .ok a → a.sudo_5Board_6ladder = b.sudo_5Board_6ladder)
    (hret : ∀ r a,
      r.sudo_5Board_6ladder = b.sudo_5Board_6ladder →
        onRet r = .ok a → a.sudo_5Board_6ladder = b.sudo_5Board_6ladder)
    (p : Ecbs.Board)
    (h : SudoRt.runLoopOn (j0, (strip, b)) fuel (combStep v toV) after onRet = .ok p) :
    p.sudo_5Board_6ladder = b.sudo_5Board_6ladder := by
  apply runLoopOn_ok_inv
      (P := fun s : Int × (Array Int × Ecbs.Board) =>
        s.2.2.sudo_5Board_6ladder = b.sudo_5Board_6ladder)
      (Q := fun a : Ecbs.Board => a.sudo_5Board_6ladder = b.sudo_5Board_6ladder)
      (h := h)
  · rfl
  · intro s s' hs hstep
    exact (combStep_ladder v toV s (.cont s') hstep).trans hs
  · intro s s' hs hstep
    exact (combStep_ladder v toV s (.brk s') hstep).trans hs
  · intro s r a hs hstep hr
    exact hret r a ((combStep_ladder v toV s (.ret r) hstep).trans hs) hr
  · intro s a hs ha
    exact hafter s a hs ha

theorem whiten_loop_ladder
    (toV j0 : Int) (fuel : Nat) (b : Ecbs.Board)
    (after : Int × Ecbs.Board → Except SudoRt.Trap Ecbs.Board)
    (onRet : Ecbs.Board → Except SudoRt.Trap Ecbs.Board)
    (hafter : ∀ s a,
      s.2.sudo_5Board_6ladder = b.sudo_5Board_6ladder →
        after s = .ok a → a.sudo_5Board_6ladder = b.sudo_5Board_6ladder)
    (hret : ∀ r a,
      r.sudo_5Board_6ladder = b.sudo_5Board_6ladder →
        onRet r = .ok a → a.sudo_5Board_6ladder = b.sudo_5Board_6ladder)
    (p : Ecbs.Board)
    (h : SudoRt.runLoopOn (j0, b) fuel (whitenStep toV) after onRet = .ok p) :
    p.sudo_5Board_6ladder = b.sudo_5Board_6ladder := by
  apply runLoopOn_ok_inv
      (P := fun s : Int × Ecbs.Board => s.2.sudo_5Board_6ladder = b.sudo_5Board_6ladder)
      (Q := fun a : Ecbs.Board => a.sudo_5Board_6ladder = b.sudo_5Board_6ladder)
      (h := h)
  · rfl
  · intro s s' hs hstep
    exact (whitenStep_ladder toV s (.cont s') hstep).trans hs
  · intro s s' hs hstep
    exact (whitenStep_ladder toV s (.brk s') hstep).trans hs
  · intro s r a hs hstep hr
    exact hret r a ((whitenStep_ladder toV s (.ret r) hstep).trans hs) hr
  · intro s a hs ha
    exact hafter s a hs ha

theorem lay_loop_ladder
    (toV j0 : Int) (fuel : Nat) (b : Ecbs.Board)
    (after : Int × Ecbs.Board → Except SudoRt.Trap Ecbs.Board)
    (onRet : Ecbs.Board → Except SudoRt.Trap Ecbs.Board)
    (hafter : ∀ s a,
      s.2.sudo_5Board_6ladder = b.sudo_5Board_6ladder →
        after s = .ok a → a.sudo_5Board_6ladder = b.sudo_5Board_6ladder)
    (hret : ∀ r a,
      r.sudo_5Board_6ladder = b.sudo_5Board_6ladder →
        onRet r = .ok a → a.sudo_5Board_6ladder = b.sudo_5Board_6ladder)
    (p : Ecbs.Board)
    (h : SudoRt.runLoopOn (j0, b) fuel (layStep toV) after onRet = .ok p) :
    p.sudo_5Board_6ladder = b.sudo_5Board_6ladder := by
  apply runLoopOn_ok_inv
      (P := fun s : Int × Ecbs.Board => s.2.sudo_5Board_6ladder = b.sudo_5Board_6ladder)
      (Q := fun a : Ecbs.Board => a.sudo_5Board_6ladder = b.sudo_5Board_6ladder)
      (h := h)
  · rfl
  · intro s s' hs hstep
    exact (layStep_ladder toV s (.cont s') hstep).trans hs
  · intro s s' hs hstep
    exact (layStep_ladder toV s (.brk s') hstep).trans hs
  · intro s r a hs hstep hr
    exact hret r a ((layStep_ladder toV s (.ret r) hstep).trans hs) hr
  · intro s a hs ha
    exact hafter s a hs ha

/-- The length write and `tally_note` after the second half of `tally_double`. -/
def tallyLayAfter (m : Int) (σ : Int × Ecbs.Board) : Except SudoRt.Trap Ecbs.Board :=
  do
    let b := σ.2
    let len ← SudoRt.mulI (2 : Int) m
    let b := ({ b with sudo_5Board_9tally_len := len } : Ecbs.Board)
    let b ← Ecbs.tally_note b
    pure b

/-- The second half of `tally_double`: lay white pegs, then record the doubled length. -/
def tallyDoubleAfter (m : Int) (σ : Int × Ecbs.Board) : Except SudoRt.Trap Ecbs.Board :=
  do
    let b := σ.2
    let two ← SudoRt.mulI (2 : Int) m
    let toV ← SudoRt.subI two (1 : Int)
    let fuel : Nat := if m > toV then 1 else (toV - m).natAbs + 1
    let out ← SudoRt.runLoopOn (m, b) fuel (layStep toV) (tallyLayAfter m) (fun r => pure r)
    pure out

theorem tallyLayAfter_ladder (m : Int) (s : Int × Ecbs.Board) (a : Ecbs.Board)
    (h : tallyLayAfter m s = .ok a) :
    a.sudo_5Board_6ladder = s.2.sudo_5Board_6ladder := by
  unfold tallyLayAfter at h
  dsimp only at h
  cases hm : SudoRt.mulI (2 : Int) m with
  | error _ =>
    rw [hm] at h
    simp only [error_bind] at h
    cases h
  | ok len =>
    rw [hm] at h
    simp only [ok_bind] at h
    cases hn : Ecbs.tally_note ({ s.2 with sudo_5Board_9tally_len := len } : Ecbs.Board) with
    | error _ =>
      rw [hn] at h
      simp only [error_bind] at h
      cases h
    | ok bN =>
      rw [hn] at h
      simp only [ok_bind, pure_eq_ok] at h
      cases h
      exact (tally_note_ladder _ a hn).trans rfl

theorem tallyDoubleAfter_ladder (m : Int) (s : Int × Ecbs.Board) (a : Ecbs.Board)
    (h : tallyDoubleAfter m s = .ok a) :
    a.sudo_5Board_6ladder = s.2.sudo_5Board_6ladder := by
  unfold tallyDoubleAfter at h
  dsimp only at h
  cases htwo : SudoRt.mulI (2 : Int) m with
  | error _ =>
    rw [htwo] at h
    simp only [error_bind] at h
    cases h
  | ok two =>
    rw [htwo] at h
    simp only [ok_bind] at h
    cases hsub : SudoRt.subI two (1 : Int) with
    | error _ =>
      rw [hsub] at h
      simp only [error_bind] at h
      cases h
    | ok toV =>
      rw [hsub] at h
      simp only [ok_bind] at h
      rw [except_bind_pure] at h
      apply lay_loop_ladder toV m _ s.2 (tallyLayAfter m) (fun r => pure r)
          ?after ?ret a h
      · intro s1 a1 hs ha
        exact (tallyLayAfter_ladder m s1 a1 ha).trans hs
      · intro r a1 hr hp
        simp only [pure_eq_ok] at hp
        cases hp
        exact hr

/-- `tally_double` writes the control row, the length, and the counter. -/
theorem tally_double_keeps : Keeps Ecbs.tally_double := by
  intro b0 b' h
  unfold Ecbs.tally_double at h
  dsimp only at h
  cases hsub : SudoRt.subI b0.sudo_5Board_9tally_len (1 : Int) with
  | error _ =>
    rw [hsub] at h
    simp only [error_bind] at h
    cases h
  | ok toV =>
    rw [hsub] at h
    simp only [ok_bind] at h
    rw [except_bind_pure] at h
    conv at h =>
      pattern (fun σ : Int × Ecbs.Board => _)
      change whitenStep toV
    conv at h =>
      pattern (fun σ : Int × Ecbs.Board => _)
      change tallyDoubleAfter b0.sudo_5Board_9tally_len
    apply whiten_loop_ladder toV (0 : Int) _ b0 (tallyDoubleAfter b0.sudo_5Board_9tally_len)
        (fun r => pure r) ?after ?ret b' h
    · intro s a hs ha
      exact (tallyDoubleAfter_ladder _ s a ha).trans hs
    · intro r a hr hp
      simp only [pure_eq_ok] at hp
      cases hp
      exact hr

private theorem clear_held_tail (b : Ecbs.Board) (home : Int) (b' : Ecbs.Board)
    (h : (do
        let held ← SudoRt.atL b.sudo_5Board_4held home
        let _ ← SudoRt.sudoAssert held 477
        let arr ← SudoRt.atL b.sudo_5Board_4home home
        let n ← Ecbs.npeg arr
        let mv ← SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_5moves n
        let b := ({ b with sudo_5Board_4cost :=
          { b.sudo_5Board_4cost with sudo_5Costs_5moves := mv } } : Ecbs.Board)
        let heldA ← SudoRt.putL b.sudo_5Board_4held home false
        let b := ({ b with sudo_5Board_4held := heldA } : Ecbs.Board)
        let homeA ← SudoRt.putL b.sudo_5Board_4home home (#[] : Array Int)
        pure ({ b with sudo_5Board_4home := homeA } : Ecbs.Board)) = .ok b') :
    b'.sudo_5Board_6ladder = b.sudo_5Board_6ladder := by
  dsimp only at h
  cases hh : SudoRt.atL b.sudo_5Board_4held home with
  | error _ =>
    rw [hh] at h
    simp only [error_bind] at h
    cases h
  | ok held =>
    rw [hh] at h
    simp only [ok_bind] at h
    cases ha : SudoRt.sudoAssert held 477 with
    | error _ =>
      rw [ha] at h
      simp only [error_bind] at h
      cases h
    | ok _ =>
      rw [ha] at h
      simp only [ok_bind] at h
      cases hv : SudoRt.atL b.sudo_5Board_4home home with
      | error _ =>
        rw [hv] at h
        simp only [error_bind] at h
        cases h
      | ok arr =>
        rw [hv] at h
        simp only [ok_bind] at h
        cases hn : Ecbs.npeg arr with
        | error _ =>
          rw [hn] at h
          simp only [error_bind] at h
          cases h
        | ok n =>
          rw [hn] at h
          simp only [ok_bind] at h
          cases hm : SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_5moves n with
          | error _ =>
            rw [hm] at h
            simp only [error_bind] at h
            cases h
          | ok mv =>
            rw [hm] at h
            simp only [ok_bind] at h
            cases hd : SudoRt.putL
                ({ b with sudo_5Board_4cost :=
                    { b.sudo_5Board_4cost with sudo_5Costs_5moves := mv } } : Ecbs.Board).sudo_5Board_4held
                home false with
            | error _ =>
              rw [hd] at h
              simp only [error_bind] at h
              cases h
            | ok heldA =>
              rw [hd] at h
              simp only [ok_bind] at h
              cases hp : SudoRt.putL
                  ({ { b with sudo_5Board_4cost :=
                        { b.sudo_5Board_4cost with sudo_5Costs_5moves := mv } } with
                      sudo_5Board_4held := heldA } : Ecbs.Board).sudo_5Board_4home
                  home (#[] : Array Int) with
              | error _ =>
                rw [hp] at h
                simp only [error_bind] at h
                cases h
              | ok _ =>
                rw [hp] at h
                simp only [ok_bind, pure_eq_ok] at h
                cases h
                rfl

private theorem clear_from_assert (b : Ecbs.Board) (home : Int) (held : Bool) (b' : Ecbs.Board)
    (h : (do
        let _ ← SudoRt.sudoAssert held 477
        let arr ← SudoRt.atL b.sudo_5Board_4home home
        let n ← Ecbs.npeg arr
        let mv ← SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_5moves n
        let heldA ← SudoRt.putL b.sudo_5Board_4held home false
        let homeA ← SudoRt.putL b.sudo_5Board_4home home (#[] : Array Int)
        pure ({ b with
          sudo_5Board_4home := homeA
          sudo_5Board_4held := heldA
          sudo_5Board_4cost :=
            { b.sudo_5Board_4cost with sudo_5Costs_5moves := mv } } : Ecbs.Board)) = .ok b') :
    b'.sudo_5Board_6ladder = b.sudo_5Board_6ladder := by
  cases ha : SudoRt.sudoAssert held 477 with
  | error _ =>
    rw [ha] at h
    simp only [error_bind] at h
    cases h
  | ok _ =>
    rw [ha] at h
    simp only [ok_bind] at h
    cases hv : SudoRt.atL b.sudo_5Board_4home home with
    | error _ =>
      rw [hv] at h
      simp only [error_bind] at h
      cases h
    | ok arr =>
      rw [hv] at h
      simp only [ok_bind] at h
      cases hn : Ecbs.npeg arr with
      | error _ =>
        rw [hn] at h
        simp only [error_bind] at h
        cases h
      | ok n =>
        rw [hn] at h
        simp only [ok_bind] at h
        cases hm : SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_5moves n with
        | error _ =>
          rw [hm] at h
          simp only [error_bind] at h
          cases h
        | ok mv =>
          rw [hm] at h
          simp only [ok_bind] at h
          cases hd : SudoRt.putL b.sudo_5Board_4held home false with
          | error _ =>
            rw [hd] at h
            simp only [error_bind] at h
            cases h
          | ok heldA =>
            rw [hd] at h
            simp only [ok_bind] at h
            cases hp : SudoRt.putL b.sudo_5Board_4home home (#[] : Array Int) with
            | error _ =>
              rw [hp] at h
              simp only [error_bind] at h
              cases h
            | ok _ =>
              rw [hp] at h
              simp only [ok_bind, pure_eq_ok] at h
              cases h
              rfl

/-- `clear` writes a home, the held flag, the move counter, or the bench flag. -/
theorem clear_board_keeps (home : Int) : Keeps (fun b => Ecbs.clear b home) := by
  intro b b' h
  unfold Ecbs.clear at h
  dsimp only at h
  by_cases hon : b.sudo_5Board_8bench_on = true
  · rw [if_pos hon, pure_eq_ok, ok_bind] at h
    by_cases hto : SudoRt.SEq.beq b.sudo_5Board_8bench_to home = true
    · rw [if_pos hto] at h
      cases hh : SudoRt.atL b.sudo_5Board_4held home with
      | error _ =>
        rw [hh] at h
        simp only [error_bind] at h
        cases h
      | ok held =>
        rw [hh] at h
        simp only [ok_bind, pure_eq_ok, ok_bind] at h
        by_cases hem : (!held) = true
        · rw [if_pos hem] at h
          cases hn : Ecbs.npeg b.sudo_5Board_5bench with
          | error _ =>
            rw [hn] at h
            simp only [error_bind] at h
            cases h
          | ok n =>
            rw [hn] at h
            simp only [ok_bind] at h
            cases hm : SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_5moves n with
            | error _ =>
              rw [hm] at h
              simp only [error_bind] at h
              cases h
            | ok _ =>
              rw [hm] at h
              simp only [ok_bind, pure_eq_ok] at h
              cases h
              rfl
        · rw [if_neg hem] at h
          exact clear_from_assert b home held b' h
    · rw [if_neg hto, pure_eq_ok, ok_bind] at h
      simp only [Bool.false_eq_true, if_false, pure_eq_ok, ok_bind] at h
      exact clear_held_tail b home b' h
  · rw [if_neg hon] at h
    simp only [pure_eq_ok, ok_bind, Bool.false_eq_true, if_false] at h
    exact clear_held_tail b home b' h

end EcbsLink2.Link2
