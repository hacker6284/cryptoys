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

theorem withHole_ladder (b : Ecbs.Board) (top : Int) :
    (withHole b top).sudo_5Board_6ladder = b.sudo_5Board_6ladder := by
  simp [withHole]

theorem topBody_no_ret (strip : Array Int) (i top : Int) (r : Ecbs.Board × Array Int) :
    topBody strip i top ≠ .ok (.ret r) := by
  intro h
  unfold topBody at h
  dsimp only at h
  cases hc : SudoRt.atL strip i with
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
    · have hzf : SudoRt.SEq.beq c (0 : Int) = false := eq_false_of_ne_true hz
      rw [hzf] at h
      simp only [Bool.not_false, if_true, pure_eq_ok] at h
      cases h

theorem topStep_no_ret (strip : Array Int) (toV : Int) (σ : Int × Int)
    (r : Ecbs.Board × Array Int) :
    topStep strip toV σ ≠ .ok (.ret r) := by
  intro h
  unfold topStep at h
  dsimp only at h
  by_cases hgt : σ.1 > toV
  · rw [if_pos hgt, pure_eq_ok] at h
    cases h
  · rw [if_neg hgt] at h
    cases hb : topBody strip σ.1 σ.2 with
    | error _ =>
      rw [hb] at h
      simp only [error_bind] at h
      cases h
    | ok fl =>
      rw [hb] at h
      simp only [ok_bind] at h
      cases fl with
      | ret r' =>
        exact topBody_no_ret strip σ.1 σ.2 r' hb
      | brk _ =>
        simp only [pure_eq_ok] at h
        cases h
      | cont _ =>
        dsimp only at h
        by_cases hlast : (σ.1 == toV) = true
        · simp only [if_pos hlast, pure_eq_ok] at h
          cases h
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

/-- The ladder carried by a peg-step result. `cont` and `brk` store the board in the
    state; `ret` stores it in the payload. -/
def pegLadder (fl : SudoRt.Flow (Array Int × Ecbs.Board) (Ecbs.Board × Array Int)) :
    Array Int :=
  match fl with
  | .cont fs => fs.2.sudo_5Board_6ladder
  | .brk fs => fs.2.sudo_5Board_6ladder
  | .ret rp => rp.1.sudo_5Board_6ladder

/-- The image writes after the range checks. They touch the strip and the move counter. -/
private theorem lane_after_assert
    (chk : Bool) (strip : Array Int) (d1 d2 c : Int) (b : Ecbs.Board)
    (fl : SudoRt.Flow (Array Int × Ecbs.Board) (Ecbs.Board × Array Int))
    (h : (do
        let _ ← SudoRt.sudoAssert chk 531
        let cur1 ← SudoRt.atL strip d1
        let sum1 ← SudoRt.addI cur1 c
        let r1 ← SudoRt.modI sum1 (3 : Int)
        let strip ← SudoRt.putL strip d1 r1
        let cur2 ← SudoRt.atL strip d2
        let sum2 ← SudoRt.addI cur2 c
        let r2 ← SudoRt.modI sum2 (3 : Int)
        let strip ← SudoRt.putL strip d2 r2
        let mv ← SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_5moves (2 : Int)
        pure (SudoRt.Flow.cont (ρ := Ecbs.Board × Array Int)
          (strip, ({ b with sudo_5Board_4cost :=
            { b.sudo_5Board_4cost with sudo_5Costs_5moves := mv } } : Ecbs.Board)))) = .ok fl) :
    pegLadder fl = b.sudo_5Board_6ladder := by
  cases ha : SudoRt.sudoAssert chk 531 with
  | error _ =>
    rw [ha] at h; simp only [error_bind] at h; cases h
  | ok _ =>
    rw [ha] at h; simp only [ok_bind] at h
    cases hc1 : SudoRt.atL strip d1 with
    | error _ =>
      rw [hc1] at h; simp only [error_bind] at h; cases h
    | ok cur1 =>
      rw [hc1] at h; simp only [ok_bind] at h
      cases hs1 : SudoRt.addI cur1 c with
      | error _ =>
        rw [hs1] at h; simp only [error_bind] at h; cases h
      | ok sum1 =>
        rw [hs1] at h; simp only [ok_bind] at h
        cases hr1 : SudoRt.modI sum1 (3 : Int) with
        | error _ =>
          rw [hr1] at h; simp only [error_bind] at h; cases h
        | ok r1 =>
          rw [hr1] at h; simp only [ok_bind] at h
          cases hp1 : SudoRt.putL strip d1 r1 with
          | error _ =>
            rw [hp1] at h; simp only [error_bind] at h; cases h
          | ok strip1 =>
            rw [hp1] at h; simp only [ok_bind] at h
            cases hc2 : SudoRt.atL strip1 d2 with
            | error _ =>
              rw [hc2] at h; simp only [error_bind] at h; cases h
            | ok cur2 =>
              rw [hc2] at h; simp only [ok_bind] at h
              cases hs2 : SudoRt.addI cur2 c with
              | error _ =>
                rw [hs2] at h; simp only [error_bind] at h; cases h
              | ok sum2 =>
                rw [hs2] at h; simp only [ok_bind] at h
                cases hr2 : SudoRt.modI sum2 (3 : Int) with
                | error _ =>
                  rw [hr2] at h; simp only [error_bind] at h; cases h
                | ok r2 =>
                  rw [hr2] at h; simp only [ok_bind] at h
                  cases hp2 : SudoRt.putL strip1 d2 r2 with
                  | error _ =>
                    rw [hp2] at h; simp only [error_bind] at h; cases h
                  | ok _ =>
                    rw [hp2] at h; simp only [ok_bind] at h
                    cases hm : SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_5moves (2 : Int) with
                    | error _ =>
                      rw [hm] at h; simp only [error_bind] at h; cases h
                    | ok _ =>
                      rw [hm] at h; simp only [ok_bind, pure_eq_ok] at h
                      cases h
                      rfl

/-- `d1` and `d2` are checked, then the image writes run. A failing check is a trap. -/
private theorem lane_from_range
    (d1 d2 e c : Int) (strip : Array Int) (b : Ecbs.Board)
    (fl : SudoRt.Flow (Array Int × Ecbs.Board) (Ecbs.Board × Array Int))
    (h : (do
        let g1 ← (if decide (d1 ≥ (0 : Int)) = true then
            pure (decide (d1 < e)) else pure false)
        let g2 ← (if g1 = true then pure (decide (d2 ≥ (0 : Int))) else pure false)
        let g3 ← (if g2 = true then pure (decide (d2 < e)) else pure false)
        let _ ← SudoRt.sudoAssert g3 531
        let cur1 ← SudoRt.atL strip d1
        let sum1 ← SudoRt.addI cur1 c
        let r1 ← SudoRt.modI sum1 (3 : Int)
        let strip ← SudoRt.putL strip d1 r1
        let cur2 ← SudoRt.atL strip d2
        let sum2 ← SudoRt.addI cur2 c
        let r2 ← SudoRt.modI sum2 (3 : Int)
        let strip ← SudoRt.putL strip d2 r2
        let mv ← SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_5moves (2 : Int)
        pure (SudoRt.Flow.cont (ρ := Ecbs.Board × Array Int)
          (strip, ({ b with sudo_5Board_4cost :=
            { b.sudo_5Board_4cost with sudo_5Costs_5moves := mv } } : Ecbs.Board)))) = .ok fl) :
    pegLadder fl = b.sudo_5Board_6ladder := by
  by_cases hg1 : decide (d1 ≥ (0 : Int)) = true
  · rw [if_pos hg1, pure_eq_ok, ok_bind] at h
    by_cases hlt : decide (d1 < e) = true
    · rw [if_pos hlt, pure_eq_ok, ok_bind] at h
      by_cases hg2 : decide (d2 ≥ (0 : Int)) = true
      · rw [if_pos hg2, pure_eq_ok, ok_bind] at h
        exact lane_after_assert (decide (d2 < e)) strip d1 d2 c b fl h
      · rw [if_neg hg2, pure_eq_ok, ok_bind] at h
        exact lane_after_assert false strip d1 d2 c b fl h
    · rw [if_neg hlt, pure_eq_ok, ok_bind] at h
      exact lane_after_assert false strip d1 d2 c b fl h
  · rw [if_neg hg1, pure_eq_ok, ok_bind] at h
    rw [if_neg Bool.false_ne_true, pure_eq_ok, ok_bind] at h
    exact lane_after_assert false strip d1 d2 c b fl h

/-- The geometry check, then the range checks and the image writes. -/
private theorem lane_peg_images
    (strip : Array Int) (e d1 d2 c n k : Int) (b : Ecbs.Board)
    (fl : SudoRt.Flow (Array Int × Ecbs.Board) (Ecbs.Board × Array Int))
    (h : (do
        let gap ← SudoRt.subI e n
        let chk ← (if SudoRt.SEq.beq d1 gap = true then do
            let nk ← SudoRt.subI n k
            let eg ← SudoRt.subI e nk
            pure (SudoRt.SEq.beq d2 eg)
          else pure false)
        let _ ← SudoRt.sudoAssert chk 530
        let g1 ← (if decide (d1 ≥ (0 : Int)) = true then
            pure (decide (d1 < e)) else pure false)
        let g2 ← (if g1 = true then pure (decide (d2 ≥ (0 : Int))) else pure false)
        let g3 ← (if g2 = true then pure (decide (d2 < e)) else pure false)
        let _ ← SudoRt.sudoAssert g3 531
        let cur1 ← SudoRt.atL strip d1
        let sum1 ← SudoRt.addI cur1 c
        let r1 ← SudoRt.modI sum1 (3 : Int)
        let strip ← SudoRt.putL strip d1 r1
        let cur2 ← SudoRt.atL strip d2
        let sum2 ← SudoRt.addI cur2 c
        let r2 ← SudoRt.modI sum2 (3 : Int)
        let strip ← SudoRt.putL strip d2 r2
        let mv ← SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_5moves (2 : Int)
        pure (SudoRt.Flow.cont (ρ := Ecbs.Board × Array Int)
          (strip, ({ b with sudo_5Board_4cost :=
            { b.sudo_5Board_4cost with sudo_5Costs_5moves := mv } } : Ecbs.Board)))) = .ok fl) :
    pegLadder fl = b.sudo_5Board_6ladder := by
  cases hgap : SudoRt.subI e n with
  | error _ =>
    rw [hgap] at h; simp only [error_bind] at h; cases h
  | ok gap =>
    rw [hgap] at h; simp only [ok_bind] at h
    by_cases hbeq : SudoRt.SEq.beq d1 gap = true
    · rw [if_pos hbeq] at h
      cases hnk : SudoRt.subI n k with
      | error _ =>
        rw [hnk] at h; simp only [error_bind] at h; cases h
      | ok nk =>
        rw [hnk] at h; simp only [ok_bind] at h
        cases heg : SudoRt.subI e nk with
        | error _ =>
          rw [heg] at h; simp only [error_bind] at h; cases h
        | ok eg =>
          rw [heg] at h; simp only [ok_bind, pure_eq_ok, ok_bind] at h
          cases hassert : SudoRt.sudoAssert (SudoRt.SEq.beq d2 eg) 530 with
          | error _ =>
            rw [hassert] at h; simp only [error_bind] at h; cases h
          | ok _ =>
            rw [hassert] at h; simp only [ok_bind] at h
            exact lane_from_range d1 d2 e c strip b fl h
    · rw [if_neg hbeq, pure_eq_ok, ok_bind] at h
      cases hassert : SudoRt.sudoAssert false 530 with
      | error _ =>
        rw [hassert] at h; simp only [error_bind] at h; cases h
      | ok _ =>
        rw [hassert] at h; simp only [ok_bind] at h
        exact lane_from_range d1 d2 e c strip b fl h

theorem lanePeg_ladder (strip : Array Int) (e : Int) (b : Ecbs.Board) (w ht r n k : Int)
    (fl : SudoRt.Flow (Array Int × Ecbs.Board) (Ecbs.Board × Array Int))
    (h : lanePeg strip e b w ht r n k = .ok fl) :
    pegLadder fl = b.sudo_5Board_6ladder := by
  unfold lanePeg at h
  dsimp only at h
  cases hc : SudoRt.atL strip e with
  | error _ =>
    rw [hc] at h; simp only [error_bind] at h; cases h
  | ok c =>
    rw [hc] at h; simp only [ok_bind] at h
    by_cases hz : SudoRt.SEq.beq c (0 : Int) = true
    · rw [hz] at h
      simp only [Bool.not_true, Bool.false_eq_true, if_false, pure_eq_ok] at h
      cases h
      rfl
    · have hzf : SudoRt.SEq.beq c (0 : Int) = false := eq_false_of_ne_true hz
      rw [hzf] at h
      simp only [Bool.not_false, if_true] at h
      cases hp0 : SudoRt.putL strip e (0 : Int) with
      | error _ =>
        rw [hp0] at h; simp only [error_bind] at h; cases h
      | ok strip0 =>
        rw [hp0] at h; simp only [ok_bind] at h
        cases hm1 : SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_5moves (1 : Int) with
        | error _ =>
          rw [hm1] at h; simp only [error_bind] at h; cases h
        | ok mv1 =>
          rw [hm1] at h; simp only [ok_bind] at h
          let b1 : Ecbs.Board :=
            { b with sudo_5Board_4cost :=
                { b.sudo_5Board_4cost with sudo_5Costs_5moves := mv1 } }
          cases hdiv : SudoRt.divI e w with
          | error _ =>
            rw [hdiv] at h; simp only [error_bind] at h; cases h
          | ok row =>
            rw [hdiv] at h; simp only [ok_bind] at h
            cases hmod : SudoRt.modI e w with
            | error _ =>
              rw [hmod] at h; simp only [error_bind] at h; cases h
            | ok col =>
              rw [hmod] at h; simp only [ok_bind] at h
              cases hsrow : SudoRt.subI row ht with
              | error _ =>
                rw [hsrow] at h; simp only [error_bind] at h; cases h
              | ok r1 =>
                rw [hsrow] at h; simp only [ok_bind] at h
                cases hc1 : SudoRt.addI col (1 : Int) with
                | error _ =>
                  rw [hc1] at h; simp only [error_bind] at h; cases h
                | ok c1 =>
                  rw [hc1] at h; simp only [ok_bind] at h
                  by_cases hwrap : SudoRt.SEq.beq c1 w = true
                  · rw [if_pos hwrap] at h
                    cases hr1 : SudoRt.addI r1 (1 : Int) with
                    | error _ =>
                      rw [hr1] at h; simp only [error_bind] at h; cases h
                    | ok r1' =>
                      rw [hr1] at h; simp only [ok_bind] at h
                      cases hm : SudoRt.mulI r1' w with
                      | error _ =>
                        rw [hm] at h; simp only [error_bind] at h; cases h
                      | ok m1 =>
                        rw [hm] at h; simp only [ok_bind] at h
                        cases hd1 : SudoRt.addI m1 (0 : Int) with
                        | error _ =>
                          rw [hd1] at h; simp only [error_bind] at h; cases h
                        | ok d1 =>
                          rw [hd1] at h; simp only [ok_bind] at h
                          cases hsr : SudoRt.subI row r with
                          | error _ =>
                            rw [hsr] at h; simp only [error_bind] at h; cases h
                          | ok rowR =>
                            rw [hsr] at h; simp only [ok_bind] at h
                            cases hm2 : SudoRt.mulI rowR w with
                            | error _ =>
                              rw [hm2] at h; simp only [error_bind] at h; cases h
                            | ok m2 =>
                              rw [hm2] at h; simp only [ok_bind] at h
                              cases hd2 : SudoRt.addI m2 col with
                              | error _ =>
                                rw [hd2] at h; simp only [error_bind] at h; cases h
                              | ok d2 =>
                                rw [hd2] at h; simp only [ok_bind] at h
                                exact (lane_peg_images strip0 e d1 d2 c n k b1 fl h).trans
                                  (by rfl : b1.sudo_5Board_6ladder = b.sudo_5Board_6ladder)
                  · rw [if_neg hwrap] at h
                    cases hm : SudoRt.mulI r1 w with
                    | error _ =>
                      rw [hm] at h; simp only [error_bind] at h; cases h
                    | ok m1 =>
                      rw [hm] at h; simp only [ok_bind] at h
                      cases hd1 : SudoRt.addI m1 c1 with
                      | error _ =>
                        rw [hd1] at h; simp only [error_bind] at h; cases h
                      | ok d1 =>
                        rw [hd1] at h; simp only [ok_bind] at h
                        cases hsr : SudoRt.subI row r with
                        | error _ =>
                          rw [hsr] at h; simp only [error_bind] at h; cases h
                        | ok rowR =>
                          rw [hsr] at h; simp only [ok_bind] at h
                          cases hm2 : SudoRt.mulI rowR w with
                          | error _ =>
                            rw [hm2] at h; simp only [error_bind] at h; cases h
                          | ok m2 =>
                            rw [hm2] at h; simp only [ok_bind] at h
                            cases hd2 : SudoRt.addI m2 col with
                            | error _ =>
                              rw [hd2] at h; simp only [error_bind] at h; cases h
                            | ok d2 =>
                              rw [hd2] at h; simp only [ok_bind] at h
                              exact (lane_peg_images strip0 e d1 d2 c n k b1 fl h).trans
                                (by rfl : b1.sudo_5Board_6ladder = b.sudo_5Board_6ladder)

/-- The ladder of a descending fold step. `ret` carries the board in the payload. -/
def foldFlowLadder
    (fl : SudoRt.Flow (Int × (Array Int × Ecbs.Board)) (Ecbs.Board × Array Int)) :
    Array Int :=
  match fl with
  | .cont s => s.2.2.sudo_5Board_6ladder
  | .brk s => s.2.2.sudo_5Board_6ladder
  | .ret rp => rp.1.sudo_5Board_6ladder

theorem laneFoldStep_ladder (w h r n k toV : Int)
    (σ : Int × (Array Int × Ecbs.Board))
    (fl : SudoRt.Flow (Int × (Array Int × Ecbs.Board)) (Ecbs.Board × Array Int))
    (hst : laneFoldStep w h r n k toV σ = .ok fl) :
    foldFlowLadder fl = σ.2.2.sudo_5Board_6ladder := by
  unfold laneFoldStep at hst
  dsimp only at hst
  by_cases hlt : σ.1 < toV
  · rw [if_pos hlt, pure_eq_ok] at hst
    cases hst
    rfl
  · rw [if_neg hlt] at hst
    cases hb : lanePeg σ.2.1 σ.1 σ.2.2 w h r n k with
    | error _ =>
      rw [hb] at hst; simp only [error_bind] at hst; cases hst
    | ok flb =>
      rw [hb] at hst; simp only [ok_bind] at hst
      have hpeg := lanePeg_ladder σ.2.1 σ.1 σ.2.2 w h r n k flb hb
      cases flb with
      | ret rp =>
        simp only [pure_eq_ok] at hst
        cases hst
        exact hpeg
      | brk fs =>
        simp only [pure_eq_ok] at hst
        cases hst
        exact hpeg
      | cont fs =>
        dsimp only at hst
        by_cases hlast : (σ.1 == toV) = true
        · simp only [if_pos hlast, pure_eq_ok] at hst
          cases hst
          exact hpeg
        · rw [if_neg hlast] at hst
          cases hi : SudoRt.subI σ.1 (1 : Int) with
          | error _ =>
            rw [hi] at hst; simp only [error_bind] at hst; cases hst
          | ok _ =>
            rw [hi] at hst; simp only [ok_bind, pure_eq_ok] at hst
            cases hst
            exact hpeg

/-- If every step keeps the ladder, the block's board is the board it started with.
    `after` returns that board; `onRet` returns the board a step returned. -/
theorem descBlock_ladder
    (step : Int × (Array Int × Ecbs.Board) →
      Except SudoRt.Trap (SudoRt.Flow (Int × (Array Int × Ecbs.Board)) (Ecbs.Board × Array Int)))
    (hf : ∀ σ fl, step σ = .ok fl →
      foldFlowLadder fl = σ.2.2.sudo_5Board_6ladder)
    (nI : Int) (strip : Array Int) (b b' : Ecbs.Board) (strip' : Array Int)
    (h : descBlock step nI strip b = .ok (b', strip')) :
    b'.sudo_5Board_6ladder = b.sudo_5Board_6ladder := by
  unfold descBlock at h
  dsimp only at h
  cases hfrom : SudoRt.subI (SudoRt.listLen strip) (1 : Int) with
  | error _ =>
    rw [hfrom] at h; simp only [error_bind] at h; cases h
  | ok fromV =>
    rw [hfrom] at h; simp only [ok_bind] at h
    rw [except_bind_pure] at h
    apply runLoopOn_ok_inv
        (P := fun σ : Int × (Array Int × Ecbs.Board) =>
          σ.2.2.sudo_5Board_6ladder = b.sudo_5Board_6ladder)
        (Q := fun p : Ecbs.Board × Array Int =>
          p.1.sudo_5Board_6ladder = b.sudo_5Board_6ladder)
        (h := h)
    · rfl
    · intro s s' hs hstep
      exact (hf s (.cont s') hstep).trans hs
    · intro s s' hs hstep
      exact (hf s (.brk s') hstep).trans hs
    · intro s rp p hs hstep hp
      simp only [pure_eq_ok] at hp
      cases hp
      exact (hf s (.ret rp) hstep).trans hs
    · intro s p hs hp
      simp only [pure_eq_ok] at hp
      cases hp
      exact hs

theorem lane_fold_ladder (b : Ecbs.Board) (strip : Array Int)
    (b' : Ecbs.Board) (strip' : Array Int)
    (h : Ecbs.lane_fold b strip = .ok (b', strip')) :
    b'.sudo_5Board_6ladder = b.sudo_5Board_6ladder := by
  rw [laneFold_emit] at h
  unfold laneFoldEmit at h
  dsimp only at h
  cases hlast : SudoRt.subI (SudoRt.listLen strip) (1 : Int) with
  | error _ =>
    rw [hlast] at h; simp only [error_bind] at h; cases h
  | ok last =>
    rw [hlast] at h; simp only [ok_bind] at h
    rw [except_bind_pure] at h
    have hsplit := runLoopOn_ok_after (0, (0 : Int))
      (if (0 : Int) > last then 1 else (last - 0).natAbs + 1)
      (topStep strip last)
      (fun σ =>
        if decide (σ.2 > b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole) = true then do
          SudoRt.sudoAssert (decide (σ.2 < b.sudo_5Board_1t.sudo_4Tier_8benchlen)) 515
          descBlock
            (laneFoldStep b.sudo_5Board_1t.sudo_4Tier_1w b.sudo_5Board_1t.sudo_4Tier_1h
              b.sudo_5Board_1t.sudo_4Tier_1r b.sudo_5Board_1t.sudo_4Tier_1n
              b.sudo_5Board_1t.sudo_4Tier_1k b.sudo_5Board_1t.sudo_4Tier_1n)
            b.sudo_5Board_1t.sudo_4Tier_1n strip (withHole b σ.2)
        else do
          SudoRt.sudoAssert (decide (σ.2 < b.sudo_5Board_1t.sudo_4Tier_8benchlen)) 515
          descBlock
            (laneFoldStep b.sudo_5Board_1t.sudo_4Tier_1w b.sudo_5Board_1t.sudo_4Tier_1h
              b.sudo_5Board_1t.sudo_4Tier_1r b.sudo_5Board_1t.sudo_4Tier_1n
              b.sudo_5Board_1t.sudo_4Tier_1k b.sudo_5Board_1t.sudo_4Tier_1n)
            b.sudo_5Board_1t.sudo_4Tier_1n strip b)
      (fun r => pure r) (b', strip') h
    cases hsplit with
    | inr hret =>
      obtain ⟨rp, _, s, hs⟩ := hret
      exact absurd hs (topStep_no_ret strip last s rp)
    | inl hex =>
      obtain ⟨σ, ha⟩ := hex
      dsimp only at ha
      let w := b.sudo_5Board_1t.sudo_4Tier_1w
      let ht := b.sudo_5Board_1t.sudo_4Tier_1h
      let rt := b.sudo_5Board_1t.sudo_4Tier_1r
      let n := b.sudo_5Board_1t.sudo_4Tier_1n
      let k := b.sudo_5Board_1t.sudo_4Tier_1k
      have hstep : ∀ s fl, laneFoldStep w ht rt n k n s = .ok fl →
          foldFlowLadder fl = s.2.2.sudo_5Board_6ladder :=
        fun s fl hs => laneFoldStep_ladder w ht rt n k n s fl hs
      by_cases hhi :
          decide (σ.2 > b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole) = true
      · rw [if_pos hhi] at ha
        cases hassert :
            SudoRt.sudoAssert (decide (σ.2 < b.sudo_5Board_1t.sudo_4Tier_8benchlen)) 515 with
        | error _ =>
          rw [hassert] at ha; simp only [error_bind] at ha; cases ha
        | ok _ =>
          rw [hassert] at ha; simp only [ok_bind] at ha
          exact (descBlock_ladder _ hstep n strip (withHole b σ.2) b' strip' ha).trans
            (withHole_ladder b σ.2)
      · rw [if_neg hhi] at ha
        cases hassert :
            SudoRt.sudoAssert (decide (σ.2 < b.sudo_5Board_1t.sudo_4Tier_8benchlen)) 515 with
        | error _ =>
          rw [hassert] at ha; simp only [error_bind] at ha; cases ha
        | ok _ =>
          rw [hassert] at ha; simp only [ok_bind] at ha
          exact descBlock_ladder _ hstep n strip b b' strip' ha

/-- One index of `settle`. The body only checks a bench cell; it never returns a board. -/
def settleIdx (b : Ecbs.Board) (toV i : Int) :
    Except SudoRt.Trap (SudoRt.Flow Int Ecbs.Board) :=
  do
    if i > toV then
      pure (SudoRt.Flow.brk (ρ := Ecbs.Board) i)
    else
      match ← (do
        let c ← SudoRt.atL b.sudo_5Board_5bench i
        let _ ← SudoRt.sudoAssertEq c (0 : Int) 414
        pure (SudoRt.Flow.cont (ρ := Ecbs.Board) ())) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Ecbs.Board) r)
      | .brk _ => pure (SudoRt.Flow.brk (ρ := Ecbs.Board) i)
      | .cont _ =>
        if i == toV then
          pure (SudoRt.Flow.brk (ρ := Ecbs.Board) i)
        else do
          let i' ← SudoRt.addI i (1 : Int)
          pure (SudoRt.Flow.cont (ρ := Ecbs.Board) i')

theorem settleIdx_no_ret (b : Ecbs.Board) (toV i : Int) (r : Ecbs.Board) :
    settleIdx b toV i ≠ .ok (.ret r) := by
  intro h
  unfold settleIdx at h
  dsimp only at h
  by_cases hgt : i > toV
  · rw [if_pos hgt, pure_eq_ok] at h
    cases h
  · rw [if_neg hgt] at h
    cases hc : SudoRt.atL b.sudo_5Board_5bench i with
    | error _ =>
      rw [hc] at h; simp only [error_bind] at h; cases h
    | ok c =>
      rw [hc] at h; simp only [ok_bind] at h
      cases ha : SudoRt.sudoAssertEq c (0 : Int) 414 with
      | error _ =>
        rw [ha] at h; simp only [error_bind] at h; cases h
      | ok _ =>
        rw [ha] at h; simp only [ok_bind, pure_eq_ok] at h
        by_cases hlast : (i == toV) = true
        · simp only [if_pos hlast, pure_eq_ok] at h
          cases h
        · rw [if_neg hlast] at h
          cases hi : SudoRt.addI i (1 : Int) with
          | error _ =>
            rw [hi] at h; simp only [error_bind] at h; cases h
          | ok _ =>
            rw [hi] at h; simp only [ok_bind, pure_eq_ok] at h
            cases h

private theorem settle_place_ladder (b : Ecbs.Board) (b' : Ecbs.Board)
    (h : (do
        let _ ← Ecbs.need_empty b b.sudo_5Board_8bench_to
        let v ← Ecbs.prefix b.sudo_5Board_5bench b.sudo_5Board_1t.sudo_4Tier_1n
        let n ← Ecbs.npeg v
        let m ← SudoRt.mulI (2 : Int) n
        let mv ← SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_5moves m
        let sl ← SudoRt.addI
          ({ b with sudo_5Board_4cost :=
              { b.sudo_5Board_4cost with sudo_5Costs_5moves := mv } } : Ecbs.Board).sudo_5Board_4cost.sudo_5Costs_6slides
          m
        let home ← SudoRt.putL
          ({ b with sudo_5Board_4cost :=
              { b.sudo_5Board_4cost with
                  sudo_5Costs_5moves := mv
                  sudo_5Costs_6slides := sl } } : Ecbs.Board).sudo_5Board_4home
          b.sudo_5Board_8bench_to v
        let held ← SudoRt.putL
          ({ b with
              sudo_5Board_4home := home
              sudo_5Board_4cost :=
                { b.sudo_5Board_4cost with
                    sudo_5Costs_5moves := mv
                    sudo_5Costs_6slides := sl } } : Ecbs.Board).sudo_5Board_4held
          b.sudo_5Board_8bench_to true
        let b ← Ecbs.note_peak
          ({ b with
              sudo_5Board_4home := home
              sudo_5Board_4held := held
              sudo_5Board_8bench_on := false
              sudo_5Board_4cost :=
                { b.sudo_5Board_4cost with
                    sudo_5Costs_5moves := mv
                    sudo_5Costs_6slides := sl } } : Ecbs.Board)
        pure b) = .ok b') :
    b'.sudo_5Board_6ladder = b.sudo_5Board_6ladder := by
  cases he : Ecbs.need_empty b b.sudo_5Board_8bench_to with
  | error _ =>
    rw [he] at h; simp only [error_bind] at h; cases h
  | ok _ =>
    rw [he] at h; simp only [ok_bind] at h
    cases hv : Ecbs.prefix b.sudo_5Board_5bench b.sudo_5Board_1t.sudo_4Tier_1n with
    | error _ =>
      rw [hv] at h; simp only [error_bind] at h; cases h
    | ok v =>
      rw [hv] at h; simp only [ok_bind] at h
      cases hn : Ecbs.npeg v with
      | error _ =>
        rw [hn] at h; simp only [error_bind] at h; cases h
      | ok n =>
        rw [hn] at h; simp only [ok_bind] at h
        cases hm : SudoRt.mulI (2 : Int) n with
        | error _ =>
          rw [hm] at h; simp only [error_bind] at h; cases h
        | ok m =>
          rw [hm] at h; simp only [ok_bind] at h
          cases hmv : SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_5moves m with
          | error _ =>
            rw [hmv] at h; simp only [error_bind] at h; cases h
          | ok mv =>
            rw [hmv] at h; simp only [ok_bind] at h
            cases hsl : SudoRt.addI
                ({ b with sudo_5Board_4cost :=
                    { b.sudo_5Board_4cost with sudo_5Costs_5moves := mv } } : Ecbs.Board).sudo_5Board_4cost.sudo_5Costs_6slides
                m with
            | error _ =>
              rw [hsl] at h; simp only [error_bind] at h; cases h
            | ok sl =>
              rw [hsl] at h; simp only [ok_bind] at h
              cases hh : SudoRt.putL
                  ({ b with sudo_5Board_4cost :=
                      { b.sudo_5Board_4cost with
                          sudo_5Costs_5moves := mv
                          sudo_5Costs_6slides := sl } } : Ecbs.Board).sudo_5Board_4home
                  b.sudo_5Board_8bench_to v with
              | error _ =>
                rw [hh] at h; simp only [error_bind] at h; cases h
              | ok home =>
                rw [hh] at h; simp only [ok_bind] at h
                cases hd : SudoRt.putL
                    ({ b with
                        sudo_5Board_4home := home
                        sudo_5Board_4cost :=
                          { b.sudo_5Board_4cost with
                              sudo_5Costs_5moves := mv
                              sudo_5Costs_6slides := sl } } : Ecbs.Board).sudo_5Board_4held
                    b.sudo_5Board_8bench_to true with
                | error _ =>
                  rw [hd] at h; simp only [error_bind] at h; cases h
                | ok held =>
                  rw [hd] at h; simp only [ok_bind] at h
                  cases hk : Ecbs.note_peak
                      ({ b with
                          sudo_5Board_4home := home
                          sudo_5Board_4held := held
                          sudo_5Board_8bench_on := false
                          sudo_5Board_4cost :=
                            { b.sudo_5Board_4cost with
                                sudo_5Costs_5moves := mv
                                sudo_5Costs_6slides := sl } } : Ecbs.Board) with
                  | error _ =>
                    rw [hk] at h; simp only [error_bind] at h; cases h
                  | ok _ =>
                    rw [hk] at h; simp only [ok_bind, pure_eq_ok] at h
                    cases h
                    exact (note_peak_ladder _ b' hk).trans rfl

/-- `settle` writes homes, the held flag, the counters, and the bench flag. -/
theorem settle_keeps : Keeps Ecbs.settle := by
  intro b b' h
  unfold Ecbs.settle at h
  dsimp only at h
  by_cases hon : b.sudo_5Board_8bench_on = true
  · rw [hon] at h
    simp only [Bool.not_true, Bool.false_eq_true, if_false] at h
    cases hsub : SudoRt.subI (SudoRt.listLen b.sudo_5Board_5bench) (1 : Int) with
    | error _ =>
      rw [hsub] at h; simp only [error_bind] at h; cases h
    | ok toV =>
      rw [hsub] at h; simp only [ok_bind] at h
      rw [except_bind_pure] at h
      conv at h =>
        pattern (fun i : Int => _)
        change settleIdx b toV
      have hsplit := runLoopOn_ok_after b.sudo_5Board_1t.sudo_4Tier_1n
        (if b.sudo_5Board_1t.sudo_4Tier_1n > toV then 1
          else (toV - b.sudo_5Board_1t.sudo_4Tier_1n).natAbs + 1)
        (settleIdx b toV)
        (fun _ =>
          (do
            let _ ← Ecbs.need_empty b b.sudo_5Board_8bench_to
            let v ← Ecbs.prefix b.sudo_5Board_5bench b.sudo_5Board_1t.sudo_4Tier_1n
            let n ← Ecbs.npeg v
            let m ← SudoRt.mulI (2 : Int) n
            let mv ← SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_5moves m
            let sl ← SudoRt.addI
              ({ b with sudo_5Board_4cost :=
                  { b.sudo_5Board_4cost with sudo_5Costs_5moves := mv } } : Ecbs.Board).sudo_5Board_4cost.sudo_5Costs_6slides
              m
            let home ← SudoRt.putL
              ({ b with sudo_5Board_4cost :=
                  { b.sudo_5Board_4cost with
                      sudo_5Costs_5moves := mv
                      sudo_5Costs_6slides := sl } } : Ecbs.Board).sudo_5Board_4home
              b.sudo_5Board_8bench_to v
            let held ← SudoRt.putL
              ({ b with
                  sudo_5Board_4home := home
                  sudo_5Board_4cost :=
                    { b.sudo_5Board_4cost with
                        sudo_5Costs_5moves := mv
                        sudo_5Costs_6slides := sl } } : Ecbs.Board).sudo_5Board_4held
              b.sudo_5Board_8bench_to true
            let b ← Ecbs.note_peak
              ({ b with
                  sudo_5Board_4home := home
                  sudo_5Board_4held := held
                  sudo_5Board_8bench_on := false
                  sudo_5Board_4cost :=
                    { b.sudo_5Board_4cost with
                        sudo_5Costs_5moves := mv
                        sudo_5Costs_6slides := sl } } : Ecbs.Board)
            pure b))
        (fun r => pure r) b' h
      cases hsplit with
      | inr hret =>
        obtain ⟨r, _, i, hi⟩ := hret
        exact absurd hi (settleIdx_no_ret b toV i r)
      | inl hex =>
        obtain ⟨_, ha⟩ := hex
        dsimp only at ha
        exact settle_place_ladder b b' ha
  · have hoff : b.sudo_5Board_8bench_on = false := eq_false_of_ne_true hon
    rw [hoff] at h
    simp only [Bool.not_false, if_true] at h
    exact keeps_pure b b' h

/-- The tail of `Ecbs.cube`: the comb-gap check, `lane_fold`, and `note_peak`. -/
private theorem cube_after_ladder (dst : Int) (b : Ecbs.Board) (strip : Array Int)
    (b' : Ecbs.Board)
    (h : (do
        let last ← SudoRt.subI b.sudo_5Board_1t.sudo_4Tier_1n (1 : Int)
        let span ← SudoRt.mulI (3 : Int) last
        let reach ← SudoRt.addI span b.sudo_5Board_1t.sudo_4Tier_7combgap
        let _ ← SudoRt.sudoAssert (decide (reach < b.sudo_5Board_1t.sudo_4Tier_8benchlen)) 614
        let folded ← Ecbs.lane_fold
          ({ b with sudo_5Board_8bench_on := true, sudo_5Board_8bench_to := dst } : Ecbs.Board) strip
        let b ← Ecbs.note_peak ({ folded.1 with sudo_5Board_5bench := folded.2 } : Ecbs.Board)
        pure b) = .ok b') :
    b'.sudo_5Board_6ladder = b.sudo_5Board_6ladder := by
  cases hlast : SudoRt.subI b.sudo_5Board_1t.sudo_4Tier_1n (1 : Int) with
  | error _ =>
    rw [hlast] at h; simp only [error_bind] at h; cases h
  | ok last =>
    rw [hlast] at h; simp only [ok_bind] at h
    cases hspan : SudoRt.mulI (3 : Int) last with
    | error _ =>
      rw [hspan] at h; simp only [error_bind] at h; cases h
    | ok span =>
      rw [hspan] at h; simp only [ok_bind] at h
      cases hreach : SudoRt.addI span b.sudo_5Board_1t.sudo_4Tier_7combgap with
      | error _ =>
        rw [hreach] at h; simp only [error_bind] at h; cases h
      | ok reach =>
        rw [hreach] at h; simp only [ok_bind] at h
        cases hassert :
            SudoRt.sudoAssert (decide (reach < b.sudo_5Board_1t.sudo_4Tier_8benchlen)) 614 with
        | error _ =>
          rw [hassert] at h; simp only [error_bind] at h; cases h
        | ok _ =>
          rw [hassert] at h; simp only [ok_bind] at h
          let bA : Ecbs.Board :=
            { b with sudo_5Board_8bench_on := true, sudo_5Board_8bench_to := dst }
          cases hf : Ecbs.lane_fold bA strip with
          | error _ =>
            rw [hf] at h; simp only [error_bind] at h; cases h
          | ok folded =>
            rw [hf] at h; simp only [ok_bind] at h
            cases folded with
            | mk bF stripF =>
              cases hk : Ecbs.note_peak
                  ({ bF with sudo_5Board_5bench := stripF } : Ecbs.Board) with
              | error _ =>
                rw [hk] at h; simp only [error_bind] at h; cases h
              | ok _ =>
                rw [hk] at h; simp only [ok_bind, pure_eq_ok] at h
                cases h
                exact (note_peak_ladder _ b' hk).trans
                  ((by rfl : ({ bF with sudo_5Board_5bench := stripF } : Ecbs.Board).sudo_5Board_6ladder
                      = bF.sudo_5Board_6ladder).trans
                    ((lane_fold_ladder bA strip bF stripF hf).trans (by rfl)))

theorem cube_board_keeps (dst src : Int) : Keeps (fun b => Ecbs.cube b dst src) := by
  intro b0 b' h
  unfold Ecbs.cube at h
  dsimp only at h
  cases hop : SudoRt.atL b0.sudo_5Board_4cost.sudo_5Costs_3ops Ecbs.op_cube with
  | error _ =>
    rw [hop] at h; simp only [error_bind] at h; cases h
  | ok c0 =>
    rw [hop] at h; simp only [ok_bind] at h
    cases hadd : SudoRt.addI c0 (1 : Int) with
    | error _ =>
      rw [hadd] at h; simp only [error_bind] at h; cases h
    | ok c1 =>
      rw [hadd] at h; simp only [ok_bind] at h
      cases hput : SudoRt.putL b0.sudo_5Board_4cost.sudo_5Costs_3ops Ecbs.op_cube c1 with
      | error _ =>
        rw [hput] at h; simp only [error_bind] at h; cases h
      | ok ops =>
        rw [hput] at h; simp only [ok_bind] at h
        let bOps : Ecbs.Board :=
          { b0 with sudo_5Board_4cost :=
              { b0.sudo_5Board_4cost with sudo_5Costs_3ops := ops } }
        cases hlog : Ecbs.log_op bOps with
        | error _ =>
          rw [hlog] at h; simp only [error_bind] at h; cases h
        | ok bL =>
          rw [hlog] at h; simp only [ok_bind] at h
          have hLL := (log_op_ladder bOps bL hlog).trans (by rfl : bOps.sudo_5Board_6ladder = b0.sudo_5Board_6ladder)
          cases hset : Ecbs.settle bL with
          | error _ =>
            rw [hset] at h; simp only [error_bind] at h; cases h
          | ok bS =>
            rw [hset] at h; simp only [ok_bind] at h
            have hLS := (settle_keeps bL bS hset).trans hLL
            cases hst : Ecbs.note_strict bS with
            | error _ =>
              rw [hst] at h; simp only [error_bind] at h; cases h
            | ok bN =>
              rw [hst] at h; simp only [ok_bind] at h
              have hLN := (note_strict_ladder bS bN hst).trans hLS
              cases hheld : SudoRt.atL bN.sudo_5Board_4held src with
              | error _ =>
                rw [hheld] at h; simp only [error_bind] at h; cases h
              | ok held =>
                rw [hheld] at h; simp only [ok_bind] at h
                cases hassert : SudoRt.sudoAssert held 605 with
                | error _ =>
                  rw [hassert] at h; simp only [error_bind] at h; cases h
                | ok _ =>
                  rw [hassert] at h; simp only [ok_bind] at h
                  cases hhome : SudoRt.atL bN.sudo_5Board_4home src with
                  | error _ =>
                    rw [hhome] at h; simp only [error_bind] at h; cases h
                  | ok v =>
                    rw [hhome] at h; simp only [ok_bind] at h
                    cases hph : SudoRt.putL bN.sudo_5Board_4held src false with
                    | error _ =>
                      rw [hph] at h; simp only [error_bind] at h; cases h
                    | ok heldA =>
                      rw [hph] at h; simp only [ok_bind] at h
                      cases hpa : SudoRt.putL
                          ({ bN with sudo_5Board_4held := heldA } : Ecbs.Board).sudo_5Board_4home
                          src (#[] : Array Int) with
                      | error _ =>
                        rw [hpa] at h; simp only [error_bind] at h; cases h
                      | ok homeA =>
                        rw [hpa] at h; simp only [ok_bind] at h
                        let bC : Ecbs.Board :=
                          { bN with sudo_5Board_4held := heldA, sudo_5Board_4home := homeA }
                        cases hfill : SudoRt.filledL bC.sudo_5Board_1t.sudo_4Tier_8benchlen (0 : Int) with
                        | error _ =>
                          rw [hfill] at h; simp only [error_bind] at h; cases h
                        | ok strip =>
                          rw [hfill] at h; simp only [ok_bind] at h
                          cases hsub : SudoRt.subI bC.sudo_5Board_1t.sudo_4Tier_1n (1 : Int) with
                          | error _ =>
                            rw [hsub] at h; simp only [error_bind] at h; cases h
                          | ok toV =>
                            rw [hsub] at h; simp only [ok_bind] at h
                            rw [except_bind_pure] at h
                            conv at h =>
                              pattern (fun σ : Int × (Array Int × Ecbs.Board) => _)
                              change combStep v toV
                            have hloop : b'.sudo_5Board_6ladder = bC.sudo_5Board_6ladder := by
                              apply comb_loop_ladder v toV (0 : Int)
                                (if (0 : Int) > toV then 1 else (toV - 0).natAbs + 1)
                                strip bC _ _ ?hafter ?hret b' h
                              · intro s a hs ha
                                exact (cube_after_ladder dst s.2.2 s.2.1 a ha).trans hs
                              · intro r a hr hp
                                simp only [pure_eq_ok] at hp
                                cases hp
                                exact hr
                            exact hloop.trans hLN

theorem colStep_ladder (a : Array Int) (i toV : Int) (mir : Bool)
    (σ : Int × (Array Int × Ecbs.Board))
    (fl : SudoRt.Flow (Int × (Array Int × Ecbs.Board)) Ecbs.Board)
    (hst : colStep a i toV mir σ = .ok fl) :
    match fl with
    | .cont s => s.2.2.sudo_5Board_6ladder = σ.2.2.sudo_5Board_6ladder
    | .brk s => s.2.2.sudo_5Board_6ladder = σ.2.2.sudo_5Board_6ladder
    | .ret r => r.sudo_5Board_6ladder = σ.2.2.sudo_5Board_6ladder := by
  unfold colStep at hst
  dsimp only at hst
  by_cases hgt : σ.1 > toV
  · rw [if_pos hgt, pure_eq_ok] at hst
    cases hst
    rfl
  · rw [if_neg hgt] at hst
    cases hb : layDo a σ.2.1 i σ.1 mir σ.2.2 with
    | error _ =>
      rw [hb] at hst; simp only [error_bind] at hst; cases hst
    | ok flb =>
      rw [hb] at hst; simp only [ok_bind] at hst
      have hlay := layDo_ladder a σ.2.1 i σ.1 mir σ.2.2 flb hb
      cases flb with
      | ret r =>
        simp only [pure_eq_ok] at hst
        cases hst
        exact hlay
      | brk fs =>
        simp only [pure_eq_ok] at hst
        cases hst
        exact hlay
      | cont fs =>
        dsimp only at hst
        by_cases hlast : (σ.1 == toV) = true
        · simp only [if_pos hlast, pure_eq_ok] at hst
          cases hst
          exact hlay
        · rw [if_neg hlast] at hst
          cases hj : SudoRt.addI σ.1 (1 : Int) with
          | error _ =>
            rw [hj] at hst; simp only [error_bind] at hst; cases hst
          | ok _ =>
            rw [hj] at hst; simp only [ok_bind, pure_eq_ok] at hst
            cases hst
            exact hlay

def rowFlowLadder (fl : SudoRt.Flow (Ecbs.Board × Array Int) Ecbs.Board) : Array Int :=
  match fl with
  | .cont p => p.1.sudo_5Board_6ladder
  | .brk p => p.1.sudo_5Board_6ladder
  | .ret r => r.sudo_5Board_6ladder

/-- One schoolbook row. A zero coefficient leaves the board; a nonzero one runs `colStep`. -/
theorem rowBody_ladder (a s : Array Int) (mirror : Bool) (nB i : Int)
    (b : Ecbs.Board) (strip : Array Int)
    (fl : SudoRt.Flow (Ecbs.Board × Array Int) Ecbs.Board)
    (hst : rowBody a s mirror nB i b strip = .ok fl) :
    rowFlowLadder fl = b.sudo_5Board_6ladder := by
  unfold rowBody at hst
  dsimp only at hst
  cases hc : SudoRt.atL s i with
  | error _ =>
    rw [hc] at hst; simp only [error_bind] at hst; cases hst
  | ok c =>
    rw [hc] at hst; simp only [ok_bind] at hst
    by_cases hz : SudoRt.SEq.beq c (0 : Int) = true
    · rw [hz] at hst
      simp only [Bool.not_true, Bool.false_eq_true, if_false, pure_eq_ok] at hst
      cases hst
      rfl
    · have hzf : SudoRt.SEq.beq c (0 : Int) = false := eq_false_of_ne_true hz
      rw [hzf] at hst
      simp only [Bool.not_false, if_true] at hst
      cases hm : SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_5moves (1 : Int) with
      | error _ =>
        rw [hm] at hst; simp only [error_bind] at hst; cases hst
      | ok mv =>
        rw [hm] at hst; simp only [ok_bind] at hst
        cases hto : SudoRt.subI nB (1 : Int) with
        | error _ =>
          rw [hto] at hst; simp only [error_bind] at hst; cases hst
        | ok toJ =>
          rw [hto] at hst; simp only [ok_bind] at hst
          rw [except_bind_pure] at hst
          let b1 := withMoves b mv
          let mir2 := !(SudoRt.SEq.beq (SudoRt.SEq.beq c (2 : Int)) mirror)
          apply runLoopOn_ok_inv
              (P := fun σ : Int × (Array Int × Ecbs.Board) =>
                σ.2.2.sudo_5Board_6ladder = b.sudo_5Board_6ladder)
              (Q := fun flq : SudoRt.Flow (Ecbs.Board × Array Int) Ecbs.Board =>
                rowFlowLadder flq = b.sudo_5Board_6ladder)
              (h := hst)
          · rfl
          · intro s0 s1 hs hstep
            have hcol := colStep_ladder a i toJ mir2 s0 (.cont s1) hstep
            exact hcol.trans hs
          · intro s0 s1 hs hstep
            have hcol := colStep_ladder a i toJ mir2 s0 (.brk s1) hstep
            exact hcol.trans hs
          · intro s0 r q hs hstep hq
            simp only [pure_eq_ok] at hq
            cases hq
            have hcol := colStep_ladder a i toJ mir2 s0 (.ret r) hstep
            exact hcol.trans hs
          · intro s0 q hs hq
            simp only [pure_eq_ok] at hq
            cases hq
            exact hs

theorem rowStep_ladder (a s : Array Int) (mirror : Bool) (nB toV : Int)
    (σ : Int × (Ecbs.Board × Array Int))
    (fl : SudoRt.Flow (Int × (Ecbs.Board × Array Int)) Ecbs.Board)
    (hst : rowStep a s mirror nB toV σ = .ok fl) :
    match fl with
    | .cont st => st.2.1.sudo_5Board_6ladder = σ.2.1.sudo_5Board_6ladder
    | .brk st => st.2.1.sudo_5Board_6ladder = σ.2.1.sudo_5Board_6ladder
    | .ret r => r.sudo_5Board_6ladder = σ.2.1.sudo_5Board_6ladder := by
  unfold rowStep at hst
  dsimp only at hst
  by_cases hlt : σ.1 < toV
  · rw [if_pos hlt, pure_eq_ok] at hst
    cases hst
    rfl
  · rw [if_neg hlt] at hst
    cases hb : rowBody a s mirror nB σ.1 σ.2.1 σ.2.2 with
    | error _ =>
      rw [hb] at hst; simp only [error_bind] at hst; cases hst
    | ok flb =>
      rw [hb] at hst; simp only [ok_bind] at hst
      have hrow := rowBody_ladder a s mirror nB σ.1 σ.2.1 σ.2.2 flb hb
      cases flb with
      | ret r =>
        simp only [pure_eq_ok] at hst
        cases hst
        exact hrow
      | brk fs =>
        simp only [pure_eq_ok] at hst
        cases hst
        exact hrow
      | cont fs =>
        dsimp only at hst
        by_cases hlast : (σ.1 == toV) = true
        · simp only [if_pos hlast, pure_eq_ok] at hst
          cases hst
          exact hrow
        · rw [if_neg hlast] at hst
          cases hi : SudoRt.subI σ.1 (1 : Int) with
          | error _ =>
            rw [hi] at hst; simp only [error_bind] at hst; cases hst
          | ok _ =>
            rw [hi] at hst; simp only [ok_bind, pure_eq_ok] at hst
            cases hst
            exact hrow

/-- Every schoolbook loop in `Ecbs.mul`. The stepper is `rowStep`; the tail is `after`. -/
theorem row_loop_ladder
    (a s : Array Int) (mirror : Bool) (nB toV j0 : Int) (fuel : Nat)
    (b : Ecbs.Board) (strip : Array Int)
    (after : Int × (Ecbs.Board × Array Int) → Except SudoRt.Trap Ecbs.Board)
    (onRet : Ecbs.Board → Except SudoRt.Trap Ecbs.Board)
    (hafter : ∀ st q,
      st.2.1.sudo_5Board_6ladder = b.sudo_5Board_6ladder →
        after st = .ok q → q.sudo_5Board_6ladder = b.sudo_5Board_6ladder)
    (hret : ∀ r q,
      r.sudo_5Board_6ladder = b.sudo_5Board_6ladder →
        onRet r = .ok q → q.sudo_5Board_6ladder = b.sudo_5Board_6ladder)
    (p : Ecbs.Board)
    (h : SudoRt.runLoopOn (j0, (b, strip)) fuel (rowStep a s mirror nB toV) after onRet = .ok p) :
    p.sudo_5Board_6ladder = b.sudo_5Board_6ladder := by
  apply runLoopOn_ok_inv
      (P := fun st : Int × (Ecbs.Board × Array Int) =>
        st.2.1.sudo_5Board_6ladder = b.sudo_5Board_6ladder)
      (Q := fun q : Ecbs.Board => q.sudo_5Board_6ladder = b.sudo_5Board_6ladder)
      (h := h)
  · rfl
  · intro st st' hs hstep
    exact (rowStep_ladder a s mirror nB toV st (.cont st') hstep).trans hs
  · intro st st' hs hstep
    exact (rowStep_ladder a s mirror nB toV st (.brk st') hstep).trans hs
  · intro st r q hs hstep hr
    exact hret r q ((rowStep_ladder a s mirror nB toV st (.ret r) hstep).trans hs) hr
  · intro st q hs ha
    exact hafter st q hs ha

end EcbsLink2.Link2
